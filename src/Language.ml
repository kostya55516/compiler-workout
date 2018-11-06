(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                              
        
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let fill_and_enter st params locals args =
          let st                    = State.enter st (params @ locals) in
          let update st (p, a)      = State.update p a st in
          List.fold_left update st (List.combine params args)


    let rec eval env ((st, i, o, r) as conf) expr =      
      match expr with
      | Const n -> n, (st, i, o, Some n)
      | Var   x -> let n = State.eval st x in n, (st, i, o, Some n)
      | Binop (op, x, y) -> 
        let a, conf = eval env conf x in
        let b, conf = eval env conf y in
        let n       = to_func op a b in
        n, (st, i, o, Some n)
      | Call (name, exps) ->
          let eval_list exp (ags, c) = let a, c = eval env c exp in (a::ags, c) in
          let args, conf             = List.fold_right eval_list exps ([], conf) in
          let st', i', o', Some r'   = env#definition env name args conf in
          r', (State.leave st' st, i', o', Some r')

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)

    let binop op x y = Binop (op, x, y)

    ostap (
      expr:
        !(Util.expr
           (fun x -> x)
           [|
             `Lefta , [ostap ("!!"), (binop "!!")];
             `Lefta , [ostap ("&&"), (binop "&&")];
             `Nona  , [ostap ("<="), (binop "<=");
                       ostap (">="), (binop ">=");
                       ostap ("<"), (binop "<");
                       ostap (">"), (binop ">")];
             `Nona  , [ostap ("=="), (binop "==");
                       ostap ("!="), (binop "!=")];
             `Lefta , [ostap ("+"), (binop "+");
                       ostap ("-"), (binop "-")];
             `Lefta , [ostap ("*"), (binop "*");
                       ostap ("/"), (binop "/");
                       ostap ("%"), (binop "%")]
           |]
           primary
         );
      
      func: fname:IDENT "(" a:args ")" { Call (fname, a) };

      args:
        e:expr "," a:args   { e :: a }
      | e:expr              { [e] }
      | empty               { [] }
      ;

      primary: func | x:IDENT {Var x} | n:DECIMAL {Const n}  | -"(" expr -")";

      parse: expr
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    
    let rec eval env ((st, i, o, r) as conf) k stmt =
      let (<>) s1 s2 = if s2 == Skip then s1 else Seq (s1, s2) in
      match stmt with
      | Skip -> if k == Skip then conf else eval env conf Skip k
      | Assign (s, exp) -> 
        let n, (st, i, o, r) = Expr.eval env conf exp in
        let st               = State.update s n st in
        eval env (st, i, o, r) Skip k
      | Write exp -> 
        let n, (st, i, o, r) = Expr.eval env conf exp in
        eval env (st, i, o @ [n], r) Skip k
      | Read s -> (
        match i with
        | n::i -> eval env ((State.update s n st), i, o, r) Skip k
        | _ -> failwith "Nothig to read"
      )
      | Seq (s1, s2) -> eval env conf (s2 <> k) s1    
      | If (exp, s1, s2) ->
        let n, conf = Expr.eval env conf exp in
        let s       = if n != 0 then s1 else s2 in
        eval env conf k s
      | While (exp, s) -> 
        let n, conf = Expr.eval env conf exp in
        let k, s    = if n != 0 then While (exp, s) <> k, s else Skip, k in 
        eval env conf k s
      | Repeat (s, exp) -> 
        (* let conf    = eval env conf Skip s in
        let n, conf = Expr.eval env conf exp in 
        let k, s    = if n == 0 then k, Repeat (s, exp) else Skip, k in
        eval env conf k s *)
        let exp = Expr.Binop ("==", exp, Const 0) in
        eval env conf (While (exp, s) <> k) s
      | Call (name, exps) -> 
        let conf = snd ( Expr.eval env conf (Expr.Call (name, exps)) ) in
        eval env conf Skip k
      | Return r ->
        match r with
        | None   -> conf
        | Some e -> snd (Expr.eval env conf e)

         
    (* Statement parser *)
    ostap (
      expr: !(Expr.expr);

      stmt:
        x:IDENT ":=" e:expr     { Assign (x, e) }
      | "read" "(" x:IDENT ")"  { Read x }
      | "write" "(" e:expr ")"  { Write e }
      | "skip"                  { Skip }
      | "if" e:expr "then" s1:parse "elif" s2:elif "fi"           { If (e, s1, s2) }
      | "if" e:expr "then" s1:parse "else" s2:parse "fi"          { If (e, s1, s2) }
      | "if" e:expr "then" s1:parse "fi"                          { If (e, s1, Skip) }
      | "while" e:expr "do" s:parse "od"                          { While (e, s) }
      | "for"   s1:stmt "," e:expr "," s2:stmt "do" s:parse "od"  { Seq (s1, While(e, Seq(s, s2))) }
      | "repeat" s:parse "until" e:expr                           { Repeat (s, e) }
      | fname:IDENT "(" a:args ")"                                { Call (fname, a) }
      | "return" e:expr                                           { Return (Some e) }
      | "return"                                                  { Return None }
      ;

      args:
        e:expr "," a:args   { e :: a }
      | e:expr              { [e] }
      | empty               { [] }
      ;
 
      elif:
        e:expr "then" s1:parse "elif" s2:elif             { If (e, s1, s2) }
      | e:expr "then" s1:parse "else" s2:parse            { If (e, s1, s2) }
      | e:expr "then" s1:parse                            { If (e, s1, Skip) }
      ;

      parse: <x::xs> :!(Util.listBy)[ostap (";")][stmt] { List.fold_left (fun x y -> Seq (x, y)) x xs }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
