(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
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
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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

      primary: x:IDENT {Var x} | n:DECIMAL {Const n}  | -"(" expr -")";

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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let fill_and_push_scope st params locals args =
          let st                    = State.push_scope st (params @ locals) in
          let update st (p, a)      = State.update p a st in
          List.fold_left update st (List.combine params args)

    let rec eval env conf stmt =
      let st, i, o = conf in
       match stmt with
        | Write exp -> (st, i, o @ [Expr.eval st exp])
        | Assign (s, exp) -> ((State.update s (Expr.eval st exp) st), i, o)
        | Seq (t1, t2) -> eval env (eval env conf t1) t2
        | Read s -> (
          match i with
          | x::xs -> ((State.update s x st), xs, o)
          | _ -> failwith "Nothig to read"
        )
        | Skip -> conf
        | If (exp, s1, s2) -> let s = if (Expr.eval st exp != 0) then s1 else s2 in eval env conf s
        | While (exp, s) -> if (Expr.eval st exp != 0) then eval env (eval env conf s) (While (exp, s)) else conf
        | Call (name, exps) -> 
          let params, locals, stmt' = env#definition name in
          let args                  = List.map (Expr.eval st) exps in
          let st'                   = fill_and_push_scope st params locals args in
          let st'', i', o'          = eval env (st', i, o) stmt' in
          (State.drop_scope st'' st, i', o')


    (* Statement parser *)
     let negate e = Expr.Binop("==", e, Expr.Const 0)
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
      | "repeat" s:parse "until" e:expr                           { Seq (s, While(negate e, s)) }
      | fname:IDENT "(" a:args ")"                                { Call (fname, a) }
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
      
      stmt: !(Stmt.parse);

      params: 
          x:IDENT "," p:params  { x :: p }
        | x:IDENT               { [x] }
        | empty                 { [] }
        ;

      locals: 
          "local" p:params  { p }
        | empty             { [] }
        ;

      parse: "fun" f:IDENT "(" p:params ")" l:locals "{" s:stmt "}" { f, (p, l, s) }
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
