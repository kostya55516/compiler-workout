(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list (*with show*)

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
                      
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
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

    let rec eval env ((st, i, o, r) as conf) expr =
      let eval_exps env conf exps = 
        let eval_list exp (ags, c) = let a, c = eval env c exp in (a::ags, c) in           
        let args, conf             = List.fold_right eval_list exps ([], conf) in
        args, conf
      in      
      match expr with
      | Const n   -> let r = Value.Int n in r, (st, i, o, Some r)
      | Array ar  -> 
        let ar, (st, i, o, _) = eval_exps env conf ar in
        let r = Value.Array (Array.of_list ar) in
        r, (st, i, o, Some r)
      | String s  -> let r = Value.String s in r, (st, i, o, Some r)
      | Var   x   -> let r = State.eval st x in r, (st, i, o, Some r)
      | Binop (op, x, y) -> 
        let a, conf = eval env conf x in
        let b, conf = eval env conf y in
        let r       = Value.Int (to_func op (Value.to_int a) (Value.to_int b)) in
        r, (st, i, o, Some r)
      | Call (name, exps) ->
        let args, conf             = eval_exps env conf exps in
        let st', i, o, Some r      = env#definition env name args conf in
        r, (State.leave st' st, i, o, Some r)
      | Sexp (t, v) -> 
        let vs, (st, i, o, _) = eval_exps env conf v in
        let r = Value.Sexp (t, vs) in
        r, (st, i, o, Some r) 
    
    let eval_exps env conf exps = 
      let eval_list exp (ags, c) = let a, c = eval env c exp in (a::ags, c) in           
      let args, conf             = List.fold_right eval_list exps ([], conf) in
      args, conf

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
        e:expr "," a:args   { e::a }
      | e:expr              { [e] }
      | empty { [] }
      ;

      builtins:
       x:primary_type ".length"  { Call (".length", [x]) }
      | x:array_elem ".length"    { Call (".length", [x]) }
      | a:array_elem              { a }
      ;
      (* Call (".elem", [x; e])  *)

      array_elem: x:primary_type br:brackets { 
           List.fold_left (fun v e -> Call (".elem", [v; e])) x br
      };

      brackets:
        "[" e:expr "]" b:brackets { e::b }
      | "[" e:expr "]" { [e] }
      ;
      
      primary_type:
        x:IDENT             { Var x }
      | n:DECIMAL           { Const n }  
      | "\"" s:IDENT "\""   { String s }
      | c:CHAR              { Const (Char.code c) }
      | "[" a:args "]"      { Call (".array", a) }
      ;

      sexp: "`" t:IDENT v:sexp_values { Sexp (t, v) };

      sexp_values:
       "(" a:args ")" { a }
      | empty         { [] }
      ;

      primary: builtins | func | primary_type | sexp | -"(" expr -")";

      parse: expr
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          args:
            "(" ps:patterns ")" { ps }
          | empty               { [] }
          ;

          patterns:
            p:parse "," ps:patterns { p::ps }
          | p:parse { [p] }
          | empty               { [] }
          ;

          parse: 
            "_"                 { Wildcard }
          | "`" t:IDENT v:args  { Sexp (t, v) }
          | x:IDENT             { Ident x }
        )
        
        let rec p_match v = function
        | Sexp (g, ps) ->
          let Value.Sexp (t, vs) = v in 
          String.compare t g == 0 && List.length vs == List.length vs && List.for_all2 (fun v p -> p_match v p) vs ps
        | _ -> true

        let bindings a p =
        let rec r_bindings s a = function
        | Wildcard -> s
        | Ident x  -> State.bind x a s
        | Sexp (_, ps) ->
          let Value.Sexp (_, vs) = a in
          List.fold_left2 (fun s p v -> r_bindings s v p) s ps vs 
        in
        r_bindings (fun k -> print_string (Printf.sprintf "no such variable %s" k); Value.Int 0) a p

        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
           ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt =
      let (<>) s1 s2 = if s2 == Skip then s1 else Seq (s1, s2) in
      match stmt with
      | Skip -> if k == Skip then conf else eval env conf Skip k
      | Assign (s, inds, exp) ->           
        let inds, conf           = Expr.eval_exps env conf inds in
        let n, (st, i, o, r)     = Expr.eval env conf exp in
        let st = update st s n inds in
        eval env (st, i, o, r) Skip k
      | Seq (s1, s2) -> eval env conf (s2 <> k) s1    
      | If (exp, s1, s2) ->
        let n, conf = Expr.eval env conf exp in
        let s       = if Value.to_int n != 0 then s1 else s2 in
        eval env conf k s
      | While (exp, s) -> 
        let n, conf = Expr.eval env conf exp in
        let k, s    = if Value.to_int n != 0 then While (exp, s) <> k, s else Skip, k in 
        eval env conf k s
      | Repeat (s, exp) -> 
        let exp = Expr.Binop ("==", exp, Const 0) in
        eval env conf (While (exp, s) <> k) s
      | Call (name, exps) ->
        let args, conf  = Expr.eval_exps env conf exps in
        let conf        = env#definition env name args conf in
        eval env conf Skip k
      | Return r ->
        (match r with
        | None   -> conf
        | Some e -> snd (Expr.eval env conf e)
        )
      | Case (e, pms) -> 
        let v, conf = Expr.eval env conf e in
        let rec pat_list ((st, i, o, r) as conf) = function
        | [] -> 
        (* eval env conf Skip k *)
         failwith (Printf.sprintf "Bad pattern match, len: %d" (List.length pms))
        | (p, t)::pms -> 
          if Pattern.p_match v p 
          then eval env ((State.push st (Pattern.bindings v p) (Pattern.vars p)), i, o, r) k (Seq (t, Leave))
          else pat_list conf pms
        in
        pat_list conf pms
      | Leave         -> eval env (State.drop st, i, o, r) Skip k
         

    (* Statement parser *)
    ostap (
      expr: !(Expr.expr);

      stmt:
        x:IDENT ":=" e:expr         { Assign (x, [], e) }
      | x:IDENT is:inds ":=" e:expr { Assign (x, is, e) } 
      | "skip"                      { Skip }
      | "if" e:expr "then" s1:parse "elif" s2:elif "fi"           { If (e, s1, s2) }
      | "if" e:expr "then" s1:parse "else" s2:parse "fi"          { If (e, s1, s2) }
      | "if" e:expr "then" s1:parse "fi"                          { If (e, s1, Skip) }
      | "while" e:expr "do" s:parse "od"                          { While (e, s) }
      | "for"   s1:stmt "," e:expr "," s2:stmt "do" s:parse "od"  { Seq (s1, While(e, Seq(s, s2))) }
      | "repeat" s:parse "until" e:expr                           { Repeat (s, e) }
      | fname:IDENT "(" a:!(Expr.args) ")"                        { Call (fname, a) }
      | "return" e:expr                                           { Return (Some e) }
      | "return"                                                  { Return None }
      | "case" e:expr "of" p:pattern_matches "esac"               { Case (e, p) }
      ;

      pattern_matches:
        p:pattern_match ps:pattern_matches_tail { p::ps }
      ;
      
      pattern_matches_tail: 
        "|" p:pattern_match ps:pattern_matches_tail { p::ps }
      | empty                                       { [] }
      ;

      pattern_match: p:!(Pattern.parse) "->" s:parse { p, s };

      inds:
       "[" i:expr "]" is:inds { i::is }
      | empty                 { [] }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
