(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let itob x = if x == 0 then false else true
    let btoi x = if x then 1 else 0

    let doop op x y = match op with
      | "+"  -> x + y
      | "-"  -> x - y
      | "*"  -> x * y
      | "/"  -> x / y
      | "%"  -> x mod y
      | "<"  -> btoi (x < y)
      | "<=" -> btoi (x <= y)
      | ">"  -> btoi (x > y)
      | ">=" -> btoi (x >= y)
      | "==" -> btoi (x == y)
      | "!=" -> btoi (x <> y)
      | "&&" -> btoi ((itob x) && (itob y))
      | "!!" -> btoi ((itob x) || (itob y))
      |  _   -> failwith (Printf.sprintf "Undefined operator %s" op)


    let rec eval st e = match e with
      | Const x -> x
      | Var x -> st x
      | Binop (op, x, y) -> doop op (eval st x) (eval st y)

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
    (* loop with a post-condition       *) (* add yourself *)  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval conf stmt =
      let (st, i, o) = conf in
       match stmt with
        | Write exp -> (st, i, o @ [Expr.eval st exp])
        | Assign (s, exp) -> ((Expr.update s (Expr.eval st exp) st), i, o)
        | Seq (t1, t2) -> eval (eval conf t1) t2
        | Read s -> (match i with
          | x::xs -> ((Expr.update s x st), xs, o)
          | _ -> failwith "Nothig to read"
        )
        | Skip -> conf
        | If (exp, s1, s2) -> let s = if (Expr.eval st exp != 0) then s1 else s2 in eval conf s
        | While (exp, s) -> if (Expr.eval st exp != 0) then eval (eval conf s) (While (exp, s)) else conf
                       
    let negate e = Expr.Binop("==", e, Expr.Const 0)
    (* Statement parser *)
    ostap (
      expr: !(Expr.expr);

      stmt:
        x:IDENT ":=" e:expr     {Assign (x, e)}
      | "read" "(" x:IDENT ")"  {Read x}
      | "write" "(" e:expr ")"  {Write e}
      | "skip"                  {Skip}
      | "if" e:expr "then" s1:parse "elif" s2:elif "fi"           {If (e, s1, s2)}
      | "if" e:expr "then" s1:parse "else" s2:parse "fi"          {If (e, s1, s2)}
      | "if" e:expr "then" s1:parse "fi"                          {If (e, s1, Skip)}
      | "while" e:expr "do" s:parse "od"                          {While (e, s)}
      | "for"   s1:stmt "," e:expr "," s2:stmt "do" s:parse "od"  {Seq (s1, While(e, Seq(s, s2)))}
      | "repeat" s:parse "until" e:expr                            {Seq (s, While(negate e, s))}
      ;

      elif:
        e:expr "then" s1:parse "elif" s2:elif             {If (e, s1, s2)}
      | e:expr "then" s1:parse "else" s2:parse            {If (e, s1, s2)}
      | e:expr "then" s1:parse                            {If (e, s1, Skip)}
      ;

      parse: <x::xs> :!(Util.listBy)[ostap (";")][stmt] {List.fold_left (fun x y -> Seq (x, y)) x xs}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
