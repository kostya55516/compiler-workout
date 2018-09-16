(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
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

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)

    let eval (st, z :: i, o) stmt = match stmt with
      | Read s -> ((Expr.update s z st), i, o)

    let rec eval (st, i, o) stmt = match stmt with
      | Write exp -> (st, i, o @ [Expr.eval st exp])
      | Assign (s, exp) -> ((Expr.update s (Expr.eval st exp) st), i, o)
      | Seq (t1, t2) -> eval (eval (st, i, o) t1) t2

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
