open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)                         
let rec eval (cf : config) (pl : prg) : config = match pl with
  | [] -> cf
  | p :: ps -> match p with
    | BINOP op -> (match cf with
      | (y :: x :: stack, c) ->  eval ((Language.Expr.doop op x y) :: stack, c) ps
      | _ -> failwith "SM eval BINOP")
    | CONST z -> (match cf with
      | (stack, c) -> eval (z :: stack, c) ps)
    | WRITE -> (match cf with
      | (z :: stack, (st, i, o)) -> eval (stack, (st, i, o @ [z])) ps
      | _ -> failwith "SM eval WRITE")
    | READ -> (match cf with
      | (stack, (st, z :: i, o)) -> eval (z :: stack, (st, i, o)) ps
      | _ -> failwith "SM eval READ")
    | ST x -> (match cf with
      | (z :: stack, (st, i, o)) -> eval (stack, ((Language.Expr.update x z st), i, o)) ps
      | _ -> failwith "SM eval ST")
    | LD x -> (match cf with
      | (stack, (st, i, o)) -> eval ((st x) :: stack, (st, i, o)) ps)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
