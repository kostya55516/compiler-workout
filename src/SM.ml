open GT       
       
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
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         

let insndebug p = match p with
	| BINOP s -> Printf.sprintf "BINOP %s" s 
	| CONST n -> Printf.sprintf "CONST %i" n
	| READ -> "READ"
	| WRITE -> "WRITE"
	| LD s -> Printf.sprintf "LD %s" s 
	| ST s -> Printf.sprintf "ST %s" s 

let rec eval (cf : config) (pl : prg) : config = match pl with
	| [] -> cf
	| p :: ps -> match p with
		| BINOP op -> (match cf with
			| (y :: x :: stack, c) ->  eval ((Syntax.Expr.doop op x y) :: stack, c) ps
			| _ -> failwith "SM eval BINOP")
		| CONST z -> (match cf with
			| (stack, c) -> eval (z :: stack, c) ps
			| _ -> failwith "SM eval CONST")
		| WRITE -> (match cf with
			| (z :: stack, (st, i, o)) -> eval (stack, (st, i, o @ [z])) ps
			| _ -> failwith "SM eval WRITE")
		| READ -> (match cf with
			| (stack, (st, z :: i, o)) -> eval (z :: stack, (st, i, o)) ps
			| _ -> failwith "SM eval READ")
		| ST x -> (match cf with
			| (z :: stack, (st, i, o)) -> eval (stack, ((Syntax.Expr.update x z st), i, o)) ps
			| _ -> failwith "SM eval ST")
		| LD x -> (match cf with
			| (stack, (st, i, o)) -> eval ((st x) :: stack, (st, i, o)) ps
			| _ -> failwith "SM eval LD")
		| _ -> failwith (Printf.sprintf "SM eval %s" (insndebug p))

(* let rec eval _ _ = failwith "not implemented yet" *)

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)


let rec ecompile (e : Syntax.Expr.t) : prg = match e with
	| Syntax.Expr.Var x -> [LD x]
	| Syntax.Expr.Const n -> [CONST n]
	| Syntax.Expr.Binop (op, ex, ey) -> (ecompile ex) @ (ecompile ey) @ [BINOP op]

(* val compile : Syntax.Stmt.t -> prg *)

let rec compile (st : Syntax.Stmt.t) : prg = match st with
	| Read x -> [READ; ST x]
	| Write exp -> (ecompile exp) @ [WRITE]
	| Assign (x, exp) -> (ecompile exp) @ [ST x]
	| Seq (t1, t2) -> (compile t1) @ (compile t2)
