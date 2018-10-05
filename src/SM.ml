open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (cf : config) (pl : prg) : config = match pl with
  | [] -> cf
  | p :: ps -> match p with
    | BINOP op -> let (y :: x :: stack, c) = cf     in eval env ((Language.Expr.doop op x y) :: stack, c) ps
    | CONST z  -> let (stack, c) = cf               in eval env (z :: stack, c) ps
    | WRITE    -> let (z :: stack, (st, i, o)) = cf in eval env (stack, (st, i, o @ [z])) ps
    | READ     -> let (stack, (st, z :: i, o)) = cf in eval env (z :: stack, (st, i, o)) ps
    | ST x     -> let (z :: stack, (st, i, o)) = cf in eval env (stack, ((Language.Expr.update x z st), i, o)) ps
    | LD x     -> let (stack, (st, i, o)) = cf      in eval env ((st x) :: stack, (st, i, o)) ps

    | LABEL _  -> eval env cf ps
    | JMP l    -> eval env cf (env#labeled l)
    | CJMP(s, l) -> let (z::stack, c) = cf in
                    let resolve = function
                    | "z"  -> z == 0 
                    | "nz" -> z != 0
                    in
                    eval env (stack, c) (if resolve s then (env#labeled l) else ps)


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

module type MONAD =
sig
 type 'a t
 val return : 'a -> 'a t
 val (>>=)  : 'a t -> ('a -> 'b t) -> 'b t
end

module type STATE = sig
  type state
  include MONAD
  val get : state t
  val put : state -> unit t
  val runState : 'a t -> init:state -> state * 'a
end

module State (S : sig type t end)
  : STATE with type state = S.t = struct
  type state = S.t
  type 'a t = state -> state * 'a
  let return v s = (s, v)
  let (>>=) m k s = let s', a = m s in k a s'
  let get s = (s, s)
  let put s' _ = (s', ())
  let runState m ~init = m init
end

module IState = State (struct type t = int end)

let fresh_label : string IState.t =
  let open IState in
  get         >>= fun i ->
  put (i + 1) >>= fun () ->
  return (Printf.sprintf "L%d" i)


let compile p =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  let rec state_comp =
  let open IState in function
  | Stmt.Seq (s1, s2)   -> state_comp s1 >>= fun cs1 ->
                           state_comp s2 >>= fun cs2 ->
                           return (cs1 @ cs2)
  | Stmt.Read x         -> return ([READ; ST x])
  | Stmt.Write e        -> return (expr e @ [WRITE])
  | Stmt.Assign (x, e)  -> return (expr e @ [ST x])
  | Stmt.Skip           -> return []
  | Stmt.If (e, s1, s2) ->  fresh_label   >>= fun l_else ->
                            fresh_label   >>= fun l_quit ->
                            state_comp s1 >>= fun cs1 ->
                            state_comp s2 >>= fun cs2 ->
                            return (
                              expr e 
                              @ [CJMP ("z", l_else)]
                              @ cs1
                              @ [JMP l_quit;
                                 LABEL l_else]
                              @ cs2
                              @ [LABEL l_quit]
                           )
  | Stmt.While (e, s)   ->  fresh_label   >>= fun l_loop ->
                            fresh_label   >>= fun l_body ->
                            state_comp s  >>= fun cs ->
                            return (
                               [JMP l_loop;
                                LABEL l_body]
                              @ cs
                              @ [LABEL l_loop]
                              @ expr e
                              @ [CJMP ("nz", l_body)]
                            )
  in
  let (state, result) = IState.runState (state_comp p) ~init:0 in result