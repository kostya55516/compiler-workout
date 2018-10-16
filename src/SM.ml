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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (cf : config) (pl : prg) : config = match pl with
  | [] -> cf
  | p :: ps ->
  let eval_d x = eval env x ps in
    match p with
    | BINOP op -> let cs, y :: x :: stack, c     = cf in eval_d (cs, (Expr.to_func op x y) :: stack, c)
    | CONST z  -> let cs, stack, c               = cf in eval_d (cs, z :: stack, c)
    | WRITE    -> let cs, z :: stack, (st, i, o) = cf in eval_d (cs, stack, (st, i, o @ [z]))
    | READ     -> let cs, stack, (st, z :: i, o) = cf in eval_d (cs, z :: stack, (st, i, o))
    | ST x     -> let cs, z :: stack, (st, i, o) = cf in eval_d (cs, stack, ((State.update x z st), i, o))
    | LD x     -> let cs, stack, (st, i, o)      = cf in eval_d (cs, (State.eval st x) :: stack, (st, i, o))

    | LABEL _  -> eval env cf ps
    | JMP l    -> eval env cf (env#labeled l)
    | CJMP(s, l) -> let (cs, z::stack, c) = cf in
                    let resolve = function
                    | "z"  -> z == 0 
                    | "nz" -> z != 0
                    in
                    eval env (cs, stack, c) (if resolve s then (env#labeled l) else ps)
    | BEGIN (a, l)  ->  let cs, stack, (st, i, o) = cf in
                        let rec cut k xs = if k <= 0 then [], xs else
                          match xs with
                          | [] -> failwith "nothing to take"
                          | x::xs -> let fs, ts = cut (k - 1) xs in x :: fs, ts  
                        in
                        let z, stack  = cut (List.length a) stack in
                        let st        = Stmt.fill_and_push_scope st a l z in 
                        eval_d (cs, stack, (st, i, o))

    | END           ->  let cs, stack, (st, i, o) = cf in
                        (match cs with
                        | (p', st') :: cs' -> 
                          let st'' = State.drop_scope st st' in
                          eval env (cs', stack, (st'', i, o)) p'
                        | []              -> cf
                        )

    | CALL f        ->  let cs, stack, (st, i, o) = cf in
                        let conf = (ps, st) :: cs, stack, (st, i, o) in
                        eval env conf (env#labeled f)



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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

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

let fun_label = Printf.sprintf "F_%s"

let compile (d, p) =
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
                              @ [CJMP  ("z", l_else)]
                              @  cs1
                              @ [JMP   l_quit;
                                 LABEL l_else]
                              @  cs2
                              @ [LABEL l_quit]
                           )
  | Stmt.While (e, s)   ->  fresh_label   >>= fun l_loop ->
                            fresh_label   >>= fun l_body ->
                            state_comp s  >>= fun cs ->
                            return (
                                [JMP   l_loop;
                                 LABEL l_body]
                              @  cs
                              @ [LABEL l_loop]
                              @  expr e
                              @ [CJMP  ("nz", l_body)]
                            )
  | Stmt.Call (f, exps) -> return (List.fold_left (fun ins e -> (expr e) @ ins) [CALL (fun_label f)] exps)
  in
  let rec state_comp_def =
  let open IState in function
  | d :: ds ->  let f, (a, l, s) = d in
                state_comp s      >>= fun cs  ->
                state_comp_def ds >>= fun cds ->
                return (
                    [LABEL (fun_label f);
                     BEGIN (a, l)]
                  @  cs
                  @ [END]
                  @  cds
                )
  | []      -> return [] 
  in
  let _, result = 
    let program =
    let open IState in
    state_comp p     >>= fun cs ->
    state_comp_def d >>= fun cd ->
    return (cs @ [END] @ cd)
    in
  IState.runState program ~init:0
  in result