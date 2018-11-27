open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
      
let rec eval env ((cs, stack, ((st, i, o) as c)) as cf) pl =
  match pl with
  | [] -> cf
  | p :: ps ->
  let eval_d x = eval env x ps in
  match p with
  | BINOP op -> let (y :: x :: stack) = stack in eval_d (cs, (Value.Int (Expr.to_func op (Value.to_int x) (Value.to_int y))) :: stack, c)
  | CONST z  -> eval_d (cs, (Value.Int z) :: stack, c)
  | STRING s -> eval_d (cs, (Value.String s) :: stack, c)
  | ST x     -> let (z :: stack)      = stack in eval_d (cs, stack, ((State.update x z st), i, o))
  | STA (x,n)->
    let (z :: stack) = stack in
    let inds, stack  = split n stack in 
    eval_d (cs, stack, ((Stmt.update st x z (List.rev inds)), i, o))
  | LD x     -> eval_d (cs, (State.eval st x) :: stack, (st, i, o))

  | LABEL _  -> eval env cf ps
  | JMP l    -> eval env cf (env#labeled l)
  | CJMP(s, l) -> 
    let (z::stack) = stack in
    let resolve = function
    | "z"  -> Value.to_int z == 0 
    | "nz" -> Value.to_int z != 0
    in
    eval env (cs, stack, c) (if resolve s then (env#labeled l) else ps)
  | BEGIN (f, xs, locs)  -> 
    let args, stack  = split (List.length xs) stack in
    let st           = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs (List.rev args)) in
    eval_d (cs, stack, (st, i, o))

  | END             ->  (match cs with
                      | (p', st') :: cs' -> 
                        let st'' = State.leave st st' in
                        eval env (cs', stack, (st'', i, o)) p'
                      | [] -> cf
                      )

  | CALL (f, n, b)  ->  let cf' = (ps, st) :: cs, stack, c in
                        if env#is_label f then eval env cf' (env#labeled f) else 
                        eval env (env#builtin cf f n (not b)) ps
  | RET b           ->  eval env cf (END::ps)


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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

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

let fun_label f = match f.[0] with '.' -> f | _ ->  Printf.sprintf "L%s" f


let compile (d, p) =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String s         -> [STRING s]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, exps)   -> List.fold_right (fun e ins -> (expr e) @ ins) exps [CALL (fun_label f, List.length exps, true)]
  in
  let rec state_comp =
  let open IState in function
  | Stmt.Seq (s1, s2)   -> state_comp s1 >>= fun cs1 ->
                           state_comp s2 >>= fun cs2 ->
                           return (cs1 @ cs2)
  | Stmt.Assign (x,i,e) -> (match i with
                           | []   -> return (expr e @ [ST x])
                           | exps -> return (List.fold_right (fun e s -> expr e @ s) exps (expr e @ [STA (x, List.length exps)]))
                           )
  | Stmt.Skip           -> return []
  | Stmt.If (e, s1, s2) -> fresh_label   >>= fun l_else ->
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
  | Stmt.While (e, s)   -> fresh_label   >>= fun l_loop ->
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
  | Stmt.Repeat (s, e)  -> fresh_label   >>= fun l_loop ->
                           fresh_label   >>= fun l_body ->
                           state_comp s  >>= fun cs ->
                           return (
                               [LABEL l_body]
                             @  cs
                             @  expr e
                             @ [CJMP  ("z", l_body)]
                           )
  | Stmt.Call (f, exps) -> return (List.fold_left (fun ins e -> (expr e) @ ins) [CALL (fun_label f, List.length exps, false)] exps)
  | Stmt.Return None    -> return [RET false]
  | Stmt.Return (Some e)-> return (expr e @ [RET true])
  in
  let rec state_comp_def =
  let open IState in function
  | d :: ds ->  let f, (a, l, s) = d in
                state_comp s      >>= fun cs  ->
                state_comp_def ds >>= fun cds ->
                return (
                    [LABEL (fun_label f);
                     BEGIN (f, a, l)]
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


