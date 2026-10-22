(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Datatypes
open FSetAVL
open Maps
open Op
open Ordered
open! RTL

module PSet = Make(OrderedPositive)

type inlining_info = {
  round: int; (* Number of the inlining round (1 or 2) *)
  call_cnt : int PTree.t; (* Count the number of direct calls to a function *)
  addr_taken : PSet.t; (* The set of globals which have their address taken *)
  fun_size: int PTree.t; (* Size of each internal function *)
  callees: ident list PTree.t; (* Direct callees of each internal function *)
  esize: (Camlcoq.P.t, int) Hashtbl.t; (* Memoized estimated sizes after inlining *)
}

let empty_inlining_info round = {
  round = round;
  call_cnt = PTree.empty;
  addr_taken = PSet.empty;
  fun_size = PTree.empty;
  callees = PTree.empty;
  esize = Hashtbl.create 17;
}

let call_count id io =
  match PTree.get id io.call_cnt with
  | Some cnt -> cnt
  | None -> 0

let called id io =
  let call_cnt = PTree.set id (1 + call_count id io) io.call_cnt in
  { io with call_cnt = call_cnt }

let address_taken id io =
  PSet.mem id io.addr_taken

let rec used_id io ids =
  match ids with
  | [] -> io
  | id::ids ->
     used_id {io with addr_taken = PSet.add id io.addr_taken} ids

let used_in_globvar io gv =
  let used_in_init_data io = function
    | Init_addrof (id,_) -> used_id io [id]
    | _ -> io in
  List.fold_left used_in_init_data io gv.gvar_init

(* Size of an RTL instruction, a rough estimate of the number of machine
   instructions it produces.  [Inop] instructions are free. *)

let instr_size = function
  | Inop _ -> 0
  | Icall (_, _, args, _, _) | Itailcall (_, _, args) -> 1 + List.length args
  | _ -> 1

let fun_inline_analysis id io fn =
  let inst (io, size, callees) nid i =
    let size = size + instr_size i in
    match i with
    | Iop (op, args, dest, succ) ->
       (used_id io (globals_operation op), size, callees)
    | Iload (chunk, addr, args, dest, succ)
    | Istore (chunk, addr, args, dest, succ) ->
       (used_id io (globals_addressing addr), size, callees)
    | Ibuiltin (ef, args, dest, succ) ->
       (used_id io (globals_of_builtin_args args), size, callees)
    | Icall (_, Coq_inr cid, _, _, _)
    | Itailcall (_, Coq_inr cid, _) -> (called cid io, size, cid :: callees)
    | _ -> (io, size, callees) in
  let (io, size, callees) = PTree.fold inst fn.fn_code (io, 0, []) in
  { io with fun_size = PTree.set id size io.fun_size;
            callees = PTree.set id callees io.callees }

(* Gather information about the program used for inlining heuristic *)
let inlining_analysis (round: nat) (p: program) =
  let io = empty_inlining_info (Camlcoq.Nat.to_int round) in
  if !Clflags.option_finline then
    List.fold_left (fun io idg ->
        match idg with
        | fid, Gfun (Internal f) -> fun_inline_analysis fid io f
        | _, Gvar gv -> used_in_globvar io gv
        | _ -> io) io p.prog_defs
  else
    io

(* Test whether a function is static and called only once *)
let static_called_once id io =
  if !Clflags.option_finline_functions_called_once then
    C2C.atom_is_static id && call_count id io <= 1 && not (address_taken id io)
  else
    false

(* Test whether a function calls itself directly *)
let self_recursive id io =
  match PTree.get id io.callees with
  | Some l -> List.exists (Camlcoq.P.eq id) l
  | None -> false

(* Inlining of small functions.  A function is small if its estimated
   size after inlining does not exceed [small_function_size].  This
   estimated size is the size of the function plus, for each call to
   a function that will be inlined, the estimated size of the callee.
   Recursive calls are not expanded, as in [Inlining.expand_cfg].
   Hence, inlining a small function at a call site increases code size
   by at most [small_function_size], even if inlining is nested.

   To bound the total code growth, as well as the compilation time of
   the callers, the estimated size multiplied by the number of call sites
   must not exceed [small_function_growth], unless the function is tiny,
   i.e. not much bigger than the code needed to call it. *)

let small_function_size () =
  if !Clflags.option_Osize then 6 else 24

let small_function_growth = 200

let tiny_function_size = 6

let rec estimated_size io visiting id =
  match Hashtbl.find_opt io.esize id with
  | Some n -> n
  | None ->
      match PTree.get id io.fun_size, PTree.get id io.callees with
      | Some size, Some callees ->
          let visiting = id :: visiting in
          let add_callee n id' =
            if List.exists (Camlcoq.P.eq id') visiting then n
            else if inline_decision io visiting id' then
              n + estimated_size io visiting id'
            else n in
          let n = List.fold_left add_callee size callees in
          Hashtbl.replace io.esize id n;
          n
      | _, _ -> max_int / 2

and is_small io visiting id =
  !Clflags.option_finline_small_functions
  && (let n = estimated_size io visiting id in
      n <= small_function_size ()
      && (n <= tiny_function_size
          || n * call_count id io <= small_function_growth))

and inline_decision io visiting id =
  match C2C.atom_inline id with
  | C2C.Inline -> true
  | C2C.Noinline -> false
  | C2C.No_specifier -> static_called_once id io || is_small io visiting id

(* The first inlining round takes place just after RTL generation.
   The second round takes place after constant propagation, which can
   turn indirect calls into direct calls, e.g. when a function pointer
   is passed as argument to a function inlined during the first round.
   During the second round, we do not inline self-recursive functions,
   whose recursive calls were already unrolled once during the first round. *)

let should_inline (io: inlining_info) (id: ident) (f: coq_function) =
  !Clflags.option_finline
  && inline_decision io [] id
  && not (io.round > 1 && self_recursive id io)

(* Bounded recursive inlining.  [inline_fuel fenv f] is the number of
   additional levels at which the self-recursive call of [f] is inlined
   into the body of [f] itself (see [Inlining.callee_env]): with fuel [n],
   the recursion is unrolled [n+1] levels deep.  This is done only for
   inlinable functions (present in [fenv]) with a single recursive call
   site, typically loops produced by accumulator tail-recursion
   elimination ([Tailacc]): then the body of [f] is copied [n+1] times.
   Unrolling functions with several recursive call sites copies their
   body exponentially many times, and was not found to be profitable.
   This is controlled by [-finline-recursive]; the depth is bounded by
   [-finline-recursive-depth], and the total size of the copies by
   [recursive_growth].  The second inlining round never
   inlines self-recursive functions, hence never unrolls them further. *)

let recursive_growth = 120

let inline_fuel (fenv: coq_function PTree.t) (f: coq_function) =
  let maxdepth = !Clflags.option_finline_recursive_depth in
  if not (!Clflags.option_finline && !Clflags.option_finline_recursive)
     || maxdepth <= 1
  then Datatypes.O else begin
    let is_self id =
      match PTree.get id fenv with Some g -> g == f | None -> false in
    let (size, selfcalls) =
      PTree.fold (fun (size, n) _ i ->
          let n =
            match i with
            | Icall (_, Coq_inr id, _, _, _)
            | Itailcall (_, Coq_inr id, _) when is_self id -> n + 1
            | _ -> n in
          (size + instr_size i, n))
        f.fn_code (0, 0) in
    if selfcalls <> 1 then Datatypes.O else begin
      let rec depth d =
        if d < maxdepth && size * (d + 1) <= recursive_growth
        then depth (d + 1) else d in
      Camlcoq.Nat.of_int (depth 1 - 1)
    end
  end
