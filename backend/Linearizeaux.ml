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

open LTL
open Maps
open Camlcoq

(* Trivial enumeration, in decreasing order of PC *)

(***
let enumerate_aux f reach =
  positive_rec
    Coq_nil
    (fun pc nodes ->
      if PMap.get pc reach
      then Coq_cons (pc, nodes)
      else nodes)
    f.fn_nextpc
***)

(* More clever enumeration that flattens basic blocks *)

module IntSet = Set.Make(struct type t = int let compare = compare end)

(* Determine join points: reachable nodes that have > 1 predecessor *)

let join_points f =
  let reached = ref IntSet.empty in
  let reached_twice = ref IntSet.empty in
  let rec traverse pc =
    let npc = P.to_int pc in
    if IntSet.mem npc !reached then begin
      if not (IntSet.mem npc !reached_twice) then
        reached_twice := IntSet.add npc !reached_twice
    end else begin
      reached := IntSet.add npc !reached;
      match PTree.get pc f.fn_code with
      | None -> ()
      | Some b -> traverse_succs (successors_block b)
    end
  and traverse_succs = function
    | [] -> ()
    | [pc] -> traverse pc
    | pc :: l -> traverse pc; traverse_succs l
  in traverse f.fn_entrypoint; !reached_twice

(* Cut into reachable basic blocks, annotated with the min value of the PC *)

let basic_blocks f joins =
  let blocks = ref [] in
  let visited = ref IntSet.empty in
  (* start_block:
       pc is the function entry point
          or a join point
          or the successor of a conditional test *)
  let rec start_block pc =
    let npc = P.to_int pc in
    if not (IntSet.mem npc !visited) then begin
      visited := IntSet.add npc !visited;
      in_block [] max_int pc
    end
  (* in_block: add pc to block and check successors *)
  and in_block blk minpc pc =
    let npc = P.to_int pc in
    let blk = pc :: blk in
    let minpc = min npc minpc in
    match PTree.get pc f.fn_code with
    | None -> assert false
    | Some b ->
       let rec do_instr_list = function
       | [] -> assert false
       | Lbranch s :: _ -> next_in_block blk minpc s
       | Ltailcall (sig0, ros) :: _ -> end_block blk minpc
       | Lcond (cond, args, ifso, ifnot) :: _ ->
             end_block blk minpc; start_block ifso; start_block ifnot
       | Ljumptable(arg, tbl) :: _ ->
             end_block blk minpc; List.iter start_block tbl
       | Lreturn :: _ -> end_block blk minpc
       | instr :: b' -> do_instr_list b' in
       do_instr_list b
  (* next_in_block: check if join point and either extend block
     or start block *)
  and next_in_block blk minpc pc =
    let npc = P.to_int pc in
    if IntSet.mem npc joins
    then (end_block blk minpc; start_block pc)
    else in_block blk minpc pc
  (* end_block: record block that we just discovered *)
  and end_block blk minpc =
    blocks := (minpc, List.rev blk) :: !blocks
  in
    start_block f.fn_entrypoint; !blocks

(* Sort basic blocks in decreasing order of minpc *)

let sort_blocks blks =
  let cmp_minpc (mpc1, _) (mpc2, _) =
    if mpc1 = mpc2 then 0 else if mpc1 > mpc2 then -1 else 1
  in
    List.map snd (List.sort cmp_minpc blks)

(* Placement of loop latches.

   Consider a block [B] that ends with an unconditional branch to a block [H]
   placed earlier, typically a block that increments the induction variable
   of a loop and branches back to the loop header [H].  Moreover, assume
   that [B] starts at a join point, e.g. the end of a conditional
   at the end of the loop body.  Placing [B] just before [H] turns the
   branch from [B] to [H] into a fall-through.  The only predecessor of [B]
   that can fall through into it is the block placed just before [B],
   which now has to branch to [B]; the other predecessors of [B]
   (there is at least one) branch to it in both cases.  Hence, the number
   of branches executed per loop iteration never increases, and decreases
   by one on the paths that reach [B] via a branch.  The price to pay is an
   additional branch on loop entry, from the block placed just before [H].

   If [B] is not a join point, it is not worth moving: there is no gain in
   terms of branches, and experiments show that turning
   [H: if (c) goto exit; B; goto H] into [goto H; B; H: if (!c) goto B]
   can be slower.

   We never move a block before the first block, which contains the entry
   point of the function, and we move at most one block before a given
   block [H]. *)

let place_latches f joins blocks =
  let first_pc = function
    | pc :: _ -> P.to_int pc
    | [] -> assert false in
  let rec last_pc = function
    | [pc] -> pc
    | _ :: l -> last_pc l
    | [] -> assert false in
  let rec branch_target = function
    | [] -> None
    | [Lbranch s] -> Some (P.to_int s)
    | _ :: b -> branch_target b in
  let target blk =
    match PTree.get (last_pc blk) f.fn_code with
    | Some b -> branch_target b
    | None -> None in
  (* [before] maps the first pc of a block [H] to the block
     to be placed just before [H]. *)
  let before = Hashtbl.create 17 in
  let moved = Hashtbl.create 17 in
  let rec scan seen = function
    | [] -> ()
    | blk :: rest ->
        let pc = first_pc blk in
        begin match target blk with
        | Some h when IntSet.mem pc joins
                   && IntSet.mem h seen
                   && not (Hashtbl.mem before h)
                   && not (Hashtbl.mem before pc) ->
            Hashtbl.add before h blk;
            Hashtbl.add moved pc ()
        | _ -> ()
        end;
        scan (IntSet.add pc seen) rest in
  match blocks with
  | [] -> []
  | entry :: others ->
      scan IntSet.empty others;
      let place blk =
        let pc = first_pc blk in
        if Hashtbl.mem moved pc then []
        else match Hashtbl.find_opt before pc with
             | Some b -> [b; blk]
             | None -> [blk] in
      entry :: List.concat_map place others

(* Build the enumeration *)

let enumerate_aux f reach =
  let joins = join_points f in
  List.flatten (place_latches f joins (sort_blocks (basic_blocks f joins)))
