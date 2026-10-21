(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(* Oracle for loop rotation.  For each natural loop whose header starts
   with a short sequence of instructions ending with an exit test, the
   sequence is duplicated and the back edges of the loop are redirected
   to the copy.  The result is validated by [Looprot.check_function]. *)

open! Camlcoq
open Maps
open Op
open RTL

(* Maximal number of non-branch instructions duplicated per loop *)

let max_copied = 3

let rotate_oracle f =
  let g = LICMaux.build_cfg f in
  let n = g.LICMaux.n and instr = g.LICMaux.instr in
  let loops = LICMaux.natural_loops g in
  let in_chain = Array.make n false in
  let next_pc = ref n in
  (* For each rotated loop: header, body, and list of (original, copy) *)
  let rotated = ref [] in
  (* Number of reachable predecessors of each node *)
  let npreds = Array.map (fun l ->
    List.length (List.filter (fun p -> g.LICMaux.visited.(p)) l)) g.LICMaux.preds in
  (* Start of the basic block containing [x], not going past [h] *)
  let rec block_start h x =
    if x = h then x else
    match List.filter (fun p -> g.LICMaux.visited.(p)) g.LICMaux.preds.(x) with
    | [p] when List.length g.LICMaux.succs.(p) = 1 -> block_start h p
    | _ -> x in
  (* Block layout ([Linearizeaux.place_latches]) already avoids the
     unconditional back branch if the block ending with the back edge
     starts at a join point other than the header.  Rotation is then
     useless, and often harmful: the latch block would end with a
     conditional branch and no longer be eligible for this placement. *)
  let latch_placed h body =
    Array.exists (fun x -> x) (Array.mapi (fun x succ ->
      body.(x) && g.LICMaux.visited.(x) && List.mem h succ
      && (match instr.(x) with
          | Some (Icond _ | Ijumptable _) -> false
          | _ -> true)
      && (let b = block_start h x in b <> h && npreds.(b) >= 2))
      g.LICMaux.succs) in
  List.iter (fun (h, body) ->
    if not (latch_placed h body) then
    let rec chain x acc cnt =
      if in_chain.(x) || List.length acc > 2 * max_copied then None else
      match instr.(x) with
      | Some (Icond (_, _, s1, s2)) ->
          let s1 = P.to_int s1 and s2 = P.to_int s2 in
          let in1 = s1 < n && body.(s1) and in2 = s2 < n && body.(s2) in
          if in1 <> in2 && s1 <> h && s2 <> h then Some (List.rev (x :: acc)) else None
      | Some (Inop s) ->
          let s = P.to_int s in
          if s < n && body.(s) && s <> h then chain s (x :: acc) cnt else None
      (* Loads are not copied: Loadfwd would forward the copied load to
         the reload of the same location in the loop body, creating a copy
         that register allocation often fails to coalesce, which
         lengthens loop-carried dependencies such as [i = next[i]]
         (3% on lzss). *)
      | Some (Iop (_, _, _, s)) ->
          let s = P.to_int s in
          if s < n && body.(s) && s <> h && cnt < max_copied
          then chain s (x :: acc) (cnt + 1) else None
      | _ -> None in
    (* Do not rotate if an argument of the exit test is assigned by a move
       elsewhere in the loop, typically [l = next] in a list traversal.
       After register allocation, the copied test then compares the
       register just written by the move, which turned out to be slower
       (e.g. 15% on the list reversal loop of test/c/lists.c) than the
       original layout, where the move and the test are separated by the
       back branch. *)
    let test_assigned_by_move nodes =
      match instr.(List.nth nodes (List.length nodes - 1)) with
      | Some (Icond (_, args, _, _)) ->
          Array.exists (fun x -> x) (Array.mapi (fun x b ->
            b && not (List.mem x nodes)
            && (match instr.(x) with
                | Some (Iop (Omove, _, d, _)) -> List.mem d args
                | _ -> false)) body)
      | _ -> false in
    match chain h [] 0 with
    | None -> ()
    | Some nodes when test_assigned_by_move nodes -> ()
    | Some nodes ->
        let copies =
          List.map (fun x ->
            in_chain.(x) <- true;
            let c = !next_pc in incr next_pc; (x, c)) nodes in
        rotated := (h, body, copies) :: !rotated)
    loops;
  if !rotated = [] then (PTree.empty, f.fn_entrypoint) else begin
    (* Redirect the edge [x -> s], where [x] is (a copy of) an original node *)
    let redirect x s =
      let s = P.to_int s in
      let r =
        List.find_map (fun (h, body, copies) ->
          if h = s && body.(x) then Some (snd (List.hd copies)) else None)
          !rotated in
      P.of_int (match r with Some c -> c | None -> s) in
    let info = ref PTree.empty in
    Array.iteri (fun x i ->
      match i with
      | None -> ()
      | Some i ->
          let px = P.of_int x in
          info := PTree.set px (px, List.map (redirect x) (successors_instr i)) !info)
      instr;
    List.iter (fun (_, _, copies) ->
      let rec add = function
        | [] -> ()
        | [(x, c)] ->
            let succs =
              match instr.(x) with
              | Some i -> List.map (redirect x) (successors_instr i)
              | None -> assert false in
            info := PTree.set (P.of_int c) (P.of_int x, succs) !info
        | (x, c) :: ((_, c') :: _ as rest) ->
            info := PTree.set (P.of_int c) (P.of_int x, [P.of_int c']) !info;
            add rest in
      add copies)
      !rotated;
    (!info, f.fn_entrypoint)
  end
