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

(* Placement of loop exits and of conditional updates.

   The order computed above follows the source code, so a block that
   leaves a loop from the middle of its body (e.g. [break] or [return]
   inside the loop, or the "found" case of a search loop) is placed
   between blocks of the loop.  Consider a block [C] of a loop that ends
   with a conditional branch to such an exit [X], placed just after [C],
   and to a block [Y] of the loop, placed after [X] with only blocks
   outside the loop in between.  The path that stays in the loop must
   branch over [X]: each iteration executes one more taken branch than
   necessary, and the loop is spread over more cache lines, which makes
   its speed depend on its alignment.

   Following the classical "loop exit" heuristic of static branch
   prediction, we assume that the edge that stays in the loop is more
   frequent than the edge that leaves it, and we move the blocks from
   [X] to [Y] (excluded) after the loop, so that [C] falls through into
   [Y].  An exit then costs one more taken branch, but an iteration one
   less.

   Second, consider a block [C] of a loop that ends with a conditional
   branch to a block [J] or to a block [M] that only contains moves and
   branches to [J], where [J] starts with a store of a register [r] that
   [C] has loaded from the same address, and [M] assigns [r].  This is a
   conditional update [a[i] = c ? a[i] : e], e.g. a minimum or maximum
   relaxation, and the store is silent on the edge from [C] to [J].  We
   assume that, as usual for such updates, the value is more often kept
   than changed, and make the edge from [C] to [J] the fall-through by
   moving [M] after the loop.  Without this rule, which of the two
   edges falls through depends on which of the two moves of
   [a[i] = c ? a[i] : e] the register allocator happened to coalesce. *)

let rec last_elt = function
  | [x] -> x
  | _ :: l -> last_elt l
  | [] -> assert false

let block_code f blk =
  List.concat_map (fun pc ->
    match PTree.get pc f.fn_code with Some b -> b | None -> []) blk

let block_succs f blk =
  match PTree.get (last_elt blk) f.fn_code with
  | Some b -> successors_block b
  | None -> []

(* Natural loops of the graph of blocks [a] (given by the successors of
   each block), merged by header, outermost first *)

let block_loops succs entry =
  let nb = Array.length succs in
  let preds = Array.make nb [] in
  Array.iteri (fun k l -> List.iter (fun s -> preds.(s) <- k :: preds.(s)) l) succs;
  let visited = Array.make nb false and post = ref [] in
  let rec dfs k =
    if not visited.(k) then begin
      visited.(k) <- true; List.iter dfs succs.(k); post := k :: !post
    end in
  dfs entry;
  let rpo = Array.of_list !post in
  let num = Array.make nb (-1) in
  Array.iteri (fun i k -> num.(k) <- i) rpo;
  (* Dominators, as in Cooper, Harvey and Kennedy, "A simple, fast
     dominance algorithm" *)
  let idom = Array.make nb (-1) in
  idom.(entry) <- entry;
  let rec inter x y =
    if x = y then x
    else if num.(x) > num.(y) then inter idom.(x) y
    else inter x idom.(y) in
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iter (fun k ->
      if k <> entry then begin
        let d = List.fold_left (fun acc p ->
          if idom.(p) < 0 then acc else if acc < 0 then p else inter p acc)
          (-1) preds.(k) in
        if idom.(k) <> d then begin idom.(k) <- d; changed := true end
      end) rpo
  done;
  let rec dominates h k =
    k = h || (k <> entry && idom.(k) >= 0 && dominates h idom.(k)) in
  let bodies = Hashtbl.create 7 in
  Array.iter (fun u ->
    List.iter (fun h ->
      if dominates h u then begin
        let body =
          match Hashtbl.find_opt bodies h with
          | Some b -> b
          | None -> let b = Array.make nb false in Hashtbl.add bodies h b; b in
        body.(h) <- true;
        let stack = ref [u] in
        while !stack <> [] do
          let x = List.hd !stack in
          stack := List.tl !stack;
          if not body.(x) then begin
            body.(x) <- true;
            List.iter (fun p -> if num.(p) >= 0 then stack := p :: !stack) preds.(x)
          end
        done
      end) succs.(u))
    rpo;
  let size b = Array.fold_left (fun c x -> if x then c + 1 else c) 0 b in
  List.stable_sort (fun b1 b2 -> compare (size b2) (size b1))
    (Hashtbl.fold (fun h b acc -> (h, b) :: acc) bodies []
     |> List.sort (fun (h1, _) (h2, _) -> compare h1 h2) |> List.map snd)

let place_exits f blocks =
  let a = Array.of_list blocks in
  let nb = Array.length a in
  let index = Hashtbl.create nb in
  Array.iteri (fun k blk -> Hashtbl.replace index (P.to_int (List.hd blk)) k) a;
  let block_of s = Hashtbl.find_opt index (P.to_int s) in
  let succs = Array.map (fun blk -> List.filter_map block_of (block_succs f blk)) a in
  let entry =
    match block_of f.fn_entrypoint with Some k -> k | None -> 0 in
  let loops = block_loops succs entry in
  let code = Array.map (block_code f) a in
  (* Does block [k] fall through into block [k']? *)
  let falls_into k k' =
    match code.(k) with
    | [] -> false
    | l -> (match last_elt l with
            | Lbranch s -> block_of s = Some k'
            | Lcond (_, _, s1, s2) -> block_of s1 = Some k' || block_of s2 = Some k'
            | _ -> false) in
  (* Insert the blocks [moved] in [order] after the first block at or
     after position [p] that does not fall through into its successor *)
  let insert_after order p moved =
    let n = Array.length order in
    let rec find q =
      if q >= n - 1 || not (falls_into order.(q) order.(q + 1)) then q
      else find (q + 1) in
    let q = find p in
    Array.concat [Array.sub order 0 (q + 1); Array.of_list moved;
                  Array.sub order (q + 1) (n - q - 1)] in
  let last_pos order body =
    let p = ref 0 in
    Array.iteri (fun i k -> if body.(k) then p := i) order; !p in
  (* Loop exits: a block [C] of a loop [L] that ends with a conditional
     branch to a block [X] outside [L] and to a block [Y] of [L], where
     [X] and the following blocks up to [Y] are not in [L] *)
  let order = ref (Array.init nb (fun k -> k)) in
  let innermost_with k k' =
    List.fold_left (fun acc b -> if b.(k) && b.(k') then Some b else acc) None loops in
  let pos = Array.make nb 0 in
  let update_pos () = Array.iteri (fun i k -> pos.(k) <- i) !order in
  update_pos ();
  for c = 0 to nb - 1 do
    match code.(c), succs.(c) with
    | (_ :: _ as l), [k1; k2] when (match last_elt l with Lcond _ -> true | _ -> false) ->
        List.iter (fun (x, y) ->
          match innermost_with c y with
          | Some body when not body.(x) && pos.(x) = pos.(c) + 1 && pos.(y) > pos.(x) ->
              let run = Array.to_list (Array.sub !order pos.(x) (pos.(y) - pos.(x))) in
              if List.for_all (fun k -> not body.(k) && k <> entry) run then begin
                let kept = Array.of_list
                    (List.filter (fun k -> not (List.mem k run)) (Array.to_list !order)) in
                order := insert_after kept (last_pos kept body) run;
                update_pos ()
              end
          | _ -> ()) [(k1, k2); (k2, k1)]
    | _ -> ()
  done;
  (* Conditional updates *)
  let npreds = Array.make nb 0 in
  Array.iter (List.iter (fun s -> npreds.(s) <- npreds.(s) + 1)) succs;
  let innermost k = List.fold_left (fun acc b -> if b.(k) then Some b else acc) None loops in
  (* [j] starts with a store of [r] at the address that the end of [c]
     loads into [r] *)
  let silent_store c j =
    match code.(j) with
    | Lstore (chunk, addr, args, src) :: _ ->
        let loads = function
          | Lload (chunk', addr', args', dst) ->
              dst = src && chunk' = chunk && Op.eq_addressing addr' addr
              && args' = args && not (List.mem dst args)
          | _ -> false in
        let preserves = function
          | Lop (_, _, r) | Lload (_, _, _, r) | Lgetstack (_, _, _, r) ->
              r <> src && not (List.mem r args)
          | Lbranch _ | Lcond _ -> true
          | _ -> false in
        let rec after = function
          | [] -> None
          | i :: rest ->
              match after rest with
              | Some l -> Some l
              | None -> if loads i then Some rest else None in
        (match after code.(c) with
         | Some rest -> List.for_all preserves rest
         | None -> false)
    | _ -> false in
  (* [m] only contains moves, one of which assigns the register stored
     by [j], and branches to [j] *)
  let update m j =
    let rec moves = function
      | [Lbranch s] -> block_of s = Some j
      | Lop (Op.Omove, _, _) :: rest -> moves rest
      | _ -> false in
    match code.(j) with
    | Lstore (_, _, _, src) :: _ ->
        moves code.(m)
        && List.exists (function Lop (Op.Omove, _, r) -> r = src | _ -> false) code.(m)
    | _ -> false in
  update_pos ();
  let out = ref [] in
  Array.iteri (fun c _ ->
    match code.(c) with
    | [] -> ()
    | l ->
        match last_elt l, succs.(c), innermost c with
        | Lcond _, [k1; k2], Some _ ->
            List.iter (fun (m, j) ->
              if m <> j && m <> entry && npreds.(m) = 1
                 && pos.(m) = pos.(c) + 1 && pos.(j) = pos.(m) + 1
                 && update m j && silent_store c j
              then out := m :: !out) [(k1, k2); (k2, k1)]
        | _ -> ()) a;
  List.iter (fun m ->
    let kept = Array.of_list (List.filter (fun k -> k <> m) (Array.to_list !order)) in
    match innermost m with
    | Some body -> order := insert_after kept (last_pos kept body) [m]
    | None -> ()) !out;
  List.map (fun k -> a.(k)) (Array.to_list !order)

(* Build the enumeration *)

let enumerate_aux f reach =
  let joins = join_points f in
  List.flatten (place_exits f (place_latches f joins (sort_blocks (basic_blocks f joins))))
