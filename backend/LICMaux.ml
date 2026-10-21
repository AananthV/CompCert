(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(* Oracle for loop-invariant code motion.  Finds natural loops and
   chooses the operations to be hoisted out of them.  The results are
   validated by [LICM.check_function]. *)

open! Camlcoq
open Maps
open Op
open RTL

let defs_all = function
  | Iop (_, _, r, _) | Iload (_, _, _, r, _) | Icall (_, _, _, r, _) -> [r]
  | Ibuiltin (_, _, res, _) -> AST.params_of_builtin_res res
  | _ -> []

(* Which operations are worth hoisting.  Integer constants are cheap
   immediates, floating-point constants are loaded from memory (which is
   no more expensive than reloading a spilled register), and hoisting
   moves is pointless. *)

let worth_hoisting op =
  match op with
  | Omove | Ointconst _ | Olongconst _ | Ofloatconst _ | Osingleconst _ -> false
  | _ -> true

let hoistable op args =
  worth_hoisting op
  && LICMop.op_safe op (Camlcoq.Nat.of_int (List.length args))
  && not (op_depends_on_memory op)

module IS = Set.Make(Int)

(* Heuristic limits on the estimated register pressure in a loop after
   hoisting (tuned for x86-64, which has 15 allocatable integer registers
   and 16 floating-point registers).  The estimate (number of live pseudo
   registers) is pessimistic, since some of them are coalesced by register
   allocation, hence the integer limit above the number of registers. *)

let max_pressure_int = 16
let max_pressure_float = 14

type loop = {
  header: int;
  body: bool array;
  size: int;
  defs: (P.t, unit) Hashtbl.t;
  hoisted: (operation * P.t list, P.t) Hashtbl.t;
  mutable chain: (P.t * ((P.t * operation) * P.t list)) list  (* reversed *)
}

(* Control-flow graph of a function, with nodes numbered by integers *)

type cfg = {
  n: int;                                (* 1 + largest node *)
  instr: instruction option array;
  succs: int list array;
  preds: int list array;
  entry: int;
  rpo: int array;                        (* reachable nodes, in reverse postorder *)
  visited: bool array                    (* reachable nodes *)
}

let build_cfg f =
  let n = P.to_int (max_pc_function f) + 1 in
  let instr = Array.make n None in
  List.iter (fun (pc, i) -> instr.(P.to_int pc) <- Some i) (PTree.elements f.fn_code);
  let succs = Array.make n [] in
  let preds = Array.make n [] in
  Array.iteri (fun pc i ->
    match i with
    | None -> ()
    | Some i ->
        let s = List.map P.to_int (successors_instr i) in
        succs.(pc) <- s;
        List.iter (fun s -> if s < n then preds.(s) <- pc :: preds.(s)) s)
    instr;
  let entry = P.to_int f.fn_entrypoint in
  let visited = Array.make n false in
  let rpo = ref [] in
  let rec dfs u =
    visited.(u) <- true;
    List.iter (fun v -> if v < n && not visited.(v) && instr.(v) <> None then dfs v)
      succs.(u);
    rpo := u :: !rpo in
  if entry < n && instr.(entry) <> None then dfs entry;
  { n; instr; succs; preds; entry; rpo = Array.of_list !rpo; visited }

(* Natural loops, merged by header.  Returns a list of (header, body). *)

let natural_loops g =
  let n = g.n and rpo = g.rpo and entry = g.entry
  and preds = g.preds and visited = g.visited in
  let rponum = Array.make n (-1) in
  Array.iteri (fun k u -> rponum.(u) <- k) rpo;
  (* Dominators (Cooper, Harvey, Kennedy) *)
  let idom = Array.make n (-1) in
  if Array.length rpo > 0 then begin
    idom.(entry) <- entry;
    let intersect b1 b2 =
      let f1 = ref b1 and f2 = ref b2 in
      while !f1 <> !f2 do
        while rponum.(!f1) > rponum.(!f2) do f1 := idom.(!f1) done;
        while rponum.(!f2) > rponum.(!f1) do f2 := idom.(!f2) done
      done;
      !f1 in
    let changed = ref true in
    while !changed do
      changed := false;
      Array.iter (fun u ->
        if u <> entry then begin
          let nd =
            List.fold_left (fun acc p ->
              if not visited.(p) || idom.(p) < 0 then acc
              else if acc < 0 then p
              else intersect p acc)
              (-1) preds.(u) in
          if nd <> idom.(u) then begin idom.(u) <- nd; changed := true end
        end)
        rpo
    done
  end;
  let rec dominates a b =
    if a = b then true
    else if b = entry || idom.(b) < 0 then false
    else dominates a idom.(b) in
  let bodies = Hashtbl.create 7 in
  let headers = ref [] in
  Array.iter (fun u ->
    List.iter (fun h ->
      if h < n && visited.(h) && dominates h u then begin
        let body =
          match Hashtbl.find_opt bodies h with
          | Some b -> b
          | None ->
              let b = Array.make n false in
              Hashtbl.add bodies h b; headers := h :: !headers; b in
        body.(h) <- true;
        let stack = ref [u] in
        while !stack <> [] do
          let x = List.hd !stack in
          stack := List.tl !stack;
          if not body.(x) then begin
            body.(x) <- true;
            List.iter (fun p -> if visited.(p) then stack := p :: !stack) preds.(x)
          end
        done
      end)
      g.succs.(u))
    rpo;
  List.rev_map (fun h -> (h, Hashtbl.find bodies h)) !headers

let licm_oracle f =
  let g = build_cfg f in
  let n = g.n and instr = g.instr and succs = g.succs
  and entry = g.entry and rpo = g.rpo in
  (* Keep the loops that can only be entered through their header,
     taking unreachable nodes into account *)
  let valid h body =
    (not body.(entry) || entry = h)
    && Array.for_all (fun x -> x) (Array.mapi (fun m s ->
         body.(m) || List.for_all (fun s -> s >= n || not body.(s) || s = h) s)
         succs) in
  let loops = ref [] in
  List.iter (fun (h, body) ->
    if valid h body then begin
      let defs = Hashtbl.create 17 in
      let size = ref 0 in
      Array.iteri (fun pc b ->
        if b then begin
          incr size;
          match instr.(pc) with
          | Some i -> List.iter (fun r -> Hashtbl.replace defs r ()) (defs_all i)
          | None -> ()
        end) body;
      loops := { header = h; body; size = !size; defs;
                 hoisted = Hashtbl.create 7; chain = [] } :: !loops
    end) (natural_loops g);
  (* Outermost loops first *)
  let loops = List.sort (fun l1 l2 -> compare l2.size l1.size) !loops in
  match loops, RTLtyping.type_function f with
  | [], _ | _, Errors.Error _ -> ([], PTree.empty)
  | _, Errors.OK env ->
  let is_float r =
    match env r with AST.Tfloat | AST.Tsingle -> true | _ -> false in
  (* Liveness analysis, to estimate register pressure *)
  let live_out = Array.make n IS.empty in
  let live_in = Array.make n IS.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for k = Array.length rpo - 1 downto 0 do
      let u = rpo.(k) in
      match instr.(u) with
      | None -> ()
      | Some i ->
          let out =
            List.fold_left (fun acc s -> if s < n then IS.union acc live_in.(s) else acc)
              IS.empty succs.(u) in
          live_out.(u) <- out;
          let defs = List.fold_left (fun acc r -> IS.add (P.to_int r) acc)
                       IS.empty (defs_all i) in
          let inn = List.fold_left (fun acc r -> IS.add (P.to_int r) acc)
                      (IS.diff out defs) (instr_uses i) in
          if not (IS.equal inn live_in.(u)) then begin
            live_in.(u) <- inn; changed := true
          end
    done
  done;
  let count_class fl s =
    IS.fold (fun r c -> if is_float (P.of_int r) = fl then c + 1 else c) s 0 in
  let is_call pc =
    match instr.(pc) with Some (Icall _) -> true | _ -> false in
  (* Register pressure at each node, for each class, including the
     registers hoisted so far.  We do not hoist out of loops that
     contain calls: hoisted registers would need to be callee-save
     (there are none for floats), and such loops are rarely limited by
     the cost of the operations we hoist. *)
  let pressure_int = Array.init n (fun pc -> count_class false live_out.(pc)) in
  let pressure_float = Array.init n (fun pc -> count_class true live_out.(pc)) in
  let fits l fl =
    let ok = ref true in
    Array.iteri (fun pc b ->
      if b && !ok then
        ok := not (is_call pc)
              && (if fl then pressure_float.(pc) < max_pressure_float
                  else pressure_int.(pc) < max_pressure_int))
      l.body;
    !ok in
  let reserve l fl =
    Array.iteri (fun pc b ->
      if b then begin
        if fl then pressure_float.(pc) <- pressure_float.(pc) + 1
        else pressure_int.(pc) <- pressure_int.(pc) + 1
      end) l.body in
  let next_reg = ref (P.succ (max_reg_function f)) in
  let next_pc = ref (P.of_int n) in
  let repl = ref PTree.empty in
  Array.iter (fun pc ->
    match instr.(pc) with
    | Some (Iop (op, args, res, _)) when hoistable op args ->
        let fl = is_float res in
        let candidates =
          List.filter (fun l ->
            l.body.(pc) && List.for_all (fun a -> not (Hashtbl.mem l.defs a)) args)
            loops in
        let hoist_to l =
          let t = !next_reg in
          next_reg := P.succ t;
          let p = !next_pc in
          next_pc := P.succ p;
          Hashtbl.add l.hoisted (op, args) t;
          l.chain <- (p, ((t, op), args)) :: l.chain;
          reserve l fl;
          t in
        let t =
          match List.find_map (fun l -> Hashtbl.find_opt l.hoisted (op, args)) candidates with
          | Some t -> Some t
          | None ->
              match List.find_opt (fun l -> fits l fl) candidates with
              | Some l -> Some (hoist_to l)
              | None -> None in
        begin match t with
        | Some t -> repl := PTree.set (P.of_int pc) t !repl
        | None -> ()
        end
    | _ -> ())
    rpo;
  let result =
    List.filter_map (fun l ->
      if l.chain = [] then None else begin
        let body = ref PTree.empty in
        Array.iteri (fun pc b -> if b then body := PTree.set (P.of_int pc) () !body) l.body;
        Some ((P.of_int l.header, !body), List.rev l.chain)
      end)
      loops in
  (result, !repl)
