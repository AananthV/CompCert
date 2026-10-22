(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(* Oracle for loop-invariant code motion.  Finds natural loops and
   chooses the operations to be hoisted out of them, including chains of
   dependent operations, and computes the equations between registers that
   justify the replacement of the operations of a chain by moves.  The
   results are validated by [LICM.check_function]. *)

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
   and 16 floating-point registers).  The estimate is the number of live
   pseudo-registers that are referenced in the loop, plus the hoisted
   registers that remain live throughout the loop.  It is pessimistic, since
   some pseudo-registers are coalesced by register allocation, hence the
   integer limit above the number of registers.  Intermediate results of
   hoisted chains, e.g. [i * 8800] in [base + i * 8800], are only live in
   the preheader and do not count. *)

let max_pressure_int = 16
let max_pressure_float = 14

(* Where the value of an argument of a loop-invariant operation comes from *)

type source =
  | Outside of P.t          (* not defined in the loop *)
  | Hoisted of int          (* defined by this loop-invariant operation *)
  | Copy of P.t * P.t       (* [a = b] in the loop, with [b] defined outside *)

type loop = {
  header: int;
  body: bool array;
  nodes: int array;                     (* the nodes of [body], in increasing order *)
  rnodes: int array;                    (* the nodes of [body], in reverse postorder *)
  size: int;
  hascall: bool;
  defcount: (P.t, int) Hashtbl.t;       (* number of definitions in the loop *)
  defnode: (P.t, int) Hashtbl.t;        (* the last definition found *)
  cands: (int, source list) Hashtbl.t;  (* loop-invariant operations *)
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

(* Loop rotation, LICM and IV widening run one after the other, and
   usually leave a function unchanged.  Its control-flow graph, natural
   loops and types are then computed only once: they are memoized,
   keyed on the physical identity of the function or of its code. *)

module PhysTbl (T: sig type t end) =
  Ephemeron.K1.Make(struct type t = T.t let equal = (==) let hash = Hashtbl.hash end)

module CodeTbl = PhysTbl(struct type t = code end)

let cfg_memo : (node * cfg) CodeTbl.t = CodeTbl.create 17

let build_cfg f =
  match CodeTbl.find_opt cfg_memo f.fn_code with
  | Some (e, g) when P.eq e f.fn_entrypoint -> g
  | _ ->
      let g = build_cfg f in
      CodeTbl.replace cfg_memo f.fn_code (f.fn_entrypoint, g);
      g

(* Dominators (Cooper, Harvey, Kennedy).  Returns the function
   [dominates a b]. *)

let dominators g =
  let n = g.n and rpo = g.rpo and entry = g.entry
  and preds = g.preds and visited = g.visited in
  let rponum = Array.make n (-1) in
  Array.iteri (fun k u -> rponum.(u) <- k) rpo;
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
  (* [a] dominates [b] iff [a] is an ancestor of [b] in the dominator
     tree, which is tested in constant time with the preorder and
     postorder numbers of a traversal of the tree. *)
  let children = Array.make n [] in
  Array.iter (fun u ->
    if u <> entry && idom.(u) >= 0 then children.(idom.(u)) <- u :: children.(idom.(u)))
    rpo;
  let pre = Array.make n (-1) and post = Array.make n (-1) in
  if Array.length rpo > 0 then begin
    let clock = ref 0 in
    let stack = ref [(entry, true)] in
    while !stack <> [] do
      let (u, enter) = List.hd !stack in
      stack := List.tl !stack;
      if enter then begin
        pre.(u) <- !clock; incr clock;
        stack := (u, false) :: !stack;
        List.iter (fun v -> stack := (v, true) :: !stack) children.(u)
      end else begin
        post.(u) <- !clock; incr clock
      end
    done
  end;
  let dominates a b =
    a = b
    || (pre.(a) >= 0 && pre.(b) >= 0 && pre.(a) <= pre.(b) && post.(b) <= post.(a)) in
  dominates

(* Natural loops, merged by header.  Returns a list of (header, body,
   nodes), where [body] is the characteristic array of the loop and
   [nodes] the array of its nodes in increasing order, along with the
   dominance relation. *)

let natural_loops_nodes g =
  let n = g.n and rpo = g.rpo and preds = g.preds and visited = g.visited in
  let dominates = dominators g in
  let bodies = Hashtbl.create 7 in
  let headers = ref [] in
  Array.iter (fun u ->
    List.iter (fun h ->
      if h < n && visited.(h) && dominates h u then begin
        let (body, nodes) =
          match Hashtbl.find_opt bodies h with
          | Some b -> b
          | None ->
              let b = (Array.make n false, ref []) in
              Hashtbl.add bodies h b; headers := h :: !headers; b in
        if not body.(h) then begin body.(h) <- true; nodes := h :: !nodes end;
        let stack = ref [u] in
        while !stack <> [] do
          let x = List.hd !stack in
          stack := List.tl !stack;
          if not body.(x) then begin
            body.(x) <- true;
            nodes := x :: !nodes;
            List.iter (fun p -> if visited.(p) then stack := p :: !stack) preds.(x)
          end
        done
      end)
      g.succs.(u))
    rpo;
  let loops =
    List.rev_map (fun h ->
      let (body, nodes) = Hashtbl.find bodies h in
      let nodes = Array.of_list !nodes in
      Array.sort compare nodes;
      (h, body, nodes)) !headers in
  (loops, dominates)

(* [true] if the loop of header [h] can only be entered through its header *)

let entered_by_header g h body nodes =
  (not body.(g.entry) || g.entry = h)
  && Array.for_all (fun s -> s = h || List.for_all (fun p -> body.(p)) g.preds.(s)) nodes

module CfgTbl = PhysTbl(struct type t = cfg end)

let loops_memo = CfgTbl.create 17

let natural_loops_nodes g =
  match CfgTbl.find_opt loops_memo g with
  | Some l -> l
  | None -> let l = natural_loops_nodes g in CfgTbl.replace loops_memo g l; l

(* Liveness analysis on reachable nodes: the registers live before and
   after each node.  Computed with a worklist, in postorder. *)

let liveness g =
  let n = g.n and rpo = g.rpo and instr = g.instr in
  let live_in = Array.make n IS.empty and live_out = Array.make n IS.empty in
  let rponum = Array.make n (-1) in
  Array.iteri (fun k u -> rponum.(u) <- k) rpo;
  let work = ref IS.empty in
  Array.iteri (fun k _ -> work := IS.add k !work) rpo;
  while not (IS.is_empty !work) do
    let k = IS.max_elt !work in
    work := IS.remove k !work;
    let u = rpo.(k) in
    match instr.(u) with
    | None -> ()
    | Some i ->
        let out =
          List.fold_left (fun acc s -> if s < n then IS.union acc live_in.(s) else acc)
            IS.empty g.succs.(u) in
        live_out.(u) <- out;
        let defs = List.fold_left (fun acc r -> IS.add (P.to_int r) acc)
                     IS.empty (defs_all i) in
        let inn = List.fold_left (fun acc r -> IS.add (P.to_int r) acc)
                    (IS.diff out defs) (instr_uses i) in
        if not (IS.equal inn live_in.(u)) then begin
          live_in.(u) <- inn;
          List.iter (fun p -> if rponum.(p) >= 0 then work := IS.add rponum.(p) !work)
            g.preds.(u)
        end
  done;
  (live_in, live_out)

module FunTbl = PhysTbl(struct type t = coq_function end)

let typing_memo = FunTbl.create 17

let type_function f =
  match FunTbl.find_opt typing_memo f with
  | Some t -> t
  | None -> let t = RTLtyping.type_function f in FunTbl.replace typing_memo f t; t

let licm_oracle f =
  let g = build_cfg f in
  let n = g.n and instr = g.instr
  and entry = g.entry and rpo = g.rpo in
  let (nloops, dominates) = natural_loops_nodes g in
  let rponum = Array.make n (-1) in
  Array.iteri (fun k u -> rponum.(u) <- k) rpo;
  (* Keep the loops that can only be entered through their header,
     taking unreachable nodes into account *)
  let loops = ref [] in
  List.iter (fun (h, body, nodes) ->
    if entered_by_header g h body nodes then begin
      let defcount = Hashtbl.create 17 and defnode = Hashtbl.create 17 in
      let hascall = ref false in
      Array.iter (fun pc ->
          match instr.(pc) with
          | Some i ->
              (match i with Icall _ -> hascall := true | _ -> ());
              List.iter (fun r ->
                Hashtbl.replace defcount r
                  (1 + Option.value ~default:0 (Hashtbl.find_opt defcount r));
                Hashtbl.replace defnode r pc) (defs_all i)
          | None -> ()) nodes;
      let rnodes = Array.copy nodes in
      Array.sort (fun x y -> compare rponum.(x) rponum.(y)) rnodes;
      loops := { header = h; body; nodes; rnodes; size = Array.length nodes; hascall = !hascall;
                 defcount; defnode; cands = Hashtbl.create 17;
                 hoisted = Hashtbl.create 7; chain = [] } :: !loops
    end) nloops;
  (* Outermost loops first *)
  let loops = List.sort (fun l1 l2 -> compare l2.size l1.size) !loops in
  match loops with
  | [] -> ([], PTree.empty), PTree.empty
  | _ ->
  match type_function f with
  | Errors.Error _ -> ([], PTree.empty), PTree.empty
  | Errors.OK env ->
  let is_float r =
    match env r with AST.Tfloat | AST.Tsingle -> true | _ -> false in
  let defcount l r = Option.value ~default:0 (Hashtbl.find_opt l.defcount r) in
  (* Loop-invariant operations of each loop, as a fixpoint: their arguments
     are defined outside the loop, by a loop-invariant operation that
     dominates them, or by a copy of a register defined outside the loop. *)
  List.iter (fun l ->
    let changed = ref true in
    while !changed do
      changed := false;
      Array.iter (fun x ->
        if not (Hashtbl.mem l.cands x) then
        match instr.(x) with
        | Some (Iop (op, args, res, _)) when hoistable op args && defcount l res = 1 ->
            let source a =
              match defcount l a with
              | 0 -> Some (Outside a)
              | 1 ->
                  let d = Hashtbl.find l.defnode a in
                  if d = x || not (dominates d x) then None
                  else if Hashtbl.mem l.cands d then Some (Hoisted d)
                  else begin match instr.(d) with
                    | Some (Iop (Omove, [b], _, _)) when defcount l b = 0 -> Some (Copy (a, b))
                    | _ -> None
                  end
              | _ -> None in
            let srcs = List.map source args in
            if List.for_all Option.is_some srcs then begin
              Hashtbl.add l.cands x (List.map Option.get srcs);
              changed := true
            end
        | _ -> ())
        l.rnodes
    done) loops;
  (* Liveness analysis, to estimate register pressure, computed on demand *)
  let live_out = lazy (snd (liveness g)) in
  let count_class fl s =
    IS.fold (fun r c -> if is_float (P.of_int r) = fl then c + 1 else c) s 0 in
  (* Register pressure at each node, for each class, including the
     registers hoisted so far.  We do not hoist out of loops that
     contain calls: hoisted registers would need to be callee-save
     (there are none for floats), and such loops are rarely limited by
     the cost of the operations we hoist. *)
  let extra_int = Array.make n 0 and extra_float = Array.make n 0 in
  (* Registers live at a node of a loop and referenced in this loop:
     registers that are live across the loop but not used in it can be
     spilled around the loop at little cost. *)
  let refs = Hashtbl.create 7 in
  let refs_of l =
    match Hashtbl.find_opt refs l.header with
    | Some r -> r
    | None ->
        let r = ref IS.empty in
        Array.iter (fun pc ->
          match instr.(pc) with
            | Some i ->
                List.iter (fun x -> r := IS.add (P.to_int x) !r) (instr_uses i @ defs_all i)
            | None -> ()) l.nodes;
        Hashtbl.add refs l.header !r; !r in
  let pressure l fl pc = count_class fl (IS.inter (Lazy.force live_out).(pc) (refs_of l)) in
  (* The pressures at the nodes of a loop, in the order of [l.nodes],
     for the integer and the floating-point classes *)
  let pressures = Hashtbl.create 7 in
  let pressures_of l =
    match Hashtbl.find_opt pressures l.header with
    | Some p -> p
    | None ->
        let p = (Array.map (pressure l false) l.nodes, Array.map (pressure l true) l.nodes) in
        Hashtbl.add pressures l.header p; p in
  (* Users of each register *)
  let users = Hashtbl.create 97 in
  Array.iteri (fun pc i ->
    match i with
    | Some i when g.visited.(pc) ->
        List.iter (fun r -> Hashtbl.replace users r
                     (pc :: Option.value ~default:[] (Hashtbl.find_opt users r)))
          (instr_uses i)
    | _ -> ()) instr;
  let dest x = match instr.(x) with Some (Iop (_, _, r, _)) -> r | _ -> assert false in
  (* Selected operations: node -> (loop, hoisted register) *)
  let selected = Hashtbl.create 17 in
  let next_reg = ref (P.succ (max_reg_function f)) in
  let next_pc = ref (P.of_int n) in
  (* A hoisted register costs a register throughout the loop if the
     destination of one of the replaced operations is used by an
     instruction that is not replaced. *)
  let costly l x =
    List.exists (fun y ->
      match Hashtbl.find_opt selected y with
      | Some (l', _) -> l' != l
      | None -> true)
      (Option.value ~default:[] (Hashtbl.find_opt users (dest x))) in
  let hargs_of srcs =
    List.map (function
      | Outside a -> a
      | Copy (_, b) -> b
      | Hoisted d -> snd (Hashtbl.find selected d)) srcs in
  (* Try to hoist [x] and the operations it depends on out of loop [l] *)
  let try_hoist l x =
    (* Dependencies first *)
    let order = ref [] and seen = Hashtbl.create 7 and ok = ref true in
    let rec visit y =
      if not (Hashtbl.mem seen y) then begin
        Hashtbl.add seen y ();
        match Hashtbl.find_opt selected y with
        | Some (l', _) -> if l' != l then ok := false
        | None ->
            List.iter (function Hoisted d -> visit d | _ -> ()) (Hashtbl.find l.cands y);
            order := y :: !order
      end in
    visit x;
    let order = List.rev !order in
    if not !ok || order = [] then false else begin
      (* Tentatively select, then evaluate the cost *)
      let fresh = ref [] in
      List.iter (fun y ->
        let key = (match instr.(y) with Some (Iop (op, _, _, _)) -> op | _ -> assert false),
                  hargs_of (Hashtbl.find l.cands y) in
        let t =
          match Hashtbl.find_opt l.hoisted key with
          | Some t -> t
          | None ->
              let t = !next_reg in
              next_reg := P.succ t;
              Hashtbl.add l.hoisted key t;
              fresh := (key, t, y) :: !fresh;
              t in
        Hashtbl.replace selected y (l, t)) order;
      let dint = ref 0 and dfloat = ref 0 in
      List.iter (fun (_, t, y) ->
        let members = Hashtbl.fold (fun z (l', t') acc ->
          if l' == l && P.eq t t' then z :: acc else acc) selected [] in
        if List.exists (costly l) members then
          (if is_float (dest y) then incr dfloat else incr dint)) !fresh;
      let fits =
        not l.hascall &&
        (!dint = 0 && !dfloat = 0 ||
         let (pint, pfloat) = pressures_of l in
         let ok = ref true in
         Array.iteri (fun k pc ->
           if !ok then
             ok := (!dint = 0 || pint.(k) + extra_int.(pc) + !dint <= max_pressure_int)
                   && (!dfloat = 0
                       || pfloat.(k) + extra_float.(pc) + !dfloat <= max_pressure_float))
           l.nodes;
         !ok) in
      if fits then begin
        Array.iter (fun pc ->
            extra_int.(pc) <- extra_int.(pc) + !dint;
            extra_float.(pc) <- extra_float.(pc) + !dfloat) l.nodes;
        List.iter (fun ((op, hargs), t, _) ->
          let p = !next_pc in
          next_pc := P.succ p;
          l.chain <- (p, ((t, op), hargs)) :: l.chain) (List.rev !fresh);
        true
      end else begin
        List.iter (fun y -> Hashtbl.remove selected y) order;
        List.iter (fun (key, _, _) -> Hashtbl.remove l.hoisted key) !fresh;
        false
      end
    end in
  (* Candidates whose results are used by other instructions than
     candidates are the roots of the chains to be hoisted. *)
  let is_cand = Array.make n false in
  List.iter (fun l -> Hashtbl.iter (fun x _ -> is_cand.(x) <- true) l.cands) loops;
  Array.iter (fun x ->
    if is_cand.(x) && not (Hashtbl.mem selected x) then begin
      let inloops = List.filter (fun l -> Hashtbl.mem l.cands x) loops in
      let is_root l =
        List.exists (fun y -> not (l.body.(y) && Hashtbl.mem l.cands y))
          (Option.value ~default:[] (Hashtbl.find_opt users (dest x))) in
      ignore (List.exists (fun l -> is_root l && try_hoist l x) inloops)
    end) rpo;
  (* Equations needed by the replaced operations *)
  let needed = Hashtbl.create 17 in
  (* The equations needed by the replaced operation [x], or [None] if one
     of the operations it depends on is no longer replaced *)
  let needs x =
    let (l, _) = Hashtbl.find selected x in
    List.fold_left (fun acc src ->
      match acc, src with
      | None, _ -> None
      | Some acc, Outside _ -> Some acc
      | Some acc, Copy (a, b) -> Some ((a, b) :: acc)
      | Some acc, Hoisted d ->
          match Hashtbl.find_opt selected d with
          | Some (_, t) -> Some ((dest d, t) :: acc)
          | None -> None)
      (Some []) (Hashtbl.find l.cands x) in
  let headers = Hashtbl.create 7 in
  List.iter (fun l -> if l.chain <> [] then Hashtbl.replace headers l.header ()) loops;
  let eqs = Array.make n None in
  let rec compute () =
    Hashtbl.reset needed;
    Hashtbl.iter (fun x _ ->
      List.iter (fun e -> Hashtbl.replace needed e ())
        (Option.value ~default:[] (needs x))) selected;
    let tinstr pc =
      match instr.(pc), Hashtbl.find_opt selected pc with
      | Some (Iop (_, _, res, s)), Some (_, t) -> Some (Iop (Omove, [t], res, s))
      | i, _ -> i in
    let transfer pc e =
      match tinstr pc with
      | None -> []
      | Some i ->
          let d = defs_all i in
          let e = List.filter (fun (x, y) -> not (List.mem x d) && not (List.mem y d)) e in
          match i with
          | Iop (Omove, [y], x, _) when Hashtbl.mem needed (x, y) && not (List.mem (x, y) e) ->
              (x, y) :: e
          | _ -> e in
    Array.fill eqs 0 n None;
    let changed = ref true in
    while !changed do
      changed := false;
      Array.iter (fun s ->
        let v =
          if s = entry || Hashtbl.mem headers s then []
          else begin
            (* Unreachable predecessors are not analyzed: the equations
               cannot be assumed to hold there *)
            let ins = List.filter_map (fun p ->
              if g.visited.(p) then Option.map (transfer p) eqs.(p)
              else Some (transfer p [])) g.preds.(s) in
            match ins with
            | [] -> []
            | e :: es -> List.filter (fun x -> List.for_all (List.mem x) es) e
          end in
        let v = List.sort compare v in
        if eqs.(s) <> Some v then begin eqs.(s) <- Some v; changed := true end)
        rpo
    done;
    (* Drop the replacements whose equations are not available *)
    let bad = Hashtbl.fold (fun x _ acc ->
      let e = Option.value ~default:[] eqs.(x) in
      match needs x with
      | Some nd when List.for_all (fun p -> List.mem p e) nd -> acc
      | _ -> x :: acc) selected [] in
    if bad <> [] then begin
      List.iter (Hashtbl.remove selected) bad;
      compute ()
    end in
  (* Without replaced operations, there are no equations *)
  if Hashtbl.length selected > 0 then compute ();
  let repl = Hashtbl.fold (fun x (_, t) acc -> PTree.set (P.of_int x) t acc) selected PTree.empty in
  let eqtree = ref PTree.empty in
  Array.iteri (fun pc e ->
    match e with
    | Some (_ :: _ as l) -> eqtree := PTree.set (P.of_int pc) l !eqtree
    | _ -> ()) eqs;
  let result =
    List.filter_map (fun l ->
      if l.chain = [] then None else begin
        let body = ref PTree.empty in
        Array.iter (fun pc -> body := PTree.set (P.of_int pc) () !body) l.nodes;
        Some ((P.of_int l.header, !body), List.rev l.chain)
      end)
      loops in
  ((result, repl), !eqtree)
