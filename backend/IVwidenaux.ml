(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(* Oracle for induction-variable widening and strength reduction.
   Chooses the induction variables of the loops, the instructions
   inserted on the edges that enter the loops and after the increments,
   and the rewritings of the instructions, and computes the facts that
   justify them.  The results are validated by [IVwiden.check_function]. *)

open! Camlcoq
open Maps
open AST
open RTL
open IVop
open IVdomain

(* Facts *)

(* Lists of facts are kept sorted by [kcmp], with at most one upper bound
   and one lower bound per register. *)

let tag = function Flin _ -> 0 | Feq _ -> 1 | Fle _ -> 2 | Fge _ -> 3

let kcmp f1 f2 =
  match f1, f2 with
  | Fle (i1, _), Fle (i2, _) | Fge (i1, _), Fge (i2, _) -> compare i1 i2
  | _ -> let c = compare (tag f1) (tag f2) in if c <> 0 then c else compare f1 f2

(* Keep the tightest bounds only, and remove duplicates. *)

let normalize l =
  let rec dedup = function
    | a :: b :: rest when kcmp a b = 0 ->
        let m = match a, b with
          | Fle (i, k1), Fle (_, k2) -> Fle (i, Z.min k1 k2)
          | Fge (i, k1), Fge (_, k2) -> Fge (i, Z.max k1 k2)
          | _ -> a in
        dedup (m :: rest)
    | a :: rest -> a :: dedup rest
    | [] -> [] in
  dedup (List.sort kcmp l)

(* The facts implied by both [l1] and [l2] (both normalized) *)

let rec meet l1 l2 =
  match l1, l2 with
  | [], _ | _, [] -> []
  | a :: r1, b :: r2 ->
      let c = kcmp a b in
      if c < 0 then meet r1 l2
      else if c > 0 then meet l1 r2
      else (match a, b with
            | Fle (i, k1), Fle (_, k2) -> Fle (i, Z.max k1 k2)
            | Fge (i, k1), Fge (_, k2) -> Fge (i, Z.min k1 k2)
            | _ -> a) :: meet r1 r2

(* Widening: the new facts [v] at a node, given the previous facts [old]
   (both normalized).  Facts only decrease; a bound that weakens is
   widened to the next threshold. *)

let rec widen widen_up widen_down old v =
  match old, v with
  | [], _ | _, [] -> []
  | a :: r1, b :: r2 ->
      let c = kcmp a b in
      if c < 0 then widen widen_up widen_down r1 v
      else if c > 0 then widen widen_up widen_down old r2
      else
        let rest = widen widen_up widen_down r1 r2 in
        match a, b with
        | Fle (_, k'), Fle (i, k) when Z.gt k k' ->
            (match widen_up k with Some t -> Fle (i, t) :: rest | None -> rest)
        | Fge (_, k'), Fge (i, k) when Z.lt k k' ->
            (match widen_down k with Some t -> Fge (i, t) :: rest | None -> rest)
        | _ -> b :: rest

(* Forward dataflow analysis over the transformed code [tc], computing
   the facts that hold at each node.  When a bound changes at a node, it
   is widened to the next threshold, taken from the constants of the
   comparisons of the function.  Returns [None] if the analysis does not
   converge. *)

let max_iterations = 100

let thresholds f =
  let s = ref [Z.sub Integers.Int.max_signed Z.one; Integers.Int.max_signed;
               Z.add Integers.Int.min_signed Z.one; Integers.Int.min_signed; Z.zero] in
  let add k =
    if Z.le Integers.Int.min_signed k && Z.le k Integers.Int.max_signed then
      s := Z.sub k Z.one :: k :: Z.add k Z.one :: !s in
  PTree.fold (fun () _ i ->
    match i with
    | Icond (cond, args, _, _) ->
        (match classify_cond cond args with
         | CCcmpimm (_, _, k) -> add (Integers.Int.signed k)
         | CCcmplimm (_, _, k) -> add (Integers.Int64.signed k)
         | _ -> ())
    | _ -> ()) f.fn_code ();
  List.sort_uniq Z.compare !s

let solve relevant f tc =
  let g = LICMaux.build_cfg { f with fn_code = tc } in
  let n = g.LICMaux.n and entry = g.LICMaux.entry in
  let facts = Array.make n None in
  if entry < n then facts.(entry) <- Some [];
  let ths = thresholds f in
  let widen_up k = List.find_opt (fun t -> Z.le k t) ths in
  let widen_down k = List.fold_left (fun acc t -> if Z.le t k then Some t else acc) None ths in
  let contrib p s =
    let l = if g.LICMaux.visited.(p) then facts.(p) else Some [] in
    match l, g.LICMaux.instr.(p) with
    | None, _ | _, None -> []
    | Some l, Some (Icond (cond, args, s1, s2)) ->
        (if P.to_int s1 = s then [transfer_cond l cond args true] else [])
        @ (if P.to_int s2 = s then [transfer_cond l cond args false] else [])
    | Some l, Some i -> [transfer l i] in
  (* Worklist, in reverse postorder *)
  let rponum = Array.make n max_int in
  Array.iteri (fun k u -> rponum.(u) <- k) g.LICMaux.rpo;
  let module WS = Set.Make(Int) in
  let work = ref (Array.fold_left (fun w u -> WS.add rponum.(u) w) WS.empty g.LICMaux.rpo) in
  let steps = ref 0 and limit = max_iterations * Array.length g.LICMaux.rpo in
  while not (WS.is_empty !work) && !steps < limit do
    let k = WS.min_elt !work in
    work := WS.remove k !work;
    incr steps;
    let s = g.LICMaux.rpo.(k) in
    if s <> entry then begin
      let cs = List.map (List.filter (relevant s))
              (List.concat_map (fun p -> contrib p s) g.LICMaux.preds.(s)) in
      match cs with
      | [] -> ()
      | l0 :: ls ->
          let v = List.fold_left (fun acc l -> meet acc (normalize l)) (normalize l0) ls in
          let v =
            match facts.(s) with
            | None -> v
            | Some old -> widen widen_up widen_down old v in
          if facts.(s) <> Some v then begin
            facts.(s) <- Some v;
            List.iter (fun s' ->
              if s' < n && rponum.(s') < max_int then work := WS.add rponum.(s') !work)
              g.LICMaux.succs.(s)
          end
    end
  done;
  if WS.is_empty !work then Some facts else None

let facts_of facts pc =
  if pc < Array.length facts then Option.value ~default:[] facts.(pc) else []

(* Induction variables *)

type iv = {
  ivreg: P.t;                   (* the 32-bit induction variable *)
  lreg: P.t;                    (* its 64-bit version *)
  header: int;
  body: bool array;
  incr: int;                    (* the node [ivreg = ivreg + step] *)
  step: Integers.Int.int;
}

(* Derived induction variables [dreg = base + (long) ivreg * mul] *)

type div = {
  dreg: P.t;
  dbase: P.t option;
  dmul: Integers.Int64.int;
  dfor: iv;
}

(* Maximal estimated integer register pressure in a loop after the
   transformation (see [LICMaux]), for the 64-bit versions of the
   induction variables and for the derived induction variables, which
   replace multiplications *)

let max_pressure_int = 14
let max_pressure_derived = 16

(* Maximal size of the function times its number of loops *)

let max_size = 20_000_000

let add_edge edges u s gi =
  let k = (u, s) in
  Hashtbl.replace edges k (Option.value ~default:[] (Hashtbl.find_opt edges k) @ [gi])

let iv_oracle f =
  let none = ((([], PTree.empty), PTree.empty), PTree.empty) in
  match mk_sext, mk_addl with
  | None, _ | _, None -> none
  | Some sext_op, Some addl_op ->
  let g = LICMaux.build_cfg f in
  let n = g.LICMaux.n and instr = g.LICMaux.instr and entry = g.LICMaux.entry in
  let succs = g.LICMaux.succs and preds = g.LICMaux.preds in
  (* Give up on functions with many loops: the loop bodies are
     represented by arrays of the size of the function *)
  let rponum = Array.make n (-1) in
  Array.iteri (fun k u -> rponum.(u) <- k) g.LICMaux.rpo;
  let nheaders = ref 0 in
  Array.iter (fun v ->
    if List.exists (fun u -> rponum.(u) >= rponum.(v)) preds.(v) then incr nheaders)
    g.LICMaux.rpo;
  if n * !nheaders > max_size then none else
  (* Loops that can only be entered through their header, outermost first *)
  let nloops =
    List.sort (fun (_, _, n1) (_, _, n2) -> compare (Array.length n2) (Array.length n1))
      (List.filter (fun (h, b, nodes) -> h <> entry && LICMaux.entered_by_header g h b nodes)
         (fst (LICMaux.natural_loops_nodes g))) in
  let loops = List.map (fun (h, b, _) -> (h, b)) nloops in
  (* The nodes of a loop body, in increasing order *)
  let nodes_of body =
    match List.find_opt (fun (_, b, _) -> b == body) nloops with
    | Some (_, _, nodes) -> nodes
    | None -> assert false in
  if loops = [] then none else
  match LICMaux.type_function f with
  | Errors.Error _ -> none
  | Errors.OK env -> begin
  let mr = max_reg_function f in
  let next_reg = ref (P.succ mr) in
  let fresh_reg () = let r = !next_reg in next_reg := P.succ r; r in
  let is_int r = env r = Tint in
  let is_new r = P.lt mr r in
  (* Liveness analysis on the original code, for the cost heuristics *)
  let module IS = Set.Make(Int) in
  let liveness = lazy (LICMaux.liveness g) in
  let live_in s = (fst (Lazy.force liveness)).(s)
  and live_out s = (snd (Lazy.force liveness)).(s) in
  let is_int_class r = match env (P.of_int r) with Tfloat | Tsingle -> false | _ -> true in
  let users = Hashtbl.create 97 in
  Array.iteri (fun pc i ->
    match i with
    | Some i -> List.iter (fun r -> Hashtbl.add users r pc) (instr_uses i)
    | None -> ()) instr;
  let users_of r = List.sort_uniq compare (Hashtbl.find_all users r) in
  let memo_body compute =
    let cache = ref [] in
    fun body ->
      match List.assq_opt body !cache with
      | Some x -> x
      | None -> let x = compute body in cache := (body, x) :: !cache; x in
  let defs_of = memo_body (fun body ->
    let h = Hashtbl.create 17 in
    Array.iter (fun pc ->
      match instr.(pc) with
        | Some i -> List.iter (fun r -> Hashtbl.replace h r ()) (LICMaux.defs_all i)
        | None -> ()) (nodes_of body);
    h) in
  let defined_in body r = Hashtbl.mem (defs_of body) r in
  let exits_of = memo_body (fun body ->
    let l = ref [] in
    Array.iter (fun pc ->
      List.iter (fun s -> if s < n && not body.(s) then l := s :: !l) succs.(pc)) (nodes_of body);
    List.sort_uniq compare !l) in
  let live_at_exit body r =
    List.exists (fun s -> IS.mem (P.to_int r) (live_in s)) (exits_of body) in
  let is_sext_of t pc =
    match instr.(pc) with
    | Some (Iop (op, args, res, _)) ->
        (match classify_op op args with OCsext t' -> P.eq t t' && not (P.eq t res) | _ -> false)
    | _ -> false in
  (* Estimated register pressure: integer registers live after a node of
     the loop and referenced in the loop *)
  let base_pressure = memo_body (fun body ->
    let rf = ref IS.empty in
    let nodes = nodes_of body in
    Array.iter (fun pc ->
      match instr.(pc) with
        | Some i -> List.iter (fun x -> rf := IS.add (P.to_int x) !rf) (instr_uses i @ LICMaux.defs_all i)
        | None -> ()) nodes;
    let rf = IS.filter is_int_class !rf in
    Array.map (fun pc -> IS.cardinal (IS.inter (live_out pc) rf)) nodes) in
  let extra = Array.make n 0 in
  (* [base_pressure body] is indexed like [nodes_of body] *)
  let pressure body =
    let bp = base_pressure body in
    let p = ref 0 in
    Array.iteri (fun k pc -> p := max !p (bp.(k) + extra.(pc))) (nodes_of body);
    !p in
  (* In loops that contain calls, the registers live across the calls must
     be callee-save: do not increase the register pressure *)
  let has_call = memo_body (fun body ->
    Array.exists (fun pc ->
      match instr.(pc) with Some (Icall _) -> true | _ -> false) (nodes_of body)) in
  let limit body = if has_call body then 0 else max_pressure_int in
  let charge body cost =
    Array.iter (fun pc -> extra.(pc) <- extra.(pc) + cost) (nodes_of body) in
  (* Choose the induction variables, each in the outermost loop where it
     is incremented exactly once *)
  let assigned = Hashtbl.create 7 in
  let cands = ref [] in
  List.iter (fun (h, body) ->
    let nodes = nodes_of body in
    let defcount = Hashtbl.create 17 in
    Array.iter (fun pc ->
      match instr.(pc) with
        | Some i ->
            List.iter (fun r ->
              Hashtbl.replace defcount r (1 + Option.value ~default:0 (Hashtbl.find_opt defcount r)))
              (LICMaux.defs_all i)
        | None -> ()) nodes;
    let defs r = Option.value ~default:0 (Hashtbl.find_opt defcount r) in
    Array.iter (fun pc ->
      match instr.(pc) with
        | Some (Iop (op, args, res, _)) ->
            (match classify_op op args with
             | OCaddimm (a, c) when P.eq a res && defs res = 1 && is_int res
                                   && not (List.exists (fun b -> b.(h)) (Hashtbl.find_all assigned res)) ->
                 Hashtbl.add assigned res body;
                 cands := { ivreg = res; lreg = fresh_reg (); header = h; body;
                            incr = pc; step = c } :: !cands
             | _ -> ())
        | _ -> ()) nodes)
    loops;
  (* The 32-bit variables sign-extended in the loop ([iv] or [iv + c]),
     the registers needed for the bounds of the comparisons, and whether
     the 32-bit variable remains live *)
  let summary v =
    let body = v.body in
    let sexts = ref [] and bounds = ref [] and keep = ref (live_at_exit body v.ivreg) in
    let add_sext t = if not (List.exists (P.eq t) !sexts) then sexts := t :: !sexts in
    List.iter (fun pc ->
      if not body.(pc) || pc = v.incr then ()
      else if is_sext_of v.ivreg pc then add_sext v.ivreg
      else match instr.(pc) with
        | Some (Iop (op, args, t, _)) ->
            (match classify_op op args with
             | OCaddimm (a, _) when P.eq a v.ivreg && not (P.eq t v.ivreg) ->
                 let us = users_of t in
                 if List.exists (is_sext_of t) us then add_sext t;
                 if not (List.for_all (fun u -> body.(u) && is_sext_of t u) us
                         && not (live_at_exit body t))
                 then keep := true
             | _ -> keep := true)
        | Some (Icond (cond, args, _, _)) ->
            (match classify_cond cond args with
             | CCcmp (c, a, b) when mk_cmpl c <> None && (P.eq a v.ivreg || P.eq b v.ivreg) ->
                 let o = if P.eq a v.ivreg then b else a in
                 if P.eq o v.ivreg || not (is_int o) || defined_in body o then keep := true
                 else if not (List.exists (P.eq o) !bounds) then bounds := o :: !bounds
             | CCcmpimm (_, a, _) when P.eq a v.ivreg -> ()
             | _ -> keep := true)
        | _ -> keep := true)
      (users_of v.ivreg);
    (List.length !sexts, List.length !bounds, !keep) in
  let ivs =
    List.filter (fun v ->
      let (nsext, nbounds, keep) = summary v in
      let cost = 1 + nbounds - (if keep then 0 else 1) in
      let p = pressure v.body in
      let ok = (nsext >= 2 || (nsext >= 1 && not keep))
               && (cost <= 0 || p + cost <= limit v.body) in
      if ok && cost > 0 then charge v.body cost;
      ok)
      (List.rev !cands) in
  if ivs = [] then none else begin
  (* The registers whose facts are tracked: the induction variables,
     the variables [iv + c] of their loops, the bounds of their
     comparisons, and the new registers *)
  let relevant ivs =
    let r = Hashtbl.create 17 in
    List.iter (fun v ->
      Hashtbl.replace r v.ivreg ();
      List.iter (fun pc ->
        if v.body.(pc) then match instr.(pc) with
          | Some (Iop (op, args, t, _)) ->
              (match classify_op op args with
               | OCaddimm (a, _) when P.eq a v.ivreg -> Hashtbl.replace r t ()
               | _ -> ())
          | Some (Icond (cond, args, _, _)) ->
              (match classify_cond cond args with
               | CCcmp (_, a, b) -> Hashtbl.replace r a (); Hashtbl.replace r b ()
               | _ -> ())
          | _ -> ()) (users_of v.ivreg)) ivs;
    (* Copies are tracked for the arguments of the addressing modes of the
       loops *)
    let addr = Hashtbl.create 17 in
    List.iter (fun v ->
      Array.iter (fun pc ->
        match instr.(pc) with
          | Some (Iload (_, _, args, _, _)) | Some (Istore (_, _, args, _, _)) ->
              List.iter (fun a -> Hashtbl.replace addr a ()) args
          | _ -> ()) (nodes_of v.body)) ivs;
    (* Facts about registers of the function that are dead are useless *)
    let live s x = is_new x || s >= n || IS.mem (P.to_int x) (live_in s) in
    fun s f ->
      match f with
      | Flin (x, _, i, _, _) -> Hashtbl.mem r i && live s x
      | Fle (i, _) | Fge (i, _) -> Hashtbl.mem r i
      | Feq (x, y) -> Hashtbl.mem addr x && live s x in
  (* Construction of the transformed code *)
  let build ivs divs hints =
    let edges = Hashtbl.create 17 in
    let hints = ref hints in
    let bounds = Hashtbl.create 7 in   (* (header, register) -> 64-bit version *)
    List.iter (fun v ->
      let body = v.body in
      let entering = List.filter (fun u -> not body.(u)) preds.(v.header) in
      let init gi = List.iter (fun u -> add_edge edges u v.header gi) entering in
      init (v.lreg, sext_op, [v.ivreg]);
      let s = match instr.(v.incr) with Some (Iop (_, _, _, s)) -> P.to_int s | _ -> assert false in
      let cstep = Integers.Int64.repr (Integers.Int.signed v.step) in
      (match mk_addlimm cstep with
       | Some op -> add_edge edges v.incr s (v.lreg, op, [v.lreg])
       | None -> ());
      List.iter (fun d ->
        if d.dfor == v then begin
          let scaled =
            if Integers.Int64.eq d.dmul Integers.Int64.one then v.lreg
            else match d.dbase with
              | None -> d.dreg
              | Some _ -> fresh_reg () in
          (if not (P.eq scaled v.lreg) then
             match mk_mullimm d.dmul with
             | Some op -> init (scaled, op, [v.lreg])
             | None -> ());
          (match d.dbase with
           | Some b -> init (d.dreg, addl_op, [b; scaled])
           | None -> ());
          match mk_addlimm (Integers.Int64.mul d.dmul cstep) with
          | Some op -> add_edge edges v.incr s (d.dreg, op, [d.dreg])
          | None -> ()
        end) divs;
      let bound r =
        match Hashtbl.find_opt bounds (v.header, r) with
        | Some lr -> lr
        | None ->
            let lr = fresh_reg () in
            Hashtbl.add bounds (v.header, r) lr;
            init (lr, sext_op, [r]);
            lr in
      Array.iter (fun pc ->
        if PTree.get (P.of_int pc) !hints = None then
          match instr.(pc) with
          | Some (Icond (cond, args, _, _)) ->
              let h =
                match classify_cond cond args with
                | CCcmp (c, a, b) when mk_cmpl c <> None ->
                    if P.eq a v.ivreg && not (P.eq b v.ivreg) && is_int b && not (defined_in body b)
                    then Some (Hcond (v.lreg, bound b))
                    else if P.eq b v.ivreg && not (P.eq a v.ivreg) && is_int a
                            && not (defined_in body a)
                    then Some (Hcond (bound a, v.lreg))
                    else None
                | CCcmpimm (c, a, k) when P.eq a v.ivreg
                      && mk_cmplimm c (Integers.Int64.repr (Integers.Int.signed k)) <> None ->
                    Some (Hcond (v.lreg, v.lreg))
                | _ -> None in
              (match h with Some h -> hints := PTree.set (P.of_int pc) h !hints | None -> ())
          | _ -> ()) (nodes_of body))
      ivs;
    (* New nodes on the edges *)
    let next_pc = ref (P.of_int n) in
    let ghosts = ref [] and redir = ref PTree.empty in
    Hashtbl.iter (fun (u, s) gis ->
      let nodes = List.map (fun gi -> let p = !next_pc in next_pc := P.succ p; (p, gi)) gis in
      let rec chain = function
        | [] -> ()
        | (p, (t, op, args)) :: rest ->
            let nxt = match rest with [] -> P.of_int s | (p', _) :: _ -> p' in
            ghosts := (p, Iop (op, args, t, nxt)) :: !ghosts;
            chain rest in
      chain nodes;
      let u' = P.of_int u in
      let l = Option.value ~default:[] (PTree.get u' !redir) in
      redir := PTree.set u' ((P.of_int s, fst (List.hd nodes)) :: l) !redir)
      edges;
    (!ghosts, !redir, !hints) in
  let make_code ghosts redir hints =
    let c = PTree.map (transf_instr redir hints) f.fn_code in
    List.fold_left (fun c (p, i) -> PTree.set p i c) c ghosts in
  let in_loops ivs pc = List.exists (fun v -> v.body.(pc)) ivs in
  (* The values computed by the operations of the loops *)
  let values ivs facts =
    PTree.fold (fun acc pc i ->
      let p = P.to_int pc in
      match i with
      | Iop (Op.Omove, _, _, _) -> acc
      | Iop (op, args, res, _) when in_loops ivs p ->
          let gen = gen_op (facts_of facts p) op args res in
          List.fold_left (fun acc f ->
            match f with
            | Flin (x, b, t, m, d) when P.eq x res && fresh_for res b t -> (pc, i, b, t, m, d) :: acc
            | _ -> acc) acc gen
      | _ -> acc) f.fn_code [] in
  (* Rewritings of the operations whose values are available in a new
     register *)
  let replacements ivs facts hints =
    List.fold_left (fun hints (pc, i, b, t, m, d) ->
      if PTree.get pc hints <> None then hints else begin
        let l = facts_of facts (P.to_int pc) in
        match List.find_opt (fun f ->
                match f with
                | Flin (y, b', t', m', _) ->
                    is_new y && b' = b && P.eq t' t && m' = m
                | _ -> false) l with
        | Some (Flin (y, _, _, _, d')) ->
            let h = Hrepl (y, b, t, m, d, d') in
            if hint_ok l i h then PTree.set pc h hints else hints
        | _ -> hints
      end) hints (values ivs facts) in
  (* Remove the hints that are not justified by the facts, until the
     facts and the hints agree *)
  let rec refine ghosts redir hints rounds =
    if rounds = 0 then None else
    let tc = make_code ghosts redir hints in
    match solve (relevant ivs) f tc with
    | None -> None
    | Some facts ->
        let bad = List.filter (fun (pc, h) ->
          match PTree.get pc f.fn_code with
          | Some i -> not (hint_ok (facts_of facts (P.to_int pc)) i h)
          | None -> true) (PTree.elements hints) in
        if bad = [] then Some (tc, facts, hints)
        else refine ghosts redir
               (List.fold_left (fun h (pc, _) -> PTree.remove pc h) hints bad) (rounds - 1) in
  (* Rewritings of the addressing modes of loads and stores: offsets
     [r = y + d] used as indices are folded into the addressing mode, and
     [b + r] is replaced by [y] if [y = b + r + d].  These rewritings do
     not change the facts. *)
  let addr_hints facts hints =
    let hints = ref hints in
    PTree.fold (fun () pc i ->
      if PTree.get pc !hints = None then begin
        let l = facts_of facts (P.to_int pc) in
        let set h = if PTree.get pc !hints = None && hint_ok l i h then hints := PTree.set pc h !hints in
        let lin_of r =
          List.filter_map (function
            | Flin (r', None, t, m, d) when P.eq r' r -> Some (t, m, d)
            | _ -> None) l in
        let try_base addr args b r =
          List.iter (fun (t, m, d1) ->
            List.iter (function
              | Flin (y, Some b', t', m', d2) when P.eq b' b && P.eq t' t && m' = m && is_new y ->
                  if rebase_addr addr args b r y (Integers.Int64.sub d1 d2) <> None
                  then set (Hbase (b, r, y, t, m, d1, d2))
              | _ -> ()) l) (lin_of r) in
        let try_index addr args =
          List.iter (fun r ->
            List.iter (fun (t, m, d1) ->
              List.iter (function
                | Flin (y, None, t', m', d2) when P.eq t' t && m' = m && is_new y
                                                  && not (P.eq y r) && d1 <> d2 ->
                    if shift_addr addr args r y (Integers.Int64.sub d1 d2) <> None
                    then set (Haddr (r, y, t, m, d1, d2))
                | _ -> ()) l) (lin_of r)) args in
        (* Offsets of the base register *)
        let try_bshift args =
          List.iter (fun r ->
            List.iter (function
              | Flin (r', b, t, m, d1) when P.eq r' r ->
                  List.iter (function
                    | Flin (y, b', t', m', d2) when is_new y && not (P.eq y r) && b' = b
                                                     && P.eq t' t && m' = m && d1 <> d2 ->
                        if shift_base (match i with Iload (_, a, _, _, _) | Istore (_, a, _, _, _) -> a
                                                    | _ -> assert false)
                                      args r y (Integers.Int64.sub d1 d2) <> None
                        then set (Hbshift (r, y, b, t, m, d1, d2))
                    | _ -> ()) l
              | _ -> ()) l) args in
        (* Copies of new registers, and copies of other registers *)
        let try_subst args =
          let sl = List.filter_map (fun r ->
            if is_new r then None else
            match List.find_map (function
                    | Flin (r', b, t, m, d) when P.eq r' r ->
                        List.find_map (function
                          | Flin (y, b', t', m', d') when is_new y && b' = b && P.eq t' t
                                                           && m' = m && d' = d -> Some (r, y)
                          | _ -> None) l
                    | _ -> None) l with
            | Some e -> Some e
            | None ->
                List.find_map (function
                  | Feq (r', y) when P.eq r' r && not (P.eq y r) -> Some (r, y)
                  | _ -> None) l) (List.sort_uniq compare args) in
          if sl <> [] then set (Hsubst sl) in
        match i with
        | Iload (_, addr, args, _, _) | Istore (_, addr, args, _, _) ->
            (match addr_base_index addr args with
             | Some (b, r) -> try_base addr args b r; try_base addr args r b
             | None -> ());
            try_index addr args;
            try_bshift args;
            try_subst args
        | _ -> ()
      end) f.fn_code ();
    !hints in
  (* Complete construction: comparisons, then replacements *)
  let construct ivs divs =
    let (ghosts, redir, hints) = build ivs divs PTree.empty in
    let rec rounds hints k =
      match refine ghosts redir hints 10 with
      | None -> None
      | Some (tc, facts, hints) ->
          let hints' = replacements ivs facts hints in
          if k = 0 || PTree.elements hints' = PTree.elements hints
          then Some (ghosts, redir, addr_hints facts hints, tc, facts)
          else rounds hints' (k - 1) in
    rounds hints 3 in
  (* Derived induction variables: values [base + (long) iv * m] computed
     in the loop of [iv], with [base] invariant in the loop *)
  let derived ivs facts =
    let divs = ref [] in
    let loop_of t pc = List.find_opt (fun v -> P.eq v.ivreg t && v.body.(pc)) ivs in
    let add v b m =
      if not (List.exists (fun d -> d.dfor == v && d.dbase = b && d.dmul = m) !divs)
      then divs := { dreg = fresh_reg (); dbase = b; dmul = m; dfor = v } :: !divs in
    let lin_at pc r =
      List.filter_map (function
        | Flin (r', None, t, m, _) when P.eq r' r -> Some (t, m)
        | _ -> None) (facts_of facts pc) in
    (* [r] is used as the index of [b + r], with [b] invariant in the loop *)
    let based_use body r u =
      body.(u) &&
      match instr.(u) with
      | Some (Iload (_, addr, args, _, _)) | Some (Istore (_, addr, args, _, _)) ->
          (match addr_base_index addr args with
           | Some (b, r') when P.eq r' r -> not (defined_in body b)
           | Some (r', b) when P.eq r' r -> not (defined_in body b)
           | _ -> false)
      | Some (Iop (op, args, _, _)) ->
          (match classify_op op args with
           | OCaddl (b, r', _) when P.eq r' r -> not (defined_in body b)
           | OCaddl (r', b, _) when P.eq r' r -> not (defined_in body b)
           | _ -> false)
      | _ -> false in
    let vals = values ivs facts in
    (* Based values computed by operations *)
    List.iter (fun (pc, _, b, t, m, _) ->
      match b, loop_of t (P.to_int pc) with
      | Some base, Some v when not (defined_in v.body base) -> add v b m
      | _ -> ()) vals;
    (* Based addresses of loads and stores *)
    PTree.fold (fun () pc i ->
      let p = P.to_int pc in
      match i with
      | Iload (_, addr, args, _, _) | Istore (_, addr, args, _, _) ->
          (match addr_base_index addr args with
           | Some (b1, b2) ->
               List.iter (fun (b, r) ->
                 List.iter (fun (t, m) ->
                   match loop_of t p with
                   | Some v when not (defined_in v.body b) -> add v (Some b) m
                   | _ -> ()) (lin_at p r)) [(b1, b2); (b2, b1)]
           | None -> ())
      | _ -> ()) f.fn_code ();
    (* Scaled values that are not only used to compute other values
       linear in the same variable, or as indices of based values *)
    let linear_in body t u =
      List.exists (fun (pc, _, b, t', _, _) ->
        P.to_int pc = u && P.eq t' t
        && (match b with None -> true | Some base -> not (defined_in body base))) vals in
    List.iter (fun (pc, i, b, t, m, _) ->
      match b, loop_of t (P.to_int pc), i with
      | None, Some v, Iop (_, _, res, _)
        when not (Integers.Int64.eq m Integers.Int64.one)
             && not (Integers.Int64.eq m Integers.Int64.zero) ->
          if live_at_exit v.body res
             || not (List.for_all (fun u -> based_use v.body res u
                                            || (v.body.(u) && linear_in v.body t u))
                                  (users_of res))
          then add v None m
      | _ -> ()) vals;
    (* Cost: one register each *)
    List.filter (fun d ->
      let p = pressure d.dfor.body in
      let ok = p + 1 <= (if has_call d.dfor.body then 0 else max_pressure_derived) in
      if ok then charge d.dfor.body 1;
      ok) (List.rev !divs) in
  (* Keep the induction variables whose new registers are used *)
  let used hints r =
    List.exists (fun (_, h) ->
      match h with
      | Hrepl (y, _, _, _, _, _) -> P.eq y r
      | Haddr (_, y, _, _, _, _) -> P.eq y r
      | Hbase (_, _, y, _, _, _, _) -> P.eq y r
      | Hbshift (_, y, _, _, _, _, _) -> P.eq y r
      | Hsubst sl -> List.exists (fun (_, y) -> P.eq y r) sl
      | Hcond _ -> false) (PTree.elements hints) in
  let rec attempt ivs divs rounds =
    if ivs = [] || rounds = 0 then None else
    match construct ivs divs with
    | None -> None
    | Some (ghosts, redir, hints, tc, facts) ->
        let divs' = List.filter (fun d -> used hints d.dreg) divs in
        let ivs' = List.filter (fun v ->
          used hints v.lreg || List.exists (fun d -> d.dfor == v) divs') ivs in
        if List.length ivs' < List.length ivs || List.length divs' < List.length divs
        then attempt ivs' (List.filter (fun d -> List.memq d.dfor ivs') divs') (rounds - 1)
        else Some (ghosts, redir, hints, tc, facts) in
  let result =
    match construct ivs [] with
    | None -> None
    | Some (_, _, _, _, facts) -> attempt ivs (derived ivs facts) 5 in
  match result with
  | None -> none
  | Some (ghosts, redir, hints, _, facts) ->
  let fm = ref PTree.empty in
  Array.iteri (fun pc l ->
    match l with
    | Some (_ :: _ as l) -> fm := PTree.set (P.of_int pc) l !fm
    | _ -> ()) facts;
  (((ghosts, redir), hints), !fm)
  end
  end
