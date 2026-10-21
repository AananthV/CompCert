(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Loop-invariant code motion over the RTL intermediate language. *)

(** An external, untrusted oracle finds loops in the CFG and proposes
  operations to be hoisted out of them.  For each selected loop, it
  provides:
- the loop header [h];
- the set of nodes of the loop body (which must contain [h]);
- a list of fresh nodes [p1 ... pk], each associated with a hoisted
  computation [ti = opi(argsi)] where [ti] is a fresh register.  The
  arguments [argsi] are registers of the original function, or registers
  [tj] with [j < i]: chains of dependent invariant operations can be
  hoisted.

  The transformation then
- adds the preheader [p1: t1 = op1(args1); ... pk: tk = opk(argsk); goto h];
- redirects to [p1] all edges [n -> h] where [n] is outside the loop;
- replaces the in-loop instructions [r = opi(args)] designated by the
  oracle with moves [r = ti].  The arguments [args] must be equal to
  [argsi], or known to have the same values as [argsi]: for a chain, the
  argument [r'] of [r = opi(r')] has been assigned [r' = tj] by an earlier
  replaced instruction of the same iteration.  These equalities are
  provided by the oracle for each node as a list of equations between
  registers, and checked to be an inductive invariant of the transformed
  code.

  The result of the oracle is checked by verified code.  The check
  establishes that the loop can only be entered through its header, that
  the hoisted operations are safe to execute speculatively and do not
  depend on memory, that their arguments are not redefined in the loop
  nor later in the preheader, and that the [ti] registers are fresh.
  Under these conditions, [ti] holds the value of [opi(argsi)] at every
  point of the loop.  Loops may be
  nested or disjoint: the check does not rely on the shape of the loop
  nest.  If the check fails, the function is left unchanged. *)

Require Import Coqlib Maps AST Integers Values Op Registers RTL LICMop.

Definition hoist : Type := (reg * operation * list reg)%type.

Definition hoist_reg (h: hoist) : reg := fst (fst h).

Record loop_info : Type := mkloop {
  lp_header: node;
  lp_body: PTree.t unit;
  lp_chain: list (node * hoist)
}.

(** The oracle, implemented in OCaml ([LICMaux.ml]).  It returns the
  list of loops (header, body, preheader chain) and the map from in-loop
  nodes to be replaced by moves to the corresponding hoisted registers. *)

Parameter licm_oracle:
  function -> list (node * PTree.t unit * list (node * hoist)) * PTree.t reg
              * PTree.t (list (reg * reg)).

Definition in_body (L: loop_info) (n: node) : bool :=
  match L.(lp_body)!n with Some _ => true | None => false end.

Definition hoists (L: loop_info) : list hoist := map snd L.(lp_chain).

Definition tregs (L: loop_info) : list reg := map hoist_reg (hoists L).

Definition chain_next (ch: list (node * hoist)) (h: node) : node :=
  match ch with nil => h | (p, _) :: _ => p end.

Definition preheader (L: loop_info) : node :=
  chain_next L.(lp_chain) L.(lp_header).

Fixpoint chain_instrs (ch: list (node * hoist)) (h: node)
                      : list (node * instruction) :=
  match ch with
  | nil => nil
  | (p, (t, op, args)) :: ch' =>
      (p, Iop op args t (chain_next ch' h)) :: chain_instrs ch' h
  end.

Definition loop_instrs (L: loop_info) : list (node * instruction) :=
  chain_instrs L.(lp_chain) L.(lp_header).

(** Redirection of the successor [s] of a node.  [inn L] states whether
  the source node belongs to loop [L].  Edges entering a loop through its
  header are redirected to the preheader. *)

Fixpoint redirect (inn: loop_info -> bool) (loops: list loop_info) (s: node)
                  : node :=
  match loops with
  | nil => s
  | L :: loops' =>
      if peq L.(lp_header) s && negb (inn L)
      then preheader L
      else redirect inn loops' s
  end.

Definition map_succ (g: node -> node) (i: instruction) : instruction :=
  match i with
  | Inop s => Inop (g s)
  | Iop op args res s => Iop op args res (g s)
  | Iload chunk addr args dst s => Iload chunk addr args dst (g s)
  | Istore chunk addr args src s => Istore chunk addr args src (g s)
  | Icall sig ros args res s => Icall sig ros args res (g s)
  | Itailcall sig ros args => i
  | Ibuiltin ef args res s => Ibuiltin ef args res (g s)
  | Icond cond args ifso ifnot => Icond cond args (g ifso) (g ifnot)
  | Ijumptable arg tbl => Ijumptable arg (map g tbl)
  | Ireturn optarg => i
  end.

Definition replace_instr (repl: PTree.t reg) (n: node) (i: instruction)
                         : instruction :=
  match repl!n, i with
  | Some t, Iop op args res s => Iop Omove (t :: nil) res s
  | _, _ => i
  end.

Definition transf_instr (loops: list loop_info) (repl: PTree.t reg)
                        (n: node) (i: instruction) : instruction :=
  map_succ (redirect (fun L => in_body L n) loops) (replace_instr repl n i).

Definition add_instrs (c: code) (l: list (node * instruction)) : code :=
  fold_left (fun c pi => PTree.set (fst pi) (snd pi) c) l c.

Definition transf_code (f: function) (loops: list loop_info)
                       (repl: PTree.t reg) : code :=
  add_instrs (PTree.map (transf_instr loops repl) f.(fn_code))
             (flat_map loop_instrs loops).

(** Validation of the oracle's results. *)

(** All the registers possibly written by an instruction. *)

Definition defs_all (i: instruction) : list reg :=
  match i with
  | Iop _ _ res _ => res :: nil
  | Iload _ _ _ dst _ => dst :: nil
  | Icall _ _ _ res _ => res :: nil
  | Ibuiltin _ _ res _ => params_of_builtin_res res
  | _ => nil
  end.

Definition disjointb (l1 l2: list reg) : bool :=
  forallb (fun r => negb (In_dec peq r l2)) l1.

(** The hoisted operations of a preheader can be executed speculatively.
  Their arguments are either registers of the original function, or
  registers hoisted earlier in the same preheader: an argument is not
  overwritten by the current or later operations of the preheader.  [tl]
  is the list of all hoisted registers of the loop. *)

Fixpoint check_chain (mr: reg) (tl: list reg) (ch: list (node * hoist)) : bool :=
  match ch with
  | nil => true
  | (_, (t, op, args)) :: ch' =>
      op_safe op (length args)
      && negb (op_depends_on_memory op)
      && Pos.ltb mr t
      && forallb (fun a => (Pos.leb a mr || In_dec peq a tl)
                           && negb (In_dec peq a (t :: map hoist_reg (map snd ch'))))
                 args
      && check_chain mr tl ch'
  end.

(** The arguments and results of the hoisted operations of a loop
  are not redefined in the loop. *)

Definition check_invariant (L: loop_info) (ni: node * instruction) : bool :=
  negb (in_body L (fst ni))
  || forallb (fun h => let '(t, op, args) := h in
                       disjointb (defs_all (snd ni)) (t :: args))
             (hoists L).

(** Loops are only entered through their headers. *)

Definition check_edges (loops: list loop_info) (ni: node * instruction) : bool :=
  forallb (fun s =>
     forallb (fun L => negb (in_body L s) || in_body L (fst ni)
                       || peq s L.(lp_header)) loops)
     (successors_instr (snd ni)).

(** Equations between registers of the transformed function, provided by
  the oracle for each node.  An equation [(x, y)] at node [n] states that
  [x] and [y] have the same value whenever control reaches [n]. *)

Definition eqs_at (eqs: PTree.t (list (reg * reg))) (n: node) : list (reg * reg) :=
  match eqs!n with Some l => l | None => nil end.

Definition eq_pair (e1 e2: reg * reg) : bool :=
  peq (fst e1) (fst e2) && peq (snd e1) (snd e2).

(** Equations that hold after executing instruction [i]. *)

Definition move_of (i: instruction) : option (reg * reg) :=
  match i with
  | Iop Omove (y :: nil) x _ => Some (x, y)
  | _ => None
  end.

Definition transfer_eqs (l: list (reg * reg)) (i: instruction) : list (reg * reg) :=
  let d := defs_all i in
  let l' := filter (fun e => negb (In_dec peq (fst e) d) && negb (In_dec peq (snd e) d)) l in
  match move_of i with
  | Some e => e :: l'
  | None => l'
  end.

(** The equations are an inductive invariant of the transformed code. *)

Definition check_eqs (eqs: PTree.t (list (reg * reg))) (ni: node * instruction) : bool :=
  let after := transfer_eqs (eqs_at eqs (fst ni)) (snd ni) in
  forallb (fun s => forallb (fun e => existsb (eq_pair e) after) (eqs_at eqs s))
          (successors_instr (snd ni)).

(** Replaced instructions compute one of the hoisted operations of an
  enclosing loop: each argument is either the corresponding argument of
  the hoisted operation, or equal to it by an equation. *)

Fixpoint match_args (l: list (reg * reg)) (args hargs: list reg) : bool :=
  match args, hargs with
  | nil, nil => true
  | a :: args', h :: hargs' =>
      (peq a h || existsb (eq_pair (a, h)) l) && match_args l args' hargs'
  | _, _ => false
  end.

Definition match_hoist (l: list (reg * reg)) (t: reg) (op: operation) (args: list reg)
                       (h: hoist) : bool :=
  let '(t', op', hargs) := h in
  peq t t' && eq_operation op op' && match_args l args hargs.

Definition check_repl (f: function) (loops: list loop_info)
                      (eqs: PTree.t (list (reg * reg))) (nt: node * reg) : bool :=
  let (n, t) := nt in
  match f.(fn_code)!n with
  | Some (Iop op args res s) =>
      existsb (fun L => in_body L n
                        && existsb (match_hoist (eqs_at eqs n) t op args) (hoists L)) loops
  | _ => true
  end.

Definition check_function (f: function) (loops: list loop_info)
                          (repl: PTree.t reg) (eqs: PTree.t (list (reg * reg)))
                          (tc: code) (entry: node) : bool :=
  let mr := max_reg_function f in
  let code := PTree.elements f.(fn_code) in
  let chain := flat_map loop_instrs loops in
  list_norepet_dec peq (map lp_header loops)
  && list_norepet_dec peq (map fst chain)
  && forallb (fun pi => match f.(fn_code)!(fst pi) with
                        | None => true | Some _ => false end) chain
  && list_norepet_dec peq (flat_map tregs loops)
  && forallb (fun L => check_chain mr (tregs L) L.(lp_chain)) loops
  && forallb (fun L => forallb (check_invariant L) code) loops
  && forallb (check_edges loops) code
  && forallb (fun L => negb (in_body L f.(fn_entrypoint))
                       || peq f.(fn_entrypoint) L.(lp_header)) loops
  && forallb (check_repl f loops eqs) (PTree.elements repl)
  && forallb (check_eqs eqs) (PTree.elements tc)
  && (match eqs_at eqs entry with nil => true | _ => false end).

Definition transf_function (f: function) : function :=
  let '(lps, repl, eqs) := licm_oracle f in
  let loops := map (fun x => let '(h, b, ch) := x in mkloop h b ch) lps in
  let tc := transf_code f loops repl in
  let entry := redirect (fun _ => false) loops f.(fn_entrypoint) in
  if check_function f loops repl eqs tc entry then
    mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize) tc entry
  else f.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
