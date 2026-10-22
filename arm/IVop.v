(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition and construction of the operators, conditions and
  addressing modes used by induction-variable widening ([IVwiden]).
  Induction-variable widening is not supported on this target:
  nothing is recognized and nothing is constructed. *)

Require Import Coqlib AST Integers Values Memory Globalenvs Op Registers.

Inductive op_class : Type :=
  | OCaddimm (a: reg) (n: int)        (**r 32-bit [a + n] *)
  | OCintconst (n: int)               (**r 32-bit constant [n] *)
  | OCsext (a: reg)                   (**r sign extension of [a] to 64 bits *)
  | OCaddlimm (a: reg) (n: int64)     (**r 64-bit [a + n] *)
  | OCmullimm (a: reg) (n: int64)     (**r 64-bit [a * n] *)
  | OCaddl (a b: reg) (n: int64)      (**r 64-bit [a + b + n] *)
  | OCscaledl (a: reg) (sc n: int64)  (**r 64-bit [a * sc + n] *)
  | OCaddlscaled (a b: reg) (sc n: int64)  (**r 64-bit [a + (b * sc + n)] *)
  | OCother.

Definition classify_op (op: operation) (args: list reg) : op_class := OCother.

Lemma classify_op_sound:
  forall (F V: Type) (ge: Genv.t F V) sp op args (rs: Regmap.t val) m v,
  eval_operation ge sp op rs##args m = Some v ->
  match classify_op op args with
  | OCaddimm a n => v = Val.add rs#a (Vint n)
  | OCintconst n => v = Vint n
  | OCsext a => v = Val.longofint rs#a
  | OCaddlimm a n => v = Val.addl rs#a (Vlong n)
  | OCmullimm a n => v = Val.mull rs#a (Vlong n)
  | OCaddl a b n => v = Val.addl (Val.addl rs#a rs#b) (Vlong n)
  | OCscaledl a sc n => v = Val.addl (Val.mull rs#a (Vlong sc)) (Vlong n)
  | OCaddlscaled a b sc n => v = Val.addl rs#a (Val.addl (Val.mull rs#b (Vlong sc)) (Vlong n))
  | OCother => True
  end.
Proof.
  intros. exact I.
Qed.

Inductive cond_class : Type :=
  | CCcmp (c: comparison) (a b: reg)            (**r signed 32-bit [a c b] *)
  | CCcmpimm (c: comparison) (a: reg) (n: int)  (**r signed 32-bit [a c n] *)
  | CCcmpl (c: comparison) (a b: reg)           (**r signed 64-bit [a c b] *)
  | CCcmplimm (c: comparison) (a: reg) (n: int64) (**r signed 64-bit [a c n] *)
  | CCother.

Definition classify_cond (cond: condition) (args: list reg) : cond_class := CCother.

Lemma classify_cond_sound:
  forall cond args (rs: Regmap.t val) m b,
  eval_condition cond rs##args m = Some b ->
  match classify_cond cond args with
  | CCcmp c x y => Val.cmp_bool c rs#x rs#y = Some b
  | CCcmpimm c x n => Val.cmp_bool c rs#x (Vint n) = Some b
  | CCcmpl c x y => Val.cmpl_bool c rs#x rs#y = Some b
  | CCcmplimm c x n => Val.cmpl_bool c rs#x (Vlong n) = Some b
  | CCother => True
  end.
Proof.
  intros. exact I.
Qed.

Definition mk_sext : option operation := None.

Definition mk_addlimm (n: int64) : option operation := None.

Definition mk_mullimm (n: int64) : option operation := None.

Definition mk_addl : option operation := None.

Definition mk_cmpl (c: comparison) : option condition := None.

Definition mk_cmplimm (c: comparison) (n: int64) : option condition := None.

Lemma mk_addlimm_sound:
  forall (F V: Type) (ge: Genv.t F V) sp n op v m,
  mk_addlimm n = Some op ->
  eval_operation ge sp op (v :: nil) m = Some (Val.addl v (Vlong n)).
Proof.
  unfold mk_addlimm; intros; discriminate.
Qed.

Lemma mk_cmpl_sound:
  forall c cond v1 v2 m,
  mk_cmpl c = Some cond ->
  eval_condition cond (v1 :: v2 :: nil) m = Val.cmpl_bool c v1 v2.
Proof.
  unfold mk_cmpl; intros; discriminate.
Qed.

Lemma mk_cmplimm_sound:
  forall c n cond v1 m,
  mk_cmplimm c n = Some cond ->
  eval_condition cond (v1 :: nil) m = Val.cmpl_bool c v1 (Vlong n).
Proof.
  unfold mk_cmplimm; intros; discriminate.
Qed.

Definition shift_addr (addr: addressing) (args: list reg) (r y: reg) (delta: int64)
                      : option (addressing * list reg) := None.

Lemma shift_addr_sound:
  forall (F V: Type) (ge: Genv.t F V) sp addr args r y delta addr' args' (rs: Regmap.t val) a,
  shift_addr addr args r y delta = Some (addr', args') ->
  rs#r = Val.addl rs#y (Vlong delta) ->
  (rs#y = Vundef \/ exists n, rs#y = Vlong n) ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists a', eval_addressing ge sp addr' rs##args' = Some a' /\ Val.lessdef a a'.
Proof.
  unfold shift_addr; intros; discriminate.
Qed.

Definition addr_base_index (addr: addressing) (args: list reg) : option (reg * reg) := None.

Definition rebase_addr (addr: addressing) (args: list reg) (b r y: reg) (delta: int64)
                       : option (addressing * list reg) := None.

Lemma rebase_addr_sound:
  forall (F V: Type) (ge: Genv.t F V) sp addr args b r y delta addr' args' (rs: Regmap.t val) a,
  rebase_addr addr args b r y delta = Some (addr', args') ->
  rs#r = Vundef \/ Val.addl rs#b rs#r = Val.addl rs#y (Vlong delta) ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists a', eval_addressing ge sp addr' rs##args' = Some a' /\ Val.lessdef a a'.
Proof.
  unfold rebase_addr; intros; discriminate.
Qed.

Definition shift_base (addr: addressing) (args: list reg) (r y: reg) (delta: int64)
                      : option (addressing * list reg) := None.

Lemma shift_base_sound:
  forall (F V: Type) (ge: Genv.t F V) sp addr args r y delta addr' args' (rs: Regmap.t val) a,
  shift_base addr args r y delta = Some (addr', args') ->
  rs#r = Val.addl rs#y (Vlong delta) ->
  eval_addressing ge sp addr rs##args = Some a ->
  eval_addressing ge sp addr' rs##args' = Some a.
Proof.
  unfold shift_base; intros; discriminate.
Qed.
