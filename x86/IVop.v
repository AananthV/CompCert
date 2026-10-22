(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition and construction of the operators, conditions and
  addressing modes used by induction-variable widening ([IVwiden]). *)

Require Import Coqlib AST Integers Values Memory Globalenvs Op Registers.

(** Operations relevant to induction variables. *)

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

Definition classify_op (op: operation) (args: list reg) : op_class :=
  match args with
  | nil =>
      match op with
      | Ointconst n => OCintconst n
      | _ => OCother
      end
  | a :: nil =>
      match op with
      | Olea (Aindexed n) => OCaddimm a (Int.repr n)
      | Ocast32signed => OCsext a
      | Oaddlimm n => OCaddlimm a n
      | Oleal (Aindexed n) => OCaddlimm a (Int64.repr n)
      | Omullimm n => OCmullimm a n
      | Oshllimm n =>
          if Int.ltu n Int64.iwordsize' then OCmullimm a (Int64.shl' Int64.one n) else OCother
      | Oleal (Ascaled sc n) => OCscaledl a (Int64.repr sc) (Int64.repr n)
      | _ => OCother
      end
  | a :: b :: nil =>
      match op with
      | Oleal (Aindexed2 n) => OCaddl a b (Int64.repr n)
      | Oleal (Aindexed2scaled sc n) => OCaddlscaled a b (Int64.repr sc) (Int64.repr n)
      | _ => OCother
      end
  | _ => OCother
  end.

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
  intros until v; intros EV.
  destruct args as [ | a1 [ | a2 [ | a3 args]]]; simpl in EV;
  destruct op; try exact I;
  try (match goal with [ x: addressing |- _ ] => destruct x; try exact I end);
  simpl in *; inv EV; try reflexivity.
  (* shift left *)
  match goal with [ |- context [Int.ltu ?n Int64.iwordsize'] ] =>
    destruct (Int.ltu n Int64.iwordsize') eqn:LT; [ | exact I];
    unfold Val.shll, Val.mull; destruct (rs#a1); auto; rewrite LT; f_equal;
    apply Int64.shl'_mul
  end.
Qed.

(** Conditions relevant to induction variables. *)

Inductive cond_class : Type :=
  | CCcmp (c: comparison) (a b: reg)            (**r signed 32-bit [a c b] *)
  | CCcmpimm (c: comparison) (a: reg) (n: int)  (**r signed 32-bit [a c n] *)
  | CCcmpl (c: comparison) (a b: reg)           (**r signed 64-bit [a c b] *)
  | CCcmplimm (c: comparison) (a: reg) (n: int64) (**r signed 64-bit [a c n] *)
  | CCother.

Definition classify_cond (cond: condition) (args: list reg) : cond_class :=
  match args with
  | a :: nil =>
      match cond with
      | Ccompimm c n => CCcmpimm c a n
      | Ccomplimm c n => CCcmplimm c a n
      | _ => CCother
      end
  | a :: b :: nil =>
      match cond with
      | Ccomp c => CCcmp c a b
      | Ccompl c => CCcmpl c a b
      | _ => CCother
      end
  | _ => CCother
  end.

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
  intros until b; intros EV.
  destruct args as [ | a1 [ | a2 [ | a3 args]]]; simpl in EV;
  destruct cond; try exact I; simpl in *; exact EV.
Qed.

(** Construction of 64-bit operations and conditions.  They are only
  produced for 64-bit targets.  The operations inserted by the oracle
  on the edges of the CFG need no specification: only [mk_addlimm],
  [mk_cmpl] and [mk_cmplimm], used to rewrite existing instructions,
  are specified. *)

Definition mk_sext : option operation :=
  if Archi.ptr64 then Some Ocast32signed else None.

Definition mk_addlimm (n: int64) : option operation :=
  if Archi.ptr64 then Some (Oleal (Aindexed (Int64.signed n))) else None.

Definition mk_mullimm (n: int64) : option operation :=
  if Archi.ptr64 then Some (Omullimm n) else None.

Definition mk_addl : option operation :=
  if Archi.ptr64 then Some (Oleal (Aindexed2 0)) else None.

Definition mk_cmpl (c: comparison) : option condition :=
  if Archi.ptr64 then Some (Ccompl c) else None.

Definition mk_cmplimm (c: comparison) (n: int64) : option condition :=
  if Archi.ptr64 then Some (Ccomplimm c n) else None.

Lemma mk_addlimm_sound:
  forall (F V: Type) (ge: Genv.t F V) sp n op v m,
  mk_addlimm n = Some op ->
  eval_operation ge sp op (v :: nil) m = Some (Val.addl v (Vlong n)).
Proof.
  unfold mk_addlimm; intros until m; intros MK.
  destruct Archi.ptr64; inv MK. simpl. rewrite Int64.repr_signed. reflexivity.
Qed.

Lemma mk_cmpl_sound:
  forall c cond v1 v2 m,
  mk_cmpl c = Some cond ->
  eval_condition cond (v1 :: v2 :: nil) m = Val.cmpl_bool c v1 v2.
Proof.
  unfold mk_cmpl; intros until m; intros MK.
  destruct Archi.ptr64; inv MK; reflexivity.
Qed.

Lemma mk_cmplimm_sound:
  forall c n cond v1 m,
  mk_cmplimm c n = Some cond ->
  eval_condition cond (v1 :: nil) m = Val.cmpl_bool c v1 (Vlong n).
Proof.
  unfold mk_cmplimm; intros until m; intros MK.
  destruct Archi.ptr64; inv MK; reflexivity.
Qed.

(** Replacing the index register [r] of an addressing mode by [y],
  where [r = y + delta], and folding [delta] into the offset.  The new
  offset must fit in 32 bits. *)

Definition shift_addr (addr: addressing) (args: list reg) (r y: reg) (delta: int64)
                      : option (addressing * list reg) :=
  if Archi.ptr64 then
    match addr, args with
    | Aindexed2scaled sc ofs, b :: x :: nil =>
        if peq x r && zle Int.min_signed (ofs + sc * Int64.signed delta)
                   && zle (ofs + sc * Int64.signed delta) Int.max_signed
        then Some (Aindexed2scaled sc (ofs + sc * Int64.signed delta), b :: y :: nil)
        else None
    | Aindexed2 ofs, b :: x :: nil =>
        if zle Int.min_signed (ofs + Int64.signed delta)
           && zle (ofs + Int64.signed delta) Int.max_signed then
          if peq x r then Some (Aindexed2 (ofs + Int64.signed delta), b :: y :: nil)
          else if peq b r then Some (Aindexed2 (ofs + Int64.signed delta), y :: x :: nil)
          else None
        else None
    | _, _ => None
    end
  else None.

Lemma repr_add64:
  forall a b, Int64.repr (a + b) = Int64.add (Int64.repr a) (Int64.repr b).
Proof.
  intros. rewrite Int64.add_unsigned. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_unsigned_repr.
Qed.

Lemma repr_mul64:
  forall a b, Int64.repr (a * b) = Int64.mul (Int64.repr a) (Int64.repr b).
Proof.
  intros. unfold Int64.mul. apply Int64.eqm_samerepr.
  apply Int64.eqm_mult; apply Int64.eqm_unsigned_repr.
Qed.

Lemma shift_addr_sound:
  forall (F V: Type) (ge: Genv.t F V) sp addr args r y delta addr' args' (rs: Regmap.t val) a,
  shift_addr addr args r y delta = Some (addr', args') ->
  rs#r = Val.addl rs#y (Vlong delta) ->
  (rs#y = Vundef \/ exists n, rs#y = Vlong n) ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists a', eval_addressing ge sp addr' rs##args' = Some a' /\ Val.lessdef a a'.
Proof.
  intros until a; intros SH R Y EV.
  unfold shift_addr in SH. destruct Archi.ptr64 eqn:P; [ | discriminate SH].
  unfold eval_addressing in EV |- *. rewrite P in EV |- *. clear P.
  destruct addr as [ ? | ofs | ? ? | sc ofs | ? ? | ? ? | ? ? ? | ? ]; try discriminate SH;
  destruct args as [ | b [ | x [ | ? ?]]]; try discriminate SH.
- (* Aindexed2 *)
  destruct (zle Int.min_signed (ofs + Int64.signed delta)); [ | discriminate SH].
  destruct (zle (ofs + Int64.signed delta) Int.max_signed); [ | discriminate SH].
  cbn [andb] in SH.
  destruct (peq x r).
  + subst x. inv SH. simpl in *. inv EV. econstructor; split. eauto.
    rewrite R. rewrite ! Val.addl_assoc. simpl.
    rewrite repr_add64, Int64.repr_signed, (Int64.add_commut delta). auto.
  + destruct (peq b r); [ | discriminate SH]. subst b. inv SH. simpl in *. inv EV.
    econstructor; split. eauto.
    rewrite R. rewrite ! Val.addl_assoc. rewrite (Val.addl_commut (Vlong delta)).
    rewrite <- ! Val.addl_assoc. rewrite (Val.addl_assoc (Val.addl rs#y rs#x)). simpl.
    rewrite repr_add64, Int64.repr_signed. auto.
- (* Aindexed2scaled *)
  destruct (peq x r); [ | discriminate SH]. subst x.
  destruct (zle Int.min_signed (ofs + sc * Int64.signed delta)); [ | discriminate SH].
  destruct (zle (ofs + sc * Int64.signed delta) Int.max_signed); [ | discriminate SH].
  inv SH. simpl in *. inv EV.
  econstructor; split. eauto.
  rewrite R. destruct Y as [U | (n & N)].
  + rewrite U. simpl. destruct (rs#b); simpl; auto.
  + rewrite N. simpl. apply Val.lessdef_same. f_equal. f_equal.
    rewrite repr_add64, repr_mul64, Int64.repr_signed.
    rewrite Int64.mul_add_distr_l, Int64.add_assoc. f_equal.
    rewrite Int64.add_commut. f_equal. apply Int64.mul_commut.
Qed.

(** Replacing the base [b] and index [r] of an addressing mode [b + r + ofs]
  by [y], where [b + r = y + delta]. *)

Definition addr_base_index (addr: addressing) (args: list reg) : option (reg * reg) :=
  match addr, args with
  | Aindexed2 _, b :: r :: nil => Some (b, r)
  | _, _ => None
  end.

Definition rebase_addr (addr: addressing) (args: list reg) (b r y: reg) (delta: int64)
                       : option (addressing * list reg) :=
  if Archi.ptr64 then
    match addr, args with
    | Aindexed2 ofs, x1 :: x2 :: nil =>
        if ((peq x1 b && peq x2 r) || (peq x1 r && peq x2 b))
           && zle Int.min_signed (ofs + Int64.signed delta)
           && zle (ofs + Int64.signed delta) Int.max_signed
        then Some (Aindexed (ofs + Int64.signed delta), y :: nil)
        else None
    | _, _ => None
    end
  else None.

Lemma rebase_addr_sound:
  forall (F V: Type) (ge: Genv.t F V) sp addr args b r y delta addr' args' (rs: Regmap.t val) a,
  rebase_addr addr args b r y delta = Some (addr', args') ->
  rs#r = Vundef \/ Val.addl rs#b rs#r = Val.addl rs#y (Vlong delta) ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists a', eval_addressing ge sp addr' rs##args' = Some a' /\ Val.lessdef a a'.
Proof.
  intros until a; intros RB R EV.
  unfold rebase_addr in RB. destruct Archi.ptr64 eqn:P; [ | discriminate RB].
  unfold eval_addressing in EV |- *. rewrite P in EV |- *. clear P.
  destruct addr as [ ? | ofs | ? ? | ? ? | ? ? | ? ? | ? ? ? | ? ]; try discriminate RB;
  destruct args as [ | x1 [ | x2 [ | ? ?]]]; try discriminate RB.
  destruct (((peq x1 b && peq x2 r) || (peq x1 r && peq x2 b))
            && zle Int.min_signed (ofs + Int64.signed delta)
            && zle (ofs + Int64.signed delta) Int.max_signed) eqn:C; [ | discriminate RB].
  inv RB. rewrite ! andb_true_iff, orb_true_iff, ! andb_true_iff in C.
  destruct C as [[[[E1 E2] | [E1 E2]] _] _];
  apply proj_sumbool_true in E1; apply proj_sumbool_true in E2; subst x1 x2;
  simpl in *; inv EV; econstructor; (split; [reflexivity | ]).
- destruct R as [U | E].
  + rewrite U. destruct (rs#b); simpl; auto.
  + rewrite E, Val.addl_assoc. simpl.
    rewrite repr_add64, Int64.repr_signed, (Int64.add_commut delta). auto.
- destruct R as [U | E].
  + rewrite U. simpl. auto.
  + rewrite (Val.addl_commut rs#r rs#b), E, Val.addl_assoc. simpl.
    rewrite repr_add64, Int64.repr_signed, (Int64.add_commut delta). auto.
Qed.

(** Replacing the base register [r] of an addressing mode by [y], where
  [r = y + delta], and folding [delta] into the offset. *)

Definition shift_base (addr: addressing) (args: list reg) (r y: reg) (delta: int64)
                      : option (addressing * list reg) :=
  if Archi.ptr64 then
    if zle Int.min_signed (match addr with
                           | Aindexed ofs | Aindexed2 ofs | Aindexed2scaled _ ofs => ofs
                           | _ => 0 end + Int64.signed delta)
       && zle (match addr with
               | Aindexed ofs | Aindexed2 ofs | Aindexed2scaled _ ofs => ofs
               | _ => 0 end + Int64.signed delta) Int.max_signed
    then
      match addr, args with
      | Aindexed ofs, x :: nil =>
          if peq x r then Some (Aindexed (ofs + Int64.signed delta), y :: nil) else None
      | Aindexed2 ofs, x1 :: x2 :: nil =>
          if peq x1 r then Some (Aindexed2 (ofs + Int64.signed delta), y :: x2 :: nil)
          else if peq x2 r then Some (Aindexed2 (ofs + Int64.signed delta), x1 :: y :: nil)
          else None
      | Aindexed2scaled sc ofs, x :: i :: nil =>
          if peq x r then Some (Aindexed2scaled sc (ofs + Int64.signed delta), y :: i :: nil)
          else None
      | _, _ => None
      end
    else None
  else None.

Lemma shift_base_sound:
  forall (F V: Type) (ge: Genv.t F V) sp addr args r y delta addr' args' (rs: Regmap.t val) a,
  shift_base addr args r y delta = Some (addr', args') ->
  rs#r = Val.addl rs#y (Vlong delta) ->
  eval_addressing ge sp addr rs##args = Some a ->
  eval_addressing ge sp addr' rs##args' = Some a.
Proof.
  intros until a; intros SH R EV.
  unfold shift_base in SH. destruct Archi.ptr64 eqn:P; [ | discriminate SH].
  unfold eval_addressing in EV |- *. rewrite P in EV |- *. clear P.
  match type of SH with
  | (if ?c then _ else None) = Some _ => destruct c; [ | discriminate SH]
  end.
  assert (AV: forall u v, Val.addl (Vlong u) (Vlong v) = Vlong (Int64.add u v)) by reflexivity.
  assert (OFS: forall ofs, Vlong (Int64.repr (ofs + Int64.signed delta))
                           = Val.addl (Vlong delta) (Vlong (Int64.repr ofs))).
  { intros. rewrite AV, repr_add64, Int64.repr_signed, Int64.add_commut. auto. }
  destruct addr as [ ofs | ofs | ? ? | sc ofs | ? ? | ? ? | ? ? ? | ? ]; try discriminate SH;
  destruct args as [ | x1 [ | x2 [ | ? ?]]]; try discriminate SH.
- (* Aindexed *)
  destruct (peq x1 r); [ | discriminate SH]. subst x1. inv SH.
  simpl in *. inv EV. rewrite R, Val.addl_assoc, OFS. auto.
- (* Aindexed2 *)
  destruct (peq x1 r).
  + subst x1. inv SH. simpl in *. inv EV.
    rewrite R, OFS, ! Val.addl_assoc. f_equal.
    rewrite (Val.addl_commut (Vlong delta)), ! Val.addl_assoc. simpl.
    rewrite (Int64.add_commut delta). auto.
  + destruct (peq x2 r); [ | discriminate SH]. subst x2. inv SH. simpl in *. inv EV.
    rewrite R, OFS, ! Val.addl_assoc. auto.
- (* Aindexed2scaled *)
  destruct (peq x1 r); [ | discriminate SH]. subst x1. inv SH.
  simpl in *. inv EV. rewrite R, OFS, ! Val.addl_assoc. f_equal.
  rewrite (Val.addl_commut (Vlong delta)), ! Val.addl_assoc. simpl.
  rewrite (Int64.add_commut delta). auto.
Qed.
