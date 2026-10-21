(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition of combined operations, addressing modes and conditions
  during the [CSE] phase. *)

From Coq Require Import FunInd.
Require Import Coqlib.
Require Import Integers Values Memory.
Require Import Op RTL CSEdomain.
Require Import CombineOp.

Section COMBINE.

Variable ge: genv.
Variable sp: val.
Variable m: mem.
Variable get: valnum -> option rhs.
Variable valu: valnum -> val.
Hypothesis get_sound: forall v rhs, get v = Some rhs -> rhs_eval_to valu ge sp m rhs (valu v).

Lemma get_op_sound:
  forall v op vl, get v = Some (Op op vl) -> eval_operation ge sp op (map valu vl) m = Some (valu v).
Proof.
  intros. exploit get_sound; eauto. intros REV; inv REV; auto.
Qed.

Ltac UseGetSound :=
  match goal with
  | [ H: get _ = Some _ |- _ ] =>
      let x := fresh "EQ" in (generalize (get_op_sound _ _ _ H); intros x; simpl in x; FuncInv)
  end.

Lemma combine_compimm_ne_0_sound:
  forall x cond args,
  combine_compimm_ne_0 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Cne (valu x) (Vint Int.zero) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Cne (valu x) (Vint Int.zero).
Proof.
  intros until args. functional induction (combine_compimm_ne_0 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  destruct (eval_condition cond (map valu args) m); simpl; auto. destruct b; auto.
  (* of and *)
  UseGetSound. rewrite <- H.
  destruct v; simpl; auto.
  (* of xorimm *)
  UseGetSound. rewrite <- H.
  destruct v; simpl; auto. rewrite Int.xor_is_zero; auto.
Qed.

Lemma combine_compimm_eq_0_sound:
  forall x cond args,
  combine_compimm_eq_0 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Ceq (valu x) (Vint Int.zero) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Ceq (valu x) (Vint Int.zero).
Proof.
  intros until args. functional induction (combine_compimm_eq_0 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  rewrite eval_negate_condition.
  destruct (eval_condition c (map valu args) m); simpl; auto. destruct b; auto.
  (* of and *)
  UseGetSound. rewrite <- H. destruct v; auto.
  (* of xorimm *)
  UseGetSound. rewrite <- H.
  destruct v; simpl; auto. rewrite Int.xor_is_zero; auto.
Qed.

Lemma combine_compimm_eq_1_sound:
  forall x cond args,
  combine_compimm_eq_1 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Ceq (valu x) (Vint Int.one) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Ceq (valu x) (Vint Int.one).
Proof.
  intros until args. functional induction (combine_compimm_eq_1 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  destruct (eval_condition cond (map valu args) m); simpl; auto. destruct b; auto.
Qed.

Lemma combine_compimm_ne_1_sound:
  forall x cond args,
  combine_compimm_ne_1 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Cne (valu x) (Vint Int.one) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Cne (valu x) (Vint Int.one).
Proof.
  intros until args. functional induction (combine_compimm_ne_1 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  rewrite eval_negate_condition.
  destruct (eval_condition c (map valu args) m); simpl; auto. destruct b; auto.
Qed.

Theorem combine_cond_sound:
  forall cond args cond' args',
  combine_cond get cond args = Some(cond', args') ->
  eval_condition cond' (map valu args') m = eval_condition cond (map valu args) m.
Proof.
  intros. functional inversion H; subst.
  (* compimm ne zero *)
  simpl; eapply combine_compimm_ne_0_sound; eauto.
  (* compimm ne one *)
  simpl; eapply combine_compimm_ne_1_sound; eauto.
  (* compimm eq zero *)
  simpl; eapply combine_compimm_eq_0_sound; eauto.
  (* compimm eq one *)
  simpl; eapply combine_compimm_eq_1_sound; eauto.
  (* compuimm ne zero *)
  simpl; eapply combine_compimm_ne_0_sound; eauto.
  (* compuimm ne one *)
  simpl; eapply combine_compimm_ne_1_sound; eauto.
  (* compuimm eq zero *)
  simpl; eapply combine_compimm_eq_0_sound; eauto.
  (* compuimm eq one *)
  simpl; eapply combine_compimm_eq_1_sound; eauto.
Qed.

Theorem combine_cond'_sound:
  forall cond args res res',
  combine_cond' cond args = Some res' ->
  eval_condition cond (map valu args) m = Some res ->
  res = res'.
Proof.
  intros.  unfold combine_cond' in *.
  destruct cond; inv H; destruct args; inv H2; destruct args; inv H1; destruct args; inv H2.
  apply (combine_comparison_cmp_sound valu c v v0 res res'); auto.
  apply (combine_comparison_cmpu_sound valu m c v v0 res res'); auto.
  apply (combine_comparison_cmpl_sound valu c v v0 res res'); auto.
  apply (combine_comparison_cmplu_sound valu m c v v0 res res'); auto.
Qed.

Theorem combine_addr_32_sound:
  forall addr args addr' args',
  combine_addr_32 get addr args = Some(addr', args') ->
  eval_addressing32 ge sp addr' (map valu args') = eval_addressing32 ge sp addr (map valu args).
Proof.
  intros. functional inversion H; subst.
  (* indexed - lea *)
  UseGetSound. simpl. unfold offset_addressing in H7. destruct (addressing_valid (offset_addressing_total a n)); inv H7.
  eapply eval_offset_addressing_total_32; eauto.
Qed.

Theorem combine_addr_64_sound:
  forall addr args addr' args',
  combine_addr_64 get addr args = Some(addr', args') ->
  eval_addressing64 ge sp addr' (map valu args') = eval_addressing64 ge sp addr (map valu args).
Proof.
  intros. functional inversion H; subst.
  (* indexed - leal *)
  UseGetSound. simpl. unfold offset_addressing in H7. destruct (addressing_valid (offset_addressing_total a n)); inv H7.
  eapply eval_offset_addressing_total_64; eauto.
Qed.

Theorem combine_addr_sound:
  forall addr args addr' args',
  combine_addr get addr args = Some(addr', args') ->
  eval_addressing ge sp addr' (map valu args') = eval_addressing ge sp addr (map valu args).
Proof.
  unfold combine_addr, eval_addressing; intros; destruct Archi.ptr64.
  apply combine_addr_64_sound; auto.
  apply combine_addr_32_sound; auto.
Qed.

Theorem combine_op_sound:
  forall op args op' args' r,
  combine_op get op args = Some(op', args') ->
  eval_operation ge sp op (map valu args) m = Some r ->
  exists r', eval_operation ge sp op' (map valu args') m = Some r' /\ Val.lessdef r r'.
Proof.
  intros. functional inversion H; subst.
(* lea-lea *)
 - exists r; split; auto. rewrite <- H0. eapply combine_addr_32_sound; eauto.
(* leal-leal *)
 - exists r; split; auto.  rewrite <- H0. eapply combine_addr_64_sound; eauto.
(* andimm - andimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.and_assoc. auto.
(* orimm - orimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.or_assoc. auto.
(* xorimm - xorimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.xor_assoc. auto.
(* andimm - andimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.andl_assoc. auto.
(* orimm - orimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.orl_assoc. auto.
(* xorimm - xorimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.xorl_assoc. auto.
 (* cmp true *)
 - exists Vtrue; split; auto. inv H0. destruct (eval_condition cond (map valu args) m) eqn:?; auto.
   rewrite (combine_cond'_sound cond args b true); eauto.
 (* cmp false *)
 - exists Vfalse; split; auto. inv H0. destruct (eval_condition cond (map valu args) m) eqn:?; auto.
   rewrite (combine_cond'_sound cond args b false); eauto.
 (* cmp reduce *)
 - exists r; split; auto. decEq; decEq. simpl. erewrite combine_cond_sound; eauto.
 (* sel cond true *)
 - exists (valu x). simpl in H0.
   destruct (eval_condition cond (map valu args1) m) eqn:?; simpl; split; auto; inv H0; auto.
   rewrite (combine_cond'_sound cond args1 b true); eauto.  destruct (valu x), ty; auto.
 (* sel cond false *)
 - exists (valu y). simpl in H0.
   destruct (eval_condition cond (map valu args1) m) eqn:?; simpl; split; auto; inv H0; auto.
   rewrite (combine_cond'_sound cond args1 b false); eauto.  destruct (valu y), ty; auto.
 (* sel cond same *)
 - exists (valu y); split; auto. inv H0. destruct (eval_condition cond (map valu args1) m); auto.
   simpl. destruct b, (valu y), ty; auto.
 - exists r; split; auto. rewrite <- H0.
   simpl. erewrite combine_cond_sound; eauto.
Qed.

(** Soundness of [addr_deltas]. *)

Lemma addressing_delta_sound:
  forall addr1 addr2 delta args b ofs v,
  addressing_delta addr1 addr2 = Some delta ->
  eval_addressing ge sp addr1 args = Some (Vptr b ofs) ->
  eval_addressing ge sp addr2 args = Some v ->
  v = Vptr b (Ptrofs.add ofs (Ptrofs.repr delta)).
Proof.
  intros until v. unfold addressing_delta.
  set (delta' := match addr1, addr2 with
                 | Aindexed n1, Aindexed n2 => n2 - n1
                 | Aindexed2 n1, Aindexed2 n2 => n2 - n1
                 | Ascaled _ n1, Ascaled _ n2 => n2 - n1
                 | Aindexed2scaled _ n1, Aindexed2scaled _ n2 => n2 - n1
                 | Aglobal _ n1, Aglobal _ n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
                 | Abased _ n1, Abased _ n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
                 | Abasedscaled _ _ n1, Abasedscaled _ _ n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
                 | Ainstack n1, Ainstack n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
                 | _, _ => 0
                 end).
  clearbody delta'.
  destruct (eq_addressing (offset_addressing_total addr1 delta') addr2); intros D E1 E2; inv D.
  unfold eval_addressing in *. destruct Archi.ptr64 eqn:SF.
- rewrite (@eval_offset_addressing_total_64 _ _ ge sp addr1 args delta _ E1) in E2. inv E2.
  unfold Val.addl; rewrite SF. f_equal. f_equal.
  apply Ptrofs.agree64_of_int_eq. apply Ptrofs.agree64_repr; auto.
- rewrite (@eval_offset_addressing_total_32 _ _ ge sp addr1 args delta _ E1) in E2. inv E2.
  unfold Val.add; rewrite SF. f_equal. f_equal.
  apply Ptrofs.agree32_of_int_eq. apply Ptrofs.agree32_repr; auto.
Qed.

Lemma index_offset_sound:
  forall k x c,
  index_offset get k = (x, c) ->
  valu k = Val.add (valu x) (Vint (Int.repr c)) \/ (x = k /\ c = 0).
Proof.
  unfold index_offset; intros.
  destruct (get k) as [[op args|chunk addr args p|bf args]|] eqn:G;
  try (inv H; auto; fail).
  destruct op; try (inv H; auto; fail).
  destruct a; try (inv H; auto; fail).
  destruct args as [ | x1 [ | ]]; try (inv H; auto; fail).
  inv H. left. exploit get_op_sound; eauto. simpl. intros E; inv E; auto.
Qed.

Lemma index_form_sound:
  forall i s x c,
  index_form get i = Some (s, x, c) ->
  valu i = Vundef \/
  exists n, valu x = Vint n /\
            valu i = Vlong (Int64.repr (if s then Int.signed (Int.add n (Int.repr c))
                                        else Int.unsigned (Int.add n (Int.repr c)))).
Proof.
  unfold index_form; intros.
  destruct (get i) as [[op args|chunk addr args p|bf args]|] eqn:G; try discriminate.
  destruct op; try discriminate; destruct args as [ | k [ | ]]; try discriminate;
  destruct (index_offset get k) as [x1 c1] eqn:IO; inv H;
  exploit get_op_sound; eauto; simpl; intros E; inv E;
  exploit index_offset_sound; eauto; intros [P | [P Q]]; try (subst k c).
- rewrite P. destruct (valu x) eqn:VX; simpl; auto;
  try (right; exists i0; auto; fail); destruct Archi.ptr64; auto.
- destruct (valu x) eqn:VX; simpl; auto.
  right; exists i0; split; auto. rewrite Int.add_zero; auto.
- rewrite P. destruct (valu x) eqn:VX; simpl; auto;
  try (right; exists i0; auto; fail); destruct Archi.ptr64; auto.
- destruct (valu x) eqn:VX; simpl; auto.
  right; exists i0; split; auto. rewrite Int.add_zero; auto.
Qed.

Lemma ext_diff:
  forall M L e1 e2 y c1 c2,
  M > 0 ->
  L <= e1 < L + M -> L <= e2 < L + M ->
  Zbits.eqmod M e1 (y + c1) -> Zbits.eqmod M e2 (y + c2) ->
  e2 - e1 = (c2 - c1) mod M \/ e2 - e1 = (c2 - c1) mod M - M.
Proof.
  intros. destruct H2 as [k1 E1]. destruct H3 as [k2 E2].
  assert (R: 0 <= (c2 - c1) mod M < M) by (apply Z.mod_pos_bound; lia).
  assert (D: c2 - c1 = M * ((c2 - c1) / M) + (c2 - c1) mod M) by (apply Z.div_mod; lia).
  set (r := (c2 - c1) mod M) in *. set (q := (c2 - c1) / M) in *.
  assert (E: e2 - e1 = M * (k2 - k1 + q) + r) by lia.
  set (t := k2 - k1 + q) in *.
  assert (t = 0 \/ t = -1) by nia.
  destruct H2; [left | right]; subst; nia.
Qed.

Lemma index_value:
  forall (s: bool) n c,
  Int.eqm (if s then Int.signed (Int.add n (Int.repr c))
           else Int.unsigned (Int.add n (Int.repr c)))
          (Int.unsigned n + c).
Proof.
  intros. apply Int.eqm_trans with (Int.unsigned (Int.add n (Int.repr c))).
  destruct s. apply Int.eqm_signed_unsigned. apply Int.eqm_refl.
  rewrite Int.add_unsigned. apply Int.eqm_sym. apply Int.eqm_unsigned_repr_r.
  apply Int.eqm_add. apply Int.eqm_refl. apply Int.eqm_unsigned_repr.
Qed.

Lemma index_value_range:
  forall (s: bool) n c,
  let e := if s then Int.signed (Int.add n (Int.repr c))
           else Int.unsigned (Int.add n (Int.repr c)) in
  (if s then Int.min_signed else 0) <= e < (if s then Int.min_signed else 0) + Int.modulus.
Proof.
  intros. unfold e. destruct s.
  generalize (Int.signed_range (Int.add n (Int.repr c))).
  unfold Int.min_signed, Int.max_signed. generalize Int.half_modulus_modulus. lia.
  generalize (Int.unsigned_range (Int.add n (Int.repr c))). lia.
Qed.

Lemma ptr_shift64_offset:
  forall X1 X2 Z1 Z2,
  Archi.ptr64 = true ->
  Int64.eqm (Int64.unsigned X1) Z1 ->
  Int64.eqm (Int64.unsigned X2) Z2 ->
  Ptrofs.of_int64 X2 = Ptrofs.add (Ptrofs.of_int64 X1) (Ptrofs.repr (Z2 - Z1)).
Proof.
  intros.
  unfold Ptrofs.of_int64. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm64 in H0; auto. apply Ptrofs.eqm64 in H1; auto.
  apply Ptrofs.eqm_trans with Z2. auto.
  replace Z2 with (Z1 + (Z2 - Z1)) at 1 by lia.
  apply Ptrofs.eqm_add.
  apply Ptrofs.eqm_trans with (Int64.unsigned X1). apply Ptrofs.eqm_sym; auto.
  apply Ptrofs.eqm_unsigned_repr.
  apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma ptr_shift64:
  forall vb X1 X2 b1 o1 Z1 Z2,
  Archi.ptr64 = true ->
  Val.addl vb (Vlong X1) = Vptr b1 o1 ->
  Int64.eqm (Int64.unsigned X1) Z1 ->
  Int64.eqm (Int64.unsigned X2) Z2 ->
  Val.addl vb (Vlong X2) = Vptr b1 (Ptrofs.add o1 (Ptrofs.repr (Z2 - Z1))).
Proof.
  (* When [Archi.ptr64] is [false], the hypotheses are contradictory and
     [simpl] can already close the goal. *)
  intros. destruct vb; simpl in *; try discriminate.
  all: rewrite H in *; inv H0; f_equal; rewrite Ptrofs.add_assoc; f_equal;
       apply ptr_shift64_offset; auto.
Qed.

Lemma eqm_addmul64:
  forall a b c,
  Int64.eqm (Int64.unsigned (Int64.add (Int64.mul (Int64.repr a) (Int64.repr b)) (Int64.repr c)))
            (a * b + c).
Proof.
  intros. unfold Int64.add, Int64.mul. apply Int64.eqm_unsigned_repr_l.
  apply Int64.eqm_add; [|apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr].
  apply Int64.eqm_unsigned_repr_l.
  apply Int64.eqm_mult; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma index_deltas_sound:
  forall sc i1 i2 d,
  index_deltas get sc i1 i2 d <> nil ->
  valu i1 <> Vundef -> valu i2 <> Vundef ->
  exists e1 e2,
     valu i1 = Vlong (Int64.repr e1) /\ valu i2 = Vlong (Int64.repr e2)
  /\ In (d + sc * (e2 - e1)) (index_deltas get sc i1 i2 d).
Proof.
  intros until d; intros NN U1 U2. unfold index_deltas in *.
  destruct (index_form get i1) as [[[s1 x1] c1]|] eqn:F1; [|congruence].
  destruct (index_form get i2) as [[[s2 x2] c2]|] eqn:F2; [|congruence].
  destruct (Bool.eqb s1 s2 && peq x1 x2) eqn:C; [|congruence].
  InvBooleans. apply Bool.eqb_prop in H. subst s2 x2.
  exploit index_form_sound. eexact F1. intros [V1 | (n1 & X1 & V1)]; [congruence|].
  exploit index_form_sound. eexact F2. intros [V2 | (n2 & X2 & V2)]; [congruence|].
  rewrite X1 in X2; inv X2.
  set (e1 := if s1 then Int.signed (Int.add n2 (Int.repr c1)) else Int.unsigned (Int.add n2 (Int.repr c1))) in *.
  set (e2 := if s1 then Int.signed (Int.add n2 (Int.repr c2)) else Int.unsigned (Int.add n2 (Int.repr c2))) in *.
  exists e1, e2; split; auto; split; auto.
  exploit (ext_diff Int.modulus (if s1 then Int.min_signed else 0) e1 e2 (Int.unsigned n2) c1 c2).
  generalize Int.modulus_pos; lia.
  apply index_value_range.
  apply index_value_range.
  apply index_value.
  apply index_value.
  intros [D|D]; rewrite D; simpl; auto.
Qed.

Lemma addr_deltas_sound:
  forall addr1 vl1 addr2 vl2 b1 ofs1 b2 ofs2,
  eval_addressing ge sp addr1 (map valu vl1) = Some (Vptr b1 ofs1) ->
  eval_addressing ge sp addr2 (map valu vl2) = Some (Vptr b2 ofs2) ->
  addr_deltas get addr1 vl1 addr2 vl2 <> nil ->
  exists d, In d (addr_deltas get addr1 vl1 addr2 vl2)
         /\ Vptr b2 ofs2 = Vptr b1 (Ptrofs.add ofs1 (Ptrofs.repr d)).
Proof.
  intros until ofs2; intros E1 E2 NN. unfold addr_deltas in *.
  destruct (list_eq_dec peq vl1 vl2).
- subst vl2. destruct (addressing_delta addr1 addr2) as [d|] eqn:AD; [|congruence].
  exists d; split. auto with coqlib. eapply addressing_delta_sound; eauto.
- destruct Archi.ptr64 eqn:SF; [|congruence].
  unfold eval_addressing in E1, E2; rewrite SF in E1, E2.
  destruct addr1; try congruence; destruct addr2; try congruence;
  destruct vl1 as [ | v1 [ | i1 [ | ]]]; try congruence;
  destruct vl2 as [ | v2 [ | i2 [ | ]]]; try congruence.
+ (* Aindexed2 *)
  destruct (peq v1 v2); [|congruence]. subst v2.
  simpl in E1, E2. inv E1; inv E2.
  rewrite Val.addl_assoc in H0, H1.
  assert (U1: valu i1 <> Vundef) by (intro U; rewrite U in H0; destruct (valu v1); discriminate).
  assert (U2: valu i2 <> Vundef) by (intro U; rewrite U in H1; destruct (valu v1); discriminate).
  exploit index_deltas_sound; eauto. intros (e1 & e2 & V1 & V2 & IN).
  rewrite V1 in H0; rewrite V2 in H1; simpl in H0, H1.
  exists (z0 - z + 1 * (e2 - e1)); split; auto.
  rewrite Val.addl_assoc, V2.
  change (Val.addl (Vlong (Int64.repr e2)) (Vlong (Int64.repr z0)))
    with (Vlong (Int64.add (Int64.repr e2) (Int64.repr z0))).
  replace (z0 - z + 1 * (e2 - e1)) with ((e2 * 1 + z0) - (e1 * 1 + z)) by ring.
  eapply ptr_shift64; eauto.
  rewrite <- (Int64.mul_one (Int64.repr e1)). apply eqm_addmul64.
  rewrite <- (Int64.mul_one (Int64.repr e2)). apply eqm_addmul64.
+ (* Aindexed2scaled *)
  destruct (zeq z z1 && peq v1 v2) eqn:C; [|congruence]. InvBooleans. subst z1 v2.
  simpl in E1, E2. inv E1; inv E2.
  assert (U1: valu i1 <> Vundef) by (intro U; rewrite U in H0; destruct (valu v1); discriminate).
  assert (U2: valu i2 <> Vundef) by (intro U; rewrite U in H1; destruct (valu v1); discriminate).
  exploit index_deltas_sound; eauto. intros (e1 & e2 & V1 & V2 & IN).
  rewrite V1 in H0; rewrite V2 in H1; simpl in H0, H1.
  exists (z2 - z0 + z * (e2 - e1)); split; auto.
  rewrite V2.
  change (Val.addl (Val.mull (Vlong (Int64.repr e2)) (Vlong (Int64.repr z))) (Vlong (Int64.repr z2)))
    with (Vlong (Int64.add (Int64.mul (Int64.repr e2) (Int64.repr z)) (Int64.repr z2))).
  replace (z2 - z0 + z * (e2 - e1)) with ((e2 * z + z2) - (e1 * z + z0)) by ring.
  eapply ptr_shift64; eauto; apply eqm_addmul64.
Qed.

End COMBINE.
