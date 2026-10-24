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
Require Import Zbits AST Memdata.

(** * Merging of byte loads: memory and integer lemmas *)

(** * Integer part *)

Lemma testbit_byte_cons:
  forall x y i, 0 <= x < 256 -> 0 <= i ->
  Z.testbit (x + y * 256) i = if zlt i 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
  intros. destruct (zlt i 8).
- rewrite <- (Z.mod_pow2_bits_low (x + y * 256) 8 i) by lia.
  change (2^8) with 256. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. auto.
- replace (Z.testbit (x + y * 256) i) with (Z.testbit (x + y * 256) (i - 8 + 8)) by (f_equal; lia).
  rewrite <- (Z.div_pow2_bits (x + y * 256) 8 (i - 8)) by lia.
  change (2^8) with 256. rewrite Z_div_plus_full by lia.
  rewrite Z.div_small by lia. auto.
Qed.

Fixpoint or_bytes (k: Z) (l: list byte) : int64 :=
  match l with
  | nil => Int64.zero
  | b :: l' => Int64.or (Int64.shl' (Int64.repr (Byte.unsigned b)) (Int.repr k))
                        (or_bytes (k + 8) l')
  end.

Lemma testbit_or_bytes:
  forall l k i,
  0 <= k -> k + 8 * Z.of_nat (length l) <= 64 -> 0 <= i < Int64.zwordsize ->
  Int64.testbit (or_bytes k l) i = (proj_sumbool (zle k i) && Z.testbit (int_of_bytes l) (i - k)).
Proof.
  induction l as [ | b l IH]; intros k i K L I; simpl.
- rewrite Int64.bits_zero. rewrite Z.testbit_0_l. destruct (zle k i); auto.
- simpl length in L. rewrite Nat2Z.inj_succ in L.
  generalize (Byte.unsigned_range b); intros BR. change Byte.modulus with 256 in BR.
  assert (KR: Int.unsigned (Int.repr k) = k).
  { apply Int.unsigned_repr. unfold Int.max_unsigned; simpl. lia. }
  rewrite Int64.bits_or by auto. rewrite Int64.bits_shl' by auto. rewrite KR.
  rewrite IH by lia.
  destruct (zle k i); destruct (zle (k + 8) i); simpl.
  + rewrite zlt_false by lia. rewrite Int64.testbit_repr by lia.
    rewrite testbit_byte_cons by lia. rewrite zlt_false by lia.
    rewrite (Ztestbit_above 8 (Byte.unsigned b)); [ | change (two_power_nat 8) with 256; lia | simpl; lia ]. simpl. f_equal; lia.
  + rewrite zlt_false by lia. rewrite Int64.testbit_repr by lia.
    rewrite testbit_byte_cons by lia. rewrite zlt_true by lia. apply orb_false_r.
  + lia.
  + rewrite zlt_true by lia. auto.
Qed.

Lemma int_of_bytes_or_bytes:
  forall l, length l = 8%nat -> Int64.repr (int_of_bytes l) = or_bytes 0 l.
Proof.
  intros. apply Int64.same_bits_eq; intros.
  rewrite Int64.testbit_repr by auto. rewrite testbit_or_bytes.
  destruct (zle 0 i); [|lia]. simpl. f_equal; lia.
  lia. rewrite H; simpl; lia. auto.
Qed.

(** * Value part *)

(** The value computed by [(u64)p[0] | (u64)p[1] << 8 | ... | (u64)p[7] << 56],
    where [v0] ... [v7] are the results of the 8 byte loads. *)

Definition shifted_byte (v: val) (k: Z) : val :=
  Val.shll (Val.longofintu v) (Vint (Int.repr k)).

Definition merge8 (v0 v1 v2 v3 v4 v5 v6 v7: val) : val :=
  Val.orl (Val.longofintu v0)
 (Val.orl (shifted_byte v1 8)
 (Val.orl (shifted_byte v2 16)
 (Val.orl (shifted_byte v3 24)
 (Val.orl (shifted_byte v4 32)
 (Val.orl (shifted_byte v5 40)
 (Val.orl (shifted_byte v6 48) (shifted_byte v7 56))))))).

Lemma byte_long:
  Archi.big_endian = false ->
  forall b, Int64.repr (Int.unsigned (Int.zero_ext 8 (Int.repr (decode_int (b :: nil)))))
            = Int64.repr (Byte.unsigned b).
Proof.
  intros BE b. unfold decode_int, rev_if_be. rewrite BE. simpl.
  generalize (Byte.unsigned_range b); intros BR. change Byte.modulus with 256 in BR.
  rewrite Int.zero_ext_mod by (compute; intuition congruence).
  rewrite Int.unsigned_repr. f_equal. change (two_p 8) with 256.
  rewrite Z.mod_small; lia.
  unfold Int.max_unsigned; simpl; lia.
Qed.

Lemma decode_val_int64u_merge:
  Archi.big_endian = false ->
  forall m0 m1 m2 m3 m4 m5 m6 m7,
  decode_val Mint64u (m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: m7 :: nil) =
  merge8 (decode_val Mint8unsigned (m0 :: nil)) (decode_val Mint8unsigned (m1 :: nil))
         (decode_val Mint8unsigned (m2 :: nil)) (decode_val Mint8unsigned (m3 :: nil))
         (decode_val Mint8unsigned (m4 :: nil)) (decode_val Mint8unsigned (m5 :: nil))
         (decode_val Mint8unsigned (m6 :: nil)) (decode_val Mint8unsigned (m7 :: nil)).
Proof.
  intros BE.
  destruct m0 as [ | b0 | ]; try reflexivity;
  destruct m1 as [ | b1 | ]; try reflexivity;
  destruct m2 as [ | b2 | ]; try reflexivity;
  destruct m3 as [ | b3 | ]; try reflexivity;
  destruct m4 as [ | b4 | ]; try reflexivity;
  destruct m5 as [ | b5 | ]; try reflexivity;
  destruct m6 as [ | b6 | ]; try reflexivity;
  destruct m7 as [ | b7 | ]; try reflexivity.
  unfold decode_val, merge8, shifted_byte. simpl proj_bytes. cbn iota beta.
  cbn [Val.longofintu]. rewrite ! byte_long by auto. simpl.
  repeat match goal with |- context [Int.ltu (Int.repr ?n) Int64.iwordsize'] =>
    let E := fresh in assert (E: Int.ltu (Int.repr n) Int64.iwordsize' = true) by reflexivity;
    rewrite E; clear E end.
  simpl.
  f_equal. unfold decode_int, rev_if_be. rewrite BE.
  rewrite int_of_bytes_or_bytes by reflexivity. simpl.
  f_equal. apply Int64.same_bits_eq; intros.
  rewrite Int64.bits_shl' by auto. change (Int.unsigned (Int.repr 0)) with 0.
  rewrite zlt_false by lia. f_equal; lia.
  all: rewrite ?Int64.or_zero; auto.
Qed.

(** * Memory part *)

Lemma load_bytes_consecutive:
  forall m b ofs v,
  (forall k, 0 <= k < 8 ->
     Mem.loadv Mint8unsigned m (Vptr b (Ptrofs.add ofs (Ptrofs.repr k))) = Some (v k)) ->
  Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus /\
  (forall k, 0 <= k < 8 -> Mem.load Mint8unsigned m b (Ptrofs.unsigned ofs + k) = Some (v k)).
Proof.
  intros m b ofs v LD.
  assert (MOD: 8 <= Ptrofs.max_unsigned).
  { unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
    destruct Archi.ptr64; simpl; lia. }
  assert (L0 := LD 0 ltac:(lia)). rewrite Ptrofs.add_zero in L0.
  unfold Mem.loadv in L0. destruct zle in L0; try discriminate.
  apply Mem.load_valid_access in L0. destruct L0 as [RP _].
  assert (P0: Mem.perm m b (Ptrofs.unsigned ofs) Cur Readable) by (apply RP; simpl; lia).
  apply Mem.perm_bounded in P0. unfold perm_limit in P0.
  split. lia.
  intros k K. generalize (LD k K). unfold Mem.loadv.
  rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr k) by lia.
  rewrite Ptrofs.unsigned_repr by (generalize (Ptrofs.unsigned_range ofs); unfold Ptrofs.max_unsigned; lia).
  destruct zle; [auto | intros; discriminate].
Qed.

Lemma load_byte_loadbytes:
  forall m b o v,
  Mem.load Mint8unsigned m b o = Some v ->
  exists mv, Mem.loadbytes m b o 1 = Some (mv :: nil) /\ v = decode_val Mint8unsigned (mv :: nil).
Proof.
  intros. exploit Mem.load_loadbytes; eauto. intros (bytes & A & B).
  exploit Mem.loadbytes_length; eauto. simpl. intros LEN.
  destruct bytes as [ | mv [ | ? ?]]; simpl in LEN; try discriminate.
  exists mv; auto.
Qed.

Theorem loadv_int64u_merge:
  Archi.big_endian = false ->
  forall m b ofs v,
  (forall k, 0 <= k < 8 ->
     Mem.loadv Mint8unsigned m (Vptr b (Ptrofs.add ofs (Ptrofs.repr k))) = Some (v k)) ->
  Mem.loadv Mint64u m (Vptr b ofs) =
  Some (merge8 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)).
Proof.
  intros BE m b ofs v LD.
  destruct (load_bytes_consecutive m b ofs v LD) as [BND L].
  set (o := Ptrofs.unsigned ofs) in *.
  destruct (load_byte_loadbytes _ _ _ _ (L 0 ltac:(lia))) as (m0 & B0 & V0).
  destruct (load_byte_loadbytes _ _ _ _ (L 1 ltac:(lia))) as (m1 & B1 & V1).
  destruct (load_byte_loadbytes _ _ _ _ (L 2 ltac:(lia))) as (m2 & B2 & V2).
  destruct (load_byte_loadbytes _ _ _ _ (L 3 ltac:(lia))) as (m3 & B3 & V3).
  destruct (load_byte_loadbytes _ _ _ _ (L 4 ltac:(lia))) as (m4 & B4 & V4).
  destruct (load_byte_loadbytes _ _ _ _ (L 5 ltac:(lia))) as (m5 & B5 & V5).
  destruct (load_byte_loadbytes _ _ _ _ (L 6 ltac:(lia))) as (m6 & B6 & V6).
  destruct (load_byte_loadbytes _ _ _ _ (L 7 ltac:(lia))) as (m7 & B7 & V7).
  rewrite Z.add_0_r in B0.
  assert (CC: forall p n x l, Mem.loadbytes m b p 1 = Some (x :: nil) ->
                Mem.loadbytes m b (p + 1) n = Some l -> 0 <= n ->
                Mem.loadbytes m b p (1 + n) = Some (x :: l)).
  { intros. exploit Mem.loadbytes_concat. eexact H. eexact H0. lia. lia. auto. }
  replace (o + 7) with (o + 6 + 1) in B7 by lia.
  generalize (CC _ _ _ _ B6 B7 ltac:(lia)); intros C6.
  replace (o + 6) with (o + 5 + 1) in C6 by lia.
  generalize (CC _ _ _ _ B5 C6 ltac:(lia)); intros C5.
  replace (o + 5) with (o + 4 + 1) in C5 by lia.
  generalize (CC _ _ _ _ B4 C5 ltac:(lia)); intros C4.
  replace (o + 4) with (o + 3 + 1) in C4 by lia.
  generalize (CC _ _ _ _ B3 C4 ltac:(lia)); intros C3.
  replace (o + 3) with (o + 2 + 1) in C3 by lia.
  generalize (CC _ _ _ _ B2 C3 ltac:(lia)); intros C2.
  replace (o + 2) with (o + 1 + 1) in C2 by lia.
  generalize (CC _ _ _ _ B1 C2 ltac:(lia)); intros C1.
  generalize (CC _ _ _ _ B0 C1 ltac:(lia)); intros C07.
  simpl in C07.
  unfold Mem.loadv. rewrite zle_true by (simpl; lia). fold o.
  rewrite (Mem.loadbytes_load Mint64u m b o _ C07) by (simpl; auto using Z.divide_1_l).
  rewrite decode_val_int64u_merge by auto.
  rewrite V0, V1, V2, V3, V4, V5, V6, V7. auto.
Qed.


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

Lemma scale_shift_sound:
  forall sc ofs n,
  scale_shift sc ofs = Some n ->
  Int.ltu n Int.iwordsize = true /\ Int.ltu n Int64.iwordsize' = true /\
  ofs = 0 /\ Int.repr sc = Int.shl Int.one n /\ Int64.repr sc = Int64.shl' Int64.one n.
Proof.
  unfold scale_shift; intros.
  destruct (zeq ofs 0); try discriminate.
  destruct (zeq sc 2). subst; inv H; intuition reflexivity.
  destruct (zeq sc 4). subst; inv H; intuition reflexivity.
  destruct (zeq sc 8). subst; inv H; intuition reflexivity.
  discriminate.
Qed.

Lemma shl_of_sound:
  forall x n a, shl_of get x = Some (n, a) -> valu x = Val.shl (valu a) (Vint n).
Proof.
  unfold shl_of; intros.
  destruct (get x) as [rh|] eqn:G; try discriminate.
  destruct rh as [op vl| | ]; try discriminate.
  destruct op; try discriminate.
- destruct vl as [|a' [|]]; inv H.
  generalize (get_op_sound _ _ _ G); simpl; intros EQ. congruence.
- destruct a0; try discriminate. destruct vl as [|a' [|]]; try discriminate.
  destruct (scale_shift z z0) as [n'|] eqn:SC; inv H.
  exploit scale_shift_sound; eauto. intros (A & B & C & D & E). subst z0.
  generalize (get_op_sound _ _ _ G); simpl; intros EQ. inv EQ. rewrite D.
  destruct (valu a); simpl; auto. rewrite A. rewrite Int.add_zero.
  rewrite <- Int.shl_mul. auto.
Qed.

Lemma shll_of_sound:
  forall x n a, shll_of get x = Some (n, a) -> valu x = Val.shll (valu a) (Vint n).
Proof.
  unfold shll_of; intros.
  destruct (get x) as [rh|] eqn:G; try discriminate.
  destruct rh as [op vl| | ]; try discriminate.
  destruct op; try discriminate.
- destruct vl as [|a' [|]]; inv H.
  generalize (get_op_sound _ _ _ G); simpl; intros EQ. congruence.
- destruct a0; try discriminate. destruct vl as [|a' [|]]; try discriminate.
  destruct (scale_shift z z0) as [n'|] eqn:SC; inv H.
  exploit scale_shift_sound; eauto. intros (A & B & C & D & E). subst z0.
  generalize (get_op_sound _ _ _ G); simpl; intros EQ. inv EQ. rewrite E.
  destruct (valu a); simpl; auto. rewrite B. rewrite Int64.add_zero.
  rewrite <- Int64.shl'_mul. auto.
Qed.

Lemma combine_ror_sound:
  forall x y op' args',
  combine_ror get x y = Some (op', args') ->
  exists r', eval_operation ge sp op' (map valu args') m = Some r'
          /\ Val.lessdef (Val.or (valu x) (valu y)) r'.
Proof.
  unfold combine_ror; intros.
  destruct (shl_of get x) as [[n1 a]|] eqn:SH; try discriminate.
  destruct (get y) as [rh|] eqn:G; try discriminate.
  destruct rh as [op vl| | ]; try discriminate.
  destruct op; try discriminate. destruct vl as [|b [|]]; try discriminate.
  destruct (eq_valnum a b); try discriminate. subst b.
  destruct (Int.eq (Int.add n1 n) Int.iwordsize) eqn:E; simpl in H; inv H.
  generalize (Int.eq_spec (Int.add n1 n) Int.iwordsize); rewrite E; intros H0. generalize (get_op_sound _ _ _ G); simpl; intros EQ. inv EQ. rewrite (shl_of_sound _ _ _ SH).
  econstructor; split. simpl. eauto.
  destruct (valu a); simpl; auto.
  destruct (Int.ltu n1 Int.iwordsize) eqn:?; auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; auto.
  simpl. rewrite <- Int.or_ror; auto.
Qed.

Lemma combine_rorl_sound:
  forall x y op' args',
  combine_rorl get x y = Some (op', args') ->
  exists r', eval_operation ge sp op' (map valu args') m = Some r'
          /\ Val.lessdef (Val.orl (valu x) (valu y)) r'.
Proof.
  unfold combine_rorl; intros.
  destruct (shll_of get x) as [[n1 a]|] eqn:SH; try discriminate.
  destruct (get y) as [rh|] eqn:G; try discriminate.
  destruct rh as [op vl| | ]; try discriminate.
  destruct op; try discriminate. destruct vl as [|b [|]]; try discriminate.
  destruct (eq_valnum a b); try discriminate. subst b.
  destruct (Int.eq (Int.add n1 n) Int64.iwordsize') eqn:E; simpl in H; inv H.
  generalize (Int.eq_spec (Int.add n1 n) Int64.iwordsize'); rewrite E; intros H0. generalize (get_op_sound _ _ _ G); simpl; intros EQ. inv EQ. rewrite (shll_of_sound _ _ _ SH).
  econstructor; split. simpl. eauto.
  destruct (valu a); simpl; auto.
  destruct (Int.ltu n1 Int64.iwordsize') eqn:?; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:?; auto.
  simpl. rewrite <- Int64.or_ror'; auto.
Qed.

Lemma combine_or_sound:
  forall x y op' args',
  combine_or get x y = Some (op', args') ->
  exists r', eval_operation ge sp op' (map valu args') m = Some r'
          /\ Val.lessdef (Val.or (valu x) (valu y)) r'.
Proof.
  unfold combine_or; intros. destruct (combine_ror get x y) as [r|] eqn:C.
- inv H. eapply combine_ror_sound; eauto.
- rewrite Val.or_commut. eapply combine_ror_sound; eauto.
Qed.

Lemma combine_orl_sound:
  forall x y op' args',
  combine_orl get x y = Some (op', args') ->
  exists r', eval_operation ge sp op' (map valu args') m = Some r'
          /\ Val.lessdef (Val.orl (valu x) (valu y)) r'.
Proof.
  unfold combine_orl; intros. destruct (combine_rorl get x y) as [r|] eqn:C.
- inv H. eapply combine_rorl_sound; eauto.
- rewrite Val.orl_commut. eapply combine_rorl_sound; eauto.
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
(* or - rotate *)
 - simpl in H0. inv H0. eapply combine_or_sound; eauto.
(* orl - rotate *)
 - simpl in H0. inv H0. eapply combine_orl_sound; eauto.
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


(** ** Merging of byte loads *)

Section MERGE_BYTES.

(** [Archi.ptr64] is stated as [Is_true] rather than as an equation, so that
  on 32-bit x86 it does not make [discriminate] close unrelated goals. *)

(** The value loaded (as an unsigned byte) from [bv + ofs]. *)

Definition byteval (bv: val) (ofs: Z) : val :=
  match Mem.loadv Mint8unsigned m (Val.addl bv (Vlong (Int64.repr ofs))) with
  | Some v => v
  | None => Vundef
  end.

Definition bytes_loaded (bv: val) (l: list (Z * Z)) : Prop :=
  forall p, In p l ->
  exists v, Mem.loadv Mint8unsigned m (Val.addl bv (Vlong (Int64.repr (fst p)))) = Some v.

Fixpoint bytes_den (bv: val) (l: list (Z * Z)) : option Z :=
  match l with
  | nil => Some 0
  | p :: l' =>
      match byteval bv (fst p), bytes_den bv l' with
      | Vint n, Some d => Some (Z.lor (Z.shiftl (Int.unsigned n) (snd p)) d)
      | _, _ => None
      end
  end.

Definition bytecomp_val (c: bytecomp) : val :=
  match bytes_den (valu (bcbase c)) (bcbytes c) with
  | Some d => if bc64 c then Vlong (Int64.repr d) else Vint (Int.repr d)
  | None => Vundef
  end.

Definition bytecomp_ok (c: bytecomp) : Prop :=
  bytes_loaded (valu (bcbase c)) (bcbytes c)
  /\ bytes_fit (if bc64 c then 64 else 32) (bcbytes c) = true.

Lemma byteval_shape:
  forall bv ofs,
  byteval bv ofs = Vundef \/ exists n, byteval bv ofs = Vint n /\ 0 <= Int.unsigned n < 256.
Proof.
  intros. unfold byteval.
  destruct (Mem.loadv Mint8unsigned m (Val.addl bv (Vlong (Int64.repr ofs)))) as [v|] eqn:L; auto.
  assert (C: v = Val.zero_ext 8 v).
  { destruct (Val.addl bv (Vlong (Int64.repr ofs))); simpl in L; try discriminate.
    all: destruct zle in L; [|discriminate].
    all: exact (Mem.load_cast _ _ _ _ _ L). }
  destruct v; simpl in C; try discriminate; auto.
  right. eexists; split; [reflexivity|]. injection C; intros C'. rewrite C'.
  match goal with |- context [Int.zero_ext 8 ?x] =>
    generalize (Int.zero_ext_range 8 x) end.
  change (two_p 8) with 256. intros R. apply R.
  compute; intuition congruence.
Qed.

Lemma byteval_loaded:
  forall bv ofs v,
  Mem.loadv Mint8unsigned m (Val.addl bv (Vlong (Int64.repr ofs))) = Some v ->
  byteval bv ofs = v.
Proof.
  unfold byteval; intros. rewrite H; auto.
Qed.

(** Properties of the denotation. *)

Lemma bytes_den_nonneg:
  forall bv l d, bytes_den bv l = Some d -> 0 <= d.
Proof.
  induction l as [ | [o p] l]; simpl; intros.
- inv H; lia.
- destruct (byteval bv o); try discriminate.
  destruct (bytes_den bv l) as [d'|] eqn:D; inv H.
  apply Z.lor_nonneg. split; [|eauto].
  apply Z.shiftl_nonneg. generalize (Int.unsigned_range i); lia.
Qed.

Lemma bytes_den_above:
  forall bv w l d,
  bytes_fit w l = true -> bytes_den bv l = Some d ->
  forall i, w <= i -> Z.testbit d i = false.
Proof.
  induction l as [ | [o p] l]; simpl; intros.
- inv H0. apply Z.testbit_0_l.
- InvBooleans.
  destruct (byteval_shape bv o) as [E | (n & E & R)]; rewrite E in H0; try discriminate.
  destruct (bytes_den bv l) as [d'|] eqn:D; inv H0.
  rewrite Z.lor_spec. rewrite (IHl d') by auto. rewrite orb_false_r.
  rewrite Z.shiftl_spec by lia. simpl in *.
  apply (Ztestbit_above 8). change (two_power_nat 8) with 256; lia. simpl; lia.
Qed.

Lemma bytes_den_app:
  forall bv l1 l2,
  bytes_den bv (l1 ++ l2) =
  match bytes_den bv l1, bytes_den bv l2 with
  | Some d1, Some d2 => Some (Z.lor d1 d2)
  | _, _ => None
  end.
Proof.
  induction l1 as [ | [o p] l1]; simpl; intros.
- destruct (bytes_den bv l2); auto.
- rewrite IHl1. destruct (byteval bv o); auto.
  destruct (bytes_den bv l1); destruct (bytes_den bv l2); auto.
  rewrite Z.lor_assoc; auto.
Qed.

Lemma bytes_den_shift:
  forall bv n w l, 0 <= n -> bytes_fit w l = true ->
  bytes_den bv (bytes_shift n l) = option_map (fun d => Z.shiftl d n) (bytes_den bv l).
Proof.
  induction l as [ | [o p] l]; simpl; intros.
- rewrite Z.shiftl_0_l; auto.
- InvBooleans. rewrite IHl by auto. destruct (byteval bv o); auto.
  destruct (bytes_den bv l); simpl; auto.
  rewrite Z.shiftl_lor. rewrite Z.shiftl_shiftl by auto. auto.
Qed.

Lemma bytes_den_some:
  forall bv l, (forall p, In p l -> exists n, byteval bv (fst p) = Vint n) ->
  exists d, bytes_den bv l = Some d.
Proof.
  induction l as [ | [o p] l]; simpl; intros.
- exists 0; auto.
- destruct (H (o, p)) as [n E]; auto. simpl in E. rewrite E.
  destruct IHl as [d D]; auto. rewrite D. econstructor; eauto.
Qed.

Lemma bytes_den_none:
  forall bv l, bytes_den bv l = None ->
  exists p, In p l /\ forall n, byteval bv (fst p) <> Vint n.
Proof.
  induction l as [ | [o p] l]; simpl; intros.
- discriminate.
- destruct (byteval bv o) eqn:E;
  try (exists (o, p); split; auto; simpl; rewrite E; congruence).
  destruct (bytes_den bv l) eqn:D; try discriminate.
  destruct IHl as (q & A & B); auto. exists q; auto.
Qed.

Lemma bytes_den_testbit:
  forall bv l d i, bytes_den bv l = Some d -> 0 <= i ->
  Z.testbit d i = true <->
  exists p n, In p l /\ byteval bv (fst p) = Vint n
           /\ Z.testbit (Z.shiftl (Int.unsigned n) (snd p)) i = true.
Proof.
  induction l as [ | [o p] l]; simpl; intros.
- inv H. rewrite Z.testbit_0_l. split; [discriminate | intros (q & n & [] & _)].
- destruct (byteval bv o) eqn:E; try discriminate.
  destruct (bytes_den bv l) as [d'|] eqn:D; inv H.
  rewrite Z.lor_spec, orb_true_iff, (IHl d' i) by auto. split.
  + intros [A | (q & n & A & B & C)].
    exists (o, p), i0; auto.
    exists q, n; auto.
  + intros (q & n & [A | A] & B & C).
    subst q. simpl in B. rewrite E in B. inv B. auto.
    right; exists q, n; auto.
Qed.

Lemma bytes_den_incl:
  forall bv l1 l2 d1 d2,
  incl l1 l2 -> incl l2 l1 ->
  bytes_den bv l1 = Some d1 -> bytes_den bv l2 = Some d2 -> d1 = d2.
Proof.
  intros. apply Z.bits_inj'; intros i I.
  apply eq_true_iff_eq.
  rewrite (bytes_den_testbit bv l1 d1 i), (bytes_den_testbit bv l2 d2 i) by auto.
  split; intros (q & n & A & B & C); exists q, n; auto.
Qed.

Lemma bytes_incl_sound:
  forall l1 l2, bytes_incl l1 l2 = true -> incl l1 l2.
Proof.
  unfold bytes_incl; intros. red; intros.
  rewrite forallb_forall in H. specialize (H a H0).
  destruct (In_dec pair_eq a l2); auto; discriminate.
Qed.

Lemma bytes_den_all:
  forall bv l,
  (exists d, bytes_den bv l = Some d) <-> (forall p, In p l -> exists n, byteval bv (fst p) = Vint n).
Proof.
  intros; split.
- induction l as [ | [o p] l]; simpl; intros (d & D) q IN.
  + contradiction.
  + destruct (byteval bv o) eqn:E; try discriminate.
    destruct (bytes_den bv l) as [d'|] eqn:D'; try discriminate.
    destruct IN as [IN | IN]. subst q; simpl; eauto. eauto.
- apply bytes_den_some.
Qed.

Lemma bytecomp_val_incl:
  forall c1 c2,
  bc64 c1 = bc64 c2 -> bcbase c1 = bcbase c2 ->
  incl (bcbytes c1) (bcbytes c2) -> incl (bcbytes c2) (bcbytes c1) ->
  bytecomp_val c1 = bytecomp_val c2.
Proof.
  intros. unfold bytecomp_val. rewrite <- H0, <- H.
  set (bv := valu (bcbase c1)).
  destruct (bytes_den bv (bcbytes c1)) as [d1|] eqn:D1;
  destruct (bytes_den bv (bcbytes c2)) as [d2|] eqn:D2; auto.
- rewrite (bytes_den_incl bv _ _ _ _ H1 H2 D1 D2). auto.
- assert (exists d, bytes_den bv (bcbytes c2) = Some d).
  { apply bytes_den_all. intros. apply (proj1 (bytes_den_all bv (bcbytes c1))); eauto. }
  destruct H3; congruence.
- assert (exists d, bytes_den bv (bcbytes c1) = Some d).
  { apply bytes_den_all. intros. apply (proj1 (bytes_den_all bv (bcbytes c2))); eauto. }
  destruct H3; congruence.
Qed.

(** Arithmetic on the denotations. *)

Lemma or32_den:
  forall d1 d2, Val.or (Vint (Int.repr d1)) (Vint (Int.repr d2)) = Vint (Int.repr (Z.lor d1 d2)).
Proof.
  intros; simpl; f_equal. apply Int.same_bits_eq; intros.
  rewrite Int.bits_or, !Int.testbit_repr, Z.lor_spec by auto. auto.
Qed.

Lemma or64_den:
  forall d1 d2, Val.orl (Vlong (Int64.repr d1)) (Vlong (Int64.repr d2)) = Vlong (Int64.repr (Z.lor d1 d2)).
Proof.
  intros; simpl; f_equal. apply Int64.same_bits_eq; intros.
  rewrite Int64.bits_or, !Int64.testbit_repr, Z.lor_spec by auto. auto.
Qed.

Lemma shl32_den:
  forall d n, Int.ltu n Int.iwordsize = true ->
  Val.shl (Vint (Int.repr d)) (Vint n) = Vint (Int.repr (Z.shiftl d (Int.unsigned n))).
Proof.
  intros; simpl; rewrite H; f_equal. unfold Int.shl. apply Int.same_bits_eq; intros.
  generalize (Int.unsigned_range n); intros.
  rewrite !Int.testbit_repr by auto. rewrite !Z.shiftl_spec by lia.
  destruct (zlt (i - Int.unsigned n) 0).
  rewrite !Z.testbit_neg_r by auto. auto.
  change (Z.testbit (Int.unsigned (Int.repr d)) (i - Int.unsigned n))
    with (Int.testbit (Int.repr d) (i - Int.unsigned n)).
  apply Int.testbit_repr. lia.
Qed.

Lemma shl64_den:
  forall d n, Int.ltu n Int64.iwordsize' = true ->
  Val.shll (Vlong (Int64.repr d)) (Vint n) = Vlong (Int64.repr (Z.shiftl d (Int.unsigned n))).
Proof.
  intros; simpl; rewrite H; f_equal. unfold Int64.shl'. apply Int64.same_bits_eq; intros.
  generalize (Int.unsigned_range n); intros.
  rewrite !Int64.testbit_repr by auto. rewrite !Z.shiftl_spec by lia.
  destruct (zlt (i - Int.unsigned n) 0).
  rewrite !Z.testbit_neg_r by auto. auto.
  change (Z.testbit (Int64.unsigned (Int64.repr d)) (i - Int.unsigned n))
    with (Int64.testbit (Int64.repr d) (i - Int.unsigned n)).
  apply Int64.testbit_repr. lia.
Qed.

Lemma cast_den:
  forall d, (forall i, 32 <= i -> Z.testbit d i = false) ->
  Val.longofintu (Vint (Int.repr d)) = Vlong (Int64.repr d).
Proof.
  intros; simpl; f_equal. apply Int64.same_bits_eq; intros.
  rewrite !Int64.testbit_repr by auto.
  destruct (zlt i 32).
  change (Z.testbit (Int.unsigned (Int.repr d)) i) with (Int.testbit (Int.repr d) i).
  apply Int.testbit_repr. change Int.zwordsize with 32; lia.
  rewrite H by lia. apply (Ztestbit_above 32). apply Int.unsigned_range. simpl; lia.
Qed.

Lemma zext8_den:
  forall d, (forall i, 8 <= i -> Z.testbit d i = false) ->
  Val.longofintu (Val.zero_ext 8 (Vint (Int.repr d))) = Vlong (Int64.repr d).
Proof.
  intros.
  assert (Z: Int.zero_ext 8 (Int.repr d) = Int.repr d).
  { apply Int.same_bits_eq; intros.
    rewrite Int.bits_zero_ext by lia. rewrite Int.testbit_repr by auto.
    destruct (zlt i 8); auto. rewrite H by lia. auto. }
  simpl Val.zero_ext. rewrite Z. apply cast_den. intros; apply H; lia.
Qed.

(** Soundness of the recognition. *)

Lemma bytes_fit_mono:
  forall w1 w2 l, w1 <= w2 -> bytes_fit w1 l = true -> bytes_fit w2 l = true.
Proof.
  unfold bytes_fit; intros. rewrite forallb_forall in *. intros. specialize (H0 x H1).
  InvBooleans. rewrite andb_true_iff; split.
  destruct (zle 0 (snd x)); auto; lia. destruct (zle (snd x + 8) w2); auto; lia.
Qed.

Definition rec_sound (rec: valnum -> option bytecomp) : Prop :=
  forall v c, rec v = Some c -> bytecomp_ok c /\ valu v = bytecomp_val c.

Lemma bytes_loaded_shift:
  forall bv n l, bytes_loaded bv l -> bytes_loaded bv (bytes_shift n l).
Proof.
  unfold bytes_loaded, bytes_shift; intros. apply in_map_iff in H0.
  destruct H0 as (q & E & IN). subst p. simpl. apply H; auto.
Qed.

Lemma bytes_loaded_app:
  forall bv l1 l2, bytes_loaded bv l1 -> bytes_loaded bv l2 -> bytes_loaded bv (l1 ++ l2).
Proof.
  unfold bytes_loaded; intros. apply in_app_or in H1. destruct H1; auto.
Qed.

Lemma bytes_fit_app:
  forall w l1 l2, bytes_fit w l1 = true -> bytes_fit w l2 = true -> bytes_fit w (l1 ++ l2) = true.
Proof.
  unfold bytes_fit; intros. rewrite forallb_app, H, H0; auto.
Qed.

Lemma val_of_32:
  forall c, bc64 c = false ->
  bytecomp_val c = match bytes_den (valu (bcbase c)) (bcbytes c) with
                   | Some d => Vint (Int.repr d) | None => Vundef end.
Proof.
  unfold bytecomp_val; intros. rewrite H. auto.
Qed.

Lemma val_of_64:
  forall c, bc64 c = true ->
  bytecomp_val c = match bytes_den (valu (bcbase c)) (bcbytes c) with
                   | Some d => Vlong (Int64.repr d) | None => Vundef end.
Proof.
  unfold bytecomp_val; intros. rewrite H. auto.
Qed.

Lemma widen_inv:
  forall oc w c, bytecomp_widen oc w = Some c ->
  exists c0, oc = Some c0 /\ bc64 c0 = false /\ bytes_fit w (bcbytes c0) = true
          /\ c = mkbytecomp true (bcbase c0) (bcbytes c0).
Proof.
  unfold bytecomp_widen; intros. destruct oc as [c0|]; try discriminate.
  destruct (negb (bc64 c0) && bytes_fit w (bcbytes c0)) eqn:C; inv H. InvBooleans.
  exists c0; intuition auto. destruct (bc64 c0); auto; discriminate.
Qed.

Lemma shl_inv:
  forall oc is64 res64 n c, bytecomp_shl oc is64 res64 n = Some c ->
  exists c0, oc = Some c0 /\ bc64 c0 = is64
          /\ bytes_fit (if is64 then 64 else 32) (bytes_shift (Int.unsigned n) (bcbytes c0)) = true
          /\ c = mkbytecomp res64 (bcbase c0) (bytes_shift (Int.unsigned n) (bcbytes c0)).
Proof.
  unfold bytecomp_shl; intros. destruct oc as [c0|]; try discriminate.
  destruct (Bool.eqb (bc64 c0) is64 && _) eqn:C; inv H. InvBooleans.
  exists c0; intuition auto. apply Bool.eqb_prop; auto.
Qed.

Lemma or_inv:
  forall oc1 oc2 is64 c, bytecomp_or oc1 oc2 is64 = Some c ->
  exists c1 c2, oc1 = Some c1 /\ oc2 = Some c2 /\ bc64 c1 = is64 /\ bc64 c2 = is64
             /\ bcbase c2 = bcbase c1
             /\ c = mkbytecomp is64 (bcbase c1) (bcbytes c1 ++ bcbytes c2).
Proof.
  unfold bytecomp_or; intros. destruct oc1 as [c1|]; destruct oc2 as [c2|]; try discriminate.
  destruct (Bool.eqb (bc64 c1) is64 && Bool.eqb (bc64 c2) is64 && peq (bcbase c1) (bcbase c2)) eqn:C;
  inv H. InvBooleans.
  exists c1, c2; intuition auto; try (apply Bool.eqb_prop; auto).
Qed.

Lemma bytecomp_op_sound:
  forall rec op args c x,
  rec_sound rec ->
  bytecomp_op rec op args = Some c ->
  eval_operation ge sp op (map valu args) m = Some x ->
  bytecomp_ok c /\ x = bytecomp_val c.
Proof.
  intros until x; intros RS BC EV.
  unfold bytecomp_op in BC.
  destruct op; try discriminate;
  repeat (destruct args as [ | ? args]; try discriminate).
- (* or *)
  apply or_inv in BC. destruct BC as (c1 & c2 & R1 & R2 & B1 & B2 & BS & E). subst c.
  destruct (RS _ _ R1) as [[LD1 FT1] V1]. destruct (RS _ _ R2) as [[LD2 FT2] V2].
  rewrite val_of_32 in V1, V2 by auto. rewrite BS in V2, LD2.
  simpl in EV; inv EV. split.
  split. apply bytes_loaded_app; auto. simpl. rewrite B1 in FT1; rewrite B2 in FT2. apply bytes_fit_app; auto.
  rewrite val_of_32 by auto. simpl. rewrite V1, V2. rewrite bytes_den_app.
  destruct (bytes_den (valu (bcbase c1)) (bcbytes c1)) as [d1|];
  destruct (bytes_den (valu (bcbase c1)) (bcbytes c2)) as [d2|]; auto.
  apply or32_den.
- (* shlimm *)
  destruct (Int.ltu n Int.iwordsize) eqn:LT; try discriminate.
  apply shl_inv in BC. destruct BC as (c0 & R & B & F & E). subst c.
  destruct (RS _ _ R) as [[LD FT] V]. rewrite val_of_32 in V by auto.
  simpl in EV; inv EV. split.
  split. apply bytes_loaded_shift; auto. auto.
  rewrite val_of_32 by auto. simpl. rewrite V.
  generalize (Int.unsigned_range n); intros NR.
  rewrite (bytes_den_shift _ _ _ _ (proj1 NR) FT).
  destruct (bytes_den (valu (bcbase c0)) (bcbytes c0)) as [d|] eqn:D; auto. simpl.
  apply shl32_den; auto.
- (* cast32unsigned *)
  apply widen_inv in BC. destruct BC as (c0 & R & B & F & E). subst c.
  destruct (RS _ _ R) as [[LD FT] V]. rewrite val_of_32 in V by auto.
  simpl in EV; inv EV. split.
  split; auto. simpl; eapply bytes_fit_mono; [|exact F]; lia.
  rewrite val_of_64 by auto. simpl. rewrite V.
  destruct (bytes_den (valu (bcbase c0)) (bcbytes c0)) as [d|] eqn:D; auto.
  apply cast_den. intros; eapply bytes_den_above; [exact F | exact D | auto].
- (* zextshlimm *)
  destruct (Int.ltu n Int.iwordsize) eqn:LT; try discriminate.
  apply shl_inv in BC. destruct BC as (c0 & R & B & F & E). subst c.
  destruct (RS _ _ R) as [[LD FT] V]. rewrite val_of_32 in V by auto.
  simpl in EV; inv EV. split.
  split. apply bytes_loaded_shift; auto. simpl; eapply bytes_fit_mono; [|exact F]; lia.
  rewrite val_of_64 by auto. simpl. rewrite V.
  generalize (Int.unsigned_range n); intros NR.
  rewrite (bytes_den_shift _ _ _ _ (proj1 NR) FT).
  destruct (bytes_den (valu (bcbase c0)) (bcbytes c0)) as [d|] eqn:D; auto. simpl.
  rewrite LT.
  replace (Int.shl (Int.repr d) n) with (Int.repr (Z.shiftl d (Int.unsigned n)))
    by (generalize (shl32_den d n LT); simpl; rewrite LT; congruence).
  apply cast_den.
  intros. eapply bytes_den_above. eexact F. rewrite (bytes_den_shift _ _ _ _ (proj1 NR) FT). rewrite D. reflexivity. auto.
- (* orl *)
  apply or_inv in BC. destruct BC as (c1 & c2 & R1 & R2 & B1 & B2 & BS & E). subst c.
  destruct (RS _ _ R1) as [[LD1 FT1] V1]. destruct (RS _ _ R2) as [[LD2 FT2] V2].
  rewrite val_of_64 in V1, V2 by auto. rewrite BS in V2, LD2.
  simpl in EV; inv EV. split.
  split. apply bytes_loaded_app; auto. simpl. rewrite B1 in FT1; rewrite B2 in FT2. apply bytes_fit_app; auto.
  rewrite val_of_64 by auto. simpl. rewrite V1, V2. rewrite bytes_den_app.
  destruct (bytes_den (valu (bcbase c1)) (bcbytes c1)) as [d1|];
  destruct (bytes_den (valu (bcbase c1)) (bcbytes c2)) as [d2|]; auto.
  apply or64_den.
- (* shllimm *)
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; try discriminate.
  apply shl_inv in BC. destruct BC as (c0 & R & B & F & E). subst c.
  destruct (RS _ _ R) as [[LD FT] V]. rewrite val_of_64 in V by auto.
  simpl in EV; inv EV. split.
  split. apply bytes_loaded_shift; auto. auto.
  rewrite val_of_64 by auto. simpl. rewrite V.
  generalize (Int.unsigned_range n); intros NR.
  rewrite (bytes_den_shift _ _ _ _ (proj1 NR) FT).
  destruct (bytes_den (valu (bcbase c0)) (bcbytes c0)) as [d|] eqn:D; auto. simpl.
  apply shl64_den; auto.
- (* zextb64 *)
  apply widen_inv in BC. destruct BC as (c0 & R & B & F & E). subst c.
  destruct (RS _ _ R) as [[LD FT] V]. rewrite val_of_32 in V by auto.
  simpl in EV; inv EV. split.
  split; auto. simpl; eapply bytes_fit_mono; [|exact F]; lia.
  rewrite val_of_64 by auto. simpl. rewrite V.
  destruct (bytes_den (valu (bcbase c0)) (bcbytes c0)) as [d|] eqn:D; auto.
  apply zext8_den. intros; eapply bytes_den_above; [exact F | exact D | auto].
- (* zextb64_ld *)
  apply widen_inv in BC. destruct BC as (c0 & R & B & F & E). subst c.
  destruct (RS _ _ R) as [[LD FT] V]. rewrite val_of_32 in V by auto.
  simpl in EV; inv EV. split.
  split; auto. simpl; eapply bytes_fit_mono; [|exact F]; lia.
  rewrite val_of_64 by auto. simpl. rewrite V.
  destruct (bytes_den (valu (bcbase c0)) (bcbytes c0)) as [d|] eqn:D; auto.
  apply zext8_den. intros; eapply bytes_den_above; [exact F | exact D | auto].
Qed.

Lemma bytecomp_of_sound:
  forall fuel, Is_true Archi.ptr64 -> rec_sound (bytecomp_of get fuel).
Proof.
  intros fuel P64; induction fuel; red; simpl; intros.
- discriminate.
- destruct (get v) as [[op args | chunk addr args p | bf args]|] eqn:G; try discriminate.
+ split; eapply bytecomp_op_sound; eauto. eapply get_op_sound; eauto.
  eapply get_op_sound; eauto.
+ destruct chunk; try discriminate. destruct addr; try discriminate.
  destruct args as [ | b [ | ]]; inv H.
  exploit get_sound; eauto. intros RE; inv RE.
  match goal with H: eval_addressing _ _ _ _ = Some _ |- _ =>
    unfold eval_addressing in H; rewrite (Is_true_eq_true _ P64) in H; simpl in H; inv H end.
  assert (BV: byteval (valu b) z = valu v) by (apply byteval_loaded; auto).
  split. split.
  red; simpl; intros. destruct H as [H|[]]; subst p0; simpl; eauto.
  reflexivity.
  unfold bytecomp_val; simpl. rewrite BV.
  destruct (byteval_shape (valu b) z) as [E | (n & E & R)]; rewrite BV in E; rewrite E; auto.
  rewrite ?Z.shiftl_0_r, Z.lor_0_r, Int.repr_unsigned; auto.
Qed.

(** The final value. *)

Lemma in_le64:
  forall o k, 0 <= k < 8 -> In (o + k, 8 * k) (bytes_le64 o).
Proof.
  intros. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  unfold bytes_le64.
  intuition (subst k; simpl; rewrite ?Z.add_0_r; tauto).
Qed.

Lemma shl'_testbit:
  forall x k i, 0 <= k < 64 -> 0 <= i < Int64.zwordsize ->
  Int64.testbit (Int64.shl' (Int64.repr x) (Int.repr k)) i = Z.testbit (Z.shiftl x k) i.
Proof.
  intros. rewrite Int64.bits_shl' by auto.
  rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia).
  rewrite Z.shiftl_spec by lia.
  destruct (zlt i k). rewrite Z.testbit_neg_r by lia; auto.
  apply Int64.testbit_repr. lia.
Qed.

Ltac solve_ltu :=
  repeat match goal with |- context [Int.ltu (Int.repr ?n) Int64.iwordsize'] =>
    let E := fresh in assert (E: Int.ltu (Int.repr n) Int64.iwordsize' = true) by reflexivity;
    rewrite E; clear E end.

Lemma merge8_den:
  forall bv o,
  merge8 (byteval bv o) (byteval bv (o + 1)) (byteval bv (o + 2)) (byteval bv (o + 3))
         (byteval bv (o + 4)) (byteval bv (o + 5)) (byteval bv (o + 6)) (byteval bv (o + 7))
  = match bytes_den bv (bytes_le64 o) with Some d => Vlong (Int64.repr d) | None => Vundef end.
Proof.
  intros. unfold bytes_le64, merge8, shifted_byte. cbn [bytes_den fst snd].
  destruct (byteval_shape bv o) as [E0 | (n0 & E0 & R0)]; rewrite E0; [reflexivity|].
  destruct (byteval_shape bv (o + 1)) as [E1 | (n1 & E1 & R1)]; rewrite E1; [solve_ltu; reflexivity|].
  destruct (byteval_shape bv (o + 2)) as [E2 | (n2 & E2 & R2)]; rewrite E2; [solve_ltu; reflexivity|].
  destruct (byteval_shape bv (o + 3)) as [E3 | (n3 & E3 & R3)]; rewrite E3; [solve_ltu; reflexivity|].
  destruct (byteval_shape bv (o + 4)) as [E4 | (n4 & E4 & R4)]; rewrite E4; [solve_ltu; reflexivity|].
  destruct (byteval_shape bv (o + 5)) as [E5 | (n5 & E5 & R5)]; rewrite E5; [solve_ltu; reflexivity|].
  destruct (byteval_shape bv (o + 6)) as [E6 | (n6 & E6 & R6)]; rewrite E6; [solve_ltu; reflexivity|].
  destruct (byteval_shape bv (o + 7)) as [E7 | (n7 & E7 & R7)]; rewrite E7; [solve_ltu; reflexivity|].
  cbn [Val.longofintu Val.shll]. solve_ltu. cbn [Val.orl]. f_equal. apply Int64.same_bits_eq; intros i I.
  rewrite !Int64.bits_or by auto. rewrite !Int64.testbit_repr by auto. rewrite !Z.lor_spec.
  rewrite !shl'_testbit by lia.
  rewrite Z.shiftl_0_r, Z.testbit_0_l, orb_false_r. auto.
Qed.

Lemma combine_merge_load_sound_64:
  forall op args addr args' v,
  Is_true Archi.ptr64 ->
  combine_merge_load get op args = Some (addr, args') ->
  eval_operation ge sp op (map valu args) m = Some v ->
  exists a v', eval_addressing ge sp addr (map valu args') = Some a
            /\ Mem.loadv Mint64u m a = Some v' /\ Val.lessdef v v'.
Proof.
  unfold combine_merge_load; intros until v; intros P64; rewrite (Is_true_eq_true _ P64); intros CM EV.
  destruct op; try discriminate.
  destruct (bytecomp_op (bytecomp_of get 12) Oorl args) as [c|] eqn:BC; try discriminate.
  destruct (find (fun p => zeq (snd p) 0) (bcbytes c)) as [[o z]|] eqn:F; try discriminate.
  destruct (bc64 c && bytes_incl (bcbytes c) (bytes_le64 o) && bytes_incl (bytes_le64 o) (bcbytes c)) eqn:CHK;
  inv CM. InvBooleans.
  exploit bytecomp_op_sound. apply bytecomp_of_sound; auto. eexact BC. eexact EV.
  intros [[LD FIT] EQ]. subst v.
  set (bv := valu (bcbase c)) in *.
  apply find_some in F. destruct F as [INo _].
  destruct (LD _ INo) as [w0 L0]; simpl in L0.
  destruct (Val.addl bv (Vlong (Int64.repr o))) eqn:A; try discriminate.
  assert (LK: forall k, 0 <= k < 8 ->
          Mem.loadv Mint8unsigned m (Vptr b (Ptrofs.add i (Ptrofs.repr k))) = Some (byteval bv (o + k))).
  { intros k K.
    assert (IN: In (o + k, 8 * k) (bcbytes c)).
    { apply (bytes_incl_sound _ _ H0). apply in_le64; auto. }
    destruct (LD _ IN) as [w W]. simpl in W.
    rewrite (byteval_loaded _ _ _ W).
    exploit (ptr_shift64 bv (Int64.repr o) (Int64.repr (o + k)) b i o (o + k) (Is_true_eq_true _ P64) A).
    apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
    apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
    replace (o + k - o) with k by lia. intros E. rewrite E in W. auto. }
  exploit (loadv_int64u_merge (eq_refl _) m b i (fun k => byteval bv (o + k))); auto.
  intros LM. cbv beta in LM. rewrite Z.add_0_r in LM.
  exists (Vptr b i); econstructor; split; [|split].
- unfold eval_addressing; rewrite (Is_true_eq_true _ P64). simpl. unfold bv in A. rewrite A. auto.
- eexact LM.
- rewrite merge8_den.
  rewrite (bytecomp_val_incl c (mkbytecomp true (bcbase c) (bytes_le64 o))); simpl; auto.
  unfold bytecomp_val; simpl. fold bv. destruct (bytes_den bv (bytes_le64 o)); auto.
  apply bytes_incl_sound; auto.
  apply bytes_incl_sound; auto.
  apply bytes_incl_sound; auto.
Qed.

End MERGE_BYTES.

Lemma combine_merge_load_sound:
  forall op args addr args' v,
  combine_merge_load get op args = Some (addr, args') ->
  eval_operation ge sp op (map valu args) m = Some v ->
  exists a v', eval_addressing ge sp addr (map valu args') = Some a
            /\ Mem.loadv Mint64u m a = Some v' /\ Val.lessdef v v'.
Proof.
  intros. destruct Archi.ptr64 eqn:P.
  eapply combine_merge_load_sound_64; eauto. rewrite P; exact I.
  unfold combine_merge_load in H; rewrite P in H; discriminate.
Qed.

End COMBINE.
