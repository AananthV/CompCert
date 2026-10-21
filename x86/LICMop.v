(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Operators that can be executed speculatively, for use by
    loop-invariant code motion ([LICM]).  An operator is safe for a
    given number of arguments if its evaluation never fails when
    given that many arguments, whatever their values. *)

Require Import Coqlib AST Integers Values Memory Globalenvs Op.

Definition addressing32_safe (a: addressing) (n: nat) : bool :=
  match a, n with
  | Aindexed _, 1%nat => true
  | Aindexed2 _, 2%nat => true
  | Ascaled _ _, 1%nat => true
  | Aindexed2scaled _ _, 2%nat => true
  | Aglobal _ _, O => negb Archi.ptr64
  | Abased _ _, 1%nat => negb Archi.ptr64
  | Abasedscaled _ _ _, 1%nat => negb Archi.ptr64
  | Ainstack _, O => negb Archi.ptr64
  | _, _ => false
  end.

Definition addressing64_safe (a: addressing) (n: nat) : bool :=
  match a, n with
  | Aindexed _, 1%nat => true
  | Aindexed2 _, 2%nat => true
  | Ascaled _ _, 1%nat => true
  | Aindexed2scaled _ _, 2%nat => true
  | Aglobal _ _, O => Archi.ptr64
  | Ainstack _, O => Archi.ptr64
  | _, _ => false
  end.

Definition op_safe (op: operation) (n: nat) : bool :=
  match op, n with
  | Omove, 1%nat => true
  | (Ointconst _ | Olongconst _ | Ofloatconst _ | Osingleconst _
     | Oindirectsymbol _), O => true
  | (Ocast8signed | Ocast8unsigned | Ocast16signed | Ocast16unsigned
     | Oneg | Omulimm _ | Oandimm _ | Oorimm _ | Oxorimm _ | Onot
     | Oshlimm _ | Oshrimm _ | Oshruimm _ | Ororimm _
     | Olowlong | Ohighlong | Ocast32signed | Ocast32unsigned
     | Onegl | Oaddlimm _ | Omullimm _ | Oandlimm _ | Oorlimm _
     | Oxorlimm _ | Onotl | Oshllimm _ | Oshrlimm _ | Oshrluimm _
     | Ororlimm _
     | Onegf | Oabsf | Onegfs | Oabsfs
     | Osingleoffloat | Ofloatofsingle), 1%nat => true
  | (Osub | Omul | Omulhs | Omulhu | Oand | Oor | Oxor
     | Oshl | Oshr | Oshru | Oshldimm _ | Omakelong
     | Osubl | Omull | Omullhs | Omullhu | Oandl | Oorl | Oxorl
     | Oshll | Oshrl | Oshrlu
     | Oaddf | Osubf | Omulf | Odivf | Omaxf | Ominf
     | Oaddfs | Osubfs | Omulfs | Odivfs), 2%nat => true
  | Olea a, _ => addressing32_safe a n
  | Oleal a, _ => addressing64_safe a n
  | Ocmp _, _ => true
  | Osel _ _, S (S _) => true
  | _, _ => false
  end.

Lemma op_safe_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op vl m,
  op_safe op (length vl) = true ->
  eval_operation ge sp op vl m <> None.
Proof.
  intros until m.
  destruct op; try (destruct a);
  destruct vl as [ | v1 [ | v2 [ | v3 vl]]]; simpl;
  unfold eval_addressing32, eval_addressing64;
  try destruct Archi.ptr64; simpl; congruence.
Qed.

Lemma eval_operation_Omove:
  forall (F V: Type) (ge: Genv.t F V) sp v m,
  eval_operation ge sp Omove (v :: nil) m = Some v.
Proof.
  intros. reflexivity.
Qed.
