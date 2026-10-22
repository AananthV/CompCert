(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition and construction of the associative and commutative
  integer operations used by accumulator tail-recursion elimination
  ([Tailacc]). *)

Require Import Coqlib AST Integers Values Memory Globalenvs Op.

(** The accumulating operations, and their meaning as operations
  over values. *)

Inductive accop : Type :=
  | AOadd | AOmul | AOand | AOor | AOxor
  | AOaddl | AOmull | AOandl | AOorl | AOxorl.

Definition accop_eq (x y: accop) : {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition accop_eval (k: accop) (v1 v2: val) : val :=
  match k with
  | AOadd => Val.add v1 v2
  | AOmul => Val.mul v1 v2
  | AOand => Val.and v1 v2
  | AOor => Val.or v1 v2
  | AOxor => Val.xor v1 v2
  | AOaddl => Val.addl v1 v2
  | AOmull => Val.mull v1 v2
  | AOandl => Val.andl v1 v2
  | AOorl => Val.orl v1 v2
  | AOxorl => Val.xorl v1 v2
  end.

(** The neutral element of each operation. *)

Definition accop_unit (k: accop) : val :=
  match k with
  | AOadd | AOor | AOxor => Vint Int.zero
  | AOmul => Vint Int.one
  | AOand => Vint Int.mone
  | AOaddl | AOorl | AOxorl => Vlong Int64.zero
  | AOmull => Vlong Int64.one
  | AOandl => Vlong Int64.mone
  end.

(** [classify_accop op] is [Some (k, None)] if [op] applied to two
  arguments [a; b] computes [accop_eval k a b], and [Some (k, Some c)]
  if [op] applied to one argument [a] computes [accop_eval k a c]. *)

Definition classify_accop (op: operation) : option (accop * option val) :=
  match op with
  | Olea (Aindexed2 n) => if zeq n 0 then Some (AOadd, None) else None
  | Olea (Aindexed n) => Some (AOadd, Some (Vint (Int.repr n)))
  | Omul => Some (AOmul, None)
  | Omulimm n => Some (AOmul, Some (Vint n))
  | Oand => Some (AOand, None)
  | Oandimm n => Some (AOand, Some (Vint n))
  | Oor => Some (AOor, None)
  | Oorimm n => Some (AOor, Some (Vint n))
  | Oxor => Some (AOxor, None)
  | Oxorimm n => Some (AOxor, Some (Vint n))
  | Oleal (Aindexed2 n) => if zeq n 0 then Some (AOaddl, None) else None
  | Oleal (Aindexed n) => Some (AOaddl, Some (Vlong (Int64.repr n)))
  | Oaddlimm n => Some (AOaddl, Some (Vlong n))
  | Omull => Some (AOmull, None)
  | Omullimm n => Some (AOmull, Some (Vlong n))
  | Oandl => Some (AOandl, None)
  | Oandlimm n => Some (AOandl, Some (Vlong n))
  | Oorl => Some (AOorl, None)
  | Oorlimm n => Some (AOorl, Some (Vlong n))
  | Oxorl => Some (AOxorl, None)
  | Oxorlimm n => Some (AOxorl, Some (Vlong n))
  | _ => None
  end.

(** An operation computing [accop_eval k] on two arguments. *)

Definition accop_binary (k: accop) : option operation :=
  match k with
  | AOadd => Some (Olea (Aindexed2 0))
  | AOmul => Some Omul
  | AOand => Some Oand
  | AOor => Some Oor
  | AOxor => Some Oxor
  | AOaddl => Some (Oleal (Aindexed2 0))
  | AOmull => Some Omull
  | AOandl => Some Oandl
  | AOorl => Some Oorl
  | AOxorl => Some Oxorl
  end.

(** An operation without arguments producing the neutral element. *)

Definition accop_const (k: accop) : option operation :=
  match accop_unit k with
  | Vint n => Some (Ointconst n)
  | Vlong n => Some (Olongconst n)
  | _ => None
  end.

Section SOUNDNESS.

Variables F V: Type.
Variable ge: Genv.t F V.

Remark add_zero_r:
  forall v1 v2, Val.add (Val.add v1 v2) (Vint (Int.repr 0)) = Val.add v1 v2.
Proof.
  intros. change (Int.repr 0) with Int.zero.
  assert (P: Ptrofs.of_int Int.zero = Ptrofs.zero) by reflexivity.
  destruct v1, v2; simpl; auto; try (rewrite Int.add_zero; auto);
  destruct Archi.ptr64; simpl; auto; rewrite P, Ptrofs.add_zero; auto.
Qed.

Remark addl_zero_r:
  forall v1 v2, Val.addl (Val.addl v1 v2) (Vlong (Int64.repr 0)) = Val.addl v1 v2.
Proof.
  intros. change (Int64.repr 0) with Int64.zero.
  assert (P: Ptrofs.of_int64 Int64.zero = Ptrofs.zero) by reflexivity.
  destruct v1, v2; simpl; auto; try (rewrite Int64.add_zero; auto);
  destruct Archi.ptr64; simpl; auto; rewrite P, Ptrofs.add_zero; auto.
Qed.

Lemma classify_accop_binary:
  forall op k sp a b m,
  classify_accop op = Some (k, None) ->
  eval_operation ge sp op (a :: b :: nil) m = Some (accop_eval k a b).
Proof.
  intros. destruct op; simpl in H; try discriminate;
  try (destruct a0; try discriminate; destruct (zeq z 0); inv H; simpl;
       f_equal; auto using add_zero_r, addl_zero_r; fail);
  inv H; reflexivity.
Qed.

Lemma classify_accop_imm:
  forall op k c sp a m,
  classify_accop op = Some (k, Some c) ->
  eval_operation ge sp op (a :: nil) m = Some (accop_eval k a c).
Proof.
  intros. destruct op; simpl in H; try discriminate;
  try (destruct a0; try discriminate; try (destruct (zeq z 0); discriminate); inv H; reflexivity);
  inv H; reflexivity.
Qed.

Lemma classify_accop_imm_inject:
  forall op k c f,
  classify_accop op = Some (k, Some c) ->
  Val.inject f c c.
Proof.
  intros. destruct op; simpl in H; try discriminate;
  try (destruct a; try discriminate; try (destruct (zeq z 0); discriminate); inv H; constructor);
  inv H; constructor.
Qed.

Lemma accop_binary_sound:
  forall k op sp a b m,
  accop_binary k = Some op ->
  eval_operation ge sp op (a :: b :: nil) m = Some (accop_eval k a b).
Proof.
  intros. destruct k; inv H; simpl; f_equal; auto using add_zero_r, addl_zero_r.
Qed.

Lemma accop_const_sound:
  forall k op sp m,
  accop_const k = Some op ->
  eval_operation ge sp op nil m = Some (accop_unit k).
Proof.
  intros. destruct k; inv H; reflexivity.
Qed.

End SOUNDNESS.
