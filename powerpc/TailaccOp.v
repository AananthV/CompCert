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
  ([Tailacc]).  Accumulator tail-recursion elimination is not supported
  on this target: nothing is recognized and nothing is constructed. *)

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

Definition classify_accop (op: operation) : option (accop * option val) := None.

Definition accop_binary (k: accop) : option operation := None.

Definition accop_const (k: accop) : option operation := None.

Section SOUNDNESS.

Variables F V: Type.
Variable ge: Genv.t F V.

Lemma classify_accop_binary:
  forall op k sp a b m,
  classify_accop op = Some (k, None) ->
  eval_operation ge sp op (a :: b :: nil) m = Some (accop_eval k a b).
Proof.
  intros. discriminate.
Qed.

Lemma classify_accop_imm:
  forall op k c sp a m,
  classify_accop op = Some (k, Some c) ->
  eval_operation ge sp op (a :: nil) m = Some (accop_eval k a c).
Proof.
  intros. discriminate.
Qed.

Lemma classify_accop_imm_inject:
  forall op k c f,
  classify_accop op = Some (k, Some c) ->
  Val.inject f c c.
Proof.
  intros. discriminate.
Qed.

Lemma accop_binary_sound:
  forall k op sp a b m,
  accop_binary k = Some op ->
  eval_operation ge sp op (a :: b :: nil) m = Some (accop_eval k a b).
Proof.
  intros. discriminate.
Qed.

Lemma accop_const_sound:
  forall k op sp m,
  accop_const k = Some op ->
  eval_operation ge sp op nil m = Some (accop_unit k).
Proof.
  intros. discriminate.
Qed.

End SOUNDNESS.
