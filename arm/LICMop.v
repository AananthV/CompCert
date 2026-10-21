(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Operators that can be executed speculatively, for use by
    loop-invariant code motion ([LICM]).  An operator is safe for a
    given number of arguments if its evaluation never fails when
    given that many arguments, whatever their values.
    Not implemented yet for this target: no operator is hoisted. *)

Require Import Coqlib AST Integers Values Memory Globalenvs Op.

Definition op_safe (op: operation) (n: nat) : bool := false.

Lemma op_safe_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op vl m,
  op_safe op (length vl) = true ->
  eval_operation ge sp op vl m <> None.
Proof.
  unfold op_safe; intros; discriminate.
Qed.

Lemma eval_operation_Omove:
  forall (F V: Type) (ge: Genv.t F V) sp v m,
  eval_operation ge sp Omove (v :: nil) m = Some v.
Proof.
  intros. reflexivity.
Qed.
