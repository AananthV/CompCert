(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Operations that can take their second argument from memory
  ([Lloadop] instructions, produced by the [Loadop] pass).  This must
  agree with the cases handled by [Asmgen.transl_loadop]. *)

Require Import Coqlib AST Values Memory Globalenvs Op Machregs.

Definition loadop_candidate (op: operation) (chunk: memory_chunk) : bool :=
  match op, chunk with
  | (Oaddf | Osubf | Omulf | Odivf), Mfloat64 => true
  | (Oand | Oor | Oxor), Mint32 => true
  | Olea (Aindexed2 n), Mint32 => zeq n 0
  | _, _ => false
  end.

(** Unary operations whose argument can be taken from memory: if
  [loadop_unary op chunk = Some op'], then [Lloadop op' chunk addr args res]
  computes [op] applied to the loaded value (the first argument of [op'],
  the old value of [res], is ignored). *)

Definition loadop_unary (op: operation) (chunk: memory_chunk) : option operation :=
  match op, chunk with
  | Ozextb64, Mint8unsigned => Some Ozextb64_ld
  | Ozextw64, Mint16unsigned => Some Ozextw64_ld
  | _, _ => None
  end.

Lemma loadop_unary_correct:
  forall op chunk op', loadop_unary op chunk = Some op' ->
  (forall (F V: Type) (ge: Genv.t F V) sp v1 v m,
     eval_operation ge sp op' (v1 :: v :: nil) m = eval_operation ge sp op (v :: nil) m)
  /\ destroyed_by_op op' = destroyed_by_op op.
Proof.
  unfold loadop_unary; intros.
  destruct op; try discriminate; destruct chunk; inv H; auto.
Qed.
