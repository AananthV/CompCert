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

Require Import Coqlib AST Op.

Definition loadop_candidate (op: operation) (chunk: memory_chunk) : bool :=
  match op, chunk with
  | (Oaddf | Osubf | Omulf | Odivf), Mfloat64 => true
  | (Oand | Oor | Oxor), Mint32 => true
  | Olea (Aindexed2 n), Mint32 => zeq n 0
  | _, _ => false
  end.
