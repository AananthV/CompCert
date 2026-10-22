(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Operations that can take their second argument from memory
  ([Lloadop] instructions, produced by the [Loadop] pass).
  This is not supported on this target. *)

Require Import Coqlib AST Op.

Definition loadop_candidate (op: operation) (chunk: memory_chunk) : bool := false.
