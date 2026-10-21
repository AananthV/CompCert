(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Loop rotation (loop header copying) over the RTL intermediate language. *)

(** Loop rotation turns a loop [while (c) { body }] into
  [if (c) { do { body } while (c) }]: the instructions of the loop header,
  up to and including the exit test, are duplicated and the back edges
  of the loop are redirected to the copy.

  The transformation is computed by an untrusted oracle and validated a
  posteriori.  The oracle returns the entry point of the transformed
  function and, for each node [n'] of the transformed function, the node
  [n] of the original function of which [n'] is a copy, along with the
  successors of [n'].  The instruction at [n'] is the instruction at [n]
  with its successors replaced.  The validator checks that the successors
  of [n'] are copies of the corresponding successors of [n], and that the
  entry point of the transformed function is a copy of the original entry
  point.  This ensures that the transformed function executes the same
  sequence of instructions as the original function.  This validation
  scheme is not specific to loop rotation: it accepts any duplication of
  nodes (tail duplication). *)

Require Import Coqlib Maps AST Op Registers RTL.

Parameter rotate_oracle: function -> PTree.t (node * list node) * node.

(** Replace the successors of an instruction. *)

Definition set_succs (i: instruction) (l: list node) : option instruction :=
  match i, l with
  | Inop _, s :: nil => Some (Inop s)
  | Iop op args res _, s :: nil => Some (Iop op args res s)
  | Iload chunk addr args dst _, s :: nil => Some (Iload chunk addr args dst s)
  | Istore chunk addr args src _, s :: nil => Some (Istore chunk addr args src s)
  | Icall sig ros args res _, s :: nil => Some (Icall sig ros args res s)
  | Itailcall sig ros args, nil => Some i
  | Ibuiltin ef args res _, s :: nil => Some (Ibuiltin ef args res s)
  | Icond cond args _ _, s1 :: s2 :: nil => Some (Icond cond args s1 s2)
  | Ijumptable arg tbl, _ =>
      if Nat.eqb (length tbl) (length l) then Some (Ijumptable arg l) else None
  | Ireturn optarg, nil => Some i
  | _, _ => None
  end.

Fixpoint forall2b {A B: Type} (p: A -> B -> bool) (l1: list A) (l2: list B) : bool :=
  match l1, l2 with
  | nil, nil => true
  | a1 :: l1, a2 :: l2 => p a1 a2 && forall2b p l1 l2
  | _, _ => false
  end.

Section CHECK.

Variable f: function.
Variable info: PTree.t (node * list node).

(** [corresp s' s] holds if [s'] is a copy of [s]. *)

Definition corresp (s' s: node) : bool :=
  match info!s' with Some (n, _) => peq n s | None => false end.

Definition transf_node (nl: node * list node) : option instruction :=
  match f.(fn_code)!(fst nl) with
  | Some i => set_succs i (snd nl)
  | None => None
  end.

Definition check_node (n': node) (nl: node * list node) : bool :=
  match f.(fn_code)!(fst nl) with
  | Some i =>
      match set_succs i (snd nl) with
      | Some _ => forall2b corresp (snd nl) (successors_instr i)
      | None => false
      end
  | None => false
  end.

Definition check_function (entry: node) : bool :=
  PTree_Properties.for_all info check_node && corresp entry f.(fn_entrypoint).

End CHECK.

Definition transf_function (f: function) : function :=
  let (info, entry) := rotate_oracle f in
  if check_function f info entry then
    mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
               (PTree.map_filter1 (transf_node f) info) entry
  else f.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
