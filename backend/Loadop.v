(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Fusion of loads into arithmetic operations (memory operands).

  A load into a temporary register, immediately followed by a two-address
  operation that uses this temporary as its second argument,
<<
      t = chunk[addr(args)]
      rd = op(rd, t)
>>
  is turned into a single [Lloadop op chunk addr args rd] instruction,
  provided that [t] is dead after the operation.  On x86 this becomes an
  arithmetic instruction with a memory operand, e.g. [addsd mem, %xmm0].
  This is enabled by [-fload-op].

  Likewise, with [-fzext-load], a load followed by a unary operation
  that can take its argument from memory ([LoadopOp.loadop_unary]),
<<
      t = chunk[addr(args)]
      rd = op(t)
>>
  is turned into [Lloadop op' chunk addr args rd], provided that [t] is
  [rd] or is dead after the operation.  On x86 this is used for loads
  zero-extended to 64 bits, e.g. [movzbl mem, %eax] with a 64-bit result.

  Deadness is decided by a backward liveness analysis over the Linear
  code.  The live sets at labels are computed by a bounded fixpoint
  iteration; they are then validated during the transformation itself,
  so the iteration needs no proof.  If the validation fails, the
  conservative assumption "every register is live at every label" is
  used instead, which is always valid. *)

Require Import Coqlib Maps Compopts.
Require Import AST Integers Values Memory Globalenvs.
Require Import Op Locations Conventions Linear.
Require Import Bounds LoadopOp.

(** * Liveness of machine registers *)

Definition all_live : RegSet.t :=
  List.fold_right RegSet.add RegSet.empty all_mregs.

Definition add_regs (rl: list mreg) (s: RegSet.t) : RegSet.t :=
  List.fold_right RegSet.add s rl.

(** Registers live at each label.  A label that is not in the map is
  assumed to have all registers live. *)

Definition labelmap := PTree.t RegSet.t.

Definition live_at (lm: labelmap) (lbl: label) : RegSet.t :=
  match lm!lbl with Some s => s | None => all_live end.

Definition live_at_labels (lm: labelmap) (tbl: list label) : RegSet.t :=
  List.fold_right (fun lbl s => RegSet.union (live_at lm lbl) s) RegSet.empty tbl.

(** Registers that a call, a tail call or a return can observe.
  A callee only sees the registers holding its parameters and the
  callee-save registers (the others are undefined at function entry);
  a caller only sees the registers holding the result and its own
  callee-save registers (see [call_regs] and [return_regs_res]). *)

Definition callee_save_live : RegSet.t :=
  List.fold_right (fun r s => if is_callee_save r then RegSet.add r s else s) RegSet.empty all_mregs.

Definition param_live (sg: signature) : RegSet.t :=
  List.fold_right (fun l s => match l with R r => RegSet.add r s | S _ _ _ => s end)
                  RegSet.empty (regs_of_rpairs (loc_arguments sg)).

Definition result_live (sg: signature) : RegSet.t :=
  add_regs (regs_of_rpair (loc_result sg)) RegSet.empty.

Definition ros_live (ros: mreg + ident) : RegSet.t :=
  match ros with inl r => RegSet.add r RegSet.empty | inr _ => RegSet.empty end.

Section TRANSFER.

Variable fsig: signature.   (**r the signature of the function being transformed *)

(** [transfer lm i s] is the set of registers live before [i],
  given the set [s] of registers live after [i].  Stack slots are
  not tracked: they are always considered live. *)

Definition transfer (lm: labelmap) (i: instruction) (s: RegSet.t) : RegSet.t :=
  match i with
  | Lgetstack sl ofs ty dst => RegSet.remove dst s
  | Lsetstack src sl ofs ty => RegSet.add src s
  | Lop op args res => add_regs args (RegSet.remove res s)
  | Lload chunk addr args dst => add_regs args (RegSet.remove dst s)
  | Lloadop op chunk addr args res => add_regs args (RegSet.add res s)
  | Lstore chunk addr args src => add_regs args (RegSet.add src s)
  | Llabel lbl => s
  | Lgoto lbl => live_at lm lbl
  | Lcond cond args lbl => add_regs args (RegSet.union (live_at lm lbl) s)
  | Ljumptable arg tbl => RegSet.add arg (live_at_labels lm tbl)
  | Lcall sg ros => RegSet.union callee_save_live (RegSet.union (param_live sg) (ros_live ros))
  | Ltailcall sg ros => RegSet.union (param_live sg) (ros_live ros)
  | Lreturn => result_live fsig
  | Lbuiltin _ _ _ => all_live
  end.

Fixpoint live (lm: labelmap) (c: code) : RegSet.t :=
  match c with
  | nil => RegSet.empty
  | i :: c' => transfer lm i (live lm c')
  end.

(** Validation of the live sets at labels. *)

Definition check_label (lm: labelmap) (i: instruction) (after: RegSet.t) : bool :=
  match i with
  | Llabel lbl => RegSet.subset after (live_at lm lbl)
  | _ => true
  end.

(** * The transformation *)

Definition fusable (chunk: memory_chunk) (addr: addressing) (t: mreg)
                   (op: operation) (args2: list mreg) (res: mreg)
                   (after: RegSet.t) : bool :=
  match args2 with
  | rd :: t' :: nil =>
      Compopts.optim_loadop tt
      && mreg_eq rd res && mreg_eq t' t && negb (mreg_eq t res)
      && loadop_candidate op chunk
      && negb (In_dec mreg_eq res (destroyed_by_load chunk addr))
      && negb (RegSet.mem t after)
  | t' :: nil =>
      match loadop_unary op chunk with
      | Some _ => mreg_eq t' t && (mreg_eq t res || negb (RegSet.mem t after))
      | None => false
      end
  | _ => false
  end.

(** The operation of the fused instruction. *)

Definition fused_op (op: operation) (chunk: memory_chunk) (args2: list mreg) : operation :=
  match args2, loadop_unary op chunk with
  | _ :: nil, Some op' => op'
  | _, _ => op
  end.

(** [tr lm c] returns the transformed code, the registers live at the
  beginning of [c], the registers live after the first instruction of [c],
  and the result of the label validation. *)

Fixpoint tr (lm: labelmap) (c: code) {struct c} : code * RegSet.t * RegSet.t * bool :=
  match c with
  | nil => (nil, RegSet.empty, RegSet.empty, true)
  | i :: c1 =>
      let '(tc1, s1, s1', ok1) := tr lm c1 in
      let dflt := (i :: tc1, transfer lm i s1, s1, ok1 && check_label lm i s1) in
      match i, c1, tc1 with
      | Lload chunk addr args t, Lop op args2 res :: _, Lop _ _ _ :: tc2 =>
          if fusable chunk addr t op args2 res s1'
          then (Lloadop (fused_op op chunk args2) chunk addr args res :: tc2, transfer lm i s1, s1, ok1)
          else dflt
      | _, _, _ => dflt
      end
  end.

Definition tr_code (lm: labelmap) (c: code) : code := fst (fst (fst (tr lm c))).
Definition tr_ok (lm: labelmap) (c: code) : bool := snd (tr lm c).

(** * Computing the live sets at labels *)

(** One round of the fixpoint iteration: the live set at the
  beginning of the code that follows each label, computed with the
  current approximation [lm], is joined into [lm]. *)

Fixpoint label_round (lm: labelmap) (c: code) (acc: labelmap) : RegSet.t * labelmap :=
  match c with
  | nil => (RegSet.empty, acc)
  | i :: c' =>
      let '(s, acc') := label_round lm c' acc in
      let acc'' :=
        match i with
        | Llabel lbl =>
            PTree.set lbl (RegSet.union s (match acc'!lbl with Some s' => s' | None => RegSet.empty end)) acc'
        | _ => acc'
        end in
      (transfer lm i s, acc'')
  end.

Definition labelmap_eq (lm1 lm2: labelmap) : bool :=
  PTree.beq RegSet.equal lm1 lm2.

Fixpoint iterate (fuel: nat) (c: code) (lm: labelmap) : labelmap :=
  match fuel with
  | O => lm
  | Datatypes.S fuel' =>
      let lm' := snd (label_round lm c lm) in
      if labelmap_eq lm lm' then lm else iterate fuel' c lm'
  end.

(** The initial approximation maps every label to the empty set. *)

Fixpoint initial_labelmap (c: code) : labelmap :=
  match c with
  | nil => PTree.empty _
  | Llabel lbl :: c' => PTree.set lbl RegSet.empty (initial_labelmap c')
  | _ :: c' => initial_labelmap c'
  end.

Definition num_iterations := 10%nat.

Definition choose_labelmap (c: code) : labelmap :=
  let lm := iterate num_iterations c (initial_labelmap c) in
  if tr_ok lm c then lm else PTree.empty _.

End TRANSFER.

Definition transf_function (f: function) : function :=
  let lm := choose_labelmap f.(fn_sig) f.(fn_code) in
  mkfunction f.(fn_sig) f.(fn_stacksize) (tr_code f.(fn_sig) lm f.(fn_code)).

Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

(** The pass is run if one of its two flags is set. *)

Definition enabled (u: unit) : bool := Compopts.optim_loadop u || Compopts.optim_zextload u.
