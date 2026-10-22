(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Accumulator tail-recursion elimination: semantic preservation.

  The simulation relates the frames of the pending recursive calls of the
  original program to the single frame of the loop of the transformed
  program.  Memory is related by an injection that maps the (empty) stack
  blocks of all these frames to the stack block of the loop.  The value of
  the accumulator is [afold] of the right operands of the pending calls;
  when the innermost call returns [v], the original program computes
  [chain] of [v] through the pending frames, one step at a time, while the
  transformed program has already returned [accop_eval acc v]: these are
  equal by associativity and commutativity (lemma [chain_afold]).  These
  stuttering steps are bounded by a measure on the original states. *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL TailaccOp Tailacc.

(** * Algebraic properties of the accumulating operations *)

Lemma accop_assoc:
  forall k a b c, accop_eval k (accop_eval k a b) c = accop_eval k a (accop_eval k b c).
Proof.
  destruct k; simpl; intros.
  apply Val.add_assoc. apply Val.mul_assoc. apply Val.and_assoc.
  apply Val.or_assoc. apply Val.xor_assoc. apply Val.addl_assoc.
  apply Val.mull_assoc. apply Val.andl_assoc. apply Val.orl_assoc.
  apply Val.xorl_assoc.
Qed.

Lemma accop_comm:
  forall k a b, accop_eval k a b = accop_eval k b a.
Proof.
  destruct k; simpl; intros.
  apply Val.add_commut. apply Val.mul_commut. apply Val.and_commut.
  apply Val.or_commut. apply Val.xor_commut. apply Val.addl_commut.
  apply Val.mull_commut. apply Val.andl_commut. apply Val.orl_commut.
  apply Val.xorl_commut.
Qed.

Lemma accop_inject:
  forall f k a a' b b',
  Val.inject f a a' -> Val.inject f b b' ->
  Val.inject f (accop_eval k a b) (accop_eval k a' b').
Proof.
  intros. destruct k; simpl; auto using Val.add_inject, Val.addl_inject;
  inv H; inv H0; simpl; auto.
Qed.

Lemma accop_undef:
  forall k v, accop_eval k Vundef v = Vundef.
Proof.
  destruct k; reflexivity.
Qed.

Lemma accop_unit_inject:
  forall f k, Val.inject f (accop_unit k) (accop_unit k).
Proof.
  destruct k; constructor.
Qed.

(** A value is normal for [k] if combining it with the neutral element
  leaves it unchanged. *)

Definition normal (k: accop) (v: val) : Prop :=
  accop_eval k (accop_unit k) v = v.

Lemma normal_undef:
  forall k, normal k Vundef.
Proof.
  destruct k; reflexivity.
Qed.

Remark ptrofs_of_int_zero: Ptrofs.of_int Int.zero = Ptrofs.zero.
Proof. reflexivity. Qed.

Remark ptrofs_of_int64_zero: Ptrofs.of_int64 Int64.zero = Ptrofs.zero.
Proof. reflexivity. Qed.

Lemma normal_int:
  forall k n, k = AOadd \/ k = AOmul \/ k = AOand \/ k = AOor \/ k = AOxor ->
  normal k (Vint n).
Proof.
  unfold normal; intros. destruct H as [E|[E|[E|[E|E]]]]; subst k; simpl; f_equal.
  apply Int.add_zero_l.
  rewrite Int.mul_commut; apply Int.mul_one.
  rewrite Int.and_commut; apply Int.and_mone.
  rewrite Int.or_commut; apply Int.or_zero.
  rewrite Int.xor_commut; apply Int.xor_zero.
Qed.

Lemma normal_long:
  forall k n, k = AOaddl \/ k = AOmull \/ k = AOandl \/ k = AOorl \/ k = AOxorl ->
  normal k (Vlong n).
Proof.
  unfold normal; intros. destruct H as [E|[E|[E|[E|E]]]]; subst k; simpl; f_equal.
  apply Int64.add_zero_l.
  rewrite Int64.mul_commut; apply Int64.mul_one.
  rewrite Int64.and_commut; apply Int64.and_mone.
  rewrite Int64.or_commut; apply Int64.or_zero.
  rewrite Int64.xor_commut; apply Int64.xor_zero.
Qed.

Lemma normal_add_ptr:
  forall b ofs, Archi.ptr64 = false -> normal AOadd (Vptr b ofs).
Proof.
  unfold normal; intros; simpl. rewrite H. rewrite ptrofs_of_int_zero, Ptrofs.add_zero. auto.
Qed.

Lemma normal_addl_ptr:
  forall b ofs, Archi.ptr64 = true -> normal AOaddl (Vptr b ofs).
Proof.
  unfold normal; intros; simpl. rewrite H. rewrite ptrofs_of_int64_zero, Ptrofs.add_zero. auto.
Qed.

Lemma accop_result_normal:
  forall k a b, normal k (accop_eval k a b).
Proof.
  intros.
  assert (I: forall k n, k = AOadd \/ k = AOmul \/ k = AOand \/ k = AOor \/ k = AOxor ->
             normal k (Vint n)) by (apply normal_int).
  assert (L: forall k n, k = AOaddl \/ k = AOmull \/ k = AOandl \/ k = AOorl \/ k = AOxorl ->
             normal k (Vlong n)) by (apply normal_long).
  destruct k; destruct a, b; simpl;
  try (apply normal_undef);
  try (apply I; tauto); try (apply L; tauto);
  destruct Archi.ptr64 eqn:SF; try (apply normal_undef);
  try (apply normal_add_ptr; auto); try (apply normal_addl_ptr; auto).
Qed.

Lemma normal_of_type:
  forall k ty v,
  accop_type_ok k ty = true -> Val.has_type v ty -> normal k v.
Proof.
  intros.
  assert (I: forall k n, k = AOadd \/ k = AOmul \/ k = AOand \/ k = AOor \/ k = AOxor ->
             normal k (Vint n)) by (apply normal_int).
  assert (L: forall k n, k = AOaddl \/ k = AOmull \/ k = AOandl \/ k = AOorl \/ k = AOxorl ->
             normal k (Vlong n)) by (apply normal_long).
  destruct v; try (apply normal_undef);
  destruct k; simpl in H; InvBooleans; subst ty; simpl in H0; try contradiction;
  try (apply I; tauto); try (apply L; tauto);
  try congruence;
  try (apply normal_add_ptr; auto); try (apply normal_addl_ptr; auto);
  try (match goal with [ A: Archi.ptr64 = _, B: negb Archi.ptr64 = true |- _ ] =>
         rewrite A in B; discriminate end).
Qed.

(** * Combination of the accumulator with the pending operands *)

(** [chain k ys v] is the value returned by the original program when the
  innermost recursive call returns [v], and the pending recursive calls
  have right operands [ys] (innermost first). *)

Fixpoint chain (k: accop) (ys: list val) (v: val) : val :=
  match ys with
  | nil => v
  | y :: ys' => chain k ys' (accop_eval k v y)
  end.

(** [afold k ys] is the value of the accumulator of the transformed
  program. *)

Fixpoint afold (k: accop) (ys: list val) : val :=
  match ys with
  | nil => accop_unit k
  | y :: ys' => accop_eval k (afold k ys') y
  end.

Lemma chain_undef:
  forall k ys, chain k ys Vundef = Vundef.
Proof.
  induction ys; simpl; auto. rewrite accop_undef; auto.
Qed.

Lemma chain_afold:
  forall f k ys Ys,
  Val.inject_list f ys Ys ->
  forall v v',
  Val.inject f v v' ->
  ys <> nil \/ normal k v ->
  Val.inject f (chain k ys v) (accop_eval k (afold k Ys) v').
Proof.
  induction 1 as [|y Y ys Ys HY HYS IH]; simpl; intros v v' INJ N.
- destruct N as [N|N]; [congruence|]. red in N. rewrite <- N.
  apply accop_inject; auto. apply accop_unit_inject.
- rewrite accop_assoc. rewrite (accop_comm k Y v').
  apply IH.
  apply accop_inject; auto.
  right. apply accop_result_normal.
Qed.

(** * Properties of the validator *)

Lemma site_of_inv:
  forall dm f i x,
  site_of dm f i = Some x ->
  exists sg id args res s, i = Icall sg (inr id) args res s.
Proof.
  unfold site_of; intros. destruct i; try discriminate. destruct s0; try discriminate.
  econstructor; econstructor; econstructor; econstructor; econstructor; eauto.
Qed.

Definition accarg_val (rs: regset) (a: accarg) : val :=
  match a with
  | AAreg r => rs#r
  | AAimm v => v
  end.

Lemma accarg_val_inject:
  forall F rs rs' op k a,
  (forall r, Val.inject F rs#r rs'#r) ->
  (forall c, a = AAimm c -> classify_accop op = Some (k, Some c)) ->
  Val.inject F (accarg_val rs a) (accarg_val rs' a).
Proof.
  intros. destruct a; simpl; auto.
  eapply classify_accop_imm_inject; eauto.
Qed.

Section SITE.

Variables FF VV: Type.
Variable gge: Genv.t FF VV.

Lemma site_of_sound:
  forall dm f sg id args res s k op a,
  site_of dm f (Icall sg (inr id) args res s) = Some (k, op, a) ->
  exists oargs d s2,
     f.(fn_code)!s = Some (Iop op oargs d s2)
  /\ f.(fn_code)!s2 = Some (Ireturn (Some d))
  /\ length args = length f.(fn_params)
  /\ dm!id = Some (Gfun (Internal f))
  /\ (forall c, a = AAimm c -> classify_accop op = Some (k, Some c))
  /\ (forall sp m (rs: regset) v,
        eval_operation gge sp op (rs#res <- v)##oargs m = Some (accop_eval k v (accarg_val rs a)))
  /\ (forall sp m (rs: regset) acc,
        eval_operation gge sp op rs##(accarg_regs acc a) m = Some (accop_eval k rs#acc (accarg_val rs a))).
Proof.
  unfold site_of; intros.
  destruct (fn_code f)!s as [i1|] eqn:S; try discriminate.
  destruct i1 as [ | op0 l d n | | | | | | | | ]; try discriminate.
  destruct (fn_code f)!n as [i2|] eqn:S2; try discriminate.
  destruct i2 as [ | | | | | | | | | od]; try discriminate.
  destruct od as [d'|]; try discriminate.
  destruct (peq d d' && Nat.eqb (length args) (length (fn_params f)) && is_self dm f id) eqn:C;
  try discriminate.
  (* On targets that recognize no operation, there are no goals left. *)
  all: rewrite ! andb_true_iff in C; destruct C as [[D1 D2] D3].
  all: destruct (peq d d'); try discriminate; subst d'; apply Nat.eqb_eq in D2.
  all: assert (SELF: dm!id = Some (Gfun (Internal f)))
         by (unfold is_self in D3; destruct dm!id as [[[g|]|]|]; try discriminate;
             apply function_beq_sound in D3; subst g; reflexivity).
  all: destruct (classify_accop op0) as [[k' [c|]]|] eqn:CL; try discriminate.
  all: first [
    (* immediate *)
    solve [
      destruct l as [|r1 [|]]; try discriminate;
      destruct (peq r1 res); inv H;
      exists (res :: nil), d, n;
      split; [auto|]; split; [auto|]; split; [auto|]; split; [auto|];
      split; [intros c0 E; inv E; auto|];
      split; intros; simpl;
      [ rewrite Regmap.gss; eapply classify_accop_imm; eauto
      | eapply classify_accop_imm; eauto ] ]
  | (* binary *)
    solve [
      destruct l as [|r1 [|r2 []]]; try discriminate;
      destruct (peq r1 res && negb (peq r2 res)) eqn:C1;
      [ InvBooleans; inv H;
        assert (NE: r2 <> res) by (destruct (peq r2 res); simpl in *; congruence);
        exists (res :: r2 :: nil), d, n;
        split; [auto|]; split; [auto|]; split; [auto|]; split; [auto|];
        split; [intros; discriminate|];
        split; intros; simpl;
        [ rewrite Regmap.gss; rewrite Regmap.gso by auto; eapply classify_accop_binary; eauto
        | eapply classify_accop_binary; eauto ]
      | destruct (peq r2 res && negb (peq r1 res)) eqn:C2; try discriminate;
        InvBooleans; inv H;
        assert (NE: r1 <> res) by (destruct (peq r1 res); simpl in *; congruence);
        exists (r1 :: res :: nil), d, n;
        split; [auto|]; split; [auto|]; split; [auto|]; split; [auto|];
        split; [intros; discriminate|];
        split; intros; simpl;
        [ rewrite Regmap.gss; rewrite Regmap.gso by auto;
          rewrite accop_comm; eapply classify_accop_binary; eauto
        | eapply classify_accop_binary; eauto ] ] ] ].
Qed.

End SITE.

(** Specification of the validated transformation. *)

Inductive tr_instr (dm: defmap) (f: function) (k: accop) (bop: operation) (tc: code) (pc: node)
                   : instruction -> Prop :=
  | tr_site: forall sg id args res s op a n1,
      site_of dm f (Icall sg (inr id) args res s) = Some (k, op, a) ->
      tc!pc = Some (Iop op (accarg_regs (acc_reg f) a) (acc_reg f) n1) ->
      check_moves tc n1 (call_moves f args) f.(fn_entrypoint) = true ->
      tr_instr dm f k bop tc pc (Icall sg (inr id) args res s)
  | tr_return: forall r n,
      ret_ok k f r = true ->
      tc!pc = Some (Iop bop (acc_reg f :: r :: nil) (acc_reg f) n) ->
      tc!n = Some (Ireturn (Some (acc_reg f))) ->
      tr_instr dm f k bop tc pc (Ireturn (Some r))
  | tr_same: forall i,
      tc!pc = Some i ->
      (forall r, i <> Ireturn (Some r)) ->
      (forall sg ros args, i <> Itailcall sg ros args) ->
      tr_instr dm f k bop tc pc i.

Record tr_function (dm: defmap) (f tf: function) (k: accop) (bop cop: operation) : Prop := {
  tr_bop: accop_binary k = Some bop;
  tr_cop: accop_const k = Some cop;
  tr_sig: tf.(fn_sig) = f.(fn_sig);
  tr_params: tf.(fn_params) = f.(fn_params);
  tr_tstacksize: tf.(fn_stacksize) = 0;
  tr_stacksize: f.(fn_stacksize) = 0;
  tr_entry: tf.(fn_code)!(tf.(fn_entrypoint)) = Some (Iop cop nil (acc_reg f) f.(fn_entrypoint));
  tr_code: forall pc i, f.(fn_code)!pc = Some i -> tr_instr dm f k bop tf.(fn_code) pc i
}.

Lemma check_instr_correct:
  forall dm f k bop tc pc i,
  check_instr dm f k bop tc pc i = true -> tr_instr dm f k bop tc pc i.
Proof.
  unfold check_instr; intros.
  destruct (site_of dm f i) as [[[k' op] a]|] eqn:S.
- exploit site_of_inv; eauto. intros (sg & id & args & res & s & E). subst i.
  destruct (accop_eq k k').
  + subst k'. destruct tc!pc as [[]|] eqn:T; try discriminate.
    InvBooleans. subst. eapply tr_site; eauto.
  + destruct tc!pc as [i'|] eqn:T; try discriminate.
    destruct (instruction_eq (Icall sg (inr id) args res s) i'); try discriminate. subst i'.
    apply tr_same; auto; intros; discriminate.
- destruct i; try (destruct tc!pc as [i'|] eqn:T; try discriminate;
                   destruct (instruction_eq _ i'); try discriminate; subst i';
                   apply tr_same; auto; intros; discriminate).
  destruct o as [r|].
    * InvBooleans. destruct tc!pc as [[]|] eqn:T; try discriminate.
      destruct l as [|a1 [|a2 []]]; try discriminate. InvBooleans.
      destruct tc!n as [[]|] eqn:T2; try discriminate. destruct o0 as [r'|]; try discriminate.
      InvBooleans. subst. eapply tr_return; eauto.
    * destruct tc!pc as [i'|] eqn:T; try discriminate.
      destruct (instruction_eq _ i'); try discriminate. subst i'.
      apply tr_same; auto; intros; discriminate.
Qed.

Lemma check_function_correct:
  forall dm f k tf,
  check_function dm f k tf = true ->
  exists bop cop, tr_function dm f tf k bop cop.
Proof.
  unfold check_function; intros.
  (* On targets that recognize no operation, there are no goals left. *)
  destruct (accop_binary k) as [bop|] eqn:B; try discriminate.
  all: destruct (accop_const k) as [cop|] eqn:C; try discriminate.
  all: destruct (fn_code tf)!(fn_entrypoint tf) as [[]|] eqn:E; InvBooleans; try discriminate.
  all: destruct l; InvBooleans; try discriminate.
  all: subst; exists bop, cop; constructor; auto;
       [ congruence
       | intros; apply check_instr_correct;
         rewrite PTree_Properties.for_all_correct in H1; eapply H1; eauto ].
Qed.

Lemma transf_function_spec:
  forall dm f,
  transf_function dm f = f \/
  exists k bop cop, tr_function dm f (transf_function dm f) k bop cop.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
  destruct (find_kind dm f) as [k|]; auto.
  all: destruct (gen_function dm f k) as [tf|]; auto.
  all: destruct (check_function dm f k tf) eqn:C; auto.
  all: right; destruct (check_function_correct _ _ _ _ C) as (bop & cop & TR);
       exists k, bop, cop; auto.
Qed.

Lemma transf_function_sig:
  forall dm f, fn_sig (transf_function dm f) = fn_sig f.
Proof.
  intros. destruct (transf_function_spec dm f) as [E | (k & bop & cop & TR)].
  rewrite E; auto.
  eapply tr_sig; eauto.
Qed.

Lemma transf_fundef_sig:
  forall dm fd, funsig (transf_fundef dm fd) = funsig fd.
Proof.
  intros. destruct fd; simpl; auto. apply transf_function_sig.
Qed.

(** Properties of [ret_ok]. *)

Lemma ret_ok_inv:
  forall k f r,
  ret_ok k f r = true ->
  ~In r f.(fn_params)
  /\ (forall pc i, f.(fn_code)!pc = Some i -> instr_defs i = Some r -> normal_def k i = true).
Proof.
  unfold ret_ok; intros. InvBooleans. split.
  destruct (in_dec peq r (fn_params f)); simpl in H0; [discriminate | auto].
  intros pc i A B. rewrite PTree_Properties.for_all_correct in H1.
  specialize (H1 _ _ A). rewrite B in H1. destruct (peq r r); simpl in H1; congruence.
Qed.

Lemma normal_def_sound:
  forall (FF VV: Type) (gge: Genv.t FF VV) k op args res s sp vl m v,
  normal_def k (Iop op args res s) = true ->
  eval_operation gge sp op vl m = Some v ->
  normal k v.
Proof.
  intros. assert (op <> Omove /\ accop_type_ok k (snd (type_of_operation op)) = true).
  { unfold normal_def in H. destruct op; try discriminate; split; auto; congruence. }
  destruct H1. eapply normal_of_type; eauto. eapply type_of_operation_sound; eauto.
Qed.

(** Properties of the moves of arguments to parameters. *)

Fixpoint apply_moves (ms: list (reg * reg)) (rs: regset) : regset :=
  match ms with
  | nil => rs
  | (s, d) :: ms' => apply_moves ms' (rs#d <- (rs#s))
  end.

Lemma apply_moves_app:
  forall ms1 ms2 rs, apply_moves (ms1 ++ ms2) rs = apply_moves ms2 (apply_moves ms1 rs).
Proof.
  induction ms1 as [|[s d] ms1]; simpl; auto.
Qed.

Lemma temps_charact:
  forall n r t, In t (temps r n) -> Plt r t.
Proof.
  induction n; simpl; intros. contradiction.
  destruct H. subst; extlia. apply IHn in H. extlia.
Qed.

Lemma temps_norepet:
  forall n r, list_norepet (temps r n).
Proof.
  induction n; simpl; intros. constructor.
  constructor; auto. intro. apply temps_charact in H. extlia.
Qed.

Lemma temps_length:
  forall n r, length (temps r n) = n.
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma apply_moves_phase1:
  forall args tmps rs,
  list_norepet tmps ->
  (forall a t, In a args -> In t tmps -> a <> t) ->
  length args = length tmps ->
  let rs1 := apply_moves (combine args tmps) rs in
  rs1##tmps = rs##args /\ (forall r, ~In r tmps -> rs1#r = rs#r).
Proof.
  induction args as [|a args]; destruct tmps as [|t tmps]; simpl; intros; try discriminate.
- auto.
- inv H.
  set (rs0 := rs#t <- (rs#a)).
  assert (A: rs0##args = rs##args).
  { apply list_map_exten; intros. unfold rs0. rewrite Regmap.gso; auto;
    apply H0; simpl; auto. }
  destruct (IHargs tmps rs0) as [B C]; auto.
  split.
  + rewrite C by auto. rewrite B, A. f_equal. unfold rs0; apply Regmap.gss.
  + intros. rewrite C by tauto. unfold rs0; rewrite Regmap.gso; auto.
Qed.

Lemma apply_moves_phase2:
  forall tmps params rs1,
  (forall t p, In t tmps -> In p params -> t <> p) ->
  length tmps = length params ->
  let rs2 := apply_moves (rev (combine tmps params)) rs1 in
  (forall p, In p params -> rs2#p = (init_regs rs1##tmps params)#p)
  /\ (forall r, ~In r params -> rs2#r = rs1#r).
Proof.
  induction tmps as [|t tmps]; destruct params as [|p params]; simpl; intros; try discriminate.
- split; intros; auto. contradiction.
- rewrite apply_moves_app. simpl.
  destruct (IHtmps params rs1) as [A B]; auto.
  set (rs0 := apply_moves (rev (combine tmps params)) rs1) in *.
  assert (T: rs0#t = rs1#t).
  { apply B. intro IN. elim (H t t); auto. }
  split; intros q IN.
  + rewrite ! Regmap.gsspec. destruct (peq q p).
    * auto.
    * apply A. destruct IN; [congruence | auto].
  + rewrite Regmap.gso by (intro; subst; tauto). apply B. tauto.
Qed.

Lemma call_moves_spec:
  forall f args rs,
  length args = length f.(fn_params) ->
  (forall r, In r args -> Ple r (max_reg_function f)) ->
  let rs2 := apply_moves (call_moves f args) rs in
  rs2#(acc_reg f) = rs#(acc_reg f)
  /\ (forall p, In p f.(fn_params) -> rs2#p = (init_regs rs##args f.(fn_params))#p).
Proof.
  intros. unfold rs2, call_moves. rewrite apply_moves_app.
  set (tmps := temps (acc_reg f) (length (fn_params f))).
  assert (TL: length tmps = length (fn_params f)) by (apply temps_length).
  assert (TC: forall t, In t tmps -> Plt (max_reg_function f) t).
  { intros. apply temps_charact in H1. unfold acc_reg in H1. extlia. }
  destruct (apply_moves_phase1 args tmps rs) as [A B].
    apply temps_norepet.
    intros. apply H0 in H1. apply TC in H2. extlia.
    rewrite TL; exact H.
  set (rs1 := apply_moves (combine args tmps) rs) in *.
  destruct (apply_moves_phase2 tmps (fn_params f) rs1) as [C D].
    intros. apply TC in H1. apply max_reg_function_params in H2. extlia.
    auto.
  fold rs1. split.
- rewrite D. apply B.
  intro IN. apply temps_charact in IN. extlia.
  intro IN. apply max_reg_function_params in IN. unfold acc_reg in IN. extlia.
- intros. rewrite C by auto. f_equal. f_equal. exact A.
Qed.

(** Properties of [init_regs]. *)

Lemma init_regs_notin:
  forall vl rl r, ~In r rl -> (init_regs vl rl)#r = Vundef.
Proof.
  induction vl; destruct rl; simpl; intros; try (apply Regmap.gi).
  rewrite Regmap.gso. apply IHvl; tauto. intuition.
Qed.

Lemma init_regs_inject:
  forall F vl vl', Val.inject_list F vl vl' ->
  forall rl r, Val.inject F (init_regs vl rl)#r (init_regs vl' rl)#r.
Proof.
  induction 1; destruct rl; simpl; intros; try (rewrite Regmap.gi; constructor).
  rewrite ! Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

(** * Semantic preservation *)

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => tf = transf_fundef (prog_defmap cu) f) eq prog tprog.

Lemma transf_program_match:
  forall prog, match_prog prog (transf_program prog).
Proof.
  intros. eapply match_transform_program_contextual. auto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cu, Genv.find_funct tge v = Some (transf_fundef (prog_defmap cu) f) /\ linkorder cu prog.
Proof.
  intros. exploit (Genv.find_funct_match TRANSL); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu, Genv.find_funct_ptr tge b = Some (transf_fundef (prog_defmap cu) f) /\ linkorder cu prog.
Proof.
  intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma find_self:
  forall cu id f rs fd,
  linkorder cu prog ->
  (prog_defmap cu)!id = Some (Gfun (Internal f)) ->
  find_function ge (inr id) rs = Some fd ->
  fd = Internal f.
Proof.
  intros. destruct (prog_defmap_linkorder _ _ _ _ H H0) as (gd & P & Q).
  inv Q. inv H3.
  apply Genv.find_def_symbol in P. destruct P as (b & A & B).
  simpl in H1. fold ge in A. rewrite A in H1.
  rewrite <- Genv.find_funct_ptr_iff in B. fold ge in B. congruence.
Qed.

(** Agreement between register sets *)

Definition regs_inject (F: meminj) (rs rs': regset) : Prop :=
  forall r, Val.inject F rs#r rs'#r.

Lemma regs_inject_list:
  forall F rs rs' rl, regs_inject F rs rs' -> Val.inject_list F rs##rl rs'##rl.
Proof.
  induction rl; simpl; intros; constructor; auto.
Qed.

Lemma regs_inject_set:
  forall F rs rs' r v v',
  regs_inject F rs rs' -> Val.inject F v v' -> regs_inject F (rs#r <- v) (rs'#r <- v').
Proof.
  intros; red; intros. rewrite ! Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma regs_inject_setres:
  forall F rs rs' res v v',
  regs_inject F rs rs' -> Val.inject F v v' ->
  regs_inject F (regmap_setres res v rs) (regmap_setres res v' rs').
Proof.
  intros. destruct res; simpl; auto. apply regs_inject_set; auto.
Qed.

Lemma regs_inject_incr:
  forall F F' rs rs', regs_inject F rs rs' -> inject_incr F F' -> regs_inject F' rs rs'.
Proof.
  intros; red; intros. eapply val_inject_incr; eauto.
Qed.

(** Invariant of the registers of a function in accumulator mode. *)

Definition group_regs (k: accop) (f: function) (rs: regset) : Prop :=
  (forall r, Plt (max_reg_function f) r -> rs#r = Vundef)
  /\ (forall r, ret_ok k f r = true -> normal k rs#r).

Lemma group_regs_set:
  forall k f rs pc i r v,
  group_regs k f rs ->
  f.(fn_code)!pc = Some i -> instr_defs i = Some r ->
  (normal_def k i = true -> normal k v) ->
  group_regs k f (rs#r <- v).
Proof.
  intros. destruct H as [A B]. split; intros.
- rewrite Regmap.gso. auto.
  generalize (max_reg_function_def _ _ _ _ H0 H1). intros. intro; subst. extlia.
- rewrite Regmap.gsspec. destruct (peq r0 r).
  + subst r0. exploit ret_ok_inv; eauto. intros [C D]. eauto.
  + auto.
Qed.

Lemma group_regs_init:
  forall k f args, group_regs k f (init_regs args f.(fn_params)).
Proof.
  intros; split; intros.
- apply init_regs_notin. intro. apply max_reg_function_params in H0. extlia.
- exploit ret_ok_inv; eauto. intros [A B]. rewrite init_regs_notin by auto. apply normal_undef.
Qed.

Lemma acc_reg_fresh:
  forall f pc i r,
  f.(fn_code)!pc = Some i -> instr_defs i = Some r -> r <> acc_reg f.
Proof.
  intros. generalize (max_reg_function_def _ _ _ _ H H0). unfold acc_reg. intros. intro; subst. extlia.
Qed.

(** Pending frames of the original program: frames of recursive calls
  in accumulator position.  When resumed with result [v], such a frame
  computes [accop_eval k v yv] and returns it. *)

Inductive pend_frame (k: accop): stackframe -> val -> Prop :=
  | pend_frame_intro: forall res f sp s rs op oargs d s2 yv
      (OP: f.(fn_code)!s = Some (Iop op oargs d s2))
      (RET: f.(fn_code)!s2 = Some (Ireturn (Some d)))
      (EV: forall v m, eval_operation ge sp op (rs#res <- v)##oargs m = Some (accop_eval k v yv)),
      pend_frame k (Stackframe res f sp s rs) yv.

Inductive match_stacks (F: meminj): list stackframe -> list stackframe -> Prop :=
  | match_stacks_nil:
      match_stacks F nil nil
  | match_stacks_plain: forall res f sp pc rs stk sp' rs' stk'
      (STK: match_stacks F stk stk')
      (RS: regs_inject F rs rs')
      (SP: F sp = Some (sp', 0)),
      match_stacks F (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                     (Stackframe res f (Vptr sp' Ptrofs.zero) pc rs' :: stk')
  | match_stacks_acc: forall res f sp pc rs pend stk tf sp' rs' stk' cu k bop cop ys Ys
                             pc0 sg ros args
      (STK: match_stacks F stk stk')
      (LINK: linkorder cu prog)
      (TR: tr_function (prog_defmap cu) f tf k bop cop)
      (CALL: f.(fn_code)!pc0 = Some (Icall sg ros args res pc))
      (PEND: list_forall2 (pend_frame k) pend ys)
      (YS: Val.inject_list F ys Ys)
      (ACC: rs'#(acc_reg f) = afold k Ys)
      (GR: group_regs k f rs)
      (RS: regs_inject F rs rs')
      (SP: F sp = Some (sp', 0))
      (SPB: Ple (Genv.genv_next ge) sp'),
      match_stacks F (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: pend ++ stk)
                     (Stackframe res tf (Vptr sp' Ptrofs.zero) pc rs' :: stk').

Lemma match_stacks_incr:
  forall F stk stk', match_stacks F stk stk' ->
  forall F', inject_incr F F' -> match_stacks F' stk stk'.
Proof.
  induction 1; intros.
- constructor.
- econstructor; eauto. eapply regs_inject_incr; eauto.
- econstructor; eauto;
  first [eapply val_inject_list_incr; eauto | eapply regs_inject_incr; eauto].
Qed.

Inductive match_states: state -> state -> Prop :=
  | match_st_plain: forall stk f sp pc rs m stk' sp' rs' m' F
      (STK: match_stacks F stk stk')
      (RS: regs_inject F rs rs')
      (SP: F sp = Some (sp', 0))
      (MEM: Mem.inject F m m')
      (GE: Genv.inject F ge),
      match_states (State stk f (Vptr sp Ptrofs.zero) pc rs m)
                   (State stk' f (Vptr sp' Ptrofs.zero) pc rs' m')
  | match_st_acc: forall pend stk f sp pc rs m tf stk' sp' rs' m' F cu k bop cop ys Ys
      (STK: match_stacks F stk stk')
      (LINK: linkorder cu prog)
      (TR: tr_function (prog_defmap cu) f tf k bop cop)
      (PEND: list_forall2 (pend_frame k) pend ys)
      (YS: Val.inject_list F ys Ys)
      (ACC: rs'#(acc_reg f) = afold k Ys)
      (GR: group_regs k f rs)
      (RS: regs_inject F rs rs')
      (SP: F sp = Some (sp', 0))
      (SPB: Ple (Genv.genv_next ge) sp')
      (MEM: Mem.inject F m m')
      (GE: Genv.inject F ge),
      match_states (State (pend ++ stk) f (Vptr sp Ptrofs.zero) pc rs m)
                   (State stk' tf (Vptr sp' Ptrofs.zero) pc rs' m')
  | match_st_call: forall stk fd args m stk' args' m' F cu
      (STK: match_stacks F stk stk')
      (LINK: linkorder cu prog)
      (ARGS: Val.inject_list F args args')
      (MEM: Mem.inject F m m')
      (GE: Genv.inject F ge),
      match_states (Callstate stk fd args m)
                   (Callstate stk' (transf_fundef (prog_defmap cu) fd) args' m')
  | match_st_reccall: forall P y pend stk f args m tf stk' sp' rs' m' F cu k bop cop ys Ys
      (STK: match_stacks F stk stk')
      (LINK: linkorder cu prog)
      (TR: tr_function (prog_defmap cu) f tf k bop cop)
      (PEN1: pend_frame k P y)
      (PEND: list_forall2 (pend_frame k) pend ys)
      (YS: Val.inject_list F (y :: ys) Ys)
      (ACC: rs'#(acc_reg f) = afold k Ys)
      (INIT: regs_inject F (init_regs args f.(fn_params)) rs')
      (VALID: Mem.valid_block m' sp')
      (SPB: Ple (Genv.genv_next ge) sp')
      (MEM: Mem.inject F m m')
      (GE: Genv.inject F ge),
      match_states (Callstate (P :: pend ++ stk) (Internal f) args m)
                   (State stk' tf (Vptr sp' Ptrofs.zero) f.(fn_entrypoint) rs' m')
  | match_st_ret: forall pend stk v m stk' v' m' F k ys
      (STK: match_stacks F stk stk')
      (PEND: list_forall2 (pend_frame k) pend ys)
      (RV: Val.inject F (chain k ys v) v')
      (MEM: Mem.inject F m m')
      (GE: Genv.inject F ge),
      match_states (Returnstate (pend ++ stk) v m)
                   (Returnstate stk' v' m')
  | match_st_retop: forall pend stk f sp s rs m stk' v' m' F k ys op oargs d s2 w
      (STK: match_stacks F stk stk')
      (PEND: list_forall2 (pend_frame k) pend ys)
      (OP: f.(fn_code)!s = Some (Iop op oargs d s2))
      (RET: f.(fn_code)!s2 = Some (Ireturn (Some d)))
      (EV: forall m0, eval_operation ge sp op rs##oargs m0 = Some w)
      (RV: Val.inject F (chain k ys w) v')
      (MEM: Mem.inject F m m')
      (GE: Genv.inject F ge),
      match_states (State (pend ++ stk) f sp s rs m)
                   (Returnstate stk' v' m')
  | match_st_retret: forall pend stk f sp s2 rs m stk' v' m' F k ys d
      (STK: match_stacks F stk stk')
      (PEND: list_forall2 (pend_frame k) pend ys)
      (RET: f.(fn_code)!s2 = Some (Ireturn (Some d)))
      (RV: Val.inject F (chain k ys rs#d) v')
      (MEM: Mem.inject F m m')
      (GE: Genv.inject F ge),
      match_states (State (pend ++ stk) f sp s2 rs m)
                   (Returnstate stk' v' m').

(** The measure decreases along the steps of the original program that
  are not matched by steps of the transformed program: the entry of a
  recursive call, and the returns through pending frames. *)

Definition is_opret (f: function) (pc: node) : bool :=
  match f.(fn_code)!pc with
  | Some (Iop _ _ _ s) =>
      match f.(fn_code)!s with Some (Ireturn _) => true | _ => false end
  | _ => false
  end.

Fixpoint lead (stk: list stackframe) : nat :=
  match stk with
  | Stackframe _ f _ pc _ :: stk' => if is_opret f pc then S (lead stk') else O
  | nil => O
  end.

Definition measure (S: state) : nat :=
  match S with
  | State stk f _ pc _ _ =>
      match f.(fn_code)!pc with
      | Some (Ireturn _) => 1 + 3 * lead stk
      | _ => if is_opret f pc then 2 + 3 * lead stk else 0
      end
  | Callstate stk _ _ _ => 3 + 3 * lead stk
  | Returnstate stk _ _ => 3 * lead stk
  end%nat.

Lemma measure_state_le:
  forall stk f sp pc rs m, (measure (State stk f sp pc rs m) <= 2 + 3 * lead stk)%nat.
Proof.
  intros; simpl. destruct (fn_code f)!pc as [[]|]; try lia;
  destruct (is_opret f pc); lia.
Qed.

Lemma lead_pend:
  forall k P y stk, pend_frame k P y -> lead (P :: stk) = S (lead stk).
Proof.
  intros. inv H. simpl. unfold is_opret. rewrite OP, RET. auto.
Qed.

(** Global environments and memory injections *)

Lemma genv_next_valid:
  forall F m m',
  Genv.inject F ge -> Mem.inject F m m' ->
  Ple (Genv.genv_next ge) (Mem.nextblock m) /\ Ple (Genv.genv_next ge) (Mem.nextblock m').
Proof.
  intros. destruct H as [A B]. split.
- destruct (plt (Mem.nextblock m) (Genv.genv_next ge)); [|extlia].
  exploit A; eauto. intros. exploit Mem.valid_block_inject_1; eauto.
  unfold Mem.valid_block. intros. extlia.
- destruct (plt (Mem.nextblock m') (Genv.genv_next ge)); [|extlia].
  exploit A; eauto. intros. exploit Mem.valid_block_inject_2; eauto.
  unfold Mem.valid_block. intros. extlia.
Qed.

Lemma genv_inject_separated:
  forall F F' m1 m1',
  Genv.inject F ge -> Mem.inject F m1 m1' ->
  inject_incr F F' -> inject_separated F F' m1 m1' ->
  Genv.inject F' ge.
Proof.
  intros. destruct (genv_next_valid F m1 m1') as [NB NB']; auto.
  destruct H as [A B]. split; intros.
- apply H1. auto.
- destruct (F b) as [[b1 d1]|] eqn:FB.
  + generalize (H1 _ _ _ FB). intros E. rewrite H in E; inv E. eauto.
  + destruct (H2 _ _ _ FB H) as [P Q]. elim Q. unfold Mem.valid_block. extlia.
Qed.

Lemma genv_inject_new:
  forall F F' m b b' m',
  Genv.inject F ge -> Mem.inject F m m' ->
  ~Mem.valid_block m b ->
  Ple (Genv.genv_next ge) b' ->
  F' b = Some (b', 0) ->
  (forall b0, b0 <> b -> F' b0 = F b0) ->
  Genv.inject F' ge.
Proof.
  intros. destruct (genv_next_valid F m m') as [NB NB']; auto.
  destruct H as [A B]. split; intros.
- rewrite H4. auto. intro; subst b0. elim H1. unfold Mem.valid_block. extlia.
- destruct (eq_block b0 b).
  + subst b0. rewrite H3 in H; inv H. extlia.
  + rewrite H4 in H by auto. eauto.
Qed.

(** Evaluation of operations, addressings and builtin arguments *)

Section EVAL.

Variable F: meminj.
Hypothesis GE: Genv.inject F ge.
Variables sp sp': block.
Hypothesis SP: F sp = Some (sp', 0).

Lemma eval_operation_inj:
  forall op vl vl' m m' v,
  Val.inject_list F vl vl' -> Mem.inject F m m' ->
  eval_operation ge (Vptr sp Ptrofs.zero) op vl m = Some v ->
  exists v', eval_operation tge (Vptr sp' Ptrofs.zero) op vl' m' = Some v' /\ Val.inject F v v'.
Proof.
  intros. exploit eval_operation_inject; eauto. intros (v' & A & B).
  exists v'; split; auto.
  rewrite eval_shift_stack_operation in A. change (Ptrofs.repr 0) with Ptrofs.zero in A.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
Qed.

Lemma eval_addressing_inj:
  forall addr vl vl' a,
  Val.inject_list F vl vl' ->
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vl = Some a ->
  exists a', eval_addressing tge (Vptr sp' Ptrofs.zero) addr vl' = Some a' /\ Val.inject F a a'.
Proof.
  intros. exploit eval_addressing_inject; eauto. intros (a' & A & B).
  exists a'; split; auto.
  rewrite eval_shift_stack_addressing in A. change (Ptrofs.repr 0) with Ptrofs.zero in A.
  rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
Qed.

Lemma symbol_address_inj:
  forall id ofs, Val.inject F (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs).
Proof.
  intros. unfold Senv.symbol_address; simpl. unfold Genv.symbol_address.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id) eqn:FS; auto.
  econstructor. eapply Genv.find_symbol_inject; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma eval_builtin_arg_inj:
  forall rs rs' m m' a v,
  regs_inject F rs rs' -> Mem.inject F m m' ->
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' a v'
          /\ Val.inject F v v'.
Proof.
  intros until v; intros RS MI. induction 1.
- exists rs'#x; split; auto. constructor.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- assert (Val.inject F (Val.offset_ptr (Vptr sp Ptrofs.zero) ofs) (Val.offset_ptr (Vptr sp' Ptrofs.zero) ofs)).
  { econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. simpl. econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- exploit Mem.loadv_inject. eauto. eauto. apply symbol_address_inj.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. apply symbol_address_inj.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  exists (Val.longofwords v1' v2'); split; auto with barg.
  apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split; eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma eval_builtin_args_inj:
  forall rs rs' m m' al vl,
  regs_inject F rs rs' -> Mem.inject F m m' ->
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' al vl'
          /\ Val.inject_list F vl vl'.
Proof.
  induction 3.
- exists (@nil val); split; constructor.
- exploit eval_builtin_arg_inj; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

End EVAL.

Lemma find_function_translated:
  forall F ros rs rs' fd,
  Genv.inject F ge -> regs_inject F rs rs' ->
  find_function ge ros rs = Some fd ->
  exists cu, find_function tge ros rs' = Some (transf_fundef (prog_defmap cu) fd)
          /\ linkorder cu prog.
Proof.
  intros. destruct ros as [r|id]; simpl in *.
- assert (EQ: rs'#r = rs#r) by (eapply Genv.find_funct_inject; eauto).
  rewrite EQ. apply functions_translated; auto.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma free_empty:
  forall m b, exists m', Mem.free m b 0 0 = Some m'.
Proof.
  intros. destruct (Mem.range_perm_free m b 0 0) as [m' P].
  red; intros. lia.
  exists m'; auto.
Qed.

(** ** The simulation diagram *)

(** Moves inserted before the jump back to the entry point. *)

Lemma check_moves_star:
  forall tc ms n target,
  check_moves tc n ms target = true ->
  forall stk tf sp rs m,
  fn_code tf = tc ->
  star step tge (State stk tf sp n rs m) E0 (State stk tf sp target (apply_moves ms rs) m).
Proof.
  induction ms as [|[src dst] ms]; simpl; intros.
- destruct (peq n target); try discriminate. subst. apply star_refl.
- destruct tc!n as [i|] eqn:C; try discriminate.
  destruct i; try discriminate. destruct o; try discriminate.
  destruct l as [|src' []]; try discriminate.
  InvBooleans. subst.
  eapply star_left. eapply exec_Iop; eauto. simpl; eauto.
  eapply IHms; eauto. traceEq.
Qed.

(** Execution of instructions that do not call nor return. *)

Ltac code_inv :=
  match goal with
  | [ H1: (fn_code ?f)!?pc = Some _, H2: (fn_code ?f)!?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
  end.

Definition is_local (i: instruction) : bool :=
  match i with
  | Icall _ _ _ _ _ | Itailcall _ _ _ | Ireturn _ => false
  | _ => true
  end.

Lemma step_local:
  forall s f sp pc rs m t S2 i F s' tf sp' rs' m',
  step ge (State s f (Vptr sp Ptrofs.zero) pc rs m) t S2 ->
  f.(fn_code)!pc = Some i ->
  tf.(fn_code)!pc = Some i ->
  is_local i = true ->
  regs_inject F rs rs' -> F sp = Some (sp', 0) -> Mem.inject F m m' -> Genv.inject F ge ->
  exists pc1 rs1 m1 rs1' m1' F',
     S2 = State s f (Vptr sp Ptrofs.zero) pc1 rs1 m1
  /\ step tge (State s' tf (Vptr sp' Ptrofs.zero) pc rs' m') t
              (State s' tf (Vptr sp' Ptrofs.zero) pc1 rs1' m1')
  /\ regs_inject F' rs1 rs1' /\ Mem.inject F' m1 m1' /\ Genv.inject F' ge
  /\ inject_incr F F'
  /\ ((rs1 = rs /\ rs1' = rs')
      \/ exists r v v', instr_defs i = Some r /\ rs1 = rs#r <- v /\ rs1' = rs'#r <- v'
                        /\ (forall k, normal_def k i = true -> normal k v)).
Proof.
  intros until m'; intros STEP C TC L RS SP MEM GE.
  inv STEP; code_inv; try discriminate.
- (* nop *)
  exists pc', rs, m, rs', m', F; intuition auto.
  eapply exec_Inop; eauto.
- (* op *)
  exploit (eval_operation_inj F GE sp sp' SP op rs##args rs'##args m m' v); auto.
  apply regs_inject_list; auto. intros (v' & A & B).
  exists pc', (rs#res <- v), m, (rs'#res <- v'), m', F; intuition auto.
  eapply exec_Iop; eauto.
  apply regs_inject_set; auto.
  right. exists res, v, v'; intuition auto. eapply normal_def_sound; eauto.
- (* load *)
  exploit (eval_addressing_inj F GE sp sp' SP addr rs##args rs'##args a); auto.
  apply regs_inject_list; auto. intros (a' & A & B).
  exploit Mem.loadv_inject; eauto. intros (v' & D & E).
  exists pc', (rs#dst <- v), m, (rs'#dst <- v'), m', F; intuition auto.
  eapply exec_Iload; eauto.
  apply regs_inject_set; auto.
  right. exists dst, v, v'; intuition auto. discriminate.
- (* store *)
  exploit (eval_addressing_inj F GE sp sp' SP addr rs##args rs'##args a); auto.
  apply regs_inject_list; auto. intros (a' & A & B).
  exploit Mem.storev_mapped_inject; eauto. intros (m1' & D & E).
  exists pc', rs, m'0, rs', m1', F; intuition auto.
  eapply exec_Istore; eauto.
- (* builtin *)
  exploit (eval_builtin_args_inj F GE sp sp' SP rs rs' m m'); eauto. intros (vargs' & A & B).
  exploit external_call_mem_inject; eauto. intros (F' & vres' & m1' & D & E & G & U1 & U2 & INCR & SEP).
  exists pc', (regmap_setres res vres rs), m'0, (regmap_setres res vres' rs'), m1', F'.
  split. auto.
  split. eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  split. apply regs_inject_setres; auto. eapply regs_inject_incr; eauto.
  split. auto.
  split. eapply genv_inject_separated; eauto.
  split. auto.
  destruct res; simpl; auto.
  right. exists x, vres, vres'; intuition auto. discriminate.
- (* cond *)
  exists (if b then ifso else ifnot), rs, m, rs', m', F; intuition auto.
  eapply exec_Icond; eauto. eapply eval_condition_inject; eauto. apply regs_inject_list; auto.
- (* jumptable *)
  exists pc', rs, m, rs', m', F; intuition auto.
  eapply exec_Ijumptable; eauto.
  generalize (RS arg). rewrite H8. intros X; inv X; auto.
Qed.

Lemma regs_inject_init:
  forall F args args' params,
  Val.inject_list F args args' ->
  regs_inject F (init_regs args params) (init_regs args' params).
Proof.
  intros; red; intros. apply init_regs_inject; auto.
Qed.

Lemma step_plain:
  forall s f sp pc rs m t S2 stk' sp' rs' m' F,
  step ge (State s f (Vptr sp Ptrofs.zero) pc rs m) t S2 ->
  match_stacks F s stk' -> regs_inject F rs rs' -> F sp = Some (sp', 0) ->
  Mem.inject F m m' -> Genv.inject F ge ->
  exists S2', plus step tge (State stk' f (Vptr sp' Ptrofs.zero) pc rs' m') t S2'
           /\ match_states S2 S2'.
Proof.
  intros until F; intros STEP STK RS SP MEM GE.
  assert (C: exists i, f.(fn_code)!pc = Some i) by (inv STEP; eauto).
  destruct C as [i C].
  destruct (is_local i) eqn:L.
- exploit (step_local s f sp pc rs m t S2 i F stk' f sp' rs' m'); eauto.
  intros (pc1 & rs1 & m1 & rs1' & m1' & F' & E & A & B & D & G & INCR & X).
  subst S2. exists (State stk' f (Vptr sp' Ptrofs.zero) pc1 rs1' m1'); split.
  apply plus_one; auto.
  apply match_st_plain with (F := F'); auto. eapply match_stacks_incr; eauto.
- inv STEP; code_inv; try discriminate.
  + (* call *)
    exploit find_function_translated; eauto. intros (cu & FIND & LINK).
    econstructor; split.
    apply plus_one. eapply exec_Icall; eauto. apply transf_fundef_sig.
    econstructor; eauto. econstructor; eauto. apply regs_inject_list; auto.
  + (* tailcall *)
    exploit find_function_translated; eauto. intros (cu & FIND & LINK).
    exploit Mem.free_parallel_inject; eauto. rewrite ! Z.add_0_r. intros (m1' & A & B).
    econstructor; split.
    apply plus_one. eapply exec_Itailcall; eauto. apply transf_fundef_sig.
    econstructor; eauto. apply regs_inject_list; auto.
  + (* return *)
    exploit Mem.free_parallel_inject; eauto. rewrite ! Z.add_0_r. intros (m1' & A & B).
    econstructor; split.
    apply plus_one. eapply exec_Ireturn; eauto.
    apply match_st_ret with (pend := nil) (k := AOadd) (ys := nil) (F := F); auto.
    constructor. simpl. destruct or; simpl; auto.
Qed.

Lemma group_regs_setres:
  forall k f rs pc ef args res pc' v,
  group_regs k f rs ->
  f.(fn_code)!pc = Some (Ibuiltin ef args res pc') ->
  group_regs k f (regmap_setres res v rs).
Proof.
  intros. destruct res; simpl; auto. eapply group_regs_set; eauto. simpl; auto.
  intros; discriminate.
Qed.

Lemma step_acc:
  forall s f sp pc rs m t S2 pend stk tf stk' sp' rs' m' F cu k bop cop ys Ys,
  step ge (State s f (Vptr sp Ptrofs.zero) pc rs m) t S2 ->
  s = pend ++ stk ->
  match_stacks F stk stk' ->
  linkorder cu prog ->
  tr_function (prog_defmap cu) f tf k bop cop ->
  list_forall2 (pend_frame k) pend ys ->
  Val.inject_list F ys Ys ->
  rs'#(acc_reg f) = afold k Ys ->
  group_regs k f rs ->
  regs_inject F rs rs' -> F sp = Some (sp', 0) ->
  Ple (Genv.genv_next ge) sp' ->
  Mem.inject F m m' -> Genv.inject F ge ->
  exists S2', plus step tge (State stk' tf (Vptr sp' Ptrofs.zero) pc rs' m') t S2'
           /\ match_states S2 S2'.
Proof.
  intros until Ys; intros STEP ES STK LINK TR PEND YS ACC GR RS SP SPB MEM GE.
  assert (C: exists i, f.(fn_code)!pc = Some i) by (inv STEP; eauto).
  destruct C as [i C].
  generalize (tr_code _ _ _ _ _ _ TR _ _ C). intros T.
  destruct (is_local i) eqn:L.
- (* local instructions *)
  assert (TC: tf.(fn_code)!pc = Some i).
  { inv T; auto. discriminate. discriminate. }
  exploit (step_local s f sp pc rs m t S2 i F stk' tf sp' rs' m'); eauto.
  intros (pc1 & rs1 & m1 & rs1' & m1' & F' & E & A & B & D & G & INCR & X).
  subst S2. exists (State stk' tf (Vptr sp' Ptrofs.zero) pc1 rs1' m1'); split.
  apply plus_one; auto.
  assert (ACC': rs1'#(acc_reg f) = afold k Ys).
  { destruct X as [[P Q] | (r & v & v' & P & Q & R & U)]; subst; auto.
    rewrite Regmap.gso; auto. apply not_eq_sym. eapply acc_reg_fresh; eauto. }
  assert (GR': group_regs k f rs1).
  { destruct X as [[P Q] | (r & v & v' & P & Q & R & U)]; subst; auto.
    eapply group_regs_set; eauto. }
  assert (STK': match_stacks F' stk stk') by (eapply match_stacks_incr; eauto).
  assert (YS': Val.inject_list F' ys Ys) by (eapply val_inject_list_incr; eauto).
  subst s. eapply match_st_acc with (F := F'); eauto.
- inv STEP; code_inv; try discriminate; inv T.
  + (* recursive call in accumulator position *)
    match goal with [ H: site_of _ _ _ = Some _ |- _ ] => rename H into SITE end.
    match goal with [ H: (fn_code tf)!pc = Some _ |- _ ] => rename H into T1 end.
    match goal with [ H: check_moves _ _ _ _ = true |- _ ] => rename H into T2 end.
    exploit (site_of_sound _ _ ge); eauto.
    intros (oargs & d & s2 & OP & RET & LEN & SELF & IMM & EV & _).
    exploit (site_of_sound _ _ tge); eauto. intros (oargs' & d' & s2' & _ & _ & _ & _ & _ & _ & EV').
    assert (FD: fd = Internal f) by (eapply find_self; eauto). subst fd.
    set (Y' := accarg_val rs' a).
    set (rs1 := rs'#(acc_reg f) <- (accop_eval k rs'#(acc_reg f) Y')).
    assert (ARGS: forall r, In r args -> Ple r (max_reg_function f)).
    { intros. eapply max_reg_function_use. eexact C. simpl; auto. }
    destruct (call_moves_spec f args rs1 LEN ARGS) as [M1 M2].
    assert (E: rs1##args = rs'##args).
    { apply list_map_exten; intros. unfold rs1. rewrite Regmap.gso; auto.
      apply ARGS in H. unfold acc_reg. intro; subst. extlia. }
    assert (ACC1: (apply_moves (call_moves f args) rs1)#(acc_reg f) = afold k (Y' :: Ys)).
    { rewrite M1. unfold rs1. rewrite Regmap.gss. rewrite ACC. auto. }
    assert (INIT1: regs_inject F (init_regs rs##args (fn_params f)) (apply_moves (call_moves f args) rs1)).
    { red; intros r. destruct (in_dec peq r (fn_params f)).
      rewrite M2 by auto. rewrite E. apply init_regs_inject. apply regs_inject_list; auto.
      rewrite init_regs_notin by auto. constructor. }
    econstructor; split.
    eapply plus_left. eapply exec_Iop; eauto.
    eapply star_trans. eapply check_moves_star; eauto. apply star_refl.
    traceEq. traceEq.
    eapply match_st_reccall with (y := accarg_val rs a) (ys := ys) (Ys := Y' :: Ys); eauto.
    * econstructor; eauto.
    * constructor; auto. unfold Y'. eapply accarg_val_inject; eauto.
    * eapply Mem.valid_block_inject_2; eauto.
  + (* other call *)
    exploit find_function_translated; eauto. intros (cu' & FIND & LINK').
    econstructor; split.
    apply plus_one. eapply exec_Icall; eauto. apply transf_fundef_sig.
    apply match_st_call with (cu := cu') (F := F); auto.
    eapply match_stacks_acc with (cu := cu); eauto.
    apply regs_inject_list; auto.
  + (* tailcall: impossible *)
    match goal with [ H: forall sg ros args, _ <> Itailcall _ _ _ |- _ ] =>
      elim (H _ _ _ eq_refl) end.
  + (* return with a value *)
    match goal with [ H: ret_ok _ _ _ = true |- _ ] => rename H into ROK end.
    match goal with [ H: (fn_code tf)!pc = Some _ |- _ ] => rename H into T1 end.
    match goal with [ H: (fn_code tf)!_ = Some (Ireturn _) |- _ ] => rename H into T2 end.
    destruct (free_empty m' sp') as [m1' FREE].
    econstructor; split.
    eapply plus_two. eapply exec_Iop; eauto.
    simpl. eapply accop_binary_sound. eapply tr_bop; eauto.
    eapply exec_Ireturn; eauto. rewrite (tr_tstacksize _ _ _ _ _ _ TR). eauto.
    traceEq.
    simpl. rewrite Regmap.gss.
    eapply match_st_ret; eauto.
    rewrite ACC. eapply chain_afold; eauto. right. destruct GR as [_ N]. apply N; auto.
    eapply Mem.free_right_inject. eapply Mem.free_left_inject; eauto. eauto.
    intros. lia.
  + (* return without a value *)
    destruct or as [r|].
    match goal with [ H: forall r, _ <> Ireturn (Some _) |- _ ] =>
      elim (H _ eq_refl) end.
    destruct (free_empty m' sp') as [m1' FREE].
    econstructor; split.
    apply plus_one. eapply exec_Ireturn; eauto. rewrite (tr_tstacksize _ _ _ _ _ _ TR). eauto.
    simpl. eapply match_st_ret; eauto.
    rewrite chain_undef. auto.
    eapply Mem.free_right_inject. eapply Mem.free_left_inject; eauto. eauto.
    intros. lia.
Qed.

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  intros. inv MS.
- (* plain *)
  left. eapply step_plain; eauto.
- (* accumulator mode *)
  left. eapply step_acc; eauto.
- (* call *)
  inv H.
  + (* internal *)
    destruct (transf_function_spec (prog_defmap cu) f) as [E | (k & bop & cop & TR)].
    * (* not transformed *)
      exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
      intros (F' & m1' & sp' & A & B & INCR & D & E').
      left; econstructor; split.
      apply plus_one. simpl. rewrite E. eapply exec_function_internal; eauto.
      eapply Val.has_argtype_list_inject; eauto.
      econstructor.
      eapply match_stacks_incr; eauto.
      apply regs_inject_init. eapply val_inject_list_incr; eauto.
      eauto. auto.
      eapply genv_inject_new; eauto.
      eapply Mem.fresh_block_alloc; eauto.
      erewrite Mem.alloc_result by eauto. eapply genv_next_valid; eauto.
    * (* transformed *)
      set (tf := transf_function (prog_defmap cu) f) in *.
      assert (SZ: fn_stacksize tf = fn_stacksize f).
      { rewrite (tr_tstacksize _ _ _ _ _ _ TR), (tr_stacksize _ _ _ _ _ _ TR). auto. }
      exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl.
      instantiate (1 := fn_stacksize tf). rewrite SZ. apply Z.le_refl.
      intros (F' & m1' & sp' & A & B & INCR & D & E').
      left; econstructor; split.
      eapply plus_two. simpl. fold tf. eapply exec_function_internal; eauto.
      rewrite (tr_sig _ _ _ _ _ _ TR). eapply Val.has_argtype_list_inject; eauto.
      eapply exec_Iop. eapply tr_entry; eauto.
      simpl. eapply accop_const_sound. eapply tr_cop; eauto.
      traceEq.
      apply match_st_acc with (pend := nil) (ys := nil) (Ys := nil) (cu := cu) (k := k)
                              (bop := bop) (cop := cop) (F := F'); auto.
      eapply match_stacks_incr; eauto.
      constructor.
      rewrite Regmap.gss; auto.
      apply group_regs_init.
      rewrite (tr_params _ _ _ _ _ _ TR).
      red; intros r. rewrite Regmap.gsspec. destruct (peq r (acc_reg f)).
      subst r. rewrite init_regs_notin. constructor.
      intro IN. apply max_reg_function_params in IN. unfold acc_reg in IN. extlia.
      apply init_regs_inject. eapply val_inject_list_incr; eauto.
      erewrite Mem.alloc_result by eauto. eapply genv_next_valid; eauto.
      eapply genv_inject_new; eauto.
      eapply Mem.fresh_block_alloc; eauto.
      erewrite Mem.alloc_result by eauto. eapply genv_next_valid; eauto.
  + (* external *)
    exploit external_call_mem_inject; eauto.
    intros (F' & vres' & m1' & A & B & D & U1 & U2 & INCR & SEP).
    left; econstructor; split.
    apply plus_one. simpl. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    apply match_st_ret with (pend := nil) (k := AOadd) (ys := nil) (F := F'); auto.
    eapply match_stacks_incr; eauto.
    constructor.
    eapply genv_inject_separated; eauto.
- (* recursive call: entry *)
  inv H.
  match goal with [ H: Mem.alloc _ _ _ = _ |- _ ] =>
    rewrite (tr_stacksize _ _ _ _ _ _ TR) in H end.
  exploit Mem.alloc_left_mapped_inject.
    eauto. eauto. eauto.
    instantiate (1 := 0). generalize Ptrofs.max_signed_unsigned Ptrofs.max_signed_pos; lia.
    left; auto.
    intros; left; auto.
    intros; lia.
    red; intros. apply Z.divide_0_r.
    intros; lia.
  intros (F' & A & INCR & D & E).
  right; split.
  generalize (measure_state_le (P :: pend ++ stk) f (Vptr stk0 Ptrofs.zero)
                (fn_entrypoint f) (init_regs args (fn_params f)) m'0).
  intros LE.
  change (measure (Callstate (P :: pend ++ stk) (Internal f) args m))
    with (3 + 3 * lead (P :: pend ++ stk))%nat.
  lia.
  split. auto.
  change (P :: pend ++ stk) with ((P :: pend) ++ stk).
  assert (STK': match_stacks F' stk stk') by (eapply match_stacks_incr; eauto).
  assert (PEND': list_forall2 (pend_frame k) (P :: pend) (y :: ys)) by (constructor; auto).
  assert (YS': Val.inject_list F' (y :: ys) Ys) by (eapply val_inject_list_incr; eauto).
  assert (RS': regs_inject F' (init_regs args (fn_params f)) rs') by (eapply regs_inject_incr; eauto).
  assert (GE': Genv.inject F' ge).
  { eapply genv_inject_new; eauto. eapply Mem.fresh_block_alloc; eauto. }
  eapply match_st_acc with (F := F') (ys := y :: ys); eauto.
  apply group_regs_init.
- (* return *)
  inv H.
  match goal with [ H: _ :: _ = _ ++ _ |- _ ] => rename H into HS end.
  destruct pend as [|P pend'].
  + (* no pending frame *)
    simpl in HS. subst stk. inv PEND. simpl in RV.
    inv STK.
    * (* plain frame *)
      left; econstructor; split.
      apply plus_one. apply exec_return.
      econstructor; eauto. apply regs_inject_set; auto.
    * (* frame in accumulator mode *)
      left; econstructor; split.
      apply plus_one. apply exec_return.
      econstructor; eauto.
      rewrite Regmap.gso; auto. apply not_eq_sym. eapply acc_reg_fresh; eauto. auto.
      eapply group_regs_set; eauto. auto. intros; discriminate.
      apply regs_inject_set; auto.
  + (* return to a pending frame *)
    simpl in HS. inv HS. inv PEND.
    match goal with [ H: pend_frame _ _ _ |- _ ] => rename H into PF end.
    right; split.
    inv PF. unfold measure. rewrite OP. simpl lead. unfold is_opret. rewrite OP, RET. lia.
    split. auto.
    inv PF. eapply match_st_retop; eauto.
- (* return through a pending frame: the operation *)
  inv H; code_inv.
  match goal with [ H: eval_operation _ _ _ _ _ = Some _ |- _ ] => rewrite EV in H; inv H end.
  right; split.
  unfold measure. rewrite OP, RET. unfold is_opret. rewrite OP, RET. lia.
  split. auto.
  eapply match_st_retret; eauto.
  rewrite Regmap.gss. auto.
- (* return through a pending frame: the return *)
  inv H; code_inv.
  right; split.
  unfold measure. rewrite RET. lia.
  split. auto.
  eapply match_st_ret; eauto.
  eapply Mem.free_left_inject; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (cu & FIND & LINK).
  exists (Callstate nil (transf_fundef (prog_defmap cu) f) nil m0); split.
  econstructor; eauto.
    eapply (Genv.init_mem_match TRANSL); eauto.
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog). auto.
    symmetry; eapply match_program_main; eauto.
    rewrite transf_fundef_sig. auto.
  econstructor. constructor. eauto. constructor.
  eapply Genv.initmem_inject; eauto.
  erewrite <- Genv.init_mem_genv_next by eauto. apply Genv.init_inject.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  destruct pend; [|discriminate]. simpl in H1; subst stk.
  inv PEND. inv STK. simpl in RV. inv RV. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.

End PRESERVATION.
