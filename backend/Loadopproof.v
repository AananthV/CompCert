(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for the fusion of loads into operations. *)

From Coq Require Import FSets.
Require Import Coqlib Maps.
Require Import AST Linking Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Conventions LTL Linear.
Require Import Bounds LoadopOp Loadop.

Module RSF := FSetFacts.Facts(RegSet).
Module RSP := FSetProperties.Properties(RegSet).

Definition match_prog (p tp: Linear.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

(** * Properties of register sets *)

Lemma In_all_live: forall r, RegSet.In r all_live.
Proof.
  intros. unfold all_live. generalize (all_mregs_complete r).
  induction all_mregs as [|r1 rl]; simpl; intros H.
- contradiction.
- rewrite RSF.add_iff. destruct H; auto.
Qed.

Lemma In_add_regs:
  forall r rl s, RegSet.In r (add_regs rl s) <-> In r rl \/ RegSet.In r s.
Proof.
  induction rl as [|r1 rl]; simpl; intros.
- tauto.
- rewrite RSF.add_iff, IHrl. intuition.
Qed.

Lemma In_live_at_labels:
  forall lm r lbl tbl,
  In lbl tbl -> RegSet.In r (live_at lm lbl) -> RegSet.In r (live_at_labels lm tbl).
Proof.
  induction tbl as [|l1 tbl]; simpl; intros.
- contradiction.
- rewrite RSF.union_iff. destruct H; [subst; auto | right; auto].
Qed.

(** * Agreement of location sets on live registers *)

Definition loc_live (s: RegSet.t) (l: loc) : Prop :=
  match l with
  | R r => RegSet.In r s
  | S _ _ _ => True
  end.

Definition agree (s: RegSet.t) (ls ls': locset) : Prop :=
  forall l, loc_live s l -> ls l = ls' l.

Definition agree_all (ls ls': locset) : Prop := forall l, ls l = ls' l.

Lemma agree_all_agree: forall s ls ls', agree_all ls ls' -> agree s ls ls'.
Proof.
  unfold agree_all, agree; auto.
Qed.

Lemma agree_all_live: forall ls ls', agree all_live ls ls' -> agree_all ls ls'.
Proof.
  intros; red; intros. apply H. destruct l; simpl; auto. apply In_all_live.
Qed.

Lemma agree_incl:
  forall s s' ls ls', agree s ls ls' -> (forall r, RegSet.In r s' -> RegSet.In r s) -> agree s' ls ls'.
Proof.
  unfold agree; intros. apply H. destruct l; simpl in *; auto.
Qed.

Lemma agree_reg:
  forall s ls ls' r, agree s ls ls' -> RegSet.In r s -> ls (R r) = ls' (R r).
Proof.
  intros. apply H; auto.
Qed.

Lemma agree_slot:
  forall s ls ls' sl ofs ty, agree s ls ls' -> ls (S sl ofs ty) = ls' (S sl ofs ty).
Proof.
  intros. apply H; exact I.
Qed.

Lemma agree_reglist:
  forall s ls ls' rl,
  agree s ls ls' -> (forall r, In r rl -> RegSet.In r s) -> reglist ls rl = reglist ls' rl.
Proof.
  induction rl as [|r rl]; simpl; intros. auto.
  f_equal. apply H; simpl; auto. auto.
Qed.

Lemma agree_add_regs_reglist:
  forall s ls ls' rl, agree (add_regs rl s) ls ls' -> reglist ls rl = reglist ls' rl.
Proof.
  intros. eapply agree_reglist; eauto. intros. apply (proj2 (In_add_regs _ _ _)); auto.
Qed.

Lemma agree_add_regs:
  forall s ls ls' rl, agree (add_regs rl s) ls ls' -> agree s ls ls'.
Proof.
  intros. eapply agree_incl; eauto. intros. apply (proj2 (In_add_regs _ _ _)); auto.
Qed.

(** Pointwise compatibility of the location map operations. *)

Lemma set_pointwise:
  forall l v ls ls' p, ls p = ls' p -> Locmap.set l v ls p = Locmap.set l v ls' p.
Proof.
  intros. unfold Locmap.set. destruct (Loc.eq l p); auto. destruct (Loc.diff_dec l p); auto.
Qed.

Lemma undef_regs_pointwise:
  forall rl ls ls' p, ls p = ls' p -> undef_regs rl ls p = undef_regs rl ls' p.
Proof.
  induction rl; simpl; intros; auto. apply set_pointwise; auto.
Qed.

Lemma agree_set:
  forall s ls ls' l v, agree s ls ls' -> agree s (Locmap.set l v ls) (Locmap.set l v ls').
Proof.
  unfold agree; intros. apply set_pointwise; auto.
Qed.

Lemma agree_undef_regs:
  forall s ls ls' rl, agree s ls ls' -> agree s (undef_regs rl ls) (undef_regs rl ls').
Proof.
  unfold agree; intros. apply undef_regs_pointwise; auto.
Qed.

Lemma agree_set_remove:
  forall s ls ls' r v,
  agree (RegSet.remove r s) ls ls' -> agree s (Locmap.set (R r) v ls) (Locmap.set (R r) v ls').
Proof.
  unfold agree; intros. destruct (Loc.eq (R r) l).
- subst l. rewrite ! Locmap.gss_reg. auto.
- apply set_pointwise. apply H. destruct l; simpl in *; auto.
  apply RegSet.remove_2; auto. congruence.
Qed.

Lemma agree_all_setpair:
  forall p v ls ls', agree_all ls ls' -> agree_all (Locmap.setpair p v ls) (Locmap.setpair p v ls').
Proof.
  unfold agree_all; intros. destruct p; simpl; repeat apply set_pointwise; auto.
Qed.

Lemma agree_all_setres:
  forall res v ls ls', agree_all ls ls' -> agree_all (Locmap.setres res v ls) (Locmap.setres res v ls').
Proof.
  induction res; simpl; intros; auto; red; intros; repeat apply set_pointwise; auto.
Qed.

(** Registers observable by calls and returns. *)

Lemma In_callee_save_live:
  forall r, RegSet.In r callee_save_live <-> is_callee_save r = true.
Proof.
  intros.
  assert (GEN: forall rl, RegSet.In r (List.fold_right (fun r s => if is_callee_save r then RegSet.add r s else s) RegSet.empty rl)
                          <-> In r rl /\ is_callee_save r = true).
  { induction rl as [|r1 rl IH]; simpl.
    - rewrite RSF.empty_iff. tauto.
    - destruct (is_callee_save r1) eqn:C.
      + rewrite RSF.add_iff, IH. split.
        * intros [E|[A B]]. subst; auto. auto.
        * intros [[E|A] B]. subst; auto. destruct (mreg_eq r1 r); auto.
      + rewrite IH. intuition (subst; auto). congruence. }
  unfold callee_save_live. rewrite GEN. generalize (all_mregs_complete r). tauto.
Qed.

Lemma In_param_live:
  forall sg r, RegSet.In r (param_live sg) <-> In (R r) (regs_of_rpairs (loc_arguments sg)).
Proof.
  intros. unfold param_live. induction (regs_of_rpairs (loc_arguments sg)) as [|l ll]; simpl.
- rewrite RSF.empty_iff. tauto.
- destruct l as [r1|sl ofs ty].
  + rewrite RSF.add_iff, IHll. intuition congruence.
  + rewrite IHll. intuition congruence.
Qed.

Lemma In_result_live:
  forall sg r, RegSet.In r (result_live sg) <-> In r (regs_of_rpair (loc_result sg)).
Proof.
  intros. unfold result_live. rewrite In_add_regs, RSF.empty_iff. tauto.
Qed.

Definition call_live (sg: signature) := RegSet.union callee_save_live (param_live sg).

Lemma agree_call_regs:
  forall sg ls ls', agree (call_live sg) ls ls' -> agree_all (call_regs sg ls) (call_regs sg ls').
Proof.
  unfold agree_all, call_regs; intros. destruct l as [r | [] ofs ty]; auto.
- destruct (is_callee_save r) eqn:C; simpl.
  apply H; simpl. apply RegSet.union_2. apply In_callee_save_live; auto.
  unfold param_reg. destruct (In_dec Loc.eq (R r) (regs_of_rpairs (loc_arguments sg))); simpl; auto.
  apply H; simpl. apply RegSet.union_3. apply In_param_live; auto.
- apply H; exact I.
Qed.

Lemma agree_return_regs_res:
  forall sg c c' ls ls',
  agree callee_save_live c c' -> agree (result_live sg) ls ls' ->
  agree_all (return_regs_res sg c ls) (return_regs_res sg c' ls').
Proof.
  unfold agree_all, return_regs_res; intros. destruct l as [r | sl ofs ty].
- destruct (is_callee_save r) eqn:C.
  apply H; simpl. apply In_callee_save_live; auto.
  unfold result_reg. destruct (In_dec mreg_eq r (regs_of_rpair (loc_result sg))); simpl; auto.
  apply H0; simpl. apply In_result_live; auto.
- destruct sl; auto; apply H; exact I.
Qed.

Lemma agree_return_regs_call:
  forall sg s c c' ls ls',
  agree callee_save_live c c' -> agree (RegSet.union (param_live sg) s) ls ls' ->
  agree (call_live sg) (return_regs c ls) (return_regs c' ls').
Proof.
  unfold agree, return_regs; intros. destruct l as [r | sl ofs ty].
- destruct (is_callee_save r) eqn:C.
  apply H; simpl. apply In_callee_save_live; auto.
  apply H0; simpl. unfold call_live in H1; simpl in H1.
  apply RegSet.union_1 in H1. destruct H1.
  apply In_callee_save_live in H1; congruence.
  apply RegSet.union_2; auto.
- destruct sl; auto; apply H; exact I.
Qed.

Lemma agree_undef_caller_save_regs:
  forall ls ls', agree callee_save_live ls ls' ->
  agree_all (undef_caller_save_regs ls) (undef_caller_save_regs ls').
Proof.
  unfold agree_all, undef_caller_save_regs; intros. destruct l as [r | sl ofs ty].
- destruct (is_callee_save r) eqn:C; auto. apply H; simpl. apply In_callee_save_live; auto.
- destruct sl; auto; apply H; exact I.
Qed.

Lemma agree_call_arguments:
  forall sg ls ls', agree (call_live sg) ls ls' ->
  map (fun p => Locmap.getpair p ls) (loc_arguments sg) =
  map (fun p => Locmap.getpair p ls') (loc_arguments sg).
Proof.
  intros. apply list_map_exten; intros p IN. symmetry.
  assert (A: forall l, In l (regs_of_rpair p) -> ls l = ls' l).
  { intros. apply H. destruct l; simpl; auto. apply RegSet.union_3. apply In_param_live.
    eapply in_regs_of_rpairs; eauto. }
  destruct p; simpl in *. rewrite A; auto. rewrite ! A; auto.
Qed.

Lemma agree_all_undef_regs:
  forall rl ls ls', agree_all ls ls' -> agree_all (undef_regs rl ls) (undef_regs rl ls').
Proof.
  unfold agree_all; intros. apply undef_regs_pointwise; auto.
Qed.

Lemma eval_builtin_arg_pointwise:
  forall (A: Type) ge (e e': A -> val) sp m a v,
  eval_builtin_arg ge e sp m a v -> (forall x, e x = e' x) -> eval_builtin_arg ge e' sp m a v.
Proof.
  induction 1; intros EQ; try rewrite EQ; econstructor; eauto.
Qed.

Lemma eval_builtin_args_pointwise:
  forall (A: Type) ge (e e': A -> val) sp m al vl,
  eval_builtin_args ge e sp m al vl -> (forall x, e x = e' x) -> eval_builtin_args ge e' sp m al vl.
Proof.
  unfold eval_builtin_args; induction 1; intros; constructor; auto.
  eapply eval_builtin_arg_pointwise; eauto.
Qed.

Lemma undef_regs_reg_other:
  forall r rl ls, ~In r rl -> undef_regs rl ls (R r) = ls (R r).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. tauto. red. intuition congruence.
Qed.

Lemma undef_regs_reg_same:
  forall r rl ls, In r rl -> undef_regs rl ls (R r) = Vundef.
Proof.
  induction rl; simpl; intros. contradiction.
  destruct (mreg_eq a r). subst. apply Locmap.gss_reg.
  rewrite Locmap.gso. apply IHrl. destruct H; congruence. red; congruence.
Qed.

Lemma undef_regs_slot:
  forall rl ls sl ofs ty, undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty).
Proof.
  induction rl; simpl; intros. auto. rewrite Locmap.gso; auto. exact I.
Qed.

(** * Properties of the transformation *)

Section TRANSF.

Variable fsig: signature.
Variable lm: labelmap.

(** A relational specification of the transformation: any
  instruction can be kept, and fusable pairs can be fused. *)

Inductive tr_spec: code -> code -> Prop :=
  | tr_nil:
      tr_spec nil nil
  | tr_cons: forall i c tc,
      tr_spec c tc ->
      tr_spec (i :: c) (i :: tc)
  | tr_fuse: forall chunk addr args t op args2 res c tc,
      tr_spec c tc ->
      fusable chunk addr t op args2 res (live fsig lm c) = true ->
      tr_spec (Lload chunk addr args t :: Lop op args2 res :: c)
              (Lloadop op chunk addr args res :: tc).

Lemma tr_correct:
  forall c,
  let '(tc, s, s', ok) := tr fsig lm c in
  tr_spec c tc /\ s = live fsig lm c
  /\ s' = (match c with nil => RegSet.empty | _ :: c' => live fsig lm c' end)
  /\ (ok = true -> forall lbl c', find_label lbl c = Some c' ->
                   forall r, RegSet.In r (live fsig lm c') -> RegSet.In r (live_at lm lbl)).
Proof.
  induction c as [|i c1 IH].
- simpl. split. constructor. split; auto. split; auto. intros; discriminate.
- simpl. destruct (tr fsig lm c1) as [[[tc1 s1] s1'] ok1].
  destruct IH as (A & B & C & D). subst s1.
  assert (DFLT:
    tr_spec (i :: c1) (i :: tc1) /\ transfer fsig lm i (live fsig lm c1) = transfer fsig lm i (live fsig lm c1)
    /\ live fsig lm c1 = live fsig lm c1
    /\ (ok1 && check_label lm i (live fsig lm c1) = true -> forall lbl c', find_label lbl (i :: c1) = Some c' ->
          forall r, RegSet.In r (live fsig lm c') -> RegSet.In r (live_at lm lbl))).
  { split. constructor; auto. split. auto. split. auto.
    intros OK lbl c' FL. apply andb_prop in OK. destruct OK as [OK1 OK2].
    simpl in FL. generalize (is_label_correct lbl i). destruct (is_label lbl i); intros IL.
    + inv FL. simpl in OK2. apply RegSet.subset_2 in OK2. auto.
    + eapply D; eauto. }
  destruct i; auto.
  destruct c1 as [|i2 c2]; auto. destruct i2; auto.
  destruct tc1 as [|ti tc2]; auto. destruct ti; auto.
  destruct (fusable m a m0 o l0 m1 s1') eqn:FUS; auto.
  inv A.
  split. constructor; auto. split. auto. split. auto.
  intros OK lbl c' FL. simpl in FL. eapply D; eauto.
Qed.

Lemma tr_code_spec: forall c, tr_spec c (tr_code fsig lm c).
Proof.
  intros. generalize (tr_correct c). unfold tr_code. destruct (tr fsig lm c) as [[[tc s] s'] ok].
  simpl. tauto.
Qed.

Lemma tr_ok_valid:
  forall c, tr_ok fsig lm c = true ->
  forall lbl c', find_label lbl c = Some c' ->
  forall r, RegSet.In r (live fsig lm c') -> RegSet.In r (live_at lm lbl).
Proof.
  intros c. generalize (tr_correct c). unfold tr_ok. destruct (tr fsig lm c) as [[[tc s] s'] ok].
  simpl. intros (A & B & C & D). auto.
Qed.

Lemma fusable_inv:
  forall chunk addr t op args2 res after,
  fusable chunk addr t op args2 res after = true ->
  args2 = res :: t :: nil /\ t <> res /\ ~In res (destroyed_by_load chunk addr) /\ ~RegSet.In t after.
Proof.
  unfold fusable; intros.
  destruct args2 as [|rd [|t' [|]]]; try discriminate.
  destruct (mreg_eq rd res); destruct (mreg_eq t' t); destruct (mreg_eq t res);
  destruct (loadop_candidate op chunk);
  destruct (In_dec mreg_eq res (destroyed_by_load chunk addr));
  destruct (RegSet.mem t after) eqn:MEM; simpl in H; try discriminate.
  subst. split; auto. split; auto. split; auto.
  intro IN. apply RegSet.mem_1 in IN. congruence.
Qed.

Lemma tr_spec_find_label:
  forall c tc, tr_spec c tc ->
  forall lbl c', find_label lbl c = Some c' ->
  exists tc', find_label lbl tc = Some tc' /\ tr_spec c' tc'.
Proof.
  induction 1; simpl; intros.
- discriminate.
- destruct (is_label lbl i). inv H0. exists tc; auto. eauto.
- eauto.
Qed.

End TRANSF.

Lemma tr_empty_ok:
  forall sg c, tr_ok sg (PTree.empty _) c = true.
Proof.
  intros sg. unfold tr_ok. induction c as [|i c1 IH]; simpl. auto.
  destruct (tr sg (PTree.empty RegSet.t) c1) as [[[tc1 s1] s1'] ok1]. simpl in IH. subst ok1.
  assert (CL: check_label (PTree.empty RegSet.t) i s1 = true).
  { destruct i; auto. simpl. apply RegSet.subset_1. red; intros.
    unfold live_at. rewrite PTree.gempty. apply In_all_live. }
  destruct i; simpl; try rewrite CL; auto.
  destruct c1 as [|i2 c2]; auto. destruct i2; auto.
  destruct tc1 as [|ti tc2]; auto. destruct ti; auto.
  destruct (fusable m a m0 o l0 m1 s1'); auto.
Qed.

(** The label map used for a function, and its validity. *)

Definition fun_lm (f: function) : labelmap := choose_labelmap f.(fn_sig) f.(fn_code).

Lemma fun_lm_valid:
  forall f lbl c',
  find_label lbl f.(fn_code) = Some c' ->
  forall r, RegSet.In r (live (fn_sig f) (fun_lm f) c') -> RegSet.In r (live_at (fun_lm f) lbl).
Proof.
  intros f. unfold fun_lm, choose_labelmap.
  set (lm0 := iterate (fn_sig f) num_iterations (fn_code f) (initial_labelmap (fn_code f))).
  destruct (tr_ok (fn_sig f) lm0 (fn_code f)) eqn:OK.
- apply tr_ok_valid; auto.
- apply tr_ok_valid. apply tr_empty_ok.
Qed.

Lemma transf_function_spec:
  forall f, tr_spec (fn_sig f) (fun_lm f) f.(fn_code) (transf_function f).(fn_code).
Proof.
  intros. unfold transf_function, fun_lm. simpl. apply tr_code_spec.
Qed.

(** * Simulation *)

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.

Lemma sig_function_translated:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros ls ls' f,
  find_function ge ros ls = Some f ->
  (forall r, ros = inl r -> ls (R r) = ls' (R r)) ->
  find_function tge ros ls' = Some (transf_fundef f).
Proof.
  unfold find_function; intros; destruct ros; simpl.
  rewrite <- H0 by auto. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

Lemma eval_addressing_preserved_2:
  forall sp addr vl, eval_addressing tge sp addr vl = eval_addressing ge sp addr vl.
Proof.
  intros. apply eval_addressing_preserved. exact symbols_preserved.
Qed.

Lemma eval_operation_preserved_2:
  forall sp op vl m, eval_operation tge sp op vl m = eval_operation ge sp op vl m.
Proof.
  intros. apply eval_operation_preserved. exact symbols_preserved.
Qed.

Inductive match_frames: stackframe -> stackframe -> Prop :=
  | match_frames_intro: forall f sp ls c ls' tc,
      tr_spec (fn_sig f) (fun_lm f) c tc ->
      agree callee_save_live ls ls' ->
      match_frames (Stackframe f sp ls c) (Stackframe (transf_function f) sp ls' tc).

Inductive match_states: state -> state -> Prop :=
  | match_states_regular: forall s f sp c ls m ts tc ls'
        (STK: list_forall2 match_frames s ts)
        (TR: tr_spec (fn_sig f) (fun_lm f) c tc)
        (AG: agree (live (fn_sig f) (fun_lm f) c) ls ls'),
      match_states (State s f sp c ls m)
                   (State ts (transf_function f) sp tc ls' m)
  | match_states_pending: forall s f sp chunk addr args t op args2 res c2 tc2 ls0 ls1 ls' m a v ts
        (STK: list_forall2 match_frames s ts)
        (TR: tr_spec (fn_sig f) (fun_lm f) c2 tc2)
        (FUS: fusable chunk addr t op args2 res (live (fn_sig f) (fun_lm f) c2) = true)
        (EA: eval_addressing ge sp addr (reglist ls0 args) = Some a)
        (LD: Mem.loadv chunk m a = Some v)
        (LS1: ls1 = Locmap.set (R t) v (undef_regs (destroyed_by_load chunk addr) ls0))
        (AG: agree (live (fn_sig f) (fun_lm f) (Lload chunk addr args t :: Lop op args2 res :: c2)) ls0 ls'),
      match_states (State s f sp (Lop op args2 res :: c2) ls1 m)
                   (State ts (transf_function f) sp (Lloadop op chunk addr args res :: tc2) ls' m)
  | match_states_call: forall s fd ls m ts ls'
        (STK: list_forall2 match_frames s ts)
        (AG: agree (call_live (funsig fd)) ls ls'),
      match_states (Callstate s fd ls m) (Callstate ts (transf_fundef fd) ls' m)
  | match_states_return: forall s ls m ts ls'
        (STK: list_forall2 match_frames s ts)
        (AG: agree_all ls ls'),
      match_states (Returnstate s ls m) (Returnstate ts ls' m).

Definition measure (S: state) : nat :=
  match S with
  | State _ _ _ c _ _ => length c
  | _ => O
  end.

Lemma parent_locset_match:
  forall s ts, list_forall2 match_frames s ts -> agree callee_save_live (parent_locset s) (parent_locset ts).
Proof.
  induction 1; simpl. red; auto. inv H; auto.
Qed.

Lemma find_label_transl:
  forall f lbl c,
  find_label lbl f.(fn_code) = Some c ->
  exists tc, find_label lbl (transf_function f).(fn_code) = Some tc /\ tr_spec (fn_sig f) (fun_lm f) c tc.
Proof.
  intros. eapply tr_spec_find_label; eauto. apply transf_function_spec.
Qed.

Lemma agree_goto:
  forall f lbl c ls ls',
  find_label lbl f.(fn_code) = Some c ->
  agree (live_at (fun_lm f) lbl) ls ls' ->
  agree (live (fn_sig f) (fun_lm f) c) ls ls'.
Proof.
  intros. eapply agree_incl; eauto. intros; eapply fun_lm_valid; eauto.
Qed.

Ltac Regular :=
  econstructor; split; [apply plus_one; econstructor; eauto | econstructor; eauto].

Theorem transf_step_correct:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS;
  (* Discard the pending states, except for the [Lop] step *)
  try (match goal with [ H: Lop _ _ _ :: _ = _ :: _ |- _ ] => discriminate H | _ => idtac end).

- (* getstack *)
  inv TR. simpl in AG. left; Regular.
  rewrite (agree_slot _ _ _ _ _ _ AG). apply agree_set_remove.
  apply agree_undef_regs; auto.
- (* setstack *)
  inv TR. simpl in AG. left; Regular.
  rewrite (agree_reg _ _ _ src AG) by (apply RegSet.add_1; auto).
  apply agree_set. apply agree_undef_regs. eapply agree_incl; eauto.
  intros; apply RegSet.add_2; auto.
- (* op *)
  inv TR.
  + simpl in AG. left; econstructor; split.
    apply plus_one. econstructor.
    rewrite eval_operation_preserved_2. rewrite <- (agree_add_regs_reglist _ _ _ _ AG). eauto.
    eauto.
    econstructor; eauto.
    apply agree_set_remove. apply agree_undef_regs. eapply agree_add_regs; eauto.
- (* op, completing a fused pair *)
  exploit fusable_inv; eauto. intros (ARGS & NE & NDBL & DEAD). subst args.
  cbn [live transfer] in AG.
  assert (RES: ls0 (R res) = ls' (R res)).
  { apply (agree_reg _ _ _ res AG). apply (proj2 (In_add_regs _ _ _)). right. apply RegSet.remove_2; auto.
    apply (proj2 (In_add_regs _ _ _)). left; simpl; auto. }
  assert (EA': eval_addressing tge sp addr (reglist ls' args0) = Some a).
  { rewrite eval_addressing_preserved_2. rewrite <- (agree_add_regs_reglist _ _ _ _ AG). auto. }
  simpl in H.
  rewrite Locmap.gss_reg in H. rewrite Locmap.gso in H by (red; auto).
  rewrite undef_regs_reg_other in H by auto.
  left; econstructor; split.
  apply plus_one. eapply exec_Lloadop. eexact EA'. eexact LD.
  rewrite eval_operation_preserved_2. rewrite <- RES. eexact H. eauto.
  econstructor; eauto.
  apply agree_set_remove. intros l LIVE. destruct l as [r|sl ofs ty].
  + simpl in LIVE. assert (NR: r <> res) by (intro; subst; eapply RegSet.remove_1; eauto).
    apply RegSet.remove_3 in LIVE.
    assert (NT: r <> t) by (intro; subst; contradiction).
    destruct (In_dec mreg_eq r (destroyed_by_op op)) as [IN1|NIN1].
    rewrite (undef_regs_reg_same r (destroyed_by_op op)) by auto.
    rewrite (undef_regs_reg_same r (_ ++ _)) by (apply in_or_app; auto). auto.
    destruct (In_dec mreg_eq r (destroyed_by_load chunk addr)) as [IN2|NIN2].
    rewrite (undef_regs_reg_same r (_ ++ _)) by (apply in_or_app; auto).
    rewrite (undef_regs_reg_other r (destroyed_by_op op)) by auto.
    rewrite Locmap.gso by (red; auto).
    rewrite (undef_regs_reg_same r (destroyed_by_load chunk addr)) by auto. auto.
    rewrite (undef_regs_reg_other r (destroyed_by_op op)) by auto.
    rewrite (undef_regs_reg_other r (_ ++ _)) by (rewrite in_app_iff; tauto).
    rewrite Locmap.gso by (red; auto).
    rewrite (undef_regs_reg_other r (destroyed_by_load chunk addr)) by auto.
    apply (agree_reg _ _ _ r AG). apply (proj2 (In_add_regs _ _ _)). right. apply RegSet.remove_2; auto.
    apply (proj2 (In_add_regs _ _ _)). right. apply RegSet.remove_2; auto.
  + rewrite ! undef_regs_slot. rewrite Locmap.gso by exact I. rewrite undef_regs_slot.
    apply agree_slot with (s := live (fn_sig f) (fun_lm f) (Lload chunk addr args0 t :: Lop op (res :: t :: nil) res :: b)).
    exact AG.
- (* load *)
  inv TR.
  + simpl in AG. left; econstructor; split.
    apply plus_one. econstructor.
    rewrite eval_addressing_preserved_2. rewrite <- (agree_add_regs_reglist _ _ _ _ AG). eauto.
    eauto. eauto.
    econstructor; eauto.
    apply agree_set_remove. apply agree_undef_regs. eapply agree_add_regs; eauto.
  + (* the start of a fused pair *)
    right. split. simpl; lia. split. auto.
    eapply match_states_pending; eauto.
- (* loadop *)
  inv TR. simpl in AG. left; econstructor; split.
  apply plus_one. econstructor.
  rewrite eval_addressing_preserved_2. rewrite <- (agree_add_regs_reglist _ _ _ _ AG). eauto.
  eauto.
  rewrite eval_operation_preserved_2.
  rewrite <- (agree_reg _ _ _ res AG). eauto.
  apply (proj2 (In_add_regs _ _ _)). right. apply RegSet.add_1; auto.
  eauto.
  econstructor; eauto.
  apply agree_set_remove. apply agree_undef_regs. eapply agree_incl. eapply agree_add_regs; eauto.
  intros. apply RegSet.add_2. eapply RegSet.remove_3; eauto.
- (* store *)
  inv TR. simpl in AG. left; econstructor; split.
  apply plus_one. econstructor.
  rewrite eval_addressing_preserved_2. rewrite <- (agree_add_regs_reglist _ _ _ _ AG). eauto.
  rewrite <- (agree_reg _ _ _ src AG). eauto.
  apply (proj2 (In_add_regs _ _ _)). right. apply RegSet.add_1; auto.
  eauto.
  econstructor; eauto.
  apply agree_undef_regs. eapply agree_incl. eapply agree_add_regs; eauto.
  intros; apply RegSet.add_2; auto.
- (* call *)
  inv TR. simpl in AG.
  left; econstructor; split.
  apply plus_one. econstructor. eapply find_function_translated; eauto.
  intros; subst ros. apply AG; simpl. apply RegSet.union_3, RegSet.union_3. simpl; apply RegSet.add_1; auto.
  symmetry; apply sig_function_translated.
  econstructor; eauto. constructor; auto. constructor; auto.
  eapply agree_incl; eauto. intros; apply RegSet.union_2; auto.
  eapply agree_incl; eauto. unfold call_live; intros r0 IN.
  apply RegSet.union_1 in IN. destruct IN as [IN|IN]. apply RegSet.union_2; auto.
  apply RegSet.union_3, RegSet.union_2; auto.
- (* tailcall *)
  inv TR. simpl in AG.
  assert (AR: agree (call_live (funsig f')) (return_regs (parent_locset s) rs) (return_regs (parent_locset ts) ls')).
  { eapply agree_return_regs_call; eauto. apply parent_locset_match; auto. }
  left; econstructor; split.
  apply plus_one. econstructor. eauto. eapply find_function_translated; eauto.
  intros; subst ros. unfold return_regs. destruct (is_callee_save r) eqn:C.
  apply parent_locset_match; auto. simpl. apply In_callee_save_live; auto.
  apply AG; simpl. apply RegSet.union_3. simpl; apply RegSet.add_1; auto.
  symmetry; apply sig_function_translated. eauto.
  econstructor; eauto.
- (* builtin *)
  inv TR. simpl in AG. apply agree_all_live in AG.
  left; econstructor; split.
  apply plus_one. econstructor.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  eapply eval_builtin_args_pointwise; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eauto.
  econstructor; eauto. apply agree_all_agree.
  apply agree_all_setres. apply agree_all_undef_regs. auto.
- (* label *)
  inv TR. simpl in AG. left; Regular.
- (* goto *)
  inv TR. simpl in AG.
  exploit find_label_transl; eauto. intros (tc' & A & B).
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto. eapply agree_goto; eauto.
- (* cond true *)
  inv TR. simpl in AG.
  exploit find_label_transl; eauto. intros (tc' & A & B).
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_true.
  rewrite <- (agree_add_regs_reglist _ _ _ _ AG). eauto. eauto. eauto.
  econstructor; eauto. apply agree_undef_regs.
  eapply agree_goto; eauto. eapply agree_incl. eapply agree_add_regs; eauto.
  intros; apply RegSet.union_2; auto.
- (* cond false *)
  inv TR. simpl in AG.
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_false.
  rewrite <- (agree_add_regs_reglist _ _ _ _ AG). eauto. eauto.
  econstructor; eauto. apply agree_undef_regs.
  eapply agree_incl. eapply agree_add_regs; eauto.
  intros; apply RegSet.union_3; auto.
- (* jumptable *)
  inv TR. simpl in AG.
  exploit find_label_transl; eauto. intros (tc' & A & B).
  left; econstructor; split.
  apply plus_one. eapply exec_Ljumptable.
  rewrite <- (agree_reg _ _ _ arg AG). eauto. apply RegSet.add_1; auto.
  eauto. eauto. eauto.
  econstructor; eauto. apply agree_undef_regs.
  eapply agree_goto; eauto. eapply agree_incl; eauto.
  intros. apply RegSet.add_2. eapply In_live_at_labels; eauto. eapply list_nth_z_in; eauto.
- (* return *)
  inv TR. simpl in AG.
  left; econstructor; split.
  apply plus_one. econstructor. eauto.
  econstructor; eauto. simpl. apply agree_return_regs_res; auto. apply parent_locset_match; auto.
- (* internal function *)
  left; econstructor; split.
  apply plus_one. econstructor. simpl; eauto. eauto.
  simpl. econstructor; eauto. apply transf_function_spec.
  apply agree_all_agree. apply agree_all_undef_regs. apply agree_call_regs. auto.
- (* external function *)
  simpl in AG.
  left; econstructor; split.
  apply plus_one. eapply exec_function_external. reflexivity.
  rewrite <- (agree_call_arguments _ _ _ AG).
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eauto.
  econstructor; eauto.
  apply agree_all_setpair. apply agree_undef_caller_save_regs.
  eapply agree_incl; eauto. intros; apply RegSet.union_2; auto.
- (* return *)
  inv STK. inv H1.
  left; econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. apply agree_all_agree; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  econstructor; split.
  eapply initial_state_intro with (f := transf_fundef f).
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite (match_program_main TRANSL), symbols_preserved; eauto.
  apply function_ptr_translated; auto.
  rewrite sig_function_translated. auto.
  constructor; auto. constructor. red; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STK. econstructor.
  destruct (map_rpair R (loc_result signature_main)); simpl in *; rewrite <- ! AG; auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct.
Qed.

End PRESERVATION.
