(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for loop rotation. *)

Require Import Coqlib Maps AST Linking Integers Values Memory Globalenvs.
Require Import Events Smallstep.
Require Import Op Registers RTL Looprot.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

(** * Properties of the validated transformation *)

(** [cor n' n] means that node [n'] of the transformed function is a copy
  of node [n] of the original function. *)

Record tr_function (f tf: function) (cor: node -> node -> Prop) : Prop := {
  tr_sig: tf.(fn_sig) = f.(fn_sig);
  tr_params: tf.(fn_params) = f.(fn_params);
  tr_stacksize: tf.(fn_stacksize) = f.(fn_stacksize);
  tr_entry: cor tf.(fn_entrypoint) f.(fn_entrypoint);
  tr_code: forall n' n i,
    cor n' n -> f.(fn_code)!n = Some i ->
    exists l i', tf.(fn_code)!n' = Some i' /\ set_succs i l = Some i'
                 /\ list_forall2 cor l (successors_instr i)
}.

Lemma set_succs_refl:
  forall i, set_succs i (successors_instr i) = Some i.
Proof.
  destruct i; simpl; auto. rewrite Nat.eqb_refl; auto.
Qed.

Lemma forall2b_correct:
  forall (A B: Type) (p: A -> B -> bool) l1 l2,
  forall2b p l1 l2 = true -> list_forall2 (fun a b => p a b = true) l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros; try discriminate.
  constructor.
  InvBooleans. constructor; auto.
Qed.

Lemma transf_function_tr:
  forall f, exists cor, tr_function f (transf_function f) cor.
Proof.
  intros. unfold transf_function. destruct (rotate_oracle f) as [info entry].
  destruct (check_function f info entry) eqn:C.
- exists (fun n' n => corresp info n' n = true).
  unfold check_function in C. InvBooleans.
  rewrite PTree_Properties.for_all_correct in H.
  constructor; simpl; auto.
  intros n' n i COR CODE. unfold corresp in COR.
  destruct (info!n') as [[m l]|] eqn:INFO; try discriminate.
  destruct (peq m n); try discriminate. subst m.
  specialize (H n' (n, l) INFO). unfold check_node in H; simpl in H. rewrite CODE in H.
  destruct (set_succs i l) as [i'|] eqn:SET; try discriminate.
  exists l, i'; split.
  rewrite PTree.gmap_filter1. rewrite INFO. unfold transf_node; simpl. rewrite CODE; auto.
  split. auto.
  eapply forall2b_correct; eauto.
- exists (fun n' n => n' = n). constructor; auto.
  intros. subst n'. exists (successors_instr i), i; split. auto. split.
  apply set_succs_refl.
  generalize (successors_instr i). induction l; constructor; auto.
Qed.

Lemma list_nth_z_forall2:
  forall (A B: Type) (P: A -> B -> Prop) l1 l2,
  list_forall2 P l1 l2 ->
  forall n x2, list_nth_z l2 n = Some x2 ->
  exists x1, list_nth_z l1 n = Some x1 /\ P x1 x2.
Proof.
  induction 1; simpl; intros.
  discriminate.
  destruct (zeq n 0). inv H1. exists a1; auto. eauto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

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

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; simpl; auto.
  destruct (transf_function_tr f) as (cor & TR). apply (tr_sig _ _ _ TR).
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Inductive match_frames: stackframe -> stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs tf pc' cor
        (TR: tr_function f tf cor)
        (COR: cor pc' pc),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res tf sp pc' rs).

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' tf pc' cor
        (STACKS: list_forall2 match_frames stk stk')
        (TR: tr_function f tf cor)
        (COR: cor pc' pc),
      match_states (State stk f sp pc rs m)
                   (State stk' tf sp pc' rs m)
  | match_callstates: forall stk fd args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m)
                   (Callstate stk' (transf_fundef fd) args m)
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).

Ltac EVALOP :=
  match goal with
  | [ E: eval_operation ge _ _ _ _ = Some _ |- _ ] =>
      rewrite <- E; apply eval_operation_preserved; exact symbols_preserved
  end.

Ltac EVALADDR :=
  match goal with
  | [ E: eval_addressing ge _ _ _ = Some _ |- _ ] =>
      rewrite <- E; apply eval_addressing_preserved; exact symbols_preserved
  end.

Ltac TRI :=
  match goal with
  | [ TR: tr_function ?f ?tf ?cor, COR: ?cor ?pc' ?pc, H: (fn_code ?f)!?pc = Some ?i |- _ ] =>
      let l := fresh "l" in let i' := fresh "i'" in
      let TI := fresh "TI" in let SET := fresh "SET" in let FA := fresh "FA" in
      destruct (tr_code _ _ _ TR _ _ _ COR H) as (l & i' & TI & SET & FA);
      simpl in FA;
      repeat (match goal with
              | [ H: list_forall2 _ _ (_ :: _) |- _ ] => inv H
              | [ H: list_forall2 _ _ nil |- _ ] => inv H
              end);
      simpl in SET; inv SET
  end.

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS.
- (* nop *)
  TRI. econstructor; split. eapply exec_Inop; eauto. econstructor; eauto.
- (* op *)
  TRI. econstructor; split. eapply exec_Iop; eauto.
  try EVALOP.
  econstructor; eauto.
- (* load *)
  TRI. econstructor; split. eapply exec_Iload; eauto.
  try EVALADDR.
  econstructor; eauto.
- (* store *)
  TRI. econstructor; split. eapply exec_Istore; eauto.
  try EVALADDR.
  econstructor; eauto.
- (* call *)
  TRI. econstructor; split.
  eapply exec_Icall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto.
  apply sig_preserved.
  constructor. constructor; auto. econstructor; eauto.
- (* tailcall *)
  TRI. econstructor; split.
  eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto.
  apply sig_preserved.
  rewrite (tr_stacksize _ _ _ TR); eauto.
  constructor; auto.
- (* builtin *)
  TRI. econstructor; split. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
- (* cond *)
  TRI. econstructor; split. eapply exec_Icond; eauto.
  econstructor; eauto. destruct b; auto.
- (* jumptable *)
  destruct (tr_code _ _ _ TR _ _ _ COR H) as (l & i' & TI & SET & FA).
  simpl in SET. destruct (Nat.eqb (length tbl) (length l)); inv SET.
  exploit list_nth_z_forall2; eauto. intros (pc'' & A & B).
  econstructor; split. eapply exec_Ijumptable; eauto.
  econstructor; eauto.
- (* return *)
  TRI. econstructor; split. eapply exec_Ireturn; eauto.
  rewrite (tr_stacksize _ _ _ TR); eauto.
  constructor; auto.
- (* internal function *)
  simpl. destruct (transf_function_tr f) as (cor & TR).
  econstructor; split.
  eapply exec_function_internal; eauto.
  rewrite (tr_sig _ _ _ TR); auto.
  rewrite (tr_stacksize _ _ _ TR); eauto.
  rewrite (tr_params _ _ _ TR). econstructor; eauto. apply (tr_entry _ _ _ TR).
- (* external function *)
  econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inv STACKS. inv H1.
  econstructor; split.
  eapply exec_return.
  econstructor; eauto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split.
  econstructor.
    eapply (Genv.init_mem_transf TRANSL); eauto.
    rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
    eapply function_ptr_translated; eauto.
    rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
