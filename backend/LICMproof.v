(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for loop-invariant code motion. *)

Require Import Coqlib Maps AST Linking Integers Values Memory Globalenvs.
Require Import Events Smallstep.
Require Import Op Registers RTL LICMop LICM.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

(** * Auxiliary lemmas *)

Lemma add_instrs_notin:
  forall l c n, ~In n (map fst l) -> (add_instrs c l)!n = c!n.
Proof.
  unfold add_instrs; induction l as [ | [p i] l]; simpl; intros.
  auto.
  rewrite IHl by tauto. apply PTree.gso. intuition congruence.
Qed.

Lemma add_instrs_in:
  forall l c n i, list_norepet (map fst l) -> In (n, i) l -> (add_instrs c l)!n = Some i.
Proof.
  induction l as [ | [p j] l]; simpl; intros.
  contradiction.
  inv H. destruct H0.
- inv H. transitivity ((PTree.set n i c)!n).
  apply add_instrs_notin; auto. apply PTree.gss.
- apply IHl; auto.
Qed.

Lemma norepet_flat_map:
  forall (A B: Type) (g: A -> list B) l x,
  list_norepet (flat_map g l) -> In x l -> list_norepet (g x).
Proof.
  induction l; simpl; intros. contradiction.
  rewrite list_norepet_app in H. destruct H as (A1 & A2 & A3).
  destruct H0. subst; auto. auto.
Qed.

Lemma norepet_flat_map_disjoint:
  forall (A B: Type) (g: A -> list B) l x y,
  list_norepet (flat_map g l) -> In x l -> In y l -> x <> y ->
  list_disjoint (g x) (g y).
Proof.
  induction l; simpl; intros. contradiction.
  rewrite list_norepet_app in H. destruct H as (A1 & A2 & A3).
  destruct H0; destruct H1; subst.
- congruence.
- red; intros. apply A3; auto. apply in_flat_map. exists y; auto.
- red; intros. intro; subst. eelim A3; eauto. apply in_flat_map. exists x; auto.
- eauto.
Qed.

Lemma norepet_map_inj:
  forall (A B: Type) (g: A -> B) l x y,
  list_norepet (map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  induction l; simpl; intros. contradiction.
  inv H. destruct H0; destruct H1; subst; auto.
- elim H5. rewrite H2. apply in_map; auto.
- elim H5. rewrite <- H2. apply in_map; auto.
Qed.

Lemma redirect_cases:
  forall inn lps s,
  (redirect inn lps s = s /\
   forall L, In L lps -> lp_header L = s -> inn L = false -> False)
  \/ (exists L, In L lps /\ lp_header L = s /\ inn L = false /\
                redirect inn lps s = preheader L).
Proof.
  induction lps as [ | L0 lps]; simpl; intros.
- left; split; auto.
- destruct (peq (lp_header L0) s); destruct (inn L0) eqn:INN; simpl.
  + destruct (IHlps s) as [[A B] | (L & A & B & C & D)].
    left; split; auto. intros L [EQ | IN] H1 H2. subst; congruence. eauto.
    right; exists L; auto.
  + right; exists L0; auto.
  + destruct (IHlps s) as [[A B] | (L & A & B & C & D)].
    left; split; auto. intros L [EQ | IN] H1 H2. subst; congruence. eauto.
    right; exists L; auto.
  + destruct (IHlps s) as [[A B] | (L & A & B & C & D)].
    left; split; auto. intros L [EQ | IN] H1 H2. subst; congruence. eauto.
    right; exists L; auto.
Qed.

Lemma setres_other:
  forall res (v: val) (rs: regset) r,
  ~In r (params_of_builtin_res res) -> (regmap_setres res v rs)#r = rs#r.
Proof.
  destruct res; simpl; intros; auto. apply Regmap.gso. intuition.
Qed.

(** * Structural properties of the transformation *)

Record tr_function (f: function) (loops: list loop_info) (repl: PTree.t reg)
                   (tf: function) : Prop := {
  tr_sig: tf.(fn_sig) = f.(fn_sig);
  tr_params: tf.(fn_params) = f.(fn_params);
  tr_stacksize: tf.(fn_stacksize) = f.(fn_stacksize);
  tr_entry: tf.(fn_entrypoint) = redirect (fun _ => false) loops f.(fn_entrypoint);
  tr_code: forall n i,
    f.(fn_code)!n = Some i -> tf.(fn_code)!n = Some (transf_instr loops repl n i);
  tr_chain: forall p i,
    In (p, i) (flat_map loop_instrs loops) -> tf.(fn_code)!p = Some i;
  tr_headers: list_norepet (map lp_header loops);
  tr_tregs: list_norepet (flat_map tregs loops);
  tr_hoists: forall t op args,
    In (t, op, args) (flat_map hoists loops) ->
    op_safe op (length args) = true /\ op_depends_on_memory op = false
    /\ Plt (max_reg_function f) t
    /\ (forall a, In a args -> Ple a (max_reg_function f));
  tr_inv: forall L n i,
    In L loops -> in_body L n = true -> f.(fn_code)!n = Some i ->
    forall t op args, In (t, op, args) (hoists L) ->
    forall r, In r (defs_all i) -> r <> t /\ ~In r args;
  tr_edges: forall n i s L,
    f.(fn_code)!n = Some i -> In s (successors_instr i) -> In L loops ->
    in_body L s = true -> in_body L n = false -> s = lp_header L;
  tr_entry_ok: forall L,
    In L loops -> in_body L f.(fn_entrypoint) = true ->
    f.(fn_entrypoint) = lp_header L;
  tr_repl: forall n t op args res s,
    repl!n = Some t -> f.(fn_code)!n = Some (Iop op args res s) ->
    exists L, In L loops /\ in_body L n = true /\ In (t, op, args) (hoists L)
}.

Lemma check_hoist_sound:
  forall mr t op args,
  check_hoist mr (t, op, args) = true ->
  op_safe op (length args) = true /\ op_depends_on_memory op = false
  /\ Plt mr t /\ (forall a, In a args -> Ple a mr).
Proof.
  intros until args. unfold check_hoist. cbv beta iota.
  rewrite ! andb_true_iff, negb_true_iff, forallb_forall, Pos.ltb_lt.
  intros (((A & B) & C) & D). split; auto. split; auto. split; auto.
  intros. apply Pos.leb_le; auto.
Qed.

Lemma map_succ_id:
  forall i, map_succ (fun s => s) i = i.
Proof.
  destruct i; simpl; auto. rewrite map_id; auto.
Qed.

Lemma transf_function_tr:
  forall f, exists loops repl, tr_function f loops repl (transf_function f).
Proof.
  intros. unfold transf_function. destruct (licm_oracle f) as [lps repl].
  set (loops := map (fun x => let '(h, b, ch) := x in mkloop h b ch) lps).
  destruct (check_function f loops repl) eqn:C.
- exists loops, repl. unfold check_function in C.
  rewrite ! andb_true_iff in C.
  destruct C as [[[[[[[[HDR0 NOREPCHAIN0] CHAINFRESH] TREGS0] HOISTS] INV] EDGES] ENTRY] REPL].
  assert (HDR := proj_sumbool_true _ HDR0).
  assert (NOREPCHAIN := proj_sumbool_true _ NOREPCHAIN0).
  assert (TREGS := proj_sumbool_true _ TREGS0).
  clear HDR0 NOREPCHAIN0 TREGS0.
  constructor; simpl; auto.
  + (* code *)
    intros. unfold transf_code. rewrite add_instrs_notin. rewrite PTree.gmap. rewrite H; auto.
    red; intros. exploit list_in_map_inv; eauto. intros ([p i'] & EQ & IN). simpl in EQ; subst p.
    rewrite forallb_forall in CHAINFRESH. exploit CHAINFRESH; eauto. simpl. rewrite H. congruence.
  + (* chain *)
    intros. unfold transf_code. apply add_instrs_in; auto.
  + (* hoists *)
    intros t op args IN. rewrite forallb_forall in HOISTS.
    apply check_hoist_sound. apply HOISTS; auto.
  + (* invariance *)
    intros. rewrite forallb_forall in INV. specialize (INV L H).
    rewrite forallb_forall in INV. exploit INV. apply PTree.elements_correct; eauto.
    unfold check_invariant; simpl. rewrite H0; simpl. rewrite forallb_forall. intros X.
    exploit X; eauto. simpl. unfold disjointb. rewrite forallb_forall. intros Y.
    exploit Y; eauto. destruct (In_dec peq r (t :: args)); simpl; try congruence.
    intros _. simpl in n0. intuition.
  + (* edges *)
    intros. rewrite forallb_forall in EDGES. exploit EDGES. apply PTree.elements_correct; eauto.
    unfold check_edges; simpl. rewrite forallb_forall. intros X. exploit X; eauto.
    rewrite forallb_forall. intros Y. exploit Y; eauto. rewrite H2, H3; simpl.
    destruct (peq s (lp_header L)); simpl; congruence.
  + (* entry *)
    intros. rewrite forallb_forall in ENTRY. exploit ENTRY; eauto. rewrite H0; simpl.
    destruct (peq (fn_entrypoint f) (lp_header L)); simpl; congruence.
  + (* replacements *)
    intros. rewrite forallb_forall in REPL. exploit REPL. apply PTree.elements_correct; eauto.
    unfold check_repl. rewrite H0. rewrite existsb_exists. intros (L & A & B).
    InvBooleans. rewrite existsb_exists in H2. destruct H2 as ([[t' op'] args'] & C & D).
    unfold hoist_eq in D. InvBooleans. subst. exists L; auto.
- exists nil, (PTree.empty _). constructor; simpl; intros; auto;
    try contradiction; try constructor; try (rewrite PTree.gempty in *; discriminate).
  unfold transf_instr, replace_instr. rewrite PTree.gempty. rewrite map_succ_id. auto.
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
  destruct (transf_function_tr f) as (loops & repl & TR). apply (tr_sig _ _ _ _ TR).
Qed.

(** The relation between the register states of the original and
  transformed functions: they agree on all the registers of the original
  function.  The extra registers of the transformed function, if they are
  hoisted registers of a loop, contain the values of the corresponding
  operations when control is in the loop. *)

Definition regs_agree (f: function) (rs rs': regset) : Prop :=
  forall r, Ple r (max_reg_function f) -> rs'#r = rs#r.

Definition loop_facts (sp: val) (L: loop_info) (rs rs': regset) : Prop :=
  forall t op args, In (t, op, args) (hoists L) ->
  forall m, eval_operation ge sp op rs##args m = Some rs'#t.

Definition facts_at (loops: list loop_info) (pc: node) (sp: val)
                    (rs rs': regset) : Prop :=
  forall L, In L loops -> in_body L pc = true -> loop_facts sp L rs rs'.

Lemma agree_args:
  forall f rs rs' args,
  regs_agree f rs rs' ->
  (forall r, In r args -> Ple r (max_reg_function f)) ->
  rs'##args = rs##args.
Proof.
  induction args; simpl; intros. auto.
  f_equal; auto.
Qed.

Lemma agree_set:
  forall f rs rs' r v,
  regs_agree f rs rs' -> regs_agree f (rs#r <- v) (rs'#r <- v).
Proof.
  unfold regs_agree; intros. rewrite ! Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_setres:
  forall f res v rs rs',
  regs_agree f rs rs' -> regs_agree f (regmap_setres res v rs) (regmap_setres res v rs').
Proof.
  destruct res; simpl; intros; auto. apply agree_set; auto.
Qed.

Lemma find_function_translated:
  forall f ros rs rs' fd,
  find_function ge ros rs = Some fd ->
  regs_agree f rs rs' ->
  (forall r, ros = inl r -> Ple r (max_reg_function f)) ->
  find_function tge ros rs' = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  rewrite H0 by auto. eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Lemma eval_builtin_arg_agree:
  forall (e e': reg -> val) sp m a v,
  eval_builtin_arg ge e sp m a v ->
  (forall r, In r (params_of_builtin_arg a) -> e' r = e r) ->
  eval_builtin_arg ge e' sp m a v.
Proof.
  induction 1; simpl; intros; try (constructor; auto).
- rewrite <- H; auto. constructor.
- apply IHeval_builtin_arg1. intros; apply H1; apply in_or_app; auto.
- apply IHeval_builtin_arg2. intros; apply H1; apply in_or_app; auto.
- apply IHeval_builtin_arg1. intros; apply H1; apply in_or_app; auto.
- apply IHeval_builtin_arg2. intros; apply H1; apply in_or_app; auto.
Qed.

Lemma eval_builtin_args_agree:
  forall (e e': reg -> val) sp m al vl,
  eval_builtin_args ge e sp m al vl ->
  (forall r, In r (params_of_builtin_args al) -> e' r = e r) ->
  eval_builtin_args ge e' sp m al vl.
Proof.
  induction 1; simpl; intros; constructor.
  eapply eval_builtin_arg_agree; eauto. intros; apply H1; apply in_or_app; auto.
  apply IHlist_forall2. intros; apply H1; apply in_or_app; auto.
Qed.

Section TRANSL_FUNCTION.

Variables f tf: function.
Variable loops: list loop_info.
Variable repl: PTree.t reg.
Hypothesis TR: tr_function f loops repl tf.

(** Execution of the preheader of a loop. *)

Lemma chain_exec:
  forall h ch stk sp rs rs' m,
  (forall p i, In (p, i) (chain_instrs ch h) -> tf.(fn_code)!p = Some i) ->
  list_norepet (map hoist_reg (map snd ch)) ->
  (forall x, In x (map snd ch) -> In x (flat_map hoists loops)) ->
  regs_agree f rs rs' ->
  exists rs'',
     star step tge (State stk tf sp (chain_next ch h) rs' m)
                E0 (State stk tf sp h rs'' m)
  /\ regs_agree f rs rs''
  /\ (forall r, ~In r (map hoist_reg (map snd ch)) -> rs''#r = rs'#r)
  /\ (forall t op args, In (t, op, args) (map snd ch) ->
      forall m', eval_operation ge sp op rs##args m' = Some rs''#t).
Proof.
  induction ch as [ | [p [[t op] args]] ch]; simpl; intros until m; intros CODE NOREP INCL AG.
- exists rs'; split. apply star_refl. split. auto. split. auto. intros; contradiction.
- inv NOREP.
  exploit (tr_hoists _ _ _ _ TR t op args). apply INCL; auto.
  intros (SAFE & MEM & FRESH & ARGS).
  assert (EQARGS: rs'##args = rs##args) by (eapply agree_args; eauto).
  destruct (eval_operation ge sp op rs##args m) as [v|] eqn:EV.
  2: { exploit (op_safe_correct _ _ ge sp op (rs##args) m);
       [ rewrite length_map; auto | exact EV | contradiction ]. }
  set (rs1' := rs'#t <- v).
  exploit (IHch stk sp rs rs1' m); auto.
  { red; intros. unfold rs1'. rewrite Regmap.gso. apply AG; auto.
    red; intros; subst. extlia. }
  intros (rs'' & STAR & AG'' & SAME & FACTS).
  exists rs''; split.
  eapply star_left. eapply exec_Iop. apply CODE; auto.
  rewrite EQARGS. rewrite <- EV. apply eval_operation_preserved. exact symbols_preserved.
  eexact STAR. traceEq.
  split. auto. split.
  intros. rewrite SAME by tauto. unfold rs1'. apply Regmap.gso. intuition.
  intros. destruct H as [EQ | IN].
  + inv EQ. rewrite SAME by auto. unfold rs1'. rewrite Regmap.gss.
    rewrite (op_depends_on_memory_correct ge sp op0 (rs##args0) m' m MEM). auto.
  + eauto.
Qed.

Lemma redirect_sim:
  forall inn pc stk sp rs rs' m,
  (forall L, In L loops -> in_body L pc = true -> inn L = false -> pc = lp_header L) ->
  regs_agree f rs rs' ->
  (forall L, In L loops -> in_body L pc = true -> inn L = true -> loop_facts sp L rs rs') ->
  exists rs'',
     star step tge (State stk tf sp (redirect inn loops pc) rs' m)
                E0 (State stk tf sp pc rs'' m)
  /\ regs_agree f rs rs''
  /\ facts_at loops pc sp rs rs''.
Proof.
  intros until m; intros EOK AG FACTS.
  destruct (redirect_cases inn loops pc) as [[A B] | (L0 & A & B & C & D)].
- rewrite A. exists rs'; split. apply star_refl. split; auto.
  red; intros. destruct (inn L) eqn:INN. auto.
  exfalso. eapply B; eauto. symmetry; eauto.
- rewrite D. subst pc. unfold preheader.
  exploit (chain_exec (lp_header L0) (lp_chain L0) stk sp rs rs' m); auto.
  + intros. eapply tr_chain; eauto. apply in_flat_map. exists L0; auto.
  + change (list_norepet (tregs L0)). eapply norepet_flat_map; eauto. apply (tr_tregs _ _ _ _ TR).
  + intros. apply in_flat_map. exists L0; auto.
  + intros (rs'' & STAR & AG' & SAME & FACTS').
    exists rs''; split. auto. split. auto.
    red; intros L IN BODY. destruct (inn L) eqn:INN.
    * assert (NE: L <> L0) by congruence.
      red; intros. rewrite SAME. apply (FACTS L IN BODY INN t op args H).
      intros IN0.
      assert (A1: In t (tregs L)).
      { unfold tregs. change t with (hoist_reg (t, op, args)). apply in_map; auto. }
      exploit (norepet_flat_map_disjoint _ _ tregs loops L L0); eauto.
      apply (tr_tregs _ _ _ _ TR).
    * exploit EOK; eauto. intros EQ.
      assert (L = L0).
      { eapply norepet_map_inj. apply (tr_headers _ _ _ _ TR). auto. auto. auto. }
      subst L. red; intros. apply FACTS'; auto.
Qed.

Lemma loop_facts_update:
  forall L pc i sp rs rs' rs1 rs1',
  In L loops -> in_body L pc = true -> f.(fn_code)!pc = Some i ->
  loop_facts sp L rs rs' ->
  (forall r, ~In r (defs_all i) -> rs1#r = rs#r /\ rs1'#r = rs'#r) ->
  loop_facts sp L rs1 rs1'.
Proof.
  intros; red; intros.
  assert (D: forall r, In r (defs_all i) -> r <> t /\ ~In r args).
  { intros. eapply (tr_inv _ _ _ _ TR); eauto. }
  assert (E: rs1##args = rs##args).
  { apply map_ext_in. intros. apply H3. intro. exploit D; eauto. tauto. }
  rewrite E. destruct (H3 t) as [_ F].
  intro. exploit D; eauto. tauto.
  rewrite F. apply H2; auto.
Qed.

Lemma succ_sim:
  forall pc i s stk sp rs rs' rs1 rs1' m,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  facts_at loops pc sp rs rs' ->
  regs_agree f rs1 rs1' ->
  (forall r, ~In r (defs_all i) -> rs1#r = rs#r /\ rs1'#r = rs'#r) ->
  exists rs'',
     star step tge (State stk tf sp (redirect (fun L => in_body L pc) loops s) rs1' m)
                E0 (State stk tf sp s rs'' m)
  /\ regs_agree f rs1 rs''
  /\ facts_at loops s sp rs1 rs''.
Proof.
  intros. apply redirect_sim; auto.
  intros. eapply (tr_edges _ _ _ _ TR); eauto.
  intros. eapply loop_facts_update; eauto.
Qed.

Lemma tr_code_nonop:
  forall n i,
  f.(fn_code)!n = Some i ->
  (forall op args res s, i <> Iop op args res s) ->
  tf.(fn_code)!n = Some (map_succ (redirect (fun L => in_body L n) loops) i).
Proof.
  intros. rewrite (tr_code _ _ _ _ TR n i H). unfold transf_instr, replace_instr.
  destruct i; try (elim (H0 o l r n0); auto; fail); destruct (repl!n); auto.
Qed.

Lemma tr_code_op:
  forall n op args res s,
  f.(fn_code)!n = Some (Iop op args res s) ->
  tf.(fn_code)!n = Some (Iop op args res (redirect (fun L => in_body L n) loops s))
  \/ exists t,
     tf.(fn_code)!n = Some (Iop Omove (t :: nil) res (redirect (fun L => in_body L n) loops s))
     /\ exists L, In L loops /\ in_body L n = true /\ In (t, op, args) (hoists L).
Proof.
  intros. rewrite (tr_code _ _ _ _ TR n _ H). unfold transf_instr, replace_instr.
  destruct (repl!n) as [t|] eqn:R; simpl; auto.
  right; exists t; split; auto. eapply (tr_repl _ _ _ _ TR); eauto.
Qed.

Lemma uses_agree:
  forall rs rs' pc i r,
  regs_agree f rs rs' -> f.(fn_code)!pc = Some i -> In r (instr_uses i) ->
  rs'#r = rs#r.
Proof.
  intros. apply H. eapply max_reg_function_use; eauto.
Qed.

Lemma uses_agree_args:
  forall rs rs' pc i args,
  regs_agree f rs rs' -> f.(fn_code)!pc = Some i -> incl args (instr_uses i) ->
  rs'##args = rs##args.
Proof.
  intros. eapply agree_args; eauto. intros. eapply max_reg_function_use; eauto.
Qed.

End TRANSL_FUNCTION.

Inductive match_frames: stackframe -> stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs tf loops repl inn rs'
        (TR: tr_function f loops repl tf)
        (EOK: forall L, In L loops -> in_body L pc = true -> inn L = false ->
              pc = lp_header L)
        (AG: regs_agree f rs rs')
        (FACTS: forall v L, In L loops -> in_body L pc = true -> inn L = true ->
                loop_facts sp L (rs#res <- v) (rs'#res <- v)),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res tf sp (redirect inn loops pc) rs').

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' tf loops repl rs'
        (STACKS: list_forall2 match_frames stk stk')
        (TR: tr_function f loops repl tf)
        (AG: regs_agree f rs rs')
        (FACTS: facts_at loops pc sp rs rs'),
      match_states (State stk f sp pc rs m)
                   (State stk' tf sp pc rs' m)
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

Ltac NONOP := intros; red; intros; discriminate.

Ltac FINISH STAR :=
  econstructor; split;
  [ eapply plus_left; [ idtac | eexact STAR | traceEq ]
  | econstructor; eauto ].

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', plus step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS.
- (* nop *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  exploit (succ_sim _ _ _ _ TR pc (Inop pc') pc'); simpl; eauto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Inop; eauto.
- (* op *)
  assert (AG1: regs_agree f (rs#res <- v) (rs'#res <- v)) by (apply agree_set; auto).
  assert (OTH: forall r, ~In r (defs_all (Iop op args res pc')) ->
               (rs#res <- v)#r = rs#r /\ (rs'#res <- v)#r = rs'#r).
  { simpl; intros. rewrite ! Regmap.gso by intuition. auto. }
  exploit (succ_sim _ _ _ _ TR pc (Iop op args res pc') pc'); simpl; eauto.
  intros (rs'' & STAR & AG' & FACTS').
  exploit tr_code_op; eauto. intros [TI | (t & TI & L & IN & BODY & HIN)].
  + FINISH STAR. eapply exec_Iop; eauto.
    erewrite uses_agree_args by (eauto; simpl; apply incl_refl).
    try EVALOP.
  + assert (V: v = rs'#t).
    { exploit FACTS; eauto. intros E.
      match goal with [ H: eval_operation ge _ _ _ _ = Some v |- _ ] => rewrite E in H end.
      congruence. }
    subst v. FINISH STAR. eapply exec_Iop; eauto; simpl; auto.
- (* load *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  exploit (succ_sim _ _ _ _ TR pc (Iload chunk addr args dst pc') pc' stk' sp rs rs'
                    (rs#dst <- v) (rs'#dst <- v)); simpl; eauto.
  apply agree_set; auto.
  simpl; intros. rewrite ! Regmap.gso by intuition. auto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Iload; eauto.
  erewrite uses_agree_args by (eauto; simpl; apply incl_refl).
  try EVALADDR.
- (* store *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  exploit (succ_sim _ _ _ _ TR pc (Istore chunk addr args src pc') pc' stk' sp rs rs' rs rs'); simpl; eauto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Istore; eauto.
  erewrite uses_agree_args by (eauto; simpl; red; auto with coqlib).
  try EVALADDR.
  erewrite uses_agree by (eauto; simpl; auto). eauto.
- (* call *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  econstructor; split.
  apply plus_one. eapply exec_Icall with (fd := transf_fundef fd). eexact TI.
  eapply find_function_translated; eauto.
  intros; subst ros. eapply max_reg_function_use; eauto. simpl; auto.
  apply sig_preserved.
  rewrite (uses_agree_args f rs rs' pc _ args AG H) by (destruct ros; simpl; red; auto with coqlib).
  constructor. constructor; auto. econstructor; eauto.
  + intros. eapply (tr_edges _ _ _ _ TR); eauto. simpl; auto.
  + intros. eapply loop_facts_update; eauto.
    simpl; intros. rewrite ! Regmap.gso by intuition. auto.
- (* tailcall *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  econstructor; split.
  apply plus_one. eapply exec_Itailcall with (fd := transf_fundef fd). eexact TI.
  eapply find_function_translated; eauto.
  intros; subst ros. eapply max_reg_function_use; eauto. simpl; auto.
  apply sig_preserved.
  rewrite (tr_stacksize _ _ _ _ TR); eauto.
  rewrite (uses_agree_args f rs rs' pc _ args AG H) by (destruct ros; simpl; red; auto with coqlib).
  constructor; auto.
- (* builtin *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  exploit (succ_sim _ _ _ _ TR pc (Ibuiltin ef args res pc') pc' stk' sp rs rs'
                    (regmap_setres res vres rs) (regmap_setres res vres rs')); simpl; eauto.
  apply agree_setres; auto.
  intros. rewrite ! setres_other by auto. auto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  eapply eval_builtin_args_agree; eauto.
  intros. eapply uses_agree; eauto. simpl; auto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
- (* cond *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  exploit (succ_sim _ _ _ _ TR pc (Icond cond args ifso ifnot) (if b then ifso else ifnot)
                    stk' sp rs rs' rs rs'); simpl; eauto.
  destruct b; auto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Icond; eauto.
  rewrite (uses_agree_args f rs rs' pc _ args AG H) by (simpl; apply incl_refl). eauto.
  destruct b; auto.
- (* jumptable *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  exploit (succ_sim _ _ _ _ TR pc (Ijumptable arg tbl) pc' stk' sp rs rs' rs rs'); simpl; eauto.
  eapply list_nth_z_in; eauto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Ijumptable; eauto.
  erewrite uses_agree by (eauto; simpl; auto). eauto.
  rewrite list_nth_z_map. rewrite H1. auto.
- (* return *)
  exploit tr_code_nonop; eauto. NONOP. simpl; intros TI.
  econstructor; split.
  apply plus_one. eapply exec_Ireturn; eauto.
  rewrite (tr_stacksize _ _ _ _ TR); eauto.
  replace (regmap_optget or Vundef rs') with (regmap_optget or Vundef rs).
  constructor; auto.
  destruct or; simpl; auto. symmetry; eapply uses_agree; eauto. simpl; auto.
- (* internal function *)
  simpl. destruct (transf_function_tr f) as (loops & repl & TR).
  exploit (redirect_sim _ _ _ _ TR (fun _ => false) (fn_entrypoint f) stk'
                        (Vptr stk Ptrofs.zero) (init_regs args (fn_params f))
                        (init_regs args (fn_params f)) m').
  intros. eapply (tr_entry_ok _ _ _ _ TR); eauto.
  red; auto.
  intros; discriminate.
  intros (rs'' & STAR & AG' & FACTS').
  econstructor; split.
  eapply plus_left. eapply exec_function_internal; eauto.
  rewrite (tr_sig _ _ _ _ TR); auto.
  rewrite (tr_stacksize _ _ _ _ TR); eauto.
  rewrite (tr_entry _ _ _ _ TR), (tr_params _ _ _ _ TR). eexact STAR. traceEq.
  econstructor; eauto.
- (* external function *)
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inv STACKS. inv H1.
  exploit (redirect_sim _ _ _ _ TR inn pc bl sp (rs#res <- vres) (rs'#res <- vres) m); eauto.
  apply agree_set; auto.
  intros (rs'' & STAR & AG' & FACTS').
  econstructor; split.
  eapply plus_left. eapply exec_return. eexact STAR. traceEq.
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
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
