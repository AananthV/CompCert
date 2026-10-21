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

(** Properties of a preheader chain established by [check_chain]. *)

Fixpoint chain_ok (mr: reg) (tl: list reg) (ch: list (node * hoist)) : Prop :=
  match ch with
  | nil => True
  | (_, (t, op, args)) :: ch' =>
      op_safe op (length args) = true /\ op_depends_on_memory op = false
      /\ Plt mr t
      /\ (forall a, In a args ->
            (Ple a mr \/ In a tl) /\ ~In a (t :: map hoist_reg (map snd ch')))
      /\ chain_ok mr tl ch'
  end.

Lemma check_chain_sound:
  forall mr tl ch, check_chain mr tl ch = true -> chain_ok mr tl ch.
Proof.
  induction ch as [ | [p [[t op] args]] ch IH]; intros C.
- exact I.
- cbn [check_chain] in C. cbn [chain_ok].
  rewrite ! andb_true_iff in C.
  destruct C as [[[[SAFE MEM] FRESH] ARGS] REST].
  split. exact SAFE. split. rewrite negb_true_iff in MEM. exact MEM.
  split. apply Pos.ltb_lt. exact FRESH.
  split; [ | apply IH; exact REST ].
  intros a IN. rewrite forallb_forall in ARGS. specialize (ARGS a IN).
  rewrite andb_true_iff, orb_true_iff, negb_true_iff in ARGS.
  destruct ARGS as [[LE | TL] NOTIN].
  + split. left; apply Pos.leb_le; exact LE.
    destruct (In_dec peq a (t :: map hoist_reg (map snd ch))); [discriminate | exact n].
  + split. right. destruct (In_dec peq a tl); [exact i | discriminate].
    destruct (In_dec peq a (t :: map hoist_reg (map snd ch))); [discriminate | exact n].
Qed.

Lemma chain_ok_hoist:
  forall mr tl ch t op args,
  chain_ok mr tl ch -> In (t, op, args) (map snd ch) ->
  op_safe op (length args) = true /\ op_depends_on_memory op = false /\ Plt mr t
  /\ (forall a, In a args -> Ple a mr \/ In a tl).
Proof.
  induction ch as [ | [p [[t' op'] args']] ch IH]; intros until args; intros OK IN.
- contradiction.
- cbn [chain_ok] in OK. destruct OK as (A & B & C & D & E).
  destruct IN as [EQ | IN].
  + inv EQ. split. auto. split. auto. split. auto.
    intros a INA. exact (proj1 (D a INA)).
  + eapply IH; eauto.
Qed.

Record tr_function (f: function) (loops: list loop_info) (repl: PTree.t reg)
                   (eqs: PTree.t (list (reg * reg))) (tf: function) : Prop := {
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
  tr_chains: forall L,
    In L loops -> chain_ok (max_reg_function f) (tregs L) L.(lp_chain);
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
    exists L hargs, In L loops /\ in_body L n = true /\ In (t, op, hargs) (hoists L)
      /\ list_forall2 (fun a h => a = h \/ In (a, h) (eqs_at eqs n)) args hargs;
  tr_eqs: forall pc i s e,
    tf.(fn_code)!pc = Some i -> In s (successors_instr i) ->
    In e (eqs_at eqs s) -> In e (transfer_eqs (eqs_at eqs pc) i);
  tr_eqs_entry: eqs_at eqs tf.(fn_entrypoint) = nil
}.

Lemma map_succ_id:
  forall i, map_succ (fun s => s) i = i.
Proof.
  destruct i; simpl; auto. rewrite map_id; auto.
Qed.

Lemma match_args_sound:
  forall l args hargs,
  match_args l args hargs = true ->
  list_forall2 (fun a h => a = h \/ In (a, h) l) args hargs.
Proof.
  induction args as [ | a args IH]; destruct hargs as [ | h hargs]; simpl; intros M;
  try discriminate.
- constructor.
- rewrite andb_true_iff, orb_true_iff in M. destruct M as [[E | E] M].
  + constructor; auto. left. destruct (peq a h); [auto | discriminate].
  + constructor; auto. right. rewrite existsb_exists in E.
    destruct E as ([x y] & IN & EQ). unfold eq_pair in EQ; simpl in EQ.
    rewrite andb_true_iff in EQ. destruct EQ as [E1 E2].
    destruct (peq a x); [ | discriminate]. destruct (peq h y); [ | discriminate].
    subst; auto.
Qed.

Lemma transf_function_tr:
  forall f, exists loops repl eqs, tr_function f loops repl eqs (transf_function f).
Proof.
  intros. unfold transf_function. destruct (licm_oracle f) as [[lps repl] eqs].
  set (loops := map (fun x => let '(h, b, ch) := x in mkloop h b ch) lps).
  set (tc := transf_code f loops repl).
  set (entry := redirect (fun _ => false) loops f.(fn_entrypoint)).
  destruct (check_function f loops repl eqs tc entry) eqn:C.
- exists loops, repl, eqs. unfold check_function in C.
  rewrite ! andb_true_iff in C.
  destruct C as [[[[[[[[[[HDR0 NOREPCHAIN0] CHAINFRESH] TREGS0] CHAINS] INV] EDGES] ENTRY]
                  REPL] EQS] EQENTRY].
  assert (HDR := proj_sumbool_true _ HDR0).
  assert (NOREPCHAIN := proj_sumbool_true _ NOREPCHAIN0).
  assert (TREGS := proj_sumbool_true _ TREGS0).
  clear HDR0 NOREPCHAIN0 TREGS0.
  constructor; simpl; auto.
  + (* code *)
    intros n i CODE. unfold tc, transf_code. rewrite add_instrs_notin.
    rewrite PTree.gmap. rewrite CODE; auto.
    red; intros IN. exploit list_in_map_inv; eauto. intros ([p i'] & EQ & IN'). simpl in EQ; subst p.
    rewrite forallb_forall in CHAINFRESH. exploit CHAINFRESH; eauto. simpl. rewrite CODE. congruence.
  + (* chain *)
    intros. unfold tc, transf_code. apply add_instrs_in; auto.
  + (* chains *)
    intros L IN. rewrite forallb_forall in CHAINS. apply check_chain_sound. apply CHAINS; auto.
  + (* invariance *)
    intros L n i INL BODY CODE t op args HIN r RIN.
    rewrite forallb_forall in INV. specialize (INV L INL).
    rewrite forallb_forall in INV. exploit INV. apply PTree.elements_correct; eauto.
    unfold check_invariant; simpl. rewrite BODY; simpl. rewrite forallb_forall. intros X.
    exploit X; eauto. simpl. unfold disjointb. rewrite forallb_forall. intros Y.
    exploit Y; eauto. destruct (In_dec peq r (t :: args)) as [INR | NIN]; simpl.
    intros; discriminate. intros _. simpl in NIN. intuition.
  + (* edges *)
    intros n i s L CODE SUCC INL BS BN.
    rewrite forallb_forall in EDGES. exploit EDGES. apply PTree.elements_correct; eauto.
    unfold check_edges; simpl. rewrite forallb_forall. intros X. exploit X; eauto.
    rewrite forallb_forall. intros Y. exploit Y; eauto. rewrite BS, BN; simpl.
    destruct (peq s (lp_header L)); simpl; congruence.
  + (* entry *)
    intros L INL BODY. rewrite forallb_forall in ENTRY. exploit ENTRY; eauto. rewrite BODY; simpl.
    destruct (peq (fn_entrypoint f) (lp_header L)); simpl; congruence.
  + (* replacements *)
    intros n t op args res s R CODE.
    rewrite forallb_forall in REPL. exploit REPL. apply PTree.elements_correct; eauto.
    unfold check_repl. rewrite CODE. rewrite existsb_exists. intros (L & INL & B).
    rewrite andb_true_iff in B. destruct B as [BODY B].
    rewrite existsb_exists in B. destruct B as ([[t' op'] hargs] & HIN & M).
    unfold match_hoist in M. rewrite ! andb_true_iff in M. destruct M as [[M1 M2] M3].
    destruct (peq t t'); [ | discriminate]. destruct (eq_operation op op'); [ | discriminate].
    subst t' op'. exists L, hargs. split. auto. split. auto. split. auto.
    apply match_args_sound; auto.
  + (* equations *)
    intros pc i s e CODE SUCC IN.
    rewrite forallb_forall in EQS.
    specialize (EQS (pc, i) (PTree.elements_correct _ _ CODE)).
    unfold check_eqs in EQS. cbn [fst snd] in EQS. rewrite forallb_forall in EQS.
    specialize (EQS s SUCC). rewrite forallb_forall in EQS. specialize (EQS e IN).
    rewrite existsb_exists in EQS.
    destruct EQS as ([x y] & IN2 & EQ). destruct e as [x' y']. unfold eq_pair in EQ; simpl in EQ.
    rewrite andb_true_iff in EQ. destruct EQ as [E1 E2].
    destruct (peq x' x); [ | discriminate]. destruct (peq y' y); [ | discriminate].
    subst; auto.
  + (* entry equations *)
    destruct (eqs_at eqs entry); [auto | discriminate].
- exists nil, (PTree.empty _), (PTree.empty _).
  constructor; simpl; intros; auto;
    try contradiction; try constructor;
    try (unfold eqs_at in *; rewrite PTree.gempty in *; first [discriminate | contradiction]).
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
  destruct (transf_function_tr f) as (loops & repl & eqs & TR). apply (tr_sig _ _ _ _ _ TR).
Qed.

(** The relation between the register states of the original and
  transformed functions: they agree on all the registers of the original
  function.  The extra registers of the transformed function, if they are
  hoisted registers of a loop, contain the values of the corresponding
  operations when control is in the loop. *)

Definition regs_agree (f: function) (rs rs': regset) : Prop :=
  forall r, Ple r (max_reg_function f) -> rs'#r = rs#r.

(** The hoisted registers of a loop contain the values of the hoisted
  operations, evaluated in the register state of the transformed function. *)

Definition loop_facts (sp: val) (L: loop_info) (rs': regset) : Prop :=
  forall t op args, In (t, op, args) (hoists L) ->
  forall m, eval_operation ge sp op rs'##args m = Some rs'#t.

Definition facts_at (loops: list loop_info) (pc: node) (sp: val) (rs': regset) : Prop :=
  forall L, In L loops -> in_body L pc = true -> loop_facts sp L rs'.

(** The equations provided by the oracle hold in the register state of the
  transformed function. *)

Definition eqs_hold (l: list (reg * reg)) (rs': regset) : Prop :=
  forall x y, In (x, y) l -> rs'#x = rs'#y.

Definition move_ok (i: instruction) (rs rs': regset) : Prop :=
  match move_of i with
  | Some (x, y) => rs'#x = rs#y
  | None => True
  end.

Lemma move_of_inv:
  forall i x y, move_of i = Some (x, y) -> exists s, i = Iop Omove (y :: nil) x s.
Proof.
  unfold move_of; intros i x y M.
  destruct i; try discriminate. destruct o; try discriminate.
  destruct l as [ | y' [ | ? ?]]; try discriminate.
  inv M. eauto.
Qed.

Lemma transfer_eqs_sound:
  forall l i rs rs',
  eqs_hold l rs ->
  (forall r, ~In r (defs_all i) -> rs'#r = rs#r) ->
  move_ok i rs rs' ->
  eqs_hold (transfer_eqs l i) rs'.
Proof.
  intros l i rs rs' EQ OTH MV. unfold transfer_eqs.
  assert (FILT: eqs_hold (filter (fun e => negb (In_dec peq (fst e) (defs_all i))
                                          && negb (In_dec peq (snd e) (defs_all i))) l) rs').
  { intros x y IN. rewrite filter_In in IN. destruct IN as [IN C].
    rewrite andb_true_iff, ! negb_true_iff in C. simpl in C. destruct C as [C1 C2].
    destruct (In_dec peq x (defs_all i)) as [I1 | N1]; [discriminate | ].
    destruct (In_dec peq y (defs_all i)) as [I2 | N2]; [discriminate | ].
    rewrite (OTH x N1), (OTH y N2). apply EQ; auto. }
  unfold move_ok in MV. destruct (move_of i) as [[x y] | ] eqn:M; auto.
  intros x' y' [E | IN]; auto.
  inv E. exploit move_of_inv; eauto. intros (s & EI). subst i.
  rewrite MV. destruct (peq y' x') as [Exy | Nxy].
  - subst y'. auto.
  - symmetry. apply OTH. simpl. intuition.
Qed.

Lemma eqs_args:
  forall l rs args hargs,
  list_forall2 (fun a h => a = h \/ In (a, h) l) args hargs ->
  eqs_hold l rs ->
  rs##args = rs##hargs.
Proof.
  induction 1; simpl; intros EQ. auto.
  f_equal; auto. destruct H as [E | IN]. subst; auto. apply EQ; auto.
Qed.

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
Variable eqs: PTree.t (list (reg * reg)).
Hypothesis TR: tr_function f loops repl eqs tf.

Let mr := max_reg_function f.

Lemma eqs_step:
  forall pc i s rs rs',
  tf.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  eqs_hold (eqs_at eqs pc) rs ->
  (forall r, ~In r (defs_all i) -> rs'#r = rs#r) ->
  move_ok i rs rs' ->
  eqs_hold (eqs_at eqs s) rs'.
Proof.
  intros pc i s rs rs' CODE SUCC EQ OTH MV x y IN.
  apply (transfer_eqs_sound (eqs_at eqs pc) i rs rs' EQ OTH MV).
  eapply (tr_eqs _ _ _ _ _ TR); eauto.
Qed.

Lemma tregs_fresh:
  forall L t, In L loops -> In t (tregs L) -> Plt mr t.
Proof.
  intros L t INL IN. unfold tregs, hoists in IN.
  apply list_in_map_inv in IN. destruct IN as ([[t' op] args] & E & IN').
  unfold hoist_reg in E; simpl in E. subst t'.
  exploit (chain_ok_hoist mr (tregs L) (lp_chain L)); eauto.
  apply (tr_chains _ _ _ _ _ TR); auto.
  tauto.
Qed.

(** Execution of the preheader of a loop. *)

Lemma chain_exec:
  forall h tl ch stk sp rs rs' m,
  (forall p i, In (p, i) (chain_instrs ch h) -> tf.(fn_code)!p = Some i) ->
  list_norepet (map hoist_reg (map snd ch)) ->
  chain_ok mr tl ch ->
  regs_agree f rs rs' ->
  eqs_hold (eqs_at eqs (chain_next ch h)) rs' ->
  exists rs'',
     star step tge (State stk tf sp (chain_next ch h) rs' m)
                E0 (State stk tf sp h rs'' m)
  /\ regs_agree f rs rs''
  /\ eqs_hold (eqs_at eqs h) rs''
  /\ (forall r, ~In r (map hoist_reg (map snd ch)) -> rs''#r = rs'#r)
  /\ (forall t op args, In (t, op, args) (map snd ch) ->
      forall m', eval_operation ge sp op rs''##args m' = Some rs''#t).
Proof.
  induction ch as [ | [p [[t op] args]] ch IH]; intros until m; intros CODE NOREP OK AG EQ.
- exists rs'; split. apply star_refl. split. auto. split. auto. split. auto.
  intros; contradiction.
- cbn [chain_ok] in OK. destruct OK as (SAFE & MEM & FRESH & ARGS & OK).
  cbn [map snd fst hoist_reg] in NOREP. inv NOREP.
  cbn [chain_next] in EQ.
  assert (CODE1: tf.(fn_code)!p = Some (Iop op args t (chain_next ch h))).
  { apply CODE. left; auto. }
  destruct (eval_operation ge sp op rs'##args m) as [v|] eqn:EV.
  2: { exploit (op_safe_correct _ _ ge sp op (rs'##args) m);
       [ rewrite length_map; auto | exact EV | contradiction ]. }
  set (rs1' := rs'#t <- v).
  assert (AG1: regs_agree f rs rs1').
  { intros r LE. unfold rs1'. rewrite Regmap.gso. apply AG; auto.
    intros E; subst r. unfold mr in FRESH. extlia. }
  assert (EQ1: eqs_hold (eqs_at eqs (chain_next ch h)) rs1').
  { eapply eqs_step. eexact CODE1. left; auto. eexact EQ.
    intros r N. unfold rs1'. apply Regmap.gso. intros E; subst r. apply N. left; auto.
    unfold move_ok. destruct (move_of (Iop op args t (chain_next ch h))) as [[x y] | ] eqn:M; auto.
    exploit move_of_inv; eauto. intros (s' & E). inv E.
    unfold rs1'. rewrite Regmap.gss.
    change (rs'##(y :: nil)) with (rs'#y :: nil) in EV.
    rewrite eval_operation_Omove in EV. inv EV. auto. }
  exploit (IH stk sp rs rs1' m).
  { intros p' i' IN'. apply CODE. right; auto. }
  auto. auto. auto. auto.
  intros (rs'' & STAR & AG'' & EQ'' & SAME & FACTS).
  exists rs''; split.
  eapply star_left. eapply exec_Iop. eexact CODE1.
  rewrite <- EV. apply eval_operation_preserved. exact symbols_preserved.
  eexact STAR. traceEq.
  split. auto. split. auto. split.
  intros r N.
  assert (N1: t <> r /\ ~In r (map hoist_reg (map snd ch))) by (simpl in N; tauto).
  destruct N1 as [N1 N2].
  rewrite SAME by auto. unfold rs1'. apply Regmap.gso. auto.
  intros t0 op0 args0 IN0. simpl in IN0. destruct IN0 as [E | IN].
  + inv E. intros m'.
    assert (A: rs''##args0 = rs'##args0).
    { apply map_ext_in. intros a INA. rewrite SAME. unfold rs1'. apply Regmap.gso.
      intros E; subst a. destruct (ARGS t0 INA) as [_ N]. apply N. left; auto.
      intros IN'. destruct (ARGS a INA) as [_ N]. apply N. right; auto. }
    rewrite A. rewrite SAME by auto. unfold rs1'. rewrite Regmap.gss.
    rewrite (op_depends_on_memory_correct ge sp op0 (rs'##args0) m' m MEM). auto.
  + eauto.
Qed.

Lemma redirect_sim:
  forall inn pc stk sp rs rs' m,
  (forall L, In L loops -> in_body L pc = true -> inn L = false -> pc = lp_header L) ->
  regs_agree f rs rs' ->
  (forall L, In L loops -> in_body L pc = true -> inn L = true -> loop_facts sp L rs') ->
  eqs_hold (eqs_at eqs (redirect inn loops pc)) rs' ->
  exists rs'',
     star step tge (State stk tf sp (redirect inn loops pc) rs' m)
                E0 (State stk tf sp pc rs'' m)
  /\ regs_agree f rs rs''
  /\ facts_at loops pc sp rs''
  /\ eqs_hold (eqs_at eqs pc) rs''.
Proof.
  intros until m; intros EOK AG FACTS EQ.
  destruct (redirect_cases inn loops pc) as [[A B] | (L0 & A & B & C & D)].
- rewrite A in *. exists rs'; split. apply star_refl. split; auto. split; auto.
  red; intros L INL BODY. destruct (inn L) eqn:INN. auto.
  exfalso. eapply B; eauto. symmetry; eauto.
- rewrite D in *. subst pc. unfold preheader in *.
  exploit (chain_exec (lp_header L0) (tregs L0) (lp_chain L0) stk sp rs rs' m); auto.
  + intros. eapply tr_chain; eauto. apply in_flat_map. exists L0; auto.
  + change (list_norepet (tregs L0)). eapply norepet_flat_map; eauto. apply (tr_tregs _ _ _ _ _ TR).
  + apply (tr_chains _ _ _ _ _ TR); auto.
  + intros (rs'' & STAR & AG' & EQ' & SAME & FACTS').
    exists rs''; split. auto. split. auto. split; auto.
    red; intros L IN BODY. destruct (inn L) eqn:INN.
    * assert (NE: L <> L0) by congruence.
      assert (DISJ: list_disjoint (tregs L) (tregs L0)).
      { eapply norepet_flat_map_disjoint; eauto. apply (tr_tregs _ _ _ _ _ TR). }
      assert (NOTIN: forall r, (Ple r mr \/ In r (tregs L)) -> ~In r (tregs L0)).
      { intros r [LE | INr] INr0.
        exploit tregs_fresh. eexact A. eexact INr0. intros. extlia.
        exact (DISJ r r INr INr0 eq_refl). }
      red; intros t op args HIN m0.
      exploit (chain_ok_hoist mr (tregs L) (lp_chain L)); eauto.
      apply (tr_chains _ _ _ _ _ TR); auto.
      intros (_ & _ & _ & ARGS).
      assert (E: rs''##args = rs'##args).
      { apply map_ext_in. intros a INA. apply SAME. apply NOTIN. apply ARGS; auto. }
      rewrite E. rewrite SAME. apply (FACTS L IN BODY INN t op args HIN).
      apply NOTIN. right. unfold tregs. change t with (hoist_reg (t, op, args)). apply in_map; auto.
    * exploit EOK; eauto. intros EQL.
      assert (L = L0).
      { eapply norepet_map_inj. apply (tr_headers _ _ _ _ _ TR). auto. auto. auto. }
      subst L. red; intros. apply FACTS'; auto.
Qed.

Lemma loop_facts_update:
  forall L pc i sp rs' rs1',
  In L loops -> in_body L pc = true -> f.(fn_code)!pc = Some i ->
  loop_facts sp L rs' ->
  (forall r, ~In r (defs_all i) -> rs1'#r = rs'#r) ->
  loop_facts sp L rs1'.
Proof.
  intros L pc i sp rs' rs1' INL BODY CODE FACTS OTH; red; intros t op args HIN m.
  assert (D: forall r, In r (defs_all i) -> r <> t /\ ~In r args).
  { intros. eapply (tr_inv _ _ _ _ _ TR); eauto. }
  assert (E: rs1'##args = rs'##args).
  { apply map_ext_in. intros a INA. apply OTH. intro INa. exploit D; eauto. tauto. }
  rewrite E. rewrite OTH. apply FACTS; auto.
  intro INt. exploit D; eauto. tauto.
Qed.

Lemma defs_transf_instr:
  forall n i, defs_all (transf_instr loops repl n i) = defs_all i.
Proof.
  intros. unfold transf_instr, replace_instr.
  destruct (repl!n); destruct i; reflexivity.
Qed.

Lemma succ_transf_instr:
  forall n i s,
  In s (successors_instr i) ->
  In (redirect (fun L => in_body L n) loops s) (successors_instr (transf_instr loops repl n i)).
Proof.
  intros. unfold transf_instr, replace_instr.
  destruct (repl!n); destruct i; simpl in *; try contradiction;
  try (destruct H; [subst; auto | contradiction]);
  try (destruct H as [E | [E | E]]; [subst; auto | subst; auto | contradiction]);
  try (apply in_map; auto).
Qed.

Lemma succ_sim:
  forall pc i s stk sp rs' rs1 rs1' m,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  facts_at loops pc sp rs' ->
  eqs_hold (eqs_at eqs pc) rs' ->
  regs_agree f rs1 rs1' ->
  (forall r, ~In r (defs_all i) -> rs1'#r = rs'#r) ->
  move_ok (transf_instr loops repl pc i) rs' rs1' ->
  exists rs'',
     star step tge (State stk tf sp (redirect (fun L => in_body L pc) loops s) rs1' m)
                E0 (State stk tf sp s rs'' m)
  /\ regs_agree f rs1 rs''
  /\ facts_at loops s sp rs''
  /\ eqs_hold (eqs_at eqs s) rs''.
Proof.
  intros until m; intros CODE SUCC FACTS EQ AG OTH MV.
  apply redirect_sim; auto.
  intros. eapply (tr_edges _ _ _ _ _ TR); eauto.
  intros. eapply loop_facts_update; eauto.
  eapply eqs_step. apply (tr_code _ _ _ _ _ TR); eauto.
  apply succ_transf_instr; eauto. eauto.
  rewrite defs_transf_instr. auto. auto.
Qed.

Lemma tr_code_nonop:
  forall n i,
  f.(fn_code)!n = Some i ->
  (forall op args res s, i <> Iop op args res s) ->
  tf.(fn_code)!n = Some (map_succ (redirect (fun L => in_body L n) loops) i)
  /\ transf_instr loops repl n i = map_succ (redirect (fun L => in_body L n) loops) i.
Proof.
  intros n i CODE NOP. rewrite (tr_code _ _ _ _ _ TR n i CODE).
  assert (E: transf_instr loops repl n i = map_succ (redirect (fun L => in_body L n) loops) i).
  { unfold transf_instr, replace_instr.
    destruct i; try (elim (NOP o l r n0); auto; fail); destruct (repl!n); auto. }
  rewrite E; auto.
Qed.

Lemma tr_code_op:
  forall n op args res s,
  f.(fn_code)!n = Some (Iop op args res s) ->
  (transf_instr loops repl n (Iop op args res s)
     = Iop op args res (redirect (fun L => in_body L n) loops s))
  \/ exists t,
     transf_instr loops repl n (Iop op args res s)
       = Iop Omove (t :: nil) res (redirect (fun L => in_body L n) loops s)
     /\ exists L hargs, In L loops /\ in_body L n = true /\ In (t, op, hargs) (hoists L)
          /\ list_forall2 (fun a h => a = h \/ In (a, h) (eqs_at eqs n)) args hargs.
Proof.
  intros n op args res s CODE. unfold transf_instr, replace_instr.
  destruct (repl!n) as [t|] eqn:R; simpl; auto.
  right; exists t; split; auto. eapply (tr_repl _ _ _ _ _ TR); eauto.
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
  | match_frames_intro: forall res f sp pc rs tf loops repl eqs inn rs'
        (TR: tr_function f loops repl eqs tf)
        (EOK: forall L, In L loops -> in_body L pc = true -> inn L = false ->
              pc = lp_header L)
        (AG: regs_agree f rs rs')
        (RES: Ple res (max_reg_function f))
        (FACTS: forall v L, In L loops -> in_body L pc = true -> inn L = true ->
                loop_facts sp L (rs'#res <- v))
        (EQS: forall v, eqs_hold (eqs_at eqs (redirect inn loops pc)) (rs'#res <- v)),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res tf sp (redirect inn loops pc) rs').

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' tf loops repl eqs rs'
        (STACKS: list_forall2 match_frames stk stk')
        (TR: tr_function f loops repl eqs tf)
        (AG: regs_agree f rs rs')
        (FACTS: facts_at loops pc sp rs')
        (EQS: eqs_hold (eqs_at eqs pc) rs'),
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
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Inop pc') pc' stk' sp rs' rs rs'); simpl; eauto.
  rewrite TE; exact I.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
  FINISH STAR. eapply exec_Inop; eauto.
- (* op *)
  rename H into CODE. rename H0 into EV.
  assert (AG1: regs_agree f (rs#res <- v) (rs'#res <- v)) by (apply agree_set; auto).
  assert (OTH: forall r, ~In r (defs_all (Iop op args res pc')) -> (rs'#res <- v)#r = rs'#r).
  { simpl; intros. rewrite Regmap.gso by intuition. auto. }
  assert (ARGS: rs'##args = rs##args).
  { eapply uses_agree_args; eauto. simpl; apply incl_refl. }
  exploit tr_code_op; eauto. intros [TE | (t & TE & L & hargs & INL & BODY & HIN & FA)].
  + assert (MV: move_ok (transf_instr loops repl pc (Iop op args res pc')) rs' (rs'#res <- v)).
    { rewrite TE. unfold move_ok.
      destruct (move_of (Iop op args res (redirect (fun L => in_body L pc) loops pc')))
        as [[x y] | ] eqn:M; auto.
      exploit move_of_inv; eauto. intros (s' & E). inv E.
      rewrite Regmap.gss. change (rs##(y :: nil)) with (rs#y :: nil) in EV.
      rewrite eval_operation_Omove in EV. inv EV.
      change (rs'##(y :: nil) = rs##(y :: nil)) in ARGS. simpl in ARGS. congruence. }
    exploit (succ_sim _ _ _ _ _ TR pc (Iop op args res pc') pc' stk' sp rs'
                      (rs#res <- v) (rs'#res <- v)); simpl; eauto.
    intros (rs'' & STAR & AG' & FACTS' & EQS').
    assert (TI := tr_code _ _ _ _ _ TR _ _ CODE). rewrite TE in TI.
    FINISH STAR. eapply exec_Iop; eauto.
    rewrite ARGS. try EVALOP.
  + assert (V: v = rs'#t).
    { assert (E := FACTS L INL BODY t op hargs HIN m).
      rewrite <- (eqs_args _ _ _ _ FA EQS), ARGS in E. congruence. }
    subst v.
    assert (MV: move_ok (transf_instr loops repl pc (Iop op args res pc')) rs' (rs'#res <- (rs'#t))).
    { rewrite TE. unfold move_ok. simpl. rewrite Regmap.gss. auto. }
    exploit (succ_sim _ _ _ _ _ TR pc (Iop op args res pc') pc' stk' sp rs'
                      (rs#res <- (rs'#t)) (rs'#res <- (rs'#t))); simpl; eauto.
    intros (rs'' & STAR & AG' & FACTS' & EQS').
    assert (TI := tr_code _ _ _ _ _ TR _ _ CODE). rewrite TE in TI.
    FINISH STAR. eapply exec_Iop; eauto; apply eval_operation_Omove.
- (* load *)
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Iload chunk addr args dst pc') pc' stk' sp rs'
                    (rs#dst <- v) (rs'#dst <- v)); simpl; eauto.
  apply agree_set; auto.
  simpl; intros. rewrite Regmap.gso by intuition. auto.
  rewrite TE; exact I.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
  FINISH STAR. eapply exec_Iload; eauto.
  erewrite uses_agree_args by (eauto; simpl; apply incl_refl).
  try EVALADDR.
- (* store *)
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Istore chunk addr args src pc') pc' stk' sp rs' rs rs'); simpl; eauto.
  rewrite TE; exact I.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
  FINISH STAR. eapply exec_Istore; eauto.
  erewrite uses_agree_args by (eauto; simpl; red; auto with coqlib).
  try EVALADDR.
  erewrite uses_agree by (eauto; simpl; auto). eauto.
- (* call *)
  rename H into CODE.
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  econstructor; split.
  apply plus_one. eapply exec_Icall with (fd := transf_fundef fd). eexact TI.
  eapply find_function_translated; eauto.
  intros; subst ros. eapply max_reg_function_use; eauto. simpl; auto.
  apply sig_preserved.
  rewrite (uses_agree_args f rs rs' pc _ args AG CODE) by (destruct ros; simpl; red; auto with coqlib).
  constructor. constructor; auto. econstructor; eauto.
  + intros. eapply (tr_edges _ _ _ _ _ TR); eauto. simpl; auto.
  + eapply max_reg_function_def; eauto; simpl; auto.
  + intros. eapply loop_facts_update; eauto.
    simpl; intros. rewrite Regmap.gso by intuition. auto.
  + intros v. eapply (eqs_step _ _ _ _ _ TR pc); eauto.
    * simpl; auto.
    * simpl; intros. rewrite Regmap.gso by intuition. auto.
    * unfold move_ok; simpl; auto.
- (* tailcall *)
  rename H into CODE.
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  econstructor; split.
  apply plus_one. eapply exec_Itailcall with (fd := transf_fundef fd). eexact TI.
  eapply find_function_translated; eauto.
  intros; subst ros. eapply max_reg_function_use; eauto. simpl; auto.
  apply sig_preserved.
  rewrite (tr_stacksize _ _ _ _ _ TR); eauto.
  rewrite (uses_agree_args f rs rs' pc _ args AG CODE) by (destruct ros; simpl; red; auto with coqlib).
  constructor; auto.
- (* builtin *)
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Ibuiltin ef args res pc') pc' stk' sp rs'
                    (regmap_setres res vres rs) (regmap_setres res vres rs')); simpl; eauto.
  apply agree_setres; auto.
  intros. rewrite setres_other by auto. auto.
  rewrite TE; exact I.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
  FINISH STAR. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  eapply eval_builtin_args_agree; eauto.
  intros. eapply uses_agree; eauto. simpl; auto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
- (* cond *)
  rename H into CODE.
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Icond cond args ifso ifnot) (if b then ifso else ifnot)
                    stk' sp rs' rs rs'); simpl; eauto.
  destruct b; auto.
  rewrite TE; exact I.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
  FINISH STAR. eapply exec_Icond; eauto.
  rewrite (uses_agree_args f rs rs' pc _ args AG CODE) by (simpl; apply incl_refl). eauto.
  destruct b; auto.
- (* jumptable *)
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Ijumptable arg tbl) pc' stk' sp rs' rs rs'); simpl; eauto.
  eapply list_nth_z_in; eauto.
  rewrite TE; exact I.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
  FINISH STAR. eapply exec_Ijumptable; eauto.
  erewrite uses_agree by (eauto; simpl; auto). eauto.
  rewrite list_nth_z_map. rewrite H1. auto.
- (* return *)
  exploit tr_code_nonop; eauto. NONOP. intros [TI TE]. simpl in TI.
  econstructor; split.
  apply plus_one. eapply exec_Ireturn; eauto.
  rewrite (tr_stacksize _ _ _ _ _ TR); eauto.
  replace (regmap_optget or Vundef rs') with (regmap_optget or Vundef rs).
  constructor; auto.
  destruct or; simpl; auto. symmetry; eapply uses_agree; eauto. simpl; auto.
- (* internal function *)
  simpl. destruct (transf_function_tr f) as (loops & repl & eqs & TR).
  exploit (redirect_sim _ _ _ _ _ TR (fun _ => false) (fn_entrypoint f) stk'
                        (Vptr stk Ptrofs.zero) (init_regs args (fn_params f))
                        (init_regs args (fn_params f)) m').
  intros. eapply (tr_entry_ok _ _ _ _ _ TR); eauto.
  red; auto.
  intros; discriminate.
  rewrite <- (tr_entry _ _ _ _ _ TR), (tr_eqs_entry _ _ _ _ _ TR). red; intros; contradiction.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
  econstructor; split.
  eapply plus_left. eapply exec_function_internal; eauto.
  rewrite (tr_sig _ _ _ _ _ TR); auto.
  rewrite (tr_stacksize _ _ _ _ _ TR); eauto.
  rewrite (tr_entry _ _ _ _ _ TR), (tr_params _ _ _ _ _ TR). eexact STAR. traceEq.
  econstructor; eauto.
- (* external function *)
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inv STACKS. match goal with [ H: match_frames _ _ |- _ ] => inv H end.
  exploit (redirect_sim _ _ _ _ _ TR inn pc bl sp (rs#res <- vres) (rs'#res <- vres) m); eauto.
  apply agree_set; auto.
  intros (rs'' & STAR & AG' & FACTS' & EQS').
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
