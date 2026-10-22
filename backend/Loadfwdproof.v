(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for global load forwarding. *)

Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL.
Require Import Loadfwd.

(** * Registers mentioned by the facts *)

(** All the facts computed by the analysis only mention registers of the
  set [M] computed by [mentionable].  This justifies the fast path of
  [kill_reg_m]. *)

Definition sexpr_ok (M: PTree.t unit) (e: sexpr) : Prop :=
  forall x, sexpr_mentions x e = true -> M!x <> None.

Definition sexprlist_ok (M: PTree.t unit) (el: sexprlist) : Prop :=
  forall x, sexprlist_mentions x el = true -> M!x <> None.

Definition fact_ok (M: PTree.t unit) (f: fact) : Prop :=
  forall x, fact_mentions x f = true -> M!x <> None.

Definition facts_ok (M: PTree.t unit) (mp: PTree.t fact) : Prop :=
  forall r f, mp!r = Some f -> fact_ok M f.

Lemma subst_mentions:
  forall x r e,
  (forall y, sexpr_mentions x (subst r e y) = true ->
             sexpr_mentions x y = true \/ sexpr_mentions x e = true)
  /\ (forall l, sexprlist_mentions x (subst_list r e l) = true ->
             sexprlist_mentions x l = true \/ sexpr_mentions x e = true).
Proof.
  intros x r e. apply sexpr_mutind; simpl; intros.
- destruct (peq r r0); auto.
- auto.
- discriminate.
- apply orb_true_iff in H1. destruct H1 as [A|A].
  destruct (H A) as [B|B]; auto. rewrite B; auto.
  destruct (H0 A) as [B|B]; auto. rewrite B, orb_true_r; auto.
Qed.

Lemma kill_one_ok:
  forall M mp r f f',
  facts_ok M mp -> fact_ok M f ->
  kill_one r (subst_for r mp) f = Some f' -> fact_ok M f'.
Proof.
  unfold kill_one; intros. destruct (fact_mentions r f).
- unfold subst_for, expr_fact in H1.
  destruct (mp!r) as [[e|]|] eqn:E; try discriminate.
  destruct (sexpr_mentions r e); try discriminate.
  destruct (Nat.leb (fact_size (subst_fact r e f)) max_sexpr_size); inv H1.
  assert (OKE: forall x, sexpr_mentions x e = true -> M!x <> None)
    by (intros; apply (H r (Fexpr e) E); auto).
  red; intros x X. destruct f; simpl in X.
  + destruct (proj1 (subst_mentions x r e) _ X) as [A|A]. apply H0; simpl; auto. auto.
  + destruct (proj2 (subst_mentions x r e) _ X) as [A|A]. apply H0; simpl; auto. auto.
- inv H1; auto.
Qed.

Lemma kill_reg_ok:
  forall M mp r, facts_ok M mp -> facts_ok M (kill_reg r mp).
Proof.
  intros.
  assert (FULL: facts_ok M (kill_reg_full r mp)).
  { unfold kill_reg_full; red; intros r0 f E.
    rewrite PTree.grspec in E. destruct (PTree.elt_eq r0 r); try discriminate.
    rewrite PTree.gmap_filter1 in E. destruct (mp!r0) as [f0|] eqn:E0; try discriminate.
    eapply kill_one_ok; eauto. }
  unfold kill_reg. destruct (mp!r); auto.
  destruct (PTree.fold1 (fun b f => b && negb (fact_mentions r f)) mp true); auto.
Qed.

Lemma kill_reg_m_ok:
  forall M mp r, facts_ok M mp -> facts_ok M (kill_reg_m M r mp).
Proof.
  unfold kill_reg_m; intros. destruct (M!r). apply kill_reg_ok; auto.
  red; intros r0 f E. rewrite PTree.grspec in E. destruct (PTree.elt_eq r0 r); try discriminate.
  eauto.
Qed.

Lemma set_fact_ok:
  forall M mp r f, facts_ok M mp -> fact_ok M f -> facts_ok M (set_fact M r f mp).
Proof.
  unfold set_fact; intros.
  destruct (kill_one r (subst_for r mp) f) as [f'|] eqn:K.
- red; intros r0 f0 E. rewrite PTree.gsspec in E. destruct (peq r0 r).
  inv E. eapply kill_one_ok; eauto.
  eapply kill_reg_m_ok; eauto.
- apply kill_reg_m_ok; auto.
Qed.

Lemma kill_loads_ok:
  forall M mp, facts_ok M mp -> facts_ok M (kill_loads mp).
Proof.
  unfold kill_loads; intros; red; intros.
  rewrite PTree.gfilter1 in H0. destruct (mp!r) as [f'|] eqn:E; try discriminate.
  destruct (is_expr_fact f'); inv H0. eauto.
Qed.

Lemma kill_regs_ok:
  forall M rl mp, facts_ok M mp -> facts_ok M (kill_regs M rl mp).
Proof.
  induction rl; simpl; intros; auto. apply IHrl. apply kill_reg_m_ok; auto.
Qed.

Lemma add_regs_mono:
  forall rl u x, u!x <> None -> (add_regs rl u)!x <> None.
Proof.
  induction rl; simpl; intros; auto. apply IHrl.
  rewrite PTree.gsspec. destruct (peq x a); auto. congruence.
Qed.

Lemma add_regs_in:
  forall rl u x, In x rl -> (add_regs rl u)!x <> None.
Proof.
  induction rl; simpl; intros. contradiction.
  destruct H. subst a. apply add_regs_mono. rewrite PTree.gss. congruence.
  auto.
Qed.

Lemma mentionable_spec:
  forall rel c pc i x,
  c!pc = Some i -> In x (mention_regs rel i) -> (mentionable rel c)!x <> None.
Proof.
  intros. unfold mentionable. rewrite PTree.fold1_spec.
  assert (A: forall (l: list (positive * instruction)) (u: PTree.t unit),
             (forall y, u!y <> None ->
                (fold_left (fun a p => add_regs (mention_regs rel (snd p)) a) l u) ! y <> None)
          /\ (forall p y, In p l -> In y (mention_regs rel (snd p)) ->
                (fold_left (fun a p => add_regs (mention_regs rel (snd p)) a) l u) ! y <> None)).
  { induction l as [|p l IH]; simpl; intros.
    - split; intros; [auto | contradiction].
    - split; intros.
      + apply (proj1 (IH _)). apply add_regs_mono; auto.
      + destruct H1. subst p0. apply (proj1 (IH _)). apply add_regs_in; auto.
        apply (proj2 (IH _)) with p0; auto. }
  apply (proj2 (A _ _)) with (pc, i); auto. apply PTree.elements_correct; auto.
Qed.

Lemma sregs_ok:
  forall M args, (forall a, In a args -> M!a <> None) -> sexprlist_ok M (sregs args).
Proof.
  induction args; simpl; intros; red; simpl; intros. discriminate.
  apply orb_true_iff in H0. destruct H0.
  apply Pos.eqb_eq in H0. subst. auto.
  apply IHargs; auto.
Qed.

Lemma transfer_instr_ok:
  forall rel c pc i mp,
  c!pc = Some i ->
  facts_ok (mentionable rel c) mp ->
  facts_ok (mentionable rel c) (transfer_instr rel (mentionable rel c) i mp).
Proof.
  intros. set (M := mentionable rel c) in *.
  assert (ARGS: forall x, In x (mention_regs rel i) -> M!x <> None)
    by (intros; eapply mentionable_spec; eauto).
  destruct i; simpl in *; auto.
- (* op *)
  unfold transfer_op. destruct (is_move_operation o l) as [src|] eqn:MV.
  + exploit is_move_operation_correct; eauto. intros [? ?]; subst o l.
    assert (DFL: facts_ok M (match rel!r with
                             | Some _ => set_fact M r (Fexpr (Sreg src)) mp
                             | None => kill_reg_m M r mp end)).
    { destruct (rel!r) eqn:R. apply set_fact_ok; auto.
      red; simpl; intros. apply Pos.eqb_eq in H1; subst. apply ARGS; simpl; auto.
      apply kill_reg_m_ok; auto. }
    destruct (mp!src) as [[e|chunk addr el]|] eqn:E; auto.
    apply set_fact_ok; eauto.
  + destruct (rel!r) eqn:R. 2: apply kill_reg_m_ok; auto.
    destruct (op_depends_on_memory o). apply kill_reg_m_ok; auto.
    apply set_fact_ok; auto. red; simpl; intros. apply (sregs_ok M l); auto.
- (* load *)
  apply set_fact_ok; auto. red; simpl; intros. apply (sregs_ok M l); auto.
- (* store *)
  assert (K: facts_ok M (kill_loads mp)) by (apply kill_loads_ok; auto).
  destruct (store_full m); auto.
  red; intros. rewrite PTree.gsspec in H1. destruct (peq r0 r); eauto.
  inv H1. red; simpl; intros. apply (sregs_ok M l); auto.
- (* call *)
  apply kill_reg_m_ok. apply kill_loads_ok; auto.
- (* builtin *)
  apply kill_regs_ok. apply kill_loads_ok; auto.
Qed.

Section AU_OK.

Variable M: PTree.t unit.
Variables m1 m2: PTree.t fact.
Hypothesis OK1: facts_ok M m1.
Hypothesis OK2: facts_ok M m2.

Lemma au_list_with_ok:
  forall (au: sexpr -> sexpr -> option sexpr),
  (forall e1 e2 e, au e1 e2 = Some e -> sexpr_ok M e1 -> sexpr_ok M e2 -> sexpr_ok M e) ->
  forall el1 el2 el, au_list_with au el1 el2 = Some el ->
  sexprlist_ok M el1 -> sexprlist_ok M el2 -> sexprlist_ok M el.
Proof.
  intros au AU. induction el1; destruct el2; simpl; intros; try discriminate.
- inv H. auto.
- destruct (au e e0) as [e1|] eqn:A; try discriminate.
  destruct (au_list_with au el1 el2) as [l1|] eqn:B; try discriminate.
  inv H. red; simpl; intros. apply orb_true_iff in H. destruct H.
  + eapply AU; eauto.
    red; intros; apply H0; simpl; rewrite H2; auto.
    red; intros; apply H1; simpl; rewrite H2; auto.
  + eapply IHel1; eauto.
    red; intros; apply H0; simpl; rewrite H2, orb_true_r; auto.
    red; intros; apply H1; simpl; rewrite H2, orb_true_r; auto.
Qed.

Lemma expr_fact_ok:
  forall mp r e, facts_ok M mp -> expr_fact mp r = Some e -> sexpr_ok M e.
Proof.
  unfold expr_fact; intros. destruct (mp!r) as [[e'|]|] eqn:E; inv H0.
  red; intros. apply (H r (Fexpr e) E); auto.
Qed.

Lemma au_ok:
  forall n e1 e2 e, au m1 m2 n e1 e2 = Some e -> sexpr_ok M e1 -> sexpr_ok M e2 -> sexpr_ok M e.
Proof.
  induction n; simpl; intros.
- destruct (sexpr_beq e1 e2); inv H; auto.
- destruct (sexpr_beq e1 e2). inv H; auto.
  destruct e1 as [r1|op1 el1].
  + destruct (expr_fact m1 r1) as [e1'|] eqn:X1.
    * apply (IHn e1' e2 e H); auto. apply expr_fact_ok with m1 r1; auto.
    * destruct e2 as [r2|op2 el2]; try discriminate.
      destruct (expr_fact m2 r2) as [e2'|] eqn:X2; try discriminate.
      apply (IHn (Sreg r1) e2' e H); auto. apply expr_fact_ok with m2 r2; auto.
  + destruct e2 as [r2|op2 el2].
    * destruct (expr_fact m2 r2) as [e2'|] eqn:X2; try discriminate.
      apply (IHn (Sop op1 el1) e2' e H); auto. apply expr_fact_ok with m2 r2; auto.
    * destruct (eq_operation op1 op2); try discriminate.
      destruct (au_list_with (au m1 m2 n) el1 el2) as [el|] eqn:L; inv H.
      red; simpl; intros. eapply au_list_with_ok; eauto.
Qed.

Lemma lub_ok:
  facts_ok M (PTree.combine (lub_fact m1 m2) m1 m2).
Proof.
  red; intros. rewrite PTree.gcombine in H by auto. unfold lub_fact in H.
  destruct (m1!r) as [f1|] eqn:E1; destruct (m2!r) as [f2|] eqn:E2; try discriminate.
  destruct (fact_beq f1 f2). inv H; eauto.
  destruct (au_fact m1 m2 f1 f2) as [g|] eqn:A; try discriminate.
  assert (G: fact_ok M g).
  { unfold au_fact in A.
    destruct f1 as [e1|chunk1 addr1 el1], f2 as [e2|chunk2 addr2 el2]; try discriminate.
    - destruct (au m1 m2 au_fuel e1 e2) as [e|] eqn:AU; inv A.
      red; simpl; intros. eapply au_ok; eauto.
      red; intros; apply (OK1 r (Fexpr e1)); auto.
      red; intros; apply (OK2 r (Fexpr e2)); auto.
    - destruct (chunk_eq chunk1 chunk2); try discriminate.
      destruct (eq_addressing addr1 addr2); try discriminate.
      destruct (au_list_with (au m1 m2 au_fuel) el1 el2) as [el|] eqn:AU; try discriminate.
      injection A; intros <-.
      red; simpl; intros. eapply au_list_with_ok. intros; eapply au_ok; eauto. eauto.
      red; intros; apply (OK1 r (Fload chunk1 addr1 el1)); auto.
      red; intros; apply (OK2 r (Fload chunk2 addr2 el2)); auto.
      auto. }
  destruct (fact_beq f1 g). inv H; eauto.
  destruct (Nat.ltb (fact_size f1) (fact_size g) && Nat.leb (fact_size g) max_sexpr_size); inv H; auto.
Qed.

End AU_OK.

Definition lfacts_ok (M: PTree.t unit) (x: LFacts.t) : Prop :=
  match x with LFacts.Bot => True | LFacts.Facts mp => facts_ok M mp end.

Lemma analyze_ok:
  forall f pc,
  lfacts_ok (mentionable (relevant_regs (fn_code f)) (fn_code f)) (analyze f)!!pc.
Proof.
  intros. set (rel := relevant_regs (fn_code f)). set (M := mentionable rel (fn_code f)).
  assert (INIT: lfacts_ok M (PMap.init empty_facts)!!pc).
  { rewrite PMap.gi. simpl. red; intros. rewrite PTree.gempty in H; discriminate. }
  unfold analyze, analyze_rel. fold rel. fold M.
  destruct (too_big f rel); auto.
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer rel M f)
                        (fn_entrypoint f) empty_facts) as [res|] eqn:FIX; auto.
  eapply DS.fixpoint_invariant with (P := lfacts_ok M) (code := fn_code f); eauto.
- simpl; auto.
- intros x y X Y. destruct x as [|m1]; destruct y as [|m2]; simpl in *; auto.
  destruct (PTree.beq fact_beq m1 m2); simpl; auto. apply lub_ok; auto.
- intros pc0 i x CODE X. unfold transfer. destruct x as [|mp]; simpl; auto.
  rewrite CODE. simpl. apply transfer_instr_ok with pc0; auto.
Qed.

(** * Soundness of the static analysis *)

Section SEMANTICS.

Context {F V: Type} (ge: Genv.t F V) (sp: val).

Definition lholds (rs: regset) (m: mem) (x: LFacts.t) : Prop :=
  match x with
  | LFacts.Bot => False
  | LFacts.Facts mp => facts_hold ge sp rs m mp
  end.

(** [fact_holds_v rs m v f] means that the fact [f] holds for a register
  containing value [v]. *)

Definition fact_holds_v (rs: regset) (m: mem) (v: val) (f: fact) : Prop :=
  match f with
  | Fexpr e => eval_sexpr ge sp rs e = Some v
  | Fload chunk addr el =>
      forall vl a v',
      eval_sexprlist ge sp rs el = Some vl ->
      eval_addressing ge sp addr vl = Some a ->
      Mem.loadv chunk m a = Some v' ->
      Val.lessdef v' v
  end.

Remark fact_holds_v_eq:
  forall rs m r f, fact_holds ge sp rs m r f = fact_holds_v rs m rs#r f.
Proof.
  destruct f; reflexivity.
Qed.

(** Evaluation only depends on the registers mentioned. *)

Lemma eval_sexpr_agree:
  forall rs rs',
  (forall e, (forall r, sexpr_mentions r e = true -> rs'#r = rs#r) ->
             eval_sexpr ge sp rs' e = eval_sexpr ge sp rs e)
  /\ (forall el, (forall r, sexprlist_mentions r el = true -> rs'#r = rs#r) ->
             eval_sexprlist ge sp rs' el = eval_sexprlist ge sp rs el).
Proof.
  intros rs rs'. apply sexpr_mutind; simpl; intros.
- f_equal. apply H. apply Pos.eqb_refl.
- rewrite H by auto. auto.
- auto.
- rewrite H, H0; auto.
  intros; apply H1; rewrite H2; apply orb_true_r.
  intros; apply H1; rewrite H2; auto.
Qed.

Lemma fact_holds_v_agree:
  forall rs m v f rs',
  fact_holds_v rs m v f ->
  (forall r, fact_mentions r f = true -> rs'#r = rs#r) ->
  fact_holds_v rs' m v f.
Proof.
  unfold fact_holds_v; intros. destruct f; simpl in H0.
- rewrite (proj1 (eval_sexpr_agree rs rs')) by auto. auto.
- intros. rewrite (proj2 (eval_sexpr_agree rs rs')) in H1 by auto. eauto.
Qed.

Lemma facts_hold_ext:
  forall rs rs' m mp,
  (forall r, rs'#r = rs#r) ->
  facts_hold ge sp rs m mp -> facts_hold ge sp rs' m mp.
Proof.
  intros; red; intros. rewrite fact_holds_v_eq. rewrite H.
  eapply fact_holds_v_agree; eauto. rewrite <- fact_holds_v_eq. auto.
Qed.

Lemma lholds_ge:
  forall rs m x y, LFacts.ge x y -> lholds rs m y -> lholds rs m x.
Proof.
  unfold LFacts.ge, lholds; intros. destruct x, y; auto; try contradiction.
Qed.

(** Substitution. *)

Lemma subst_eval:
  forall rs r e, eval_sexpr ge sp rs e = Some rs#r ->
  (forall x, eval_sexpr ge sp rs (subst r e x) = eval_sexpr ge sp rs x)
  /\ (forall xl, eval_sexprlist ge sp rs (subst_list r e xl) = eval_sexprlist ge sp rs xl).
Proof.
  intros rs r e EV. apply sexpr_mutind; simpl; intros.
- destruct (peq r r0); auto. subst; auto.
- rewrite H; auto.
- auto.
- rewrite H, H0; auto.
Qed.

Lemma subst_not_mentions:
  forall r e, sexpr_mentions r e = false ->
  (forall x, sexpr_mentions r (subst r e x) = false)
  /\ (forall xl, sexprlist_mentions r (subst_list r e xl) = false).
Proof.
  intros r e NM. apply sexpr_mutind; simpl; intros.
- destruct (peq r r0); auto. simpl. apply Pos.eqb_neq; auto.
- auto.
- auto.
- rewrite H, H0; auto.
Qed.

Lemma sregs_sound:
  forall rs rl, eval_sexprlist ge sp rs (sregs rl) = Some rs##rl.
Proof.
  induction rl; simpl; auto. rewrite IHrl; auto.
Qed.

(** Soundness of the basic operations. *)

Lemma kill_one_sound:
  forall rs m mp r v f f' w,
  facts_hold ge sp rs m mp ->
  kill_one r (subst_for r mp) f = Some f' ->
  fact_holds_v rs m w f ->
  fact_holds_v (rs#r <- v) m w f'.
Proof.
  unfold kill_one; intros. destruct (fact_mentions r f) eqn:M.
- unfold subst_for, expr_fact in H0.
  destruct (mp!r) as [[e|]|] eqn:E; try discriminate.
  destruct (sexpr_mentions r e) eqn:ME; try discriminate.
  destruct (Nat.leb (fact_size (subst_fact r e f)) max_sexpr_size); inv H0.
  assert (EV: eval_sexpr ge sp rs e = Some rs#r) by exact (H _ _ E).
  destruct (subst_eval rs r e EV) as [S1 S2].
  destruct (subst_not_mentions r e ME) as [N1 N2].
  apply fact_holds_v_agree with rs.
  destruct f; simpl in *. rewrite S1; auto. intros. rewrite S2 in H0. eauto.
  intros. rewrite Regmap.gso. auto. intro; subst r0.
  destruct f; simpl in H0. rewrite N1 in H0; discriminate. rewrite N2 in H0; discriminate.
- inv H0. apply fact_holds_v_agree with rs; auto.
  intros. rewrite Regmap.gso. auto. congruence.
Qed.

Lemma kill_reg_sound:
  forall rs m mp r v,
  facts_hold ge sp rs m mp ->
  facts_hold ge sp (rs#r <- v) m (kill_reg r mp).
Proof.
  assert (FULL: forall rs m mp r v,
            facts_hold ge sp rs m mp ->
            facts_hold ge sp (rs#r <- v) m (kill_reg_full r mp)).
  { unfold kill_reg_full; intros; red; intros.
  rewrite PTree.grspec in H0. destruct (PTree.elt_eq r0 r); try discriminate.
  rewrite PTree.gmap_filter1 in H0. destruct (mp!r0) as [f0|] eqn:E; try discriminate.
  rewrite fact_holds_v_eq. rewrite Regmap.gso by auto.
  eapply kill_one_sound; eauto. rewrite <- fact_holds_v_eq. apply H; auto. }
  intros. unfold kill_reg.
  destruct (mp!r) as [f0|] eqn:R; auto.
  destruct (PTree.fold1 (fun b f => b && negb (fact_mentions r f)) mp true) eqn:FA; auto.
  assert (FA': forall (l: list (positive * fact)) b, fold_left (fun b p => b && negb (fact_mentions r (snd p))) l b = true ->
                b = true /\ forall p, In p l -> fact_mentions r (snd p) = false).
  { induction l; simpl; intros. split; auto; tauto.
    apply IHl in H0. destruct H0 as [B C]. apply andb_prop in B. destruct B as [B1 B2].
    split; auto. intros p [<-|IN]; auto. apply negb_true_iff; auto. }
  rewrite PTree.fold1_spec in FA. apply FA' in FA. destruct FA as [_ FA].
  red; intros r0 f E.
  assert (N: fact_mentions r f = false) by (apply (FA (r0, f)); apply PTree.elements_correct; auto).
  rewrite fact_holds_v_eq. rewrite Regmap.gso by congruence.
  eapply kill_one_sound; eauto. unfold kill_one; rewrite N; auto.
  rewrite <- fact_holds_v_eq. apply H; auto.
Qed.

Lemma kill_reg_m_sound:
  forall M rs m mp r v,
  facts_ok M mp ->
  facts_hold ge sp rs m mp ->
  facts_hold ge sp (rs#r <- v) m (kill_reg_m M r mp).
Proof.
  unfold kill_reg_m; intros. destruct (M!r) eqn:MR. apply kill_reg_sound; auto.
  red; intros r0 f E. rewrite PTree.grspec in E. destruct (PTree.elt_eq r0 r); try discriminate.
  assert (N: fact_mentions r f = false).
  { destruct (fact_mentions r f) eqn:FM; auto. elim (H r0 f E r FM); auto. }
  rewrite fact_holds_v_eq. rewrite Regmap.gso by auto.
  apply fact_holds_v_agree with rs. rewrite <- fact_holds_v_eq. apply H0; auto.
  intros. rewrite Regmap.gso; auto. intro; subst; congruence.
Qed.

Lemma set_fact_sound:
  forall M rs m mp r v f,
  facts_ok M mp ->
  facts_hold ge sp rs m mp ->
  fact_holds_v rs m v f ->
  facts_hold ge sp (rs#r <- v) m (set_fact M r f mp).
Proof.
  intros. unfold set_fact.
  destruct (kill_one r (subst_for r mp) f) as [f'|] eqn:K.
- red; intros. rewrite PTree.gsspec in H2. destruct (peq r0 r).
  + inv H2. rewrite fact_holds_v_eq. rewrite Regmap.gss. eapply kill_one_sound; eauto.
  + eapply kill_reg_m_sound; eauto.
- apply kill_reg_m_sound; auto.
Qed.

Lemma kill_loads_sound:
  forall rs m mp m',
  facts_hold ge sp rs m mp ->
  facts_hold ge sp rs m' (kill_loads mp).
Proof.
  unfold kill_loads; intros; red; intros.
  rewrite PTree.gfilter1 in H0. destruct (mp!r) as [f'|] eqn:E; try discriminate.
  destruct (is_expr_fact f') eqn:X; inv H0.
  exploit H; eauto. destruct f; simpl in *; auto; discriminate.
Qed.

Lemma kill_regs_same:
  forall M rl rs m mp,
  facts_ok M mp ->
  facts_hold ge sp rs m mp ->
  facts_hold ge sp rs m (kill_regs M rl mp).
Proof.
  induction rl; simpl; intros. auto.
  apply IHrl. apply kill_reg_m_ok; auto. apply facts_hold_ext with (rs#a <- (rs#a)).
  intros. rewrite Regmap.gsspec. destruct (peq r a); subst; auto.
  apply kill_reg_m_sound; auto.
Qed.

(** Soundness of the transfer function, instruction by instruction. *)

Lemma transfer_op_sound:
  forall rel M rs m mp op (args: list reg) (res: reg) v,
  facts_ok M mp ->
  facts_hold ge sp rs m mp ->
  eval_operation ge sp op rs##args m = Some v ->
  facts_hold ge sp (rs#res <- v) m (transfer_op rel M op args res mp).
Proof.
  intros until v; intros OK H H0. unfold transfer_op.
  destruct (is_move_operation op args) as [src|] eqn:MV.
- exploit is_move_operation_correct; eauto. intros [? ?]; subst op args.
  simpl in H0. inv H0.
  assert (DFL: facts_hold ge sp (rs#res <- (rs#src)) m
                 (match rel!res with
                  | Some _ => set_fact M res (Fexpr (Sreg src)) mp
                  | None => kill_reg_m M res mp end)).
  { destruct (rel!res). apply set_fact_sound; [auto | auto | reflexivity]. apply kill_reg_m_sound; auto. }
  destruct (mp!src) as [[e|chunk addr el]|] eqn:E; auto.
  apply set_fact_sound; auto. rewrite <- fact_holds_v_eq. apply H; auto.
- destruct (rel!res). 2: apply kill_reg_m_sound; auto.
  destruct (op_depends_on_memory op) eqn:DM.
  apply kill_reg_m_sound; auto.
  apply set_fact_sound; auto. simpl.
  rewrite sregs_sound. rewrite <- H0. apply op_depends_on_memory_correct; auto.
Qed.

Lemma transfer_load_sound:
  forall M rs m mp chunk addr args dst a v,
  facts_ok M mp ->
  facts_hold ge sp rs m mp ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  facts_hold ge sp (rs#dst <- v) m (set_fact M dst (Fload chunk addr (sregs args)) mp).
Proof.
  intros until v; intros OK H H0 H1. apply set_fact_sound; auto. simpl; intros.
  rewrite sregs_sound in H2. inv H2.
  assert (a0 = a) by congruence. subst a0.
  assert (v' = v) by congruence. subst v'. auto.
Qed.

Lemma load_result_full:
  forall chunk v, store_full chunk = true -> Val.lessdef (Val.load_result chunk v) v.
Proof.
  intros. destruct chunk; try discriminate; destruct v; simpl; auto;
  destruct Archi.ptr64; auto.
Qed.

Lemma transfer_store_sound:
  forall rel M rs m mp chunk addr args src s a m',
  facts_hold ge sp rs m mp ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.storev chunk m a rs#src = Some m' ->
  facts_hold ge sp rs m' (transfer_instr rel M (Istore chunk addr args src s) mp).
Proof.
  intros. simpl.
  assert (K: facts_hold ge sp rs m' (kill_loads mp)) by (eapply kill_loads_sound; eauto).
  destruct (store_full chunk) eqn:FULL; auto.
  red; intros. rewrite PTree.gsspec in H2. destruct (peq r src); auto.
  inv H2. simpl; intros.
  rewrite sregs_sound in H2. inv H2.
  assert (a0 = a) by congruence. subst a0.
  destruct a; simpl in H1, H4; try discriminate.
  destruct (zle (Ptrofs.unsigned i + size_chunk chunk) Ptrofs.modulus); try discriminate.
  rewrite (Mem.load_store_same _ _ _ _ _ _ H1) in H4. inv H4.
  apply load_result_full; auto.
Qed.

Lemma transfer_call_sound:
  forall M rs m mp res v m',
  facts_ok M mp ->
  facts_hold ge sp rs m mp ->
  facts_hold ge sp (rs#res <- v) m' (kill_reg_m M res (kill_loads mp)).
Proof.
  intros. apply kill_reg_m_sound. apply kill_loads_ok; auto. eapply kill_loads_sound; eauto.
Qed.

Lemma transfer_builtin_sound:
  forall M rs m mp res v m',
  facts_ok M mp ->
  facts_hold ge sp rs m mp ->
  facts_hold ge sp (regmap_setres res v rs) m' (kill_regs M (params_of_builtin_res res) (kill_loads mp)).
Proof.
  intros. destruct res; simpl.
- apply kill_reg_m_sound. apply kill_loads_ok; auto. eapply kill_loads_sound; eauto.
- eapply kill_loads_sound; eauto.
- apply kill_regs_same. apply kill_loads_ok; auto. eapply kill_loads_sound; eauto.
Qed.

Lemma find_load_sound:
  forall rs m mp chunk addr args r,
  facts_hold ge sp rs m mp ->
  find_load mp chunk addr args = Some r ->
  fact_holds_v rs m rs#r (Fload chunk addr (sregs args)).
Proof.
  unfold find_load; intros.
  set (l := filter (fun p => match_load mp chunk addr (sregs args) (snd p)) (PTree.elements mp)) in H0.
  assert (MIN: forall (l': list (positive * fact)) r0,
               fold_left (fun r q => Pos.min r (fst q)) l' r0 = r0
            \/ exists f, In (fold_left (fun r q => Pos.min r (fst q)) l' r0, f) l').
  { induction l' as [|[r1 f1] l' IH]; simpl; intros. auto.
    destruct (IH (Pos.min r0 r1)) as [E|[f E]].
    - rewrite E. destruct (Pos.min_spec r0 r1) as [[_ X]|[_ X]]; rewrite X; auto.
      right; exists f1; simpl; auto.
    - right; exists f; auto. }
  assert (IN: exists f, In (r, f) l).
  { destruct l as [|[r0 f0] l'] eqn:L; inv H0.
    destruct (MIN l' r0) as [E|[f E]]; rewrite ? E.
    exists f0; simpl; auto.
    exists f; simpl; auto. }
  destruct IN as [f IN]. unfold l in IN. apply filter_In in IN. destruct IN as [A B]. simpl in B.
  apply PTree.elements_complete in A.
  unfold match_load in B. destruct f as [|chunk' addr' el']; try discriminate.
  destruct (chunk_eq chunk' chunk); try discriminate.
  destruct (eq_addressing addr' addr); try discriminate. subst.
  destruct (au_list_with (au mp mp au_fuel) el' (sregs args)) as [el|] eqn:AU; try discriminate.
  exploit (au_list_with_sound ge sp rs mp mp). intros; eapply au_sound; eauto. eexact AU.
  intros [P Q].
  assert (EX: exprs_hold ge sp rs mp) by (eapply facts_exprs_hold; eauto).
  specialize (P EX). specialize (Q EX). rewrite P in Q.
  exploit H; eauto. simpl. intros. eapply H1; eauto. congruence.
Qed.

End SEMANTICS.

(** Correctness of the dataflow analysis. *)

Lemma analyze_entry:
  forall {F V} (ge: Genv.t F V) sp f rs m,
  lholds ge sp rs m (analyze f)!!(fn_entrypoint f).
Proof.
  intros. unfold analyze, analyze_rel.
  assert (E: lholds ge sp rs m (PMap.init empty_facts)!!(fn_entrypoint f)).
  { rewrite PMap.gi. simpl; red; intros. rewrite PTree.gempty in H; discriminate. }
  destruct (too_big f (relevant_regs (fn_code f))); auto.
  destruct (DS.fixpoint (fn_code f) successors_instr
              (transfer (relevant_regs (fn_code f)) (mentionable (relevant_regs (fn_code f)) (fn_code f)) f)
              (fn_entrypoint f) empty_facts) as [res|] eqn:FIX; auto.
  apply lholds_ge with empty_facts. eapply DS.fixpoint_entry; eauto.
  simpl; red; intros. rewrite PTree.gempty in H; discriminate.
Qed.

Lemma analyze_succ:
  forall {F V} (ge: Genv.t F V) sp f pc i s rs m rs' m',
  (fn_code f)!pc = Some i ->
  In s (successors_instr i) ->
  lholds ge sp rs m (analyze f)!!pc ->
  (forall rel M mp, facts_ok M mp -> facts_hold ge sp rs m mp ->
                    facts_hold ge sp rs' m' (transfer_instr rel M i mp)) ->
  lholds ge sp rs' m' (analyze f)!!s.
Proof.
  intros. generalize (analyze_ok f pc). intros OK.
  destruct ((analyze f)!!pc) as [|mp] eqn:A; simpl in H1, OK; try contradiction.
  set (rel := relevant_regs (fn_code f)) in *.
  set (M := mentionable rel (fn_code f)) in *.
  apply lholds_ge with (transfer rel M f pc (analyze f)!!pc).
- assert (INIT: LFacts.ge (PMap.init empty_facts)!!s (transfer rel M f pc (analyze f)!!pc)).
  { rewrite PMap.gi. destruct (transfer rel M f pc (analyze f)!!pc); simpl; auto.
    intros. red; intros. rewrite PTree.gempty in H4; discriminate. }
  unfold analyze at 1. unfold analyze_rel. fold rel. fold M.
  destruct (too_big f rel) eqn:TB; auto.
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer rel M f) (fn_entrypoint f) empty_facts) as [res|] eqn:FIX; auto.
  replace (analyze f) with res.
  eapply DS.fixpoint_solution; eauto. intros; reflexivity.
  unfold analyze, analyze_rel. fold rel. fold M. rewrite TB, FIX; auto.
- rewrite A. unfold transfer. rewrite H. simpl. auto.
Qed.

(** * Correctness of the replacement of loads *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Section PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_cons:
      forall res f sp pc rs s rs' s'
           (SAT: forall v m, lholds ge sp (rs#res <- v) m (analyze f)!!pc)
           (RLD: regs_lessdef rs rs')
           (STACKS: match_stackframes s s'),
    match_stackframes
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (transf_function f) sp pc rs' :: s').

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f
             (SAT: lholds ge sp rs m (analyze f)!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m')
             (STACKS: match_stackframes s s'),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function f) sp pc rs' m')
  | match_states_call:
      forall s f args m s' args' m'
             (STACKS: match_stackframes s s')
             (ARGS: Val.lessdef_list args args')
             (MEXT: Mem.extends m m'),
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef f) args' m')
  | match_states_return:
      forall s s' v v' m m'
             (STACK: match_stackframes s s')
             (RES: Val.lessdef v v')
             (MEXT: Mem.extends m m'),
      match_states (Returnstate s v m)
                   (Returnstate s' v' m').

Lemma transf_code_at:
  forall f pc i,
  (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!pc = Some (transf_instr (analyze f) pc i).
Proof.
  intros. unfold transf_function; simpl. rewrite PTree.gmap. rewrite H. auto.
Qed.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get ?pc (fn_code ?f) = Some ?instr) |- _ =>
      generalize (transf_code_at _ _ _ H); simpl transf_instr
  end.

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

- (* Inop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analyze_succ; eauto; simpl; auto.

- (* Iop *)
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  try (rewrite <- A; apply eval_operation_preserved; exact symbols_preserved).
  econstructor; eauto.
  eapply analyze_succ; eauto. simpl; auto.
  intros; simpl. eapply transfer_op_sound; eauto.
  apply set_reg_lessdef; auto.

- (* Iload *)
  assert (TR: forall rel M mp, facts_ok M mp -> facts_hold ge sp rs m mp ->
              facts_hold ge sp (rs#dst <- v) m (transfer_instr rel M (Iload chunk addr args dst pc') mp)).
  { intros; simpl. eapply transfer_load_sound; eauto. }
  destruct ((analyze f)!!pc) as [|mp] eqn:AP; simpl in SAT; try contradiction.
  destruct (find_load mp chunk addr args) as [r|] eqn:FL.
+ (* replaced by a move *)
  assert (LD: Val.lessdef v rs#r).
  { generalize (find_load_sound ge sp rs m mp chunk addr args r SAT FL). unfold fact_holds_v. intros LDF. eapply LDF; eauto.
    apply sregs_sound. }
  econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analyze_succ; eauto. simpl; auto. rewrite AP; auto.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.
+ (* not replaced *)
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact H0.
  intros [a' [A B]].
  exploit Mem.loadv_extends; eauto.
  intros [v' [X Y]].
  econstructor; split.
  eapply exec_Iload; eauto.
  try (rewrite <- A; apply eval_addressing_preserved; exact symbols_preserved).
  econstructor; eauto.
  eapply analyze_succ; eauto. simpl; auto. rewrite AP; auto.
  apply set_reg_lessdef; auto.

- (* Istore *)
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact H0.
  intros [a' [A B]].
  exploit Mem.storev_extends; eauto. intros [m'' [X Y]].
  econstructor; split.
  eapply exec_Istore; eauto.
  try (rewrite <- A; apply eval_addressing_preserved; exact symbols_preserved).
  econstructor; eauto.
  eapply analyze_succ; eauto. simpl; auto.
  intros. eapply transfer_store_sound; eauto.

- (* Icall *)
  econstructor; split.
  eapply exec_Icall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto.
  apply sig_preserved.
  econstructor; eauto.
  econstructor; eauto.
  intros. eapply analyze_succ; eauto. simpl; auto.
  intros. simpl. eapply transfer_call_sound; eauto.
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto.
  apply sig_preserved.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & A & B).
  exploit external_call_mem_extends; eauto.
  intros (v' & m1' & P & Q & R & S).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  eapply analyze_succ; eauto. simpl; auto.
  intros. simpl. eapply transfer_builtin_sound; eauto.
  apply set_res_lessdef; auto.

- (* Icond *)
  econstructor; split.
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef; eauto. apply regs_lessdef_regs; auto.
  econstructor; eauto.
  destruct b; eapply analyze_succ; eauto; simpl; auto.

- (* Ijumptable *)
  generalize (RLD arg); rewrite H0; intro LD; inv LD.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  econstructor; eauto.
  eapply analyze_succ; eauto. simpl. eapply list_nth_z_in; eauto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Ireturn; eauto.
  econstructor; eauto.
  destruct or; simpl; auto.

- (* internal function *)
  exploit Mem.alloc_extends; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (m'' & A & B).
  econstructor; split.
  simpl. eapply exec_function_internal; simpl; eauto using Val.has_argtype_list_lessdef.
  simpl. econstructor; eauto.
  apply analyze_entry.
  apply init_regs_lessdef; auto.

- (* external function *)
  exploit external_call_mem_extends; eauto.
  intros (v' & m1' & P & Q & R & S).
  econstructor; split.
  simpl. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

- (* return *)
  inv STACK.
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_preserved.
  constructor. constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv RES. inv STACK. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct.
Qed.

End PRESERVATION.

(** * Correctness of the insertion of moves *)

Section INSERT_SPEC.

Variable choice: node -> instruction -> option reg.
Variables maxpc maxreg: positive.
Variable c: code.
Hypothesis MAXPC: forall pc i, c!pc = Some i -> Ple pc maxpc.

Lemma insert_code_spec:
  forall pc i, c!pc = Some i ->
  (insert_code choice maxpc maxreg c)!pc = Some (redirect choice maxpc maxreg pc i)
  /\ (forall x t s, move_for choice maxreg pc i = Some (x, t, s) ->
      (insert_code choice maxpc maxreg c)!(Pos.add maxpc pc) = Some (Iop Omove (x :: nil) t s)).
Proof.
  intros pc0 i0 H0. unfold insert_code.
  set (c1 := PTree.map (redirect choice maxpc maxreg) c).
  set (P := fun (cm: code) (acc: code) =>
          (forall q, Ple q maxpc -> acc!q = c1!q) /\
          (forall q i, cm!q = Some i -> forall x t s, move_for choice maxreg q i = Some (x, t, s) ->
                acc!(Pos.add maxpc q) = Some (Iop Omove (x :: nil) t s))).
  assert (P c (PTree.fold (add_move choice maxpc maxreg) c c1)).
  { apply PTree_Properties.fold_rec; unfold P.
  - intros m m' a EQ [A B]. split; auto. intros. rewrite <- EQ in H. eauto.
  - split; auto. intros. rewrite PTree.gempty in H; discriminate.
  - intros m a k v NONE GET [A B]. unfold add_move.
    destruct (move_for choice maxreg k v) as [[[x t] s]|] eqn:MV.
    + split.
      * intros. rewrite PTree.gso. auto. extlia.
      * intros. rewrite PTree.gsspec in H. rewrite PTree.gsspec.
        destruct (peq (Pos.add maxpc q) (Pos.add maxpc k)).
        assert (q = k) by (eapply Pos.add_reg_l; eauto). subst q.
        rewrite peq_true in H. inv H. rewrite MV in H1; inv H1. auto.
        destruct (peq q k). subst; contradiction. eauto.
    + split; auto. intros. rewrite PTree.gsspec in H. destruct (peq q k).
      inv H. congruence. eauto.
  }
  destruct H as [A B]. split.
  rewrite A by eauto. unfold c1. rewrite PTree.gmap, H0. auto.
  eauto.
Qed.

End INSERT_SPEC.

Lemma redirect_cases:
  forall ch maxpc maxreg pc i,
  (move_for ch maxreg pc i = None /\ redirect ch maxpc maxreg pc i = i)
  \/ (exists x t s, move_for ch maxreg pc i = Some (x, t, s) /\ Plt maxreg t /\
      ((exists chunk addr args, i = Iload chunk addr args x s
          /\ redirect ch maxpc maxreg pc i = Iload chunk addr args x (Pos.add maxpc pc))
    \/ (exists chunk addr args, i = Istore chunk addr args x s
          /\ redirect ch maxpc maxreg pc i = Istore chunk addr args x (Pos.add maxpc pc)))).
Proof.
  intros. unfold redirect, move_for.
  destruct (ch pc i) as [t|]; auto. destruct (plt maxreg t); auto.
  destruct i; auto; right; do 3 econstructor; split; eauto; split; auto.
  left; do 3 econstructor; eauto.
  right; do 3 econstructor; eauto.
Qed.

Lemma insert_at:
  forall f pc i, (fn_code f)!pc = Some i ->
  exists ch,
     (fn_code (insert_function f))!pc = Some (redirect ch (max_pc_function f) (max_reg_function f) pc i)
  /\ (forall x t s, move_for ch (max_reg_function f) pc i = Some (x, t, s) ->
      (fn_code (insert_function f))!(Pos.add (max_pc_function f) pc) = Some (Iop Omove (x :: nil) t s)).
Proof.
  intros. econstructor. unfold insert_function; simpl.
  apply insert_code_spec; auto. intros; eapply max_pc_function_sound; eauto.
Qed.

Definition agree (n: positive) (rs trs: regset) : Prop :=
  forall r, Ple r n -> trs#r = rs#r.

Lemma agree_set:
  forall n rs trs r v, agree n rs trs -> agree n (rs#r <- v) (trs#r <- v).
Proof.
  unfold agree; intros. rewrite ! Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_set_fresh:
  forall n rs trs t v, agree n rs trs -> Plt n t -> agree n rs (trs#t <- v).
Proof.
  unfold agree; intros. rewrite Regmap.gso. auto. extlia.
Qed.

Lemma agree_setres:
  forall n rs trs res v, agree n rs trs -> agree n (regmap_setres res v rs) (regmap_setres res v trs).
Proof.
  intros. destruct res; simpl; auto. apply agree_set; auto.
Qed.

Lemma agree_uses:
  forall f pc i rs trs,
  agree (max_reg_function f) rs trs ->
  (fn_code f)!pc = Some i ->
  forall r, In r (instr_uses i) -> trs#r = rs#r.
Proof.
  intros. apply H. eapply max_reg_function_use; eauto.
Qed.

Lemma agree_uses_list:
  forall f pc i rs trs rl,
  agree (max_reg_function f) rs trs ->
  (fn_code f)!pc = Some i ->
  (forall r, In r rl -> In r (instr_uses i)) ->
  trs##rl = rs##rl.
Proof.
  induction rl; simpl; intros; auto.
  f_equal. eapply agree_uses; eauto. eauto.
Qed.

Lemma eval_builtin_arg_agree:
  forall {F V} (ge: Genv.t F V) sp m rs trs a v,
  eval_builtin_arg ge (fun r => rs#r) sp m a v ->
  (forall r, In r (params_of_builtin_arg a) -> trs#r = rs#r) ->
  eval_builtin_arg ge (fun r => trs#r) sp m a v.
Proof.
  induction 1; simpl; intros; try (constructor; auto; fail).
- rewrite <- H; auto. constructor.
- constructor; [apply IHeval_builtin_arg1 | apply IHeval_builtin_arg2];
  intros; apply H1; apply in_app_iff; auto.
- constructor; [apply IHeval_builtin_arg1 | apply IHeval_builtin_arg2];
  intros; apply H1; apply in_app_iff; auto.
Qed.

Lemma eval_builtin_args_agree:
  forall {F V} (ge: Genv.t F V) sp m rs trs al vl,
  eval_builtin_args ge (fun r => rs#r) sp m al vl ->
  (forall r, In r (params_of_builtin_args al) -> trs#r = rs#r) ->
  eval_builtin_args ge (fun r => trs#r) sp m al vl.
Proof.
  induction 1; simpl; intros; constructor.
  eapply eval_builtin_arg_agree; eauto. intros; apply H1; apply in_app_iff; auto.
  apply IHlist_forall2. intros; apply H1; apply in_app_iff; auto.
Qed.

Definition match_prog_insert (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = insert_fundef f) eq p tp.

Lemma insert_program_match:
  forall p, match_prog_insert p (insert_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Section INSERT_PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog_insert prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma ins_symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.

Lemma ins_senv_preserved:
  Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.

Lemma ins_sig_preserved:
  forall f, funsig (insert_fundef f) = funsig f.
Proof.
  destruct f; auto.
Qed.

Lemma ins_find_function_translated:
  forall ros rs trs fd,
  find_function ge ros rs = Some fd ->
  (forall r, ros = inl r -> trs#r = rs#r) ->
  find_function tge ros trs = Some (insert_fundef fd).
Proof.
  intros until fd; destruct ros; simpl; intros.
- rewrite H0 by auto. apply (Genv.find_funct_transf TRANSL); auto.
- rewrite ins_symbols_preserved. destruct (Genv.find_symbol ge i); try discriminate.
  apply (Genv.find_funct_ptr_transf TRANSL); auto.
Qed.

Inductive ins_match_stackframes: list stackframe -> list stackframe -> Prop :=
  | ins_match_stackframes_nil:
      ins_match_stackframes nil nil
  | ins_match_stackframes_cons:
      forall res f sp pc rs s trs ts
           (AG: agree (max_reg_function f) rs trs)
           (STACKS: ins_match_stackframes s ts),
    ins_match_stackframes
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (insert_function f) sp pc trs :: ts).

Inductive ins_match_states: state -> state -> Prop :=
  | ins_match_states_intro:
      forall s sp pc rs m ts trs f
             (AG: agree (max_reg_function f) rs trs)
             (STACKS: ins_match_stackframes s ts),
      ins_match_states (State s f sp pc rs m)
                       (State ts (insert_function f) sp pc trs m)
  | ins_match_states_call:
      forall s fd args m ts
             (STACKS: ins_match_stackframes s ts),
      ins_match_states (Callstate s fd args m)
                       (Callstate ts (insert_fundef fd) args m)
  | ins_match_states_return:
      forall s ts v m
             (STACKS: ins_match_stackframes s ts),
      ins_match_states (Returnstate s v m)
                       (Returnstate ts v m).

(** Instructions other than loads and stores are unchanged. *)

Ltac Unchanged :=
  match goal with
  | H: (fn_code ?f)!?pc = Some ?i |- _ =>
      let ch := fresh "ch" in let C := fresh "C" in
      destruct (insert_at _ _ _ H) as (ch & C & _);
      destruct (redirect_cases ch (max_pc_function f) (max_reg_function f) pc i)
        as [[_ R] | (? & ? & ? & _ & _ & [(? & ? & ? & ? & _) | (? & ? & ? & ? & _)])];
      [rewrite R in C | discriminate | discriminate]
  end.

Lemma ins_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: ins_match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ ins_match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.

- (* Inop *)
  Unchanged.
  econstructor; split.
  apply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

- (* Iop *)
  Unchanged.
  econstructor; split.
  apply plus_one. eapply exec_Iop; eauto.
  erewrite agree_uses_list; eauto.
  try (rewrite <- H0; apply eval_operation_preserved; exact ins_symbols_preserved).
  simpl; auto.
  econstructor; eauto. apply agree_set; auto.

- (* Iload *)
  assert (ADDR: eval_addressing tge sp addr trs##args = Some a).
  { erewrite agree_uses_list; eauto.
    all: try (rewrite <- H0; apply eval_addressing_preserved; exact ins_symbols_preserved).
    all: simpl; auto. }
  destruct (insert_at _ _ _ H) as (ch & C & MV).
  destruct (redirect_cases ch (max_pc_function f) (max_reg_function f) pc (Iload chunk addr args dst pc'))
    as [[_ R] | (x & t & s0 & M & FRESH & [(? & ? & ? & E & R) | (? & ? & ? & ? & _)])];
    try discriminate.
+ rewrite R in C.
  econstructor; split.
  apply plus_one. eapply exec_Iload; eauto.
  econstructor; eauto. apply agree_set; auto.
+ inv E. rewrite R in C. specialize (MV _ _ _ M).
  econstructor; split.
  eapply plus_two. eapply exec_Iload; eauto.
  eapply exec_Iop; eauto. simpl; eauto. traceEq.
  econstructor; eauto. rewrite Regmap.gss.
  apply agree_set_fresh; auto. apply agree_set; auto.

- (* Istore *)
  assert (ADDR: eval_addressing tge sp addr trs##args = Some a).
  { erewrite agree_uses_list; eauto.
    all: try (rewrite <- H0; apply eval_addressing_preserved; exact ins_symbols_preserved).
    all: simpl; auto. }
  assert (SRC: trs#src = rs#src).
  { eapply agree_uses; eauto. simpl; auto. }
  destruct (insert_at _ _ _ H) as (ch & C & MV).
  destruct (redirect_cases ch (max_pc_function f) (max_reg_function f) pc (Istore chunk addr args src pc'))
    as [[_ R] | (x & t & s0 & M & FRESH & [(? & ? & ? & ? & _) | (? & ? & ? & E & R)])];
    try discriminate.
+ rewrite R in C.
  econstructor; split.
  apply plus_one. eapply exec_Istore; eauto. rewrite SRC; eauto.
  econstructor; eauto.
+ inv E. rewrite R in C. specialize (MV _ _ _ M).
  econstructor; split.
  eapply plus_two. eapply exec_Istore; eauto. rewrite SRC; eauto.
  eapply exec_Iop; eauto. simpl; eauto. traceEq.
  econstructor; eauto.
  apply agree_set_fresh; auto.

- (* Icall *)
  Unchanged.
  assert (ARGS: trs##args = rs##args).
  { eapply agree_uses_list; eauto. intros; destruct ros; simpl; auto. }
  assert (FIND: find_function tge ros trs = Some (insert_fundef fd)).
  { eapply ins_find_function_translated; eauto.
    intros; subst ros. eapply agree_uses; eauto. simpl; auto. }
  econstructor; split.
  apply plus_one. eapply exec_Icall; eauto. apply ins_sig_preserved.
  rewrite ARGS. econstructor; eauto. econstructor; eauto.

- (* Itailcall *)
  Unchanged.
  assert (ARGS: trs##args = rs##args).
  { eapply agree_uses_list; eauto. intros; destruct ros; simpl; auto. }
  assert (FIND: find_function tge ros trs = Some (insert_fundef fd)).
  { eapply ins_find_function_translated; eauto.
    intros; subst ros. eapply agree_uses; eauto. simpl; auto. }
  econstructor; split.
  apply plus_one. eapply exec_Itailcall; eauto. apply ins_sig_preserved.
  rewrite ARGS. econstructor; eauto.

- (* Ibuiltin *)
  Unchanged.
  econstructor; split.
  apply plus_one. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact ins_symbols_preserved.
  eapply eval_builtin_args_agree; eauto.
  intros. eapply agree_uses; eauto. simpl; auto.
  eapply external_call_symbols_preserved; eauto. apply ins_senv_preserved.
  econstructor; eauto. apply agree_setres; auto.

- (* Icond *)
  Unchanged.
  econstructor; split.
  apply plus_one. eapply exec_Icond; eauto.
  erewrite agree_uses_list; eauto.
  econstructor; eauto.

- (* Ijumptable *)
  Unchanged.
  econstructor; split.
  apply plus_one. eapply exec_Ijumptable; eauto.
  erewrite agree_uses; eauto. simpl; auto.
  econstructor; eauto.

- (* Ireturn *)
  Unchanged.
  econstructor; split.
  apply plus_one. eapply exec_Ireturn; eauto.
  replace (regmap_optget or Vundef trs) with (regmap_optget or Vundef rs).
  econstructor; eauto.
  destruct or; simpl; auto. symmetry; eapply agree_uses; eauto. simpl; auto.

- (* internal function *)
  econstructor; split.
  apply plus_one. simpl. eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto. red; auto.

- (* external function *)
  econstructor; split.
  apply plus_one. simpl. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply ins_senv_preserved.
  econstructor; eauto.

- (* return *)
  inv STACKS.
  econstructor; split.
  apply plus_one. eapply exec_return; eauto.
  econstructor; eauto. apply agree_set; auto.
Qed.

Lemma ins_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ ins_match_states st1 st2.
Proof.
  intros. inv H.
  exploit (Genv.find_funct_ptr_transf TRANSL); eauto. intro FIND.
  exists (Callstate nil (insert_fundef f) nil m0); split.
  econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite ins_symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply ins_sig_preserved.
  constructor. constructor.
Qed.

Lemma ins_final_states:
  forall st1 st2 r,
  ins_match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Theorem insert_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply ins_senv_preserved.
  eexact ins_initial_states.
  eexact ins_final_states.
  exact ins_step_correct.
Qed.

End INSERT_PRESERVATION.
