(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for induction-variable widening. *)

Require Import Coqlib Maps AST Linking Integers Values Memory Globalenvs.
Require Import Events Smallstep.
Require Import Op Registers RTL LICMop IVop IVdomain IVwiden.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

(** * Arithmetic lemmas *)

Lemma int64_repr_add:
  forall a b, Int64.repr (a + b) = Int64.add (Int64.repr a) (Int64.repr b).
Proof.
  intros. rewrite Int64.add_unsigned. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_unsigned_repr.
Qed.

Lemma int64_add_sub_cancel:
  forall x y, Int64.add y (Int64.sub x y) = x.
Proof.
  intros. rewrite Int64.sub_add_opp, Int64.add_permut, Int64.add_neg_zero.
  apply Int64.add_zero.
Qed.

Lemma int64_add_neg_cancel:
  forall x d, Int64.add (Int64.add x d) (Int64.neg d) = x.
Proof.
  intros. rewrite Int64.add_assoc, Int64.add_neg_zero. apply Int64.add_zero.
Qed.

Lemma addl_longofint_zero:
  forall v, Val.addl (Val.longofint v) (Vlong Int64.zero) = Val.longofint v.
Proof.
  destruct v; simpl; auto. rewrite Int64.add_zero; auto.
Qed.

Lemma int_signed_in_int64:
  forall x, Int64.min_signed <= Int.signed x <= Int64.max_signed.
Proof.
  intros. generalize (Int.signed_range x). intros [A B].
  assert (C: Int64.min_signed <= Int.min_signed) by (unfold Z.le; vm_compute; discriminate).
  assert (D: Int.max_signed <= Int64.max_signed) by (unfold Z.le; vm_compute; discriminate).
  lia.
Qed.

Lemma signed64_sext:
  forall x, Int64.signed (Int64.repr (Int.signed x)) = Int.signed x.
Proof.
  intros. apply Int64.signed_repr. apply int_signed_in_int64.
Qed.

Lemma signed_add_no_overflow:
  forall x n,
  Int.min_signed <= Int.signed x + Int.signed n <= Int.max_signed ->
  Int.signed (Int.add x n) = Int.signed x + Int.signed n.
Proof.
  intros. rewrite Int.add_signed. apply Int.signed_repr; auto.
Qed.

Lemma int_eq_signed:
  forall x y, Int.signed x = Int.signed y -> x = y.
Proof.
  intros. rewrite <- (Int.repr_signed x), <- (Int.repr_signed y). congruence.
Qed.

Lemma eq_sext:
  forall x y,
  Int64.eq (Int64.repr (Int.signed x)) (Int64.repr (Int.signed y)) = Int.eq x y.
Proof.
  intros. destruct (Int.eq_dec x y) as [E | N].
- subst y. rewrite Int.eq_true, Int64.eq_true. auto.
- rewrite Int.eq_false by auto. apply Int64.eq_false. intros E.
  apply N. apply int_eq_signed.
  rewrite <- (signed64_sext x), <- (signed64_sext y). congruence.
Qed.

Lemma lt_sext:
  forall x y,
  Int64.lt (Int64.repr (Int.signed x)) (Int64.repr (Int.signed y)) = Int.lt x y.
Proof.
  intros. unfold Int64.lt, Int.lt. rewrite ! signed64_sext. auto.
Qed.

Lemma cmpl_sext:
  forall c x y,
  Int64.cmp c (Int64.repr (Int.signed x)) (Int64.repr (Int.signed y)) = Int.cmp c x y.
Proof.
  intros. destruct c; simpl; rewrite ?eq_sext, ?lt_sext; auto.
Qed.

(** Comparisons of signed values. *)

Definition zcmp (c: comparison) (x y: Z) : Prop :=
  match c with
  | Ceq => x = y
  | Cne => x <> y
  | Clt => x < y
  | Cle => x <= y
  | Cgt => x > y
  | Cge => x >= y
  end.

Lemma int_cmp_zcmp:
  forall c x y, Int.cmp c x y = true -> zcmp c (Int.signed x) (Int.signed y).
Proof.
  intros c x y C. destruct c; simpl in *; unfold Int.lt in *.
- f_equal. apply Int.same_if_eq; auto.
- intros E. apply int_eq_signed in E. subst y. rewrite Int.eq_true in C. discriminate.
- destruct (zlt (Int.signed x) (Int.signed y)); [lia | discriminate].
- destruct (zlt (Int.signed y) (Int.signed x)); [discriminate | lia].
- destruct (zlt (Int.signed y) (Int.signed x)); [lia | discriminate].
- destruct (zlt (Int.signed x) (Int.signed y)); [discriminate | lia].
Qed.

Lemma int64_cmp_zcmp:
  forall c x y, Int64.cmp c x y = true -> zcmp c (Int64.signed x) (Int64.signed y).
Proof.
  intros c x y C. destruct c; simpl in *; unfold Int64.lt in *.
- f_equal. apply Int64.same_if_eq; auto.
- intros E. assert (x = y).
  { rewrite <- (Int64.repr_signed x), <- (Int64.repr_signed y). congruence. }
  subst y. rewrite Int64.eq_true in C. discriminate.
- destruct (zlt (Int64.signed x) (Int64.signed y)); [lia | discriminate].
- destruct (zlt (Int64.signed y) (Int64.signed x)); [discriminate | lia].
- destruct (zlt (Int64.signed y) (Int64.signed x)); [lia | discriminate].
- destruct (zlt (Int64.signed x) (Int64.signed y)); [discriminate | lia].
Qed.

Lemma int_cmp_outcome:
  forall c x y b, Int.cmp c x y = b -> Int.cmp (outcome c b) x y = true.
Proof.
  intros. destruct b; simpl; auto. rewrite Int.negate_cmp, H. auto.
Qed.

Lemma int64_cmp_outcome:
  forall c x y b, Int64.cmp c x y = b -> Int64.cmp (outcome c b) x y = true.
Proof.
  intros. destruct b; simpl; auto. rewrite Int64.negate_cmp, H. auto.
Qed.

(** * Semantics of facts *)

(** 64-bit integers form a ring. *)

Lemma int64_ring:
  ring_theory Int64.zero Int64.one Int64.add Int64.mul Int64.sub Int64.neg (@eq int64).
Proof.
  constructor.
- exact Int64.add_zero_l.
- exact Int64.add_commut.
- intros; symmetry; apply Int64.add_assoc.
- intros; rewrite Int64.mul_commut; apply Int64.mul_one.
- exact Int64.mul_commut.
- intros; symmetry; apply Int64.mul_assoc.
- intros; apply Int64.mul_add_distr_l.
- exact Int64.sub_add_opp.
- exact Int64.add_neg_zero.
Qed.

Add Ring int64ring: int64_ring.

(** [lin v m d] is [(long) v * m + d]. *)

Definition lin (v: val) (m d: int64) : val :=
  Val.addl (Val.mull (Val.longofint v) (Vlong m)) (Vlong d).

Definition bval (rs: regset) (b: option reg) (v: val) : val :=
  match b with Some r => Val.addl rs#r v | None => v end.

Lemma lin_spec:
  forall v m d,
  lin v m d = match v with
              | Vint n => Vlong (Int64.add (Int64.mul (Int64.repr (Int.signed n)) m) d)
              | _ => Vundef
              end.
Proof.
  destruct v; reflexivity.
Qed.

Lemma lin_one_zero:
  forall v, lin v Int64.one Int64.zero = Val.longofint v.
Proof.
  intros. rewrite lin_spec. destruct v; auto. simpl. f_equal. ring.
Qed.

Lemma lin_addl:
  forall v m d n, Val.addl (lin v m d) (Vlong n) = lin v m (Int64.add d n).
Proof.
  intros. rewrite ! lin_spec. destruct v; auto. simpl. f_equal. ring.
Qed.

Lemma bval_addl:
  forall rs b v m d n,
  Val.addl (bval rs b (lin v m d)) (Vlong n) = bval rs b (lin v m (Int64.add d n)).
Proof.
  intros. destruct b as [r|]; simpl.
- rewrite Val.addl_assoc, lin_addl. auto.
- apply lin_addl.
Qed.

Lemma lin_scale:
  forall v m d sc n,
  Val.addl (Val.mull (lin v m d) (Vlong sc)) (Vlong n)
  = lin v (Int64.mul m sc) (Int64.add (Int64.mul d sc) n).
Proof.
  intros. rewrite ! lin_spec. destruct v; auto. simpl. f_equal. ring.
Qed.

Lemma lin_mul:
  forall v m d sc,
  Val.mull (lin v m d) (Vlong sc)
  = lin v (Int64.mul m sc) (Int64.add (Int64.mul d sc) Int64.zero).
Proof.
  intros. rewrite ! lin_spec. destruct v; auto. simpl. f_equal. ring.
Qed.

Lemma lin_sum:
  forall v m d m' d' n,
  Val.addl (Val.addl (lin v m d) (lin v m' d')) (Vlong n)
  = lin v (Int64.add m m') (Int64.add (Int64.add d d') n).
Proof.
  intros. rewrite ! lin_spec. destruct v; auto. simpl. f_equal. ring.
Qed.

Lemma lin_vlong_or_undef:
  forall v m d, lin v m d = Vundef \/ exists n, lin v m d = Vlong n.
Proof.
  intros. rewrite lin_spec. destruct v; eauto.
Qed.

Definition fact_holds (rs: regset) (f: fact) : Prop :=
  match f with
  | Flin x b i m d => rs#x = bval rs b (lin rs#i m d)
  | Fle i k => exists n, rs#i = Vint n /\ Int.signed n <= k
  | Fge i k => exists n, rs#i = Vint n /\ k <= Int.signed n
  | Feq x y => rs#x = rs#y
  end.

Definition facts_hold (l: list fact) (rs: regset) : Prop :=
  forall f, In f l -> fact_holds rs f.

Lemma facts_hold_nil:
  forall rs, facts_hold nil rs.
Proof.
  intros rs f IN. contradiction.
Qed.

Lemma facts_hold_app:
  forall l1 l2 rs, facts_hold l1 rs -> facts_hold l2 rs -> facts_hold (l1 ++ l2) rs.
Proof.
  intros l1 l2 rs H1 H2 f IN. apply in_app_or in IN. destruct IN; auto.
Qed.

Lemma bval_ext:
  forall rs rs' b v,
  (forall r, In r (base_regs b) -> rs'#r = rs#r) ->
  bval rs' b v = bval rs b v.
Proof.
  intros. destruct b as [r|]; simpl in *; auto. rewrite H; auto.
Qed.

Lemma fact_holds_ext:
  forall rs rs' f,
  (forall r, In r (fact_regs f) -> rs'#r = rs#r) ->
  fact_holds rs f -> fact_holds rs' f.
Proof.
  intros rs rs' f E H. destruct f as [x b i m d | i k | i k | x y]; simpl in *.
- rewrite (E x), (E i), (bval_ext rs rs'); auto.
- rewrite (E i); auto.
- rewrite (E i); auto.
- rewrite (E x), (E y); auto.
Qed.

Lemma fresh_for_true:
  forall r b i, fresh_for r b i = true -> i <> r /\ ~In r (base_regs b).
Proof.
  unfold fresh_for; intros. rewrite andb_true_iff, ! negb_true_iff in H.
  destruct H as [A B]. split.
  destruct (peq i r); [discriminate | auto].
  destruct (In_dec peq r (base_regs b)); [discriminate | auto].
Qed.

Lemma implied_sound:
  forall l f rs, implied l f = true -> facts_hold l rs -> fact_holds rs f.
Proof.
  intros l f rs IMP H. destruct f as [x b i m d | i k | i k | x y]; cbn [implied] in IMP;
  apply existsb_exists in IMP; destruct IMP as (g & IN & EQ).
- destruct (fact_eq (Flin x b i m d) g); [ | discriminate]. subst g. apply H; auto.
- destruct g as [ ? ? ? ? ? | j k' | ? ? | ? ? ]; try discriminate.
  rewrite andb_true_iff in EQ. destruct EQ as [E1 E2].
  destruct (peq i j); [ | discriminate]. subst j.
  destruct (zle k' k); [ | discriminate].
  destruct (H _ IN) as (n & A & B). exists n; split; auto. lia.
- destruct g as [ ? ? ? ? ? | ? ? | j k' | ? ? ]; try discriminate.
  rewrite andb_true_iff in EQ. destruct EQ as [E1 E2].
  destruct (peq i j); [ | discriminate]. subst j.
  destruct (zle k k'); [ | discriminate].
  destruct (H _ IN) as (n & A & B). exists n; split; auto. lia.
- destruct (fact_eq (Feq x y) g); [ | discriminate]. subst g. apply H; auto.
Qed.

Lemma check_succ_sound:
  forall fm l s rs,
  check_succ fm l s = true -> facts_hold l rs -> facts_hold (facts_at fm s) rs.
Proof.
  unfold check_succ; intros fm l s rs C H f IN.
  rewrite forallb_forall in C. eapply implied_sound; eauto.
Qed.

Lemma kill_sound:
  forall r l rs rs',
  facts_hold l rs ->
  (forall r', r' <> r -> rs'#r' = rs#r') ->
  facts_hold (kill r l) rs'.
Proof.
  unfold kill; intros r l rs rs' H E f IN. rewrite filter_In in IN. destruct IN as [IN M].
  apply fact_holds_ext with rs; auto.
  intros r' IN'. apply E. intros EQ; subst r'.
  unfold mentions in M. destruct (In_dec peq r (fact_regs f)); [discriminate | contradiction].
Qed.

Lemma kill_list_sound:
  forall rl l rs rs',
  facts_hold l rs ->
  (forall r', ~In r' rl -> rs'#r' = rs#r') ->
  facts_hold (kill_list rl l) rs'.
Proof.
  intros rl l rs rs' H E f IN.
  assert (A: In f l /\ forall r, In r rl -> mentions r f = false).
  { clear H E. revert IN. induction rl as [ | r rl IH]; simpl; intros IN.
    - split; auto. intros; contradiction.
    - unfold kill in IN at 1. rewrite filter_In in IN. destruct IN as [IN M].
      destruct (IH IN) as [A B]. split; auto.
      intros r' [EQ | IN']. subst r'. destruct (mentions r f); [discriminate | auto]. auto. }
  destruct A as [A B].
  apply fact_holds_ext with rs; auto.
  intros r' IN'. apply E. intros INr. specialize (B r' INr).
  unfold mentions in B. destruct (In_dec peq r' (fact_regs f)); [discriminate | contradiction].
Qed.

(** ** Soundness of the transfer functions *)

Lemma no_overflow_sound:
  forall l a n rs,
  no_overflow l a n = true -> facts_hold l rs ->
  exists x, rs#a = Vint x
         /\ Int.min_signed <= Int.signed x + Int.signed n <= Int.max_signed.
Proof.
  unfold no_overflow; intros l a n rs NO H.
  generalize (Int.signed_range n); intros RN.
  destruct (zle 0 (Int.signed n)) as [POS | NEG];
  apply existsb_exists in NO; destruct NO as (g & IN & EQ).
- destruct g as [ ? ? ? ? ? | i k | ? ? | ? ? ]; try discriminate.
  rewrite andb_true_iff in EQ. destruct EQ as [E1 E2].
  destruct (peq i a); [ | discriminate]. subst i.
  destruct (zle (k + Int.signed n) Int.max_signed); [ | discriminate].
  destruct (H _ IN) as (x & A & B). exists x; split; auto.
  generalize (Int.signed_range x); lia.
- destruct g as [ ? ? ? ? ? | ? ? | i k | ? ? ]; try discriminate.
  rewrite andb_true_iff in EQ. destruct EQ as [E1 E2].
  destruct (peq i a); [ | discriminate]. subst i.
  destruct (zle Int.min_signed (k + Int.signed n)); [ | discriminate].
  destruct (H _ IN) as (x & A & B). exists x; split; auto.
  generalize (Int.signed_range x); lia.
Qed.

(** Membership in the result of a conditional singleton. *)

Ltac clean_bools :=
  repeat match goal with
  | [ H: negb _ = true |- _ ] => apply negb_true_iff in H
  | [ H: _ = false |- _ ] =>
      match type of H with
      | context [peq ?a ?b] =>
          let E := fresh "E" in let N := fresh "N" in
          destruct (peq a b) as [E | N]; [simpl in H; discriminate | clear H]
      | context [In_dec peq ?a ?b] =>
          let E := fresh "E" in let N := fresh "N" in
          destruct (In_dec peq a b) as [E | N]; [simpl in H; discriminate | clear H]
      end
  | [ H: fresh_for _ _ _ = true |- _ ] =>
      let N1 := fresh "N" in let N2 := fresh "N" in
      apply fresh_for_true in H; destruct H as [N1 N2]
  end.

Ltac in_cond IN :=
  match type of IN with
  | In _ (if ?c then _ :: nil else nil) =>
      let C := fresh "C" in
      destruct c eqn:C; [ destruct IN as [IN | []]; InvBooleans; clean_bools | contradiction ]
  end.

Section GEN.

Variable rs: regset.
Variable l: list fact.
Hypothesis H: facts_hold l rs.
Variable res: reg.

Remark gso': forall v r, r <> res -> (rs#res <- v)#r = rs#r.
Proof. intros. apply Regmap.gso; auto. Qed.

Remark gss': forall v, (rs#res <- v)#res = v.
Proof. intros. apply Regmap.gss. Qed.

Lemma bval_set:
  forall v b w, ~In res (base_regs b) -> bval (rs#res <- v) b w = bval rs b w.
Proof.
  intros. apply bval_ext. intros r IN. apply gso'. intros E; subst; contradiction.
Qed.

Lemma flin_res:
  forall v b i m d,
  i <> res -> ~In res (base_regs b) ->
  v = bval rs b (lin rs#i m d) ->
  fact_holds (rs#res <- v) (Flin res b i m d).
Proof.
  intros. cbn [fact_holds]. rewrite gss', gso', bval_set; auto.
Qed.

Ltac flin := apply flin_res; [ auto | simpl in *; tauto | ].

Lemma move_fact_sound:
  forall v a, v = rs#a -> facts_hold (flat_map (move_fact a res) l) (rs#res <- v).
Proof.
  intros v a V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  destruct g as [x b i m d | i k | i k | ? ?]; cbn [move_fact] in IN; try contradiction;
  in_cond IN; subst.
- flin. auto.
- cbn [fact_holds] in *. rewrite gss'. auto.
- cbn [fact_holds] in *. rewrite gss'. auto.
Qed.

Lemma addl_fact_sound:
  forall v x n, v = Val.addl rs#x (Vlong n) -> facts_hold (flat_map (addl_fact x res n) l) (rs#res <- v).
Proof.
  intros v x n V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  destruct g as [y b i m d | i k | i k | ? ?]; cbn [addl_fact] in IN; try contradiction.
  in_cond IN; subst. flin.
  cbn [fact_holds] in H. rewrite H. apply bval_addl.
Qed.

Lemma scale_fact_sound:
  forall v x sc n,
  v = Val.addl (Val.mull rs#x (Vlong sc)) (Vlong n) ->
  facts_hold (flat_map (scale_fact x res sc n) l) (rs#res <- v).
Proof.
  intros v x sc n V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  destruct g as [y [b|] i m d | i k | i k | ? ?]; cbn [scale_fact] in IN; try contradiction.
  in_cond IN; subst. flin.
  cbn [fact_holds bval] in H. rewrite H. apply lin_scale.
Qed.

Lemma mul_fact_sound:
  forall v x n,
  v = Val.mull rs#x (Vlong n) ->
  facts_hold (flat_map (scale_fact x res n Int64.zero) l) (rs#res <- v).
Proof.
  intros v x n V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  destruct g as [y [b|] i m d | i k | i k | ? ?]; cbn [scale_fact] in IN; try contradiction.
  in_cond IN; subst. flin.
  cbn [fact_holds bval] in H. rewrite H. apply lin_mul.
Qed.

Lemma based_fact_sound:
  forall v x y sc n,
  v = Val.addl rs#x (Val.addl (Val.mull rs#y (Vlong sc)) (Vlong n)) ->
  facts_hold (flat_map (based_fact x y res sc n) l) (rs#res <- v).
Proof.
  intros v x y sc n V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  destruct g as [z [b|] i m d | i k | i k | ? ?]; cbn [based_fact] in IN; try contradiction.
  in_cond IN; subst. flin.
  cbn [fact_holds bval] in *. rewrite H. rewrite lin_scale. auto.
Qed.

Lemma based1_fact_sound:
  forall v x y n,
  v = Val.addl (Val.addl rs#x rs#y) (Vlong n) ->
  facts_hold (flat_map (based_fact x y res Int64.one n) l) (rs#res <- v).
Proof.
  intros v x y n V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  destruct g as [z [b|] i m d | i k | i k | ? ?]; cbn [based_fact] in IN; try contradiction.
  in_cond IN; subst. flin.
  cbn [fact_holds bval] in *. rewrite H. rewrite Val.addl_assoc, lin_addl.
  f_equal. rewrite ! lin_spec. destruct (rs#i); auto. f_equal. ring.
Qed.

Lemma lin_sum_scaled:
  forall w m d m' d' sc n,
  Val.addl (lin w m d) (Val.addl (Val.mull (lin w m' d') (Vlong sc)) (Vlong n))
  = lin w (Int64.add m (Int64.mul m' sc)) (Int64.add (Int64.add d (Int64.mul d' sc)) n).
Proof.
  intros. rewrite ! lin_spec. destruct w; auto. simpl. f_equal. ring.
Qed.

Lemma lin_sum_one:
  forall w m d m' d' n,
  Val.addl (Val.addl (lin w m d) (lin w m' d')) (Vlong n)
  = lin w (Int64.add m (Int64.mul m' Int64.one)) (Int64.add (Int64.add d (Int64.mul d' Int64.one)) n).
Proof.
  intros. rewrite ! lin_spec. destruct w; auto. simpl. f_equal. ring.
Qed.

Lemma sum_fact_sound:
  forall v x y sc n,
  (forall w m d m' d', rs#x = lin w m d -> rs#y = lin w m' d' ->
     v = lin w (Int64.add m (Int64.mul m' sc)) (Int64.add (Int64.add d (Int64.mul d' sc)) n)) ->
  facts_hold (flat_map (sum_fact l x y res sc n) l) (rs#res <- v).
Proof.
  intros v x y sc n V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  generalize (H g G); intros HG.
  destruct g as [z [b|] i m d | i k | i k | ? ?]; cbn [sum_fact] in IN; try contradiction.
  destruct (peq z x && negb (peq i res)) eqn:C; [ | contradiction].
  InvBooleans. clean_bools. subst z.
  apply in_flat_map in IN. destruct IN as (g' & G' & IN).
  generalize (H g' G'); intros HG'.
  destruct g' as [z' [b'|] i' m' d' | ? ? | ? ? | ? ?]; try contradiction.
  in_cond IN; subst. flin.
  cbn [fact_holds bval] in *. apply V; auto.
Qed.

Lemma shift_fact_sound:
  forall v a n x,
  rs#a = Vint x ->
  Int.min_signed <= Int.signed x + Int.signed n <= Int.max_signed ->
  v = Vint (Int.add x n) ->
  facts_hold (flat_map (shift_fact a res n) l) (rs#res <- v).
Proof.
  intros v a n x RA RANGE V f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  assert (SG := signed_add_no_overflow x n RANGE).
  destruct g as [y b i m d | i k | i k | ? ?]; cbn [shift_fact] in IN; [ | | | contradiction].
- destruct (peq i a && negb (peq y res) && negb (In_dec peq res (base_regs b))) eqn:C;
    [ | contradiction].
  destruct IN as [IN | []]. subst f. InvBooleans. clean_bools. subst i.
  cbn [fact_holds] in *.
  rewrite gso' by auto. rewrite gss', bval_set by auto.
  rewrite H, RA, V, ! lin_spec. f_equal. f_equal.
  rewrite SG, int64_repr_add. ring.
- in_cond IN; subst. cbn [fact_holds] in *. rewrite gss'.
  exists (Int.add x n); split; auto.
  destruct H as (x' & A & B). rewrite RA in A. inv A. lia.
- in_cond IN; subst. cbn [fact_holds] in *. rewrite gss'.
  exists (Int.add x n); split; auto.
  destruct H as (x' & A & B). rewrite RA in A. inv A. lia.
Qed.

End GEN.

Lemma gen_op_sound:
  forall (F V: Type) (ge: Genv.t F V) sp l op args res rs m v,
  facts_hold l rs ->
  eval_operation ge sp op rs##args m = Some v ->
  facts_hold (gen_op l op args res) (rs#res <- v).
Proof.
  intros until v; intros H EV. unfold gen_op.
  assert (DEFAULT:
    facts_hold (match classify_op op args with
                | OCaddimm a n => if no_overflow l a n then flat_map (shift_fact a res n) l else nil
                | OCintconst n => Fle res (Int.signed n) :: Fge res (Int.signed n) :: nil
                | OCsext a => if peq a res then nil else Flin res None a Int64.one Int64.zero :: nil
                | OCaddlimm x n => flat_map (addl_fact x res n) l
                | OCmullimm x n => flat_map (scale_fact x res n Int64.zero) l
                | OCscaledl x sc n => flat_map (scale_fact x res sc n) l
                | OCaddl x y n =>
                    flat_map (sum_fact l x y res Int64.one n) l
                    ++ flat_map (based_fact x y res Int64.one n) l
                    ++ flat_map (based_fact y x res Int64.one n) l
                | OCaddlscaled x y sc n =>
                    flat_map (sum_fact l x y res sc n) l ++ flat_map (based_fact x y res sc n) l
                | OCother => nil
                end) (rs#res <- v)).
  2: { destruct op; try exact DEFAULT.
       destruct args as [ | a [ | ? ?]]; try exact DEFAULT.
       simpl in EV. inv EV. apply facts_hold_app.
       destruct (peq a res); [apply facts_hold_nil | ].
       intros f [E | []]. subst f. cbn [fact_holds].
       rewrite Regmap.gss, Regmap.gso by auto. auto.
       apply move_fact_sound; auto. }
  generalize (classify_op_sound _ _ ge sp op args rs m v EV).
  destruct (classify_op op args) as [a n | n | a | x n | x n | x y n | x sc n | x y sc n | ];
  intros EQV; try subst v.
- (* 32-bit addition *)
  destruct (no_overflow l a n) eqn:NO; [ | apply facts_hold_nil].
  destruct (no_overflow_sound l a n rs NO H) as (x & RA & RANGE).
  eapply shift_fact_sound; eauto. rewrite RA; auto.
- (* constant *)
  intros f [E | [E | []]]; subst f; simpl; rewrite Regmap.gss; exists n; split; auto; lia.
- (* sign extension *)
  destruct (peq a res); [apply facts_hold_nil | ].
  intros f [E | []]. subst f. apply flin_res; [auto | simpl; tauto | ].
  simpl. rewrite lin_one_zero. auto.
- eapply addl_fact_sound; eauto.
- eapply mul_fact_sound; eauto.
- apply facts_hold_app. eapply sum_fact_sound; eauto.
  intros w m0 d0 m1 d1 X Y. rewrite X, Y. apply lin_sum_one.
  apply facts_hold_app. eapply based1_fact_sound; eauto.
  eapply based1_fact_sound; eauto. rewrite Val.addl_commut with (x := rs#y). auto.
- eapply scale_fact_sound; eauto.
- apply facts_hold_app. eapply sum_fact_sound; eauto.
  intros w m0 d0 m1 d1 X Y. rewrite X, Y. apply lin_sum_scaled.
  eapply based_fact_sound; eauto.
- apply facts_hold_nil.
Qed.

Lemma transfer_op_sound:
  forall (F V: Type) (ge: Genv.t F V) sp l op args res rs m v,
  facts_hold l rs ->
  eval_operation ge sp op rs##args m = Some v ->
  facts_hold (transfer_op l op args res) (rs#res <- v).
Proof.
  intros. unfold transfer_op. apply facts_hold_app.
  eapply gen_op_sound; eauto.
  eapply kill_sound; eauto. intros. apply Regmap.gso; auto.
Qed.

Lemma cmp_bounds_sound:
  forall l c a b x y rs,
  facts_hold l rs ->
  rs#a = Vint x -> rs#b = Vint y -> zcmp c (Int.signed x) (Int.signed y) ->
  facts_hold (cmp_bounds l c a b) rs.
Proof.
  intros until rs; intros H A B ZC.
  generalize (Int.signed_range x) (Int.signed_range y); intros RX RY.
  unfold cmp_bounds. apply facts_hold_app.
- destruct c; cbn [zcmp] in ZC; try apply facts_hold_nil;
  intros f [E | [E | []]]; subst f; cbn [fact_holds].
  + exists x; split; auto. lia.
  + exists y; split; auto. lia.
  + exists x; split; auto. lia.
  + exists y; split; auto. lia.
- intros f IN. apply in_flat_map in IN. destruct IN as (g & G & IN).
  specialize (H g G).
  destruct g as [? ? ? | j k | j k | ? ?]; destruct c; cbn [cmp_bound zcmp] in IN, ZC;
  try contradiction;
  match goal with
  | [ IN: In f (if peq j ?r then _ else nil) |- _ ] =>
      destruct (peq j r); [ | contradiction]; subst j;
      destruct IN as [E | []]; subst f; cbn [fact_holds] in *;
      destruct H as (z & Z1 & Z2)
  end;
  first [ rewrite A in Z1 | rewrite B in Z1 ]; inv Z1;
  first [ exists x; split; [assumption | lia] | exists y; split; [assumption | lia] ].
Qed.

Lemma cmpimm_bounds_sound:
  forall c a x k rs,
  rs#a = Vint x -> zcmp c (Int.signed x) k ->
  facts_hold (cmpimm_bounds c a k) rs.
Proof.
  intros until rs; intros A ZC.
  destruct c; cbn [cmpimm_bounds zcmp] in *; try apply facts_hold_nil.
- intros f [E | [E | []]]; subst f; cbn [fact_holds]; exists x; split; auto; lia.
- intros f [E | []]; subst f; cbn [fact_holds]; exists x; split; auto; lia.
- intros f [E | []]; subst f; cbn [fact_holds]; exists x; split; auto; lia.
- intros f [E | []]; subst f; cbn [fact_holds]; exists x; split; auto; lia.
- intros f [E | []]; subst f; cbn [fact_holds]; exists x; split; auto; lia.
Qed.

Lemma sext_of_sound:
  forall l x a rs,
  In a (sext_of l x) -> facts_hold l rs -> rs#x = Val.longofint rs#a.
Proof.
  unfold sext_of; intros l x a rs IN H.
  apply in_flat_map in IN. destruct IN as (g & G & IN).
  destruct g as [y [b|] i m d | ? ? | ? ? | ? ?]; try contradiction.
  destruct (peq y x); [subst y | simpl in IN; contradiction].
  destruct (Int64.eq m Int64.one) eqn:M; [ | simpl in IN; contradiction].
  destruct (Int64.eq d Int64.zero) eqn:D; [ | simpl in IN; contradiction].
  simpl in IN. destruct IN as [E | []]. subst a.
  apply Int64.same_if_eq in M. apply Int64.same_if_eq in D. subst m d.
  rewrite (H _ G). cbn [bval]. apply lin_one_zero.
Qed.

Lemma longofint_vlong:
  forall v n, Val.longofint v = Vlong n -> exists x, v = Vint x /\ n = Int64.repr (Int.signed x).
Proof.
  destruct v; simpl; intros; try discriminate. inv H. eauto.
Qed.

Lemma cond_facts_sound:
  forall l cond args rs m b,
  facts_hold l rs ->
  eval_condition cond rs##args m = Some b ->
  facts_hold (cond_facts l cond args b) rs.
Proof.
  intros until b; intros H EV. unfold cond_facts.
  generalize (classify_cond_sound cond args rs m b EV).
  destruct (classify_cond cond args) as [c x y | c x n | c x y | c x n | ]; intros C.
- unfold Val.cmp_bool in C.
  destruct (rs#x) eqn:X; try discriminate; destruct (rs#y) eqn:Y; try discriminate.
  inv C. eapply cmp_bounds_sound; eauto. apply int_cmp_zcmp. apply int_cmp_outcome; auto.
- unfold Val.cmp_bool in C.
  destruct (rs#x) eqn:X; try discriminate. inv C.
  eapply cmpimm_bounds_sound; eauto. apply int_cmp_zcmp. apply int_cmp_outcome; auto.
- intros f IN. apply in_flat_map in IN. destruct IN as (a & A & IN).
  apply in_flat_map in IN. destruct IN as (a' & A' & IN).
  rewrite (sext_of_sound l x a rs A H), (sext_of_sound l y a' rs A' H) in C.
  destruct (rs#a) as [ | xa | ? | ? | ? | ? ?] eqn:RA; cbn [Val.longofint Val.cmpl_bool] in C;
  try discriminate.
  destruct (rs#a') as [ | xa' | ? | ? | ? | ? ?] eqn:RA'; cbn [Val.longofint Val.cmpl_bool] in C;
  try discriminate.
  injection C; intros CB. rewrite cmpl_sext in CB.
  revert f IN. eapply cmp_bounds_sound; eauto.
  apply int_cmp_zcmp. apply int_cmp_outcome; auto.
- intros f IN. apply in_flat_map in IN. destruct IN as (a & A & IN).
  rewrite (sext_of_sound l x a rs A H) in C.
  destruct (rs#a) as [ | xa | ? | ? | ? | ? ?] eqn:RA; cbn [Val.longofint Val.cmpl_bool] in C;
  try discriminate.
  injection C; intros CB.
  assert (ZC: zcmp (outcome c b) (Int64.signed (Int64.repr (Int.signed xa))) (Int64.signed n)).
  { apply int64_cmp_zcmp. apply int64_cmp_outcome; auto. }
  rewrite signed64_sext in ZC.
  revert f IN. eapply cmpimm_bounds_sound; eauto.
- apply facts_hold_nil.
Qed.

Lemma transfer_cond_sound:
  forall l cond args rs m b,
  facts_hold l rs ->
  eval_condition cond rs##args m = Some b ->
  facts_hold (transfer_cond l cond args b) rs.
Proof.
  intros. unfold transfer_cond. apply facts_hold_app; auto.
  eapply cond_facts_sound; eauto.
Qed.

Lemma check_node_succ:
  forall fm pc i s rs,
  check_node fm (pc, i) = true ->
  (forall c a s1 s2, i <> Icond c a s1 s2) ->
  In s (successors_instr i) ->
  facts_hold (transfer (facts_at fm pc) i) rs ->
  facts_hold (facts_at fm s) rs.
Proof.
  intros until rs; intros C NC IN H.
  assert (C': forallb (check_succ fm (transfer (facts_at fm pc) i)) (successors_instr i) = true).
  { unfold check_node in C; simpl in C.
    destruct i; auto. elim (NC c l n n0); auto. }
  rewrite forallb_forall in C'. eapply check_succ_sound; eauto.
Qed.

Lemma check_node_cond:
  forall fm pc cond args s1 s2 b rs,
  check_node fm (pc, Icond cond args s1 s2) = true ->
  facts_hold (transfer_cond (facts_at fm pc) cond args b) rs ->
  facts_hold (facts_at fm (if b then s1 else s2)) rs.
Proof.
  intros until rs; intros C H. unfold check_node in C; simpl in C.
  rewrite andb_true_iff in C. destruct C as [C1 C2].
  destruct b; eapply check_succ_sound; eauto.
Qed.

(** ** Correctness of the rewritings *)

Lemma flin_pair:
  forall rs r y t m d1 d2,
  fact_holds rs (Flin r None t m d1) -> fact_holds rs (Flin y None t m d2) ->
  rs#r = Val.addl rs#y (Vlong (Int64.sub d1 d2))
  /\ (rs#y = Vundef \/ exists n, rs#y = Vlong n).
Proof.
  cbn [fact_holds bval]; intros until d2; intros R Y. rewrite R, Y, ! lin_spec.
  destruct (rs#t); simpl; auto.
  split. f_equal. ring. eauto.
Qed.

Section REWRITE.

Variable F V: Type.
Variable ge: Genv.t F V.
Variable sp: val.
Variable l: list fact.
Variables rs rs': regset.
Hypothesis FACTS: facts_hold l rs'.

Lemma rewrite_op_sound:
  forall h op args res s m v,
  (forall h0, h = Some h0 -> hint_ok l (Iop op args res s) h0 = true) ->
  rs'##args = rs##args ->
  eval_operation ge sp op rs##args m = Some v ->
  exists op' args',
     rewrite_instr h (Iop op args res s) = Iop op' args' res s
  /\ eval_operation ge sp op' rs'##args' m = Some v.
Proof.
  intros until v; intros OK ARGS EV.
  rewrite <- ARGS in EV.
  assert (DFLT: exists op' args', Iop op args res s = Iop op' args' res s
                                  /\ eval_operation ge sp op' rs'##args' m = Some v).
  { exists op, args; split; [reflexivity | exact EV]. }
  destruct h as [h|]; [ | exact DFLT].
  specialize (OK _ eq_refl).
  destruct h as [y b t mm d d' | x y | r y t mm d1 d2 | bb r y t mm d1 d2 | r y bb t mm d1 d2 | sl];
  cbn [hint_ok rewrite_instr] in OK |- *; [ | exact DFLT | exact DFLT | exact DFLT | exact DFLT | exact DFLT].
  rewrite ! andb_true_iff in OK. destruct OK as [[[OK1 OK2] OK3] OK4].
  rewrite negb_true_iff in OK1.
  destruct (fresh_for_true _ _ _ OK2) as [N1 N2].
  assert (G := gen_op_sound _ _ ge sp l op args res rs' m v FACTS EV).
  assert (R := implied_sound _ _ _ OK3 G).
  assert (Y := implied_sound _ _ _ OK4 FACTS).
  cbn [fact_holds] in R, Y.
  rewrite Regmap.gss, Regmap.gso in R by auto.
  rewrite (bval_ext rs' (rs'#res <- v)) in R.
  2: { intros r' IN. apply Regmap.gso. intros E; subst; contradiction. }
  destruct (Int64.eq d d') eqn:D.
- apply Int64.same_if_eq in D. subst d'.
  exists Omove, (y :: nil); split; auto. simpl. congruence.
- destruct (mk_addlimm (Int64.sub d d')) as [op'|] eqn:MK.
  + exists op', (y :: nil); split; auto. simpl.
    erewrite mk_addlimm_sound by eauto. rewrite Y, bval_addl, R. do 3 f_equal. ring.
  + exact DFLT.
Qed.

Lemma shift_hint_sound:
  forall r y t mm d1 d2 addr args addr' args' a,
  implied l (Flin r None t mm d1) && implied l (Flin y None t mm d2) = true ->
  shift_addr addr args r y (Int64.sub d1 d2) = Some (addr', args') ->
  rs'##args = rs##args ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a'.
Proof.
  intros until a; intros OK SH ARGS EV.
  rewrite andb_true_iff in OK. destruct OK as [OK1 OK2].
  destruct (flin_pair rs' r y t mm d1 d2) as [R Y].
  apply implied_sound with l; auto. apply implied_sound with l; auto.
  eapply shift_addr_sound; eauto. rewrite ARGS; auto.
Qed.

Lemma flin_shift:
  forall (rs1: regset) r y b t m d1 d2,
  fact_holds rs1 (Flin r b t m d1) -> fact_holds rs1 (Flin y b t m d2) ->
  rs1#r = Val.addl rs1#y (Vlong (Int64.sub d1 d2)).
Proof.
  cbn [fact_holds]; intros until d2; intros R Y. rewrite R, Y, bval_addl.
  do 3 f_equal. ring.
Qed.

Lemma flin_base:
  forall (rs1: regset) b r y t m d1 d2,
  fact_holds rs1 (Flin r None t m d1) -> fact_holds rs1 (Flin y (Some b) t m d2) ->
  rs1#r = Vundef \/ Val.addl rs1#b rs1#r = Val.addl rs1#y (Vlong (Int64.sub d1 d2)).
Proof.
  cbn [fact_holds bval]; intros until d2; intros R Y. rewrite R, Y, ! lin_spec.
  assert (AV: forall a b, Val.addl (Vlong a) (Vlong b) = Vlong (Int64.add a b)) by reflexivity.
  destruct (rs1#t); auto. right. rewrite Val.addl_assoc, AV. f_equal. f_equal. ring.
Qed.

Lemma rebase_hint_sound:
  forall b r y t mm d1 d2 addr args addr' args' a,
  implied l (Flin r None t mm d1) && implied l (Flin y (Some b) t mm d2) = true ->
  rebase_addr addr args b r y (Int64.sub d1 d2) = Some (addr', args') ->
  rs'##args = rs##args ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a'.
Proof.
  intros until a; intros OK RB ARGS EV.
  rewrite andb_true_iff in OK. destruct OK as [OK1 OK2].
  eapply rebase_addr_sound; eauto.
  apply flin_base with t mm; apply implied_sound with l; auto.
  rewrite ARGS; auto.
Qed.

Lemma equal_regs_sound:
  forall r y, equal_regs l r y = true -> rs'#r = rs'#y.
Proof.
  unfold equal_regs; intros r y E. rewrite orb_true_iff in E. destruct E as [E | E].
- exact (implied_sound _ _ _ E FACTS).
- apply existsb_exists in E. destruct E as (g & G & E).
  destruct g as [r' b t m d | ? ? | ? ? | ? ?]; try discriminate.
  rewrite andb_true_iff in E. destruct E as [E1 E2].
  destruct (peq r' r); [subst r' | discriminate].
  rewrite (FACTS _ G), (implied_sound _ _ _ E2 FACTS). auto.
Qed.

Lemma subst_args_sound:
  forall sl args,
  forallb (fun e => equal_regs l (fst e) (snd e)) sl = true ->
  rs'##(map (subst_reg sl) args) = rs'##args.
Proof.
  intros sl args OK. rewrite map_map. apply map_ext. intros a.
  induction sl as [ | [r y] sl IH]; cbn [subst_reg]; auto.
  cbn [forallb] in OK. rewrite andb_true_iff in OK. destruct OK as [OK1 OK2].
  destruct (peq a r); auto. subst a. symmetry. apply equal_regs_sound; auto.
Qed.

Lemma rewrite_load_sound:
  forall h chunk addr args dst s a,
  (forall h0, h = Some h0 -> hint_ok l (Iload chunk addr args dst s) h0 = true) ->
  rs'##args = rs##args ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists addr' args' a',
     rewrite_instr h (Iload chunk addr args dst s) = Iload chunk addr' args' dst s
  /\ eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a'.
Proof.
  intros until a; intros OK ARGS EV.
  assert (DFLT: exists addr' args' a',
     Iload chunk addr args dst s = Iload chunk addr' args' dst s
  /\ eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
  { exists addr, args, a; split; [reflexivity | split; [rewrite ARGS; exact EV | auto]]. }
  destruct h as [h|]; [ | exact DFLT].
  specialize (OK _ eq_refl).
  destruct h as [y b t mm d d' | x y | r y t mm d1 d2 | bb r y t mm d1 d2 | r y bb t mm d1 d2 | sl];
  cbn [hint_ok rewrite_instr] in OK |- *; [exact DFLT | exact DFLT | | | | ].
- destruct (shift_addr addr args r y (Int64.sub d1 d2)) as [[addr' args'] | ] eqn:SH.
  + exploit shift_hint_sound; eauto. intros (a' & EV' & LD).
    exists addr', args', a'; auto.
  + exact DFLT.
- destruct (rebase_addr addr args bb r y (Int64.sub d1 d2)) as [[addr' args'] | ] eqn:RB.
  + exploit rebase_hint_sound; eauto. intros (a' & EV' & LD).
    exists addr', args', a'; auto.
  + exact DFLT.
- destruct (shift_base addr args r y (Int64.sub d1 d2)) as [[addr' args'] | ] eqn:SB.
  + rewrite andb_true_iff in OK. destruct OK as [OK1 OK2].
    exists addr', args', a; split; [reflexivity | split; [ | auto]].
    eapply shift_base_sound; eauto.
    apply flin_shift with bb t mm; apply implied_sound with l; auto.
    rewrite ARGS; auto.
  + exact DFLT.
- exists addr, (map (subst_reg sl) args), a; split; [reflexivity | split; [ | auto]].
  rewrite subst_args_sound by auto. rewrite ARGS; exact EV.
Qed.

Lemma rewrite_store_sound:
  forall h chunk addr args src s a,
  (forall h0, h = Some h0 -> hint_ok l (Istore chunk addr args src s) h0 = true) ->
  rs'##args = rs##args ->
  eval_addressing ge sp addr rs##args = Some a ->
  exists addr' args' a',
     rewrite_instr h (Istore chunk addr args src s) = Istore chunk addr' args' src s
  /\ eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a'.
Proof.
  intros until a; intros OK ARGS EV.
  assert (DFLT: exists addr' args' a',
     Istore chunk addr args src s = Istore chunk addr' args' src s
  /\ eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
  { exists addr, args, a; split; [reflexivity | split; [rewrite ARGS; exact EV | auto]]. }
  destruct h as [h|]; [ | exact DFLT].
  specialize (OK _ eq_refl).
  destruct h as [y b t mm d d' | x y | r y t mm d1 d2 | bb r y t mm d1 d2 | r y bb t mm d1 d2 | sl];
  cbn [hint_ok rewrite_instr] in OK |- *; [exact DFLT | exact DFLT | | | | ].
- destruct (shift_addr addr args r y (Int64.sub d1 d2)) as [[addr' args'] | ] eqn:SH.
  + exploit shift_hint_sound; eauto. intros (a' & EV' & LD).
    exists addr', args', a'; auto.
  + exact DFLT.
- destruct (rebase_addr addr args bb r y (Int64.sub d1 d2)) as [[addr' args'] | ] eqn:RB.
  + exploit rebase_hint_sound; eauto. intros (a' & EV' & LD).
    exists addr', args', a'; auto.
  + exact DFLT.
- destruct (shift_base addr args r y (Int64.sub d1 d2)) as [[addr' args'] | ] eqn:SB.
  + rewrite andb_true_iff in OK. destruct OK as [OK1 OK2].
    exists addr', args', a; split; [reflexivity | split; [ | auto]].
    eapply shift_base_sound; eauto.
    apply flin_shift with bb t mm; apply implied_sound with l; auto.
    rewrite ARGS; auto.
  + exact DFLT.
- exists addr, (map (subst_reg sl) args), a; split; [reflexivity | split; [ | auto]].
  rewrite subst_args_sound by auto. rewrite ARGS; exact EV.
Qed.

Lemma rewrite_cond_sound:
  forall h cond args s1 s2 m b,
  (forall h0, h = Some h0 -> hint_ok l (Icond cond args s1 s2) h0 = true) ->
  rs'##args = rs##args ->
  eval_condition cond rs##args m = Some b ->
  exists cond' args',
     rewrite_instr h (Icond cond args s1 s2) = Icond cond' args' s1 s2
  /\ eval_condition cond' rs'##args' m = Some b.
Proof.
  intros until b; intros OK ARGS EV.
  rewrite <- ARGS in EV.
  assert (DFLT: exists cond' args', Icond cond args s1 s2 = Icond cond' args' s1 s2
                                    /\ eval_condition cond' rs'##args' m = Some b).
  { exists cond, args; split; [reflexivity | exact EV]. }
  destruct h as [h|]; [ | exact DFLT].
  specialize (OK _ eq_refl).
  destruct h as [y0 b0 t mm d d' | x y | r y0 t mm d1 d2 | bb r y0 t mm d1 d2 | r y0 bb t mm d1 d2 | sl];
  cbn [hint_ok rewrite_instr] in OK |- *; [exact DFLT | | exact DFLT | exact DFLT | exact DFLT | exact DFLT].
  generalize (classify_cond_sound cond args rs' m b EV).
  destruct (classify_cond cond args) as [c a a' | c a n | ? ? ? | ? ? ? | ];
  [ | | intros; exact DFLT | intros; exact DFLT | intros; exact DFLT].
- intros C. rewrite andb_true_iff in OK. destruct OK as [OK1 OK2].
  assert (X := implied_sound _ _ _ OK1 FACTS). assert (Y := implied_sound _ _ _ OK2 FACTS).
  cbn [fact_holds bval] in X, Y. rewrite lin_one_zero in X, Y.
  destruct (mk_cmpl c) as [cond'|] eqn:MK.
  + exists cond', (x :: y :: nil); split; auto. cbn [map].
    erewrite mk_cmpl_sound by eauto. rewrite X, Y.
    destruct (rs'#a) as [ | xa | ? | ? | ? | ? ?]; cbn [Val.cmp_bool] in C; try discriminate C.
    destruct (rs'#a') as [ | xa' | ? | ? | ? | ? ?]; cbn [Val.cmp_bool] in C; try discriminate C.
    cbn [Val.longofint Val.cmpl_bool]. rewrite cmpl_sext. auto.
  + exact DFLT.
- intros C.
  assert (X := implied_sound _ _ _ OK FACTS).
  cbn [fact_holds bval] in X. rewrite lin_one_zero in X.
  destruct (mk_cmplimm c (Int64.repr (Int.signed n))) as [cond'|] eqn:MK.
  + exists cond', (x :: nil); split; auto. cbn [map].
    erewrite mk_cmplimm_sound by eauto. rewrite X.
    destruct (rs'#a) as [ | xa | ? | ? | ? | ? ?]; cbn [Val.cmp_bool] in C; try discriminate C.
    cbn [Val.longofint Val.cmpl_bool]. rewrite cmpl_sext. auto.
  + exact DFLT.
Qed.

Lemma rewrite_other:
  forall h i,
  (forall op args res s, i <> Iop op args res s) ->
  (forall cond args s1 s2, i <> Icond cond args s1 s2) ->
  (forall chunk addr args dst s, i <> Iload chunk addr args dst s) ->
  (forall chunk addr args src s, i <> Istore chunk addr args src s) ->
  rewrite_instr h i = i.
Proof.
  intros h i N1 N2 N3 N4.
  destruct i as [ s0 | op args res s0 | chunk addr args dst s0 | chunk addr args src s0
                | sg ros args res s0 | sg ros args | ef args res s0 | cond args s1 s2
                | arg tbl | optarg ].
- destruct h as [[ ] | ]; reflexivity.
- elim (N1 op args res s0); reflexivity.
- elim (N3 chunk addr args dst s0); reflexivity.
- elim (N4 chunk addr args src s0); reflexivity.
- destruct h as [[ ] | ]; reflexivity.
- destruct h as [[ ] | ]; reflexivity.
- destruct h as [[ ] | ]; reflexivity.
- elim (N2 cond args s1 s2); reflexivity.
- destruct h as [[ ] | ]; reflexivity.
- destruct h as [[ ] | ]; reflexivity.
Qed.

End REWRITE.

(** * Structural properties of the transformation *)

Lemma add_instrs_notin:
  forall l c n, ~In n (map fst l) -> (add_instrs c l)!n = c!n.
Proof.
  unfold add_instrs; induction l as [ | [p i] l]; simpl; intros.
  auto.
  rewrite IHl by tauto. apply PTree.gso. intuition congruence.
Qed.

Lemma map_succ_id:
  forall g i, (forall s, g s = s) -> map_succ g i = i.
Proof.
  intros g i G. destruct i; simpl; rewrite ?G; auto.
  f_equal. rewrite <- (map_id l) at 2. apply map_ext. auto.
Qed.

Record tr_function (f: function) (redir: PTree.t (list (node * node)))
                   (hints: PTree.t hint) (fm: PTree.t (list fact)) (tf: function) : Prop := {
  tr_sig: tf.(fn_sig) = f.(fn_sig);
  tr_params: tf.(fn_params) = f.(fn_params);
  tr_stacksize: tf.(fn_stacksize) = f.(fn_stacksize);
  tr_entry: tf.(fn_entrypoint) = f.(fn_entrypoint);
  tr_code: forall n i,
    f.(fn_code)!n = Some i -> tf.(fn_code)!n = Some (transf_instr redir hints n i);
  tr_paths: forall n i s,
    f.(fn_code)!n = Some i -> In s (successors_instr i) ->
    exists fuel, ghost_path tf.(fn_code) (max_reg_function f) fuel (redirect redir n s) s = true;
  tr_hints: forall n i h,
    f.(fn_code)!n = Some i -> hints!n = Some h -> hint_ok (facts_at fm n) i h = true;
  tr_facts: forall n i,
    tf.(fn_code)!n = Some i -> check_node fm (n, i) = true;
  tr_entry_facts: facts_at fm f.(fn_entrypoint) = nil
}.

Lemma check_succ_empty:
  forall l s, check_succ (PTree.empty (list fact)) l s = true.
Proof.
  intros. unfold check_succ, facts_at. rewrite PTree.gempty. reflexivity.
Qed.

Lemma check_node_empty:
  forall ni, check_node (PTree.empty (list fact)) ni = true.
Proof.
  intros [n i]. unfold check_node; cbn [fst snd].
  destruct i; rewrite ?check_succ_empty; auto;
  apply forallb_forall; intros; apply check_succ_empty.
Qed.

Lemma transf_function_tr:
  forall f, exists redir hints fm, tr_function f redir hints fm (transf_function f).
Proof.
  intros. unfold transf_function. destruct (iv_oracle f) as [[[ghosts redir] hints] fm].
  set (tc := transf_code f ghosts redir hints).
  destruct (check_function f ghosts redir hints fm tc) eqn:C.
- exists redir, hints, fm. unfold check_function in C.
  rewrite ! andb_true_iff in C.
  destruct C as [[[[FRESH PATHS] HINTS] FACTS] ENTRY].
  constructor; cbn [fn_sig fn_params fn_stacksize fn_entrypoint fn_code];
    [reflexivity | reflexivity | reflexivity | reflexivity | | | | | ].
  + (* code *)
    intros n i CODE. unfold tc, transf_code. rewrite add_instrs_notin.
    rewrite PTree.gmap. rewrite CODE; auto.
    intros IN. apply list_in_map_inv in IN. destruct IN as ([p i'] & EQ & IN').
    cbn [fst] in EQ; subst p.
    rewrite forallb_forall in FRESH. specialize (FRESH _ IN'). cbn [fst] in FRESH.
    rewrite CODE in FRESH. discriminate.
  + (* paths *)
    intros n i s CODE SUCC. exists (S (length ghosts)).
    rewrite forallb_forall in PATHS.
    specialize (PATHS (n, i) (PTree.elements_correct _ _ CODE)). cbn [fst snd] in PATHS.
    rewrite forallb_forall in PATHS. apply PATHS; auto.
  + (* hints *)
    intros n i h CODE HINT. rewrite forallb_forall in HINTS.
    specialize (HINTS (n, h) (PTree.elements_correct _ _ HINT)). cbn [fst snd] in HINTS.
    rewrite CODE in HINTS. auto.
  + (* facts *)
    intros n i CODE. rewrite forallb_forall in FACTS.
    apply FACTS. apply PTree.elements_correct; auto.
  + (* entry *)
    destruct (facts_at fm (fn_entrypoint f)); [auto | discriminate].
- exists (PTree.empty _), (PTree.empty _), (PTree.empty _).
  constructor; [reflexivity | reflexivity | reflexivity | reflexivity | | | | | ].
  + intros n i CODE. rewrite CODE. f_equal. unfold transf_instr.
    rewrite PTree.gempty.
    assert (RW: rewrite_instr None i = i) by (destruct i; reflexivity).
    rewrite RW. symmetry. apply map_succ_id.
    intros s. unfold redirect. rewrite PTree.gempty. auto.
  + intros n i s CODE SUCC. exists O. unfold redirect. rewrite PTree.gempty. simpl.
    destruct (peq s s); congruence.
  + intros n i h CODE HINT. rewrite PTree.gempty in HINT. discriminate.
  + intros. apply check_node_empty.
  + unfold facts_at. rewrite PTree.gempty. auto.
Qed.

(** * Semantic preservation *)

Lemma setres_other:
  forall res (v: val) (rs: regset) r,
  ~In r (params_of_builtin_res res) -> (regmap_setres res v rs)#r = rs#r.
Proof.
  destruct res; simpl; intros; auto. apply Regmap.gso. intuition.
Qed.

Lemma loadv_lessdef:
  forall chunk m a a' v,
  Mem.loadv chunk m a = Some v -> Val.lessdef a a' -> Mem.loadv chunk m a' = Some v.
Proof.
  intros. inv H0; auto. discriminate.
Qed.

Lemma storev_lessdef:
  forall chunk m a a' v m',
  Mem.storev chunk m a v = Some m' -> Val.lessdef a a' -> Mem.storev chunk m a' v = Some m'.
Proof.
  intros. inv H0; auto. discriminate.
Qed.

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
  destruct (transf_function_tr f) as (redir & hints & fm & TR). apply (tr_sig _ _ _ _ _ TR).
Qed.

(** The registers of the original function have the same values in both
  executions. *)

Definition regs_agree (f: function) (rs rs': regset) : Prop :=
  forall r, Ple r (max_reg_function f) -> rs'#r = rs#r.

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
Variable redir: PTree.t (list (node * node)).
Variable hints: PTree.t hint.
Variable fm: PTree.t (list fact).
Hypothesis TR: tr_function f redir hints fm tf.

Let mr := max_reg_function f.

(** Execution of a path of new nodes. *)

Lemma ghost_exec:
  forall fuel s' s stk sp rs rs' m,
  ghost_path tf.(fn_code) mr fuel s' s = true ->
  regs_agree f rs rs' ->
  facts_hold (facts_at fm s') rs' ->
  exists rs'',
     star step tge (State stk tf sp s' rs' m) E0 (State stk tf sp s rs'' m)
  /\ regs_agree f rs rs''
  /\ facts_hold (facts_at fm s) rs''.
Proof.
  induction fuel as [ | fuel IH]; intros until m; intros GP AG FH; cbn [ghost_path] in GP.
- destruct (peq s' s); [ | discriminate].
  subst s'. exists rs'; split. apply star_refl. auto.
- destruct (peq s' s).
  { subst s'. exists rs'; split. apply star_refl. auto. }
  destruct (tf.(fn_code)!s') as [i|] eqn:C; [ | discriminate GP].
  assert (GH: exists op args t s'', i = Iop op args t s''
               /\ op_safe op (length args) = true /\ Plt mr t
               /\ ghost_path tf.(fn_code) mr fuel s'' s = true).
  { destruct i; first [ discriminate GP
                      | rewrite ! andb_true_iff in GP; destruct GP as [[G1 G2] G3];
                        apply Pos.ltb_lt in G2; eauto 10 ]. }
  clear GP. destruct GH as (op & args & t & s'' & EQ & SAFE & FRESH & GP). subst i.
  destruct (eval_operation tge sp op rs'##args m) as [v|] eqn:EV.
  2: { exfalso. apply (op_safe_correct _ _ tge sp op (rs'##args) m).
       rewrite length_map; auto. exact EV. }
  assert (FH1: facts_hold (facts_at fm s'') (rs'#t <- v)).
  { eapply check_node_succ.
    eapply (tr_facts _ _ _ _ _ TR); eauto.
    intros; discriminate.
    simpl; auto.
    cbn [transfer]. eapply transfer_op_sound; eauto. }
  assert (AG1: regs_agree f rs (rs'#t <- v)).
  { intros r LE. rewrite Regmap.gso. apply AG; auto. intros E; subst r. unfold mr in FRESH. extlia. }
  destruct (IH s'' s stk sp rs (rs'#t <- v) m GP AG1 FH1) as (rs'' & STAR & AG'' & FH'').
  exists rs''; split; auto.
  eapply star_left. eapply exec_Iop; eauto. eexact STAR. traceEq.
Qed.

Lemma succ_sim:
  forall pc i s stk sp rs1 rs1' m,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  regs_agree f rs1 rs1' ->
  facts_hold (facts_at fm (redirect redir pc s)) rs1' ->
  exists rs'',
     star step tge (State stk tf sp (redirect redir pc s) rs1' m) E0 (State stk tf sp s rs'' m)
  /\ regs_agree f rs1 rs''
  /\ facts_hold (facts_at fm s) rs''.
Proof.
  intros. destruct (tr_paths _ _ _ _ _ TR pc i s) as [fuel GP]; auto.
  eapply ghost_exec; eauto.
Qed.

Lemma hints_ok_at:
  forall pc i,
  f.(fn_code)!pc = Some i ->
  forall h0, hints!pc = Some h0 -> hint_ok (facts_at fm pc) i h0 = true.
Proof.
  intros. eapply (tr_hints _ _ _ _ _ TR); eauto.
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

Lemma tr_code_other:
  forall pc i,
  f.(fn_code)!pc = Some i ->
  (forall op args res s, i <> Iop op args res s) ->
  (forall cond args s1 s2, i <> Icond cond args s1 s2) ->
  (forall chunk addr args dst s, i <> Iload chunk addr args dst s) ->
  (forall chunk addr args src s, i <> Istore chunk addr args src s) ->
  tf.(fn_code)!pc = Some (map_succ (redirect redir pc) i).
Proof.
  intros. rewrite (tr_code _ _ _ _ _ TR pc i H). unfold transf_instr.
  rewrite rewrite_other; auto.
Qed.

End TRANSL_FUNCTION.

Inductive match_frames: stackframe -> stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs tf redir hints fm rs' pc'
        (TR: tr_function f redir hints fm tf)
        (AG: regs_agree f rs rs')
        (RES: Ple res (max_reg_function f))
        (PATH: exists fuel, ghost_path tf.(fn_code) (max_reg_function f) fuel pc' pc = true)
        (FACTS: forall v, facts_hold (facts_at fm pc') (rs'#res <- v)),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res tf sp pc' rs').

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' tf redir hints fm rs'
        (STACKS: list_forall2 match_frames stk stk')
        (TR: tr_function f redir hints fm tf)
        (AG: regs_agree f rs rs')
        (FACTS: facts_hold (facts_at fm pc) rs'),
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

Ltac NOTSHAPE := intros; discriminate.

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
  exploit tr_code_other; eauto; try NOTSHAPE. intros TI. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Inop pc') pc' stk' sp rs rs'); simpl; eauto.
  eapply check_node_succ. eapply (tr_facts _ _ _ _ _ TR); eauto.
  NOTSHAPE. simpl; auto. exact FACTS.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Inop; eauto.
- (* op *)
  rename H into CODE. rename H0 into EV.
  assert (ARGS: rs'##args = rs##args).
  { eapply uses_agree_args; eauto. simpl; apply incl_refl. }
  destruct (rewrite_op_sound _ _ ge sp _ rs rs' FACTS (hints!pc) op args res pc' m v)
    as (op' & args' & RW & EV'); auto.
  { intros h0 H0. eapply hints_ok_at; eauto. }
  assert (TI: tf.(fn_code)!pc = Some (Iop op' args' res (redirect redir pc pc'))).
  { rewrite (tr_code _ _ _ _ _ TR pc _ CODE). unfold transf_instr. rewrite RW. auto. }
  exploit (succ_sim _ _ _ _ _ TR pc (Iop op args res pc') pc' stk' sp
                    (rs#res <- v) (rs'#res <- v)); simpl; eauto.
  apply agree_set; auto.
  eapply check_node_succ. eapply (tr_facts _ _ _ _ _ TR); eauto.
  NOTSHAPE. simpl; auto.
  cbn [transfer]. eapply transfer_op_sound; eauto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Iop; eauto.
  rewrite <- EV'. apply eval_operation_preserved. exact symbols_preserved.
- (* load *)
  rename H into CODE. rename H0 into EV. rename H1 into LOAD.
  assert (ARGS: rs'##args = rs##args).
  { eapply uses_agree_args; eauto. simpl; apply incl_refl. }
  destruct (rewrite_load_sound _ _ ge sp _ rs rs' FACTS (hints!pc) chunk addr args dst pc' a)
    as (addr' & args' & a' & RW & EV' & LD); auto.
  { intros h0 H0. eapply hints_ok_at; eauto. }
  assert (TI: tf.(fn_code)!pc = Some (Iload chunk addr' args' dst (redirect redir pc pc'))).
  { rewrite (tr_code _ _ _ _ _ TR pc _ CODE). unfold transf_instr. rewrite RW. auto. }
  exploit (succ_sim _ _ _ _ _ TR pc (Iload chunk addr args dst pc') pc' stk' sp
                    (rs#dst <- v) (rs'#dst <- v)); simpl; eauto.
  apply agree_set; auto.
  eapply check_node_succ. eapply (tr_facts _ _ _ _ _ TR); eauto.
  NOTSHAPE. simpl; auto.
  cbn [transfer]. eapply kill_sound; eauto. intros; apply Regmap.gso; auto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Iload with (a := a'). eexact TI.
  rewrite <- EV'. apply eval_addressing_preserved. exact symbols_preserved.
  eapply loadv_lessdef; eauto.
- (* store *)
  rename H into CODE. rename H0 into EV. rename H1 into STORE.
  assert (ARGS: rs'##args = rs##args).
  { eapply uses_agree_args; eauto. simpl; red; auto with coqlib. }
  destruct (rewrite_store_sound _ _ ge sp _ rs rs' FACTS (hints!pc) chunk addr args src pc' a)
    as (addr' & args' & a' & RW & EV' & LD); auto.
  { intros h0 H0. eapply hints_ok_at; eauto. }
  assert (TI: tf.(fn_code)!pc = Some (Istore chunk addr' args' src (redirect redir pc pc'))).
  { rewrite (tr_code _ _ _ _ _ TR pc _ CODE). unfold transf_instr. rewrite RW. auto. }
  exploit (succ_sim _ _ _ _ _ TR pc (Istore chunk addr args src pc') pc' stk' sp rs rs');
    simpl; eauto.
  eapply check_node_succ. eapply (tr_facts _ _ _ _ _ TR); eauto.
  NOTSHAPE. simpl; auto. exact FACTS.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Istore with (a := a'). eexact TI.
  rewrite <- EV'. apply eval_addressing_preserved. exact symbols_preserved.
  erewrite uses_agree by (eauto; simpl; auto). eapply storev_lessdef; eauto.
- (* call *)
  rename H into CODE.
  exploit tr_code_other; eauto; try NOTSHAPE. intros TI. simpl in TI.
  econstructor; split.
  apply plus_one. eapply exec_Icall with (fd := transf_fundef fd). eexact TI.
  eapply find_function_translated; eauto.
  intros; subst ros. eapply max_reg_function_use; eauto. simpl; auto.
  apply sig_preserved.
  rewrite (uses_agree_args f rs rs' pc _ args AG CODE) by (destruct ros; simpl; red; auto with coqlib).
  constructor. constructor; auto. econstructor; eauto.
  + eapply max_reg_function_def; eauto; simpl; auto.
  + eapply (tr_paths _ _ _ _ _ TR); eauto. simpl; auto.
  + intros v. eapply check_node_succ. eapply (tr_facts _ _ _ _ _ TR); eauto.
    NOTSHAPE. simpl; auto.
    cbn [transfer]. eapply kill_sound; eauto. intros; apply Regmap.gso; auto.
- (* tailcall *)
  rename H into CODE.
  exploit tr_code_other; eauto; try NOTSHAPE. intros TI. simpl in TI.
  econstructor; split.
  apply plus_one. eapply exec_Itailcall with (fd := transf_fundef fd). eexact TI.
  eapply find_function_translated; eauto.
  intros; subst ros. eapply max_reg_function_use; eauto. simpl; auto.
  apply sig_preserved.
  rewrite (tr_stacksize _ _ _ _ _ TR); eauto.
  rewrite (uses_agree_args f rs rs' pc _ args AG CODE) by (destruct ros; simpl; red; auto with coqlib).
  constructor; auto.
- (* builtin *)
  rename H into CODE.
  exploit tr_code_other; eauto; try NOTSHAPE. intros TI. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Ibuiltin ef args res pc') pc' stk' sp
                    (regmap_setres res vres rs) (regmap_setres res vres rs')); simpl; eauto.
  apply agree_setres; auto.
  eapply check_node_succ. eapply (tr_facts _ _ _ _ _ TR); eauto.
  NOTSHAPE. simpl; auto.
  cbn [transfer]. eapply kill_list_sound; eauto. intros. apply setres_other; auto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  eapply eval_builtin_args_agree; eauto.
  intros. eapply uses_agree; eauto. simpl; auto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
- (* cond *)
  rename H into CODE. rename H0 into EV.
  assert (ARGS: rs'##args = rs##args).
  { eapply uses_agree_args; eauto. simpl; apply incl_refl. }
  destruct (rewrite_cond_sound _ rs rs' FACTS (hints!pc) cond args ifso ifnot m b)
    as (cond' & args' & RW & EV'); auto.
  { intros h0 H0. eapply hints_ok_at; eauto. }
  assert (TI: tf.(fn_code)!pc = Some (Icond cond' args' (redirect redir pc ifso)
                                                        (redirect redir pc ifnot))).
  { rewrite (tr_code _ _ _ _ _ TR pc _ CODE). unfold transf_instr. rewrite RW. auto. }
  assert (FH: facts_hold (facts_at fm (redirect redir pc (if b then ifso else ifnot))) rs').
  { replace (redirect redir pc (if b then ifso else ifnot))
       with (if b then redirect redir pc ifso else redirect redir pc ifnot)
       by (destruct b; auto).
    eapply check_node_cond. eapply (tr_facts _ _ _ _ _ TR); eauto.
    eapply transfer_cond_sound; eauto. }
  exploit (succ_sim _ _ _ _ _ TR pc (Icond cond args ifso ifnot) (if b then ifso else ifnot)
                    stk' sp rs rs'); simpl; eauto.
  destruct b; auto.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Icond; eauto.
  destruct b; auto.
- (* jumptable *)
  rename H into CODE.
  exploit tr_code_other; eauto; try NOTSHAPE. intros TI. simpl in TI.
  exploit (succ_sim _ _ _ _ _ TR pc (Ijumptable arg tbl) pc' stk' sp rs rs'); simpl; eauto.
  eapply list_nth_z_in; eauto.
  eapply check_node_succ. eapply (tr_facts _ _ _ _ _ TR); eauto.
  NOTSHAPE. simpl. apply in_map. eapply list_nth_z_in; eauto.
  exact FACTS.
  intros (rs'' & STAR & AG' & FACTS').
  FINISH STAR. eapply exec_Ijumptable; eauto.
  erewrite uses_agree by (eauto; simpl; auto). eauto.
  rewrite list_nth_z_map. rewrite H1. auto.
- (* return *)
  exploit tr_code_other; eauto; try NOTSHAPE. intros TI. simpl in TI.
  econstructor; split.
  apply plus_one. eapply exec_Ireturn; eauto.
  rewrite (tr_stacksize _ _ _ _ _ TR); eauto.
  replace (regmap_optget or Vundef rs') with (regmap_optget or Vundef rs).
  constructor; auto.
  destruct or; simpl; auto. symmetry; eapply uses_agree; eauto. simpl; auto.
- (* internal function *)
  change (transf_fundef (Internal f)) with (Internal (transf_function f)).
  destruct (transf_function_tr f) as (redir & hints & fm & TR).
  econstructor; split.
  apply plus_one. eapply exec_function_internal.
  rewrite (tr_sig _ _ _ _ _ TR); eauto.
  rewrite (tr_stacksize _ _ _ _ _ TR); eauto.
  rewrite (tr_entry _ _ _ _ _ TR), (tr_params _ _ _ _ _ TR).
  econstructor; eauto.
  red; auto.
  rewrite (tr_entry_facts _ _ _ _ _ TR). apply facts_hold_nil.
- (* external function *)
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inv STACKS. match goal with [ H: match_frames _ _ |- _ ] => inv H end.
  destruct PATH as [fuel GP].
  exploit (ghost_exec _ _ _ _ _ TR fuel pc' pc bl sp (rs#res <- vres) (rs'#res <- vres) m); eauto.
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
