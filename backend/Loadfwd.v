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

(** Global load forwarding over RTL.

  This optimization eliminates loads whose value is already available
  in a register, including across join points of the CFG, and in
  particular in the loop-carried case:
<<
     a[i] = 0;                        a[i] = 0; t = 0;
     for (j...)                       for (j...)
       a[i] = a[i] + x;     ===>        { y = t + x; a[i] = y; t = y; }
>>
  It is made of two passes.

  The first pass, [Loadfwd.insert_program], picks a fresh register [t_L]
  for each memory location [L] (a chunk, an addressing mode, and
  symbolic arguments) that is loaded at least once and accessed at least
  twice in the function, and inserts a move [t_L := r] after every
  load [r := L] and after every store [L := r].  Since [t_L] is fresh,
  these moves do not change the semantics.  The choice of the locations
  is a heuristic that does not need to be proved correct.

  The second pass, [Loadfwd.transf_program], performs a forward dataflow
  analysis (using Kildall's algorithm, hence merging information at join
  points) computing, at each program point, facts of the form
  "register [r] holds the value of the symbolic expression [e]" and
  "register [r] holds the value of the load [L]".  A load [r' := L] is
  then replaced by the move [r' := r] if [r] is known to hold the value
  of [L].  The moves inserted by the first pass ensure that the same
  register [t_L] holds the value of [L] on all paths reaching a join point.

  Symbolic expressions are trees of memory-independent operators over
  registers.  Facts are recorded in terms of the registers used by the
  instructions; when a register is overwritten, the facts that mention it
  are rewritten using its defining expression.  At join points, and when
  comparing addresses, registers are expanded into their defining
  expressions as needed (a form of anti-unification).  This way,
  addresses computed in different registers along different paths (e.g.
  [longofint(i)] recomputed at each access to [a[i]]) are identified.

  Unused moves are later removed by the [Deadcode] pass and the
  remaining ones are coalesced by register allocation. *)

Require Import Coqlib Maps Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs.
Require Import Op Registers RTL.

(** * Symbolic expressions and facts *)

Inductive sexpr : Type :=
  | Sreg (r: reg)
  | Sop (op: operation) (args: sexprlist)
with sexprlist : Type :=
  | Snil
  | Scons (e: sexpr) (el: sexprlist).

(** A fact attached to register [r] is either:
- [Fexpr e]: the value of [r] is the value of the symbolic expression [e];
- [Fload chunk addr el]: the value of [r] is greater than or equal to
  (in the [Val.lessdef] ordering) the value obtained by loading
  [chunk] at the address [addr] applied to the values of [el]. *)

Inductive fact : Type :=
  | Fexpr (e: sexpr)
  | Fload (chunk: memory_chunk) (addr: addressing) (args: sexprlist).

Fixpoint sexpr_beq (e1 e2: sexpr) : bool :=
  match e1, e2 with
  | Sreg r1, Sreg r2 => Pos.eqb r1 r2
  | Sop op1 el1, Sop op2 el2 =>
      (if eq_operation op1 op2 then true else false) && sexprlist_beq el1 el2
  | _, _ => false
  end
with sexprlist_beq (el1 el2: sexprlist) : bool :=
  match el1, el2 with
  | Snil, Snil => true
  | Scons e1 el1, Scons e2 el2 => sexpr_beq e1 e2 && sexprlist_beq el1 el2
  | _, _ => false
  end.

Definition fact_beq (f1 f2: fact) : bool :=
  match f1, f2 with
  | Fexpr e1, Fexpr e2 => sexpr_beq e1 e2
  | Fload chunk1 addr1 el1, Fload chunk2 addr2 el2 =>
      (if chunk_eq chunk1 chunk2 then true else false)
      && (if eq_addressing addr1 addr2 then true else false)
      && sexprlist_beq el1 el2
  | _, _ => false
  end.

Fixpoint sexpr_mentions (r: reg) (e: sexpr) : bool :=
  match e with
  | Sreg r' => Pos.eqb r r'
  | Sop op el => sexprlist_mentions r el
  end
with sexprlist_mentions (r: reg) (el: sexprlist) : bool :=
  match el with
  | Snil => false
  | Scons e el => sexpr_mentions r e || sexprlist_mentions r el
  end.

Definition fact_mentions (r: reg) (f: fact) : bool :=
  match f with
  | Fexpr e => sexpr_mentions r e
  | Fload chunk addr el => sexprlist_mentions r el
  end.

Fixpoint sexpr_size (e: sexpr) : nat :=
  match e with
  | Sreg r => 1
  | Sop op el => S (sexprlist_size el)
  end
with sexprlist_size (el: sexprlist) : nat :=
  match el with
  | Snil => O
  | Scons e el => sexpr_size e + sexprlist_size el
  end.

(** To avoid the exponential growth of expression trees, we do not
  record expressions larger than [max_sexpr_size]. *)

Definition max_sexpr_size : nat := 16%nat.

Scheme sexpr_ind2 := Induction for sexpr Sort Prop
  with sexprlist_ind2 := Induction for sexprlist Sort Prop.
Combined Scheme sexpr_mutind from sexpr_ind2, sexprlist_ind2.

Lemma sexpr_beq_correct:
  (forall e1 e2, sexpr_beq e1 e2 = true -> e1 = e2)
  /\ (forall el1 el2, sexprlist_beq el1 el2 = true -> el1 = el2).
Proof.
  apply sexpr_mutind; intros.
- destruct e2; simpl in H; try discriminate. apply Pos.eqb_eq in H. congruence.
- destruct e2; simpl in H0; try discriminate.
  destruct (eq_operation op op0); simpl in H0; try discriminate.
  subst. f_equal. auto.
- destruct el2; simpl in H; congruence.
- destruct el2; simpl in H1; try discriminate. InvBooleans. f_equal; auto.
Qed.

Lemma fact_beq_correct:
  forall f1 f2, fact_beq f1 f2 = true -> f1 = f2.
Proof.
  destruct f1, f2; simpl; intros; try discriminate.
- f_equal. apply sexpr_beq_correct; auto.
- InvBooleans. destruct (chunk_eq chunk chunk0); try discriminate.
  destruct (eq_addressing addr addr0); try discriminate.
  subst. f_equal. apply sexpr_beq_correct; auto.
Qed.

Definition fact_size (f: fact) : nat :=
  match f with
  | Fexpr e => sexpr_size e
  | Fload chunk addr el => sexprlist_size el
  end.

Fixpoint sregs (rl: list reg) : sexprlist :=
  match rl with
  | nil => Snil
  | r :: rl => Scons (Sreg r) (sregs rl)
  end.

(** Substitution of expression [e] for register [r]. *)

Fixpoint subst (r: reg) (e: sexpr) (x: sexpr) : sexpr :=
  match x with
  | Sreg r' => if peq r r' then e else x
  | Sop op el => Sop op (subst_list r e el)
  end
with subst_list (r: reg) (e: sexpr) (el: sexprlist) : sexprlist :=
  match el with
  | Snil => Snil
  | Scons x el => Scons (subst r e x) (subst_list r e el)
  end.

Definition subst_fact (r: reg) (e: sexpr) (f: fact) : fact :=
  match f with
  | Fexpr x => Fexpr (subst r e x)
  | Fload chunk addr el => Fload chunk addr (subst_list r e el)
  end.

Local Notation facts := (PTree.t fact).

(** * Semantics of facts *)

Section SEMANTICS.

Context {F V: Type} (ge: Genv.t F V) (sp: val).

(** Operators in symbolic expressions do not depend on memory.
  We evaluate them in the empty memory. *)

Fixpoint eval_sexpr (rs: regset) (e: sexpr) : option val :=
  match e with
  | Sreg r => Some rs#r
  | Sop op el =>
      match eval_sexprlist rs el with
      | Some vl => eval_operation ge sp op vl Mem.empty
      | None => None
      end
  end
with eval_sexprlist (rs: regset) (el: sexprlist) : option (list val) :=
  match el with
  | Snil => Some nil
  | Scons e el =>
      match eval_sexpr rs e, eval_sexprlist rs el with
      | Some v, Some vl => Some (v :: vl)
      | _, _ => None
      end
  end.

Definition fact_holds (rs: regset) (m: mem) (r: reg) (f: fact) : Prop :=
  match f with
  | Fexpr e => eval_sexpr rs e = Some rs#r
  | Fload chunk addr el =>
      forall vl a v,
      eval_sexprlist rs el = Some vl ->
      eval_addressing ge sp addr vl = Some a ->
      Mem.loadv chunk m a = Some v ->
      Val.lessdef v rs#r
  end.

Definition facts_hold (rs: regset) (m: mem) (mp: facts) : Prop :=
  forall r f, mp!r = Some f -> fact_holds rs m r f.

Definition exprs_hold (rs: regset) (mp: facts) : Prop :=
  forall r e, mp!r = Some (Fexpr e) -> eval_sexpr rs e = Some rs#r.

Lemma facts_exprs_hold:
  forall rs m mp, facts_hold rs m mp -> exprs_hold rs mp.
Proof.
  intros; red; intros. exact (H _ _ H0).
Qed.

End SEMANTICS.

(** * Generalization of two expressions *)

(** [au m1 m2 n e1 e2] computes an expression [e] that is equal to [e1]
  in states satisfying the facts [m1], and equal to [e2] in states
  satisfying the facts [m2].  This is a form of anti-unification where
  registers are replaced by their defining expressions (as given by [m1]
  or [m2]) only when necessary.  It is used at join points of the
  control-flow graph, as well as to compare the address of a load
  with the address of a known load (in which case [m1 = m2]). *)

Definition expr_fact (mp: facts) (r: reg) : option sexpr :=
  match mp!r with Some (Fexpr e) => Some e | _ => None end.

Section GENERALIZE.

Variables m1 m2: facts.

Definition au_list_with (au: sexpr -> sexpr -> option sexpr) :
                        sexprlist -> sexprlist -> option sexprlist :=
  fix aul (el1 el2: sexprlist) : option sexprlist :=
    match el1, el2 with
    | Snil, Snil => Some Snil
    | Scons e1 l1, Scons e2 l2 =>
        match au e1 e2, aul l1 l2 with
        | Some e, Some l => Some (Scons e l)
        | _, _ => None
        end
    | _, _ => None
    end.

Fixpoint au (n: nat) (e1 e2: sexpr) {struct n} : option sexpr :=
  match n with
  | O => if sexpr_beq e1 e2 then Some e1 else None
  | S n' =>
      if sexpr_beq e1 e2 then Some e1 else
      match e1, e2 with
      | Sop op1 el1, Sop op2 el2 =>
          if eq_operation op1 op2 then
            match au_list_with (au n') el1 el2 with
            | Some el => Some (Sop op1 el)
            | None => None
            end
          else None
      | Sreg r1, _ =>
          match expr_fact m1 r1 with
          | Some e1' => au n' e1' e2
          | None =>
              match e2 with
              | Sreg r2 =>
                  match expr_fact m2 r2 with
                  | Some e2' => au n' e1 e2'
                  | None => None
                  end
              | _ => None
              end
          end
      | _, Sreg r2 =>
          match expr_fact m2 r2 with
          | Some e2' => au n' e1 e2'
          | None => None
          end
      end
  end.

Definition au_fuel : nat := 8%nat.

Definition au_fact (f1 f2: fact) : option fact :=
  match f1, f2 with
  | Fexpr e1, Fexpr e2 =>
      match au au_fuel e1 e2 with
      | Some e => Some (Fexpr e)
      | None => None
      end
  | Fload chunk1 addr1 el1, Fload chunk2 addr2 el2 =>
      if chunk_eq chunk1 chunk2 then if eq_addressing addr1 addr2 then
        match au_list_with (au au_fuel) el1 el2 with
        | Some el => Some (Fload chunk1 addr1 el)
        | None => None
        end
      else None else None
  | _, _ => None
  end.

(** At join points, we keep the generalization of the two facts
  only if it is the first fact, or if it is strictly larger than the first
  fact (this ensures termination of the dataflow analysis) and not too
  large. *)

Definition lub_fact (o1 o2: option fact) : option fact :=
  match o1, o2 with
  | Some f1, Some f2 =>
      if fact_beq f1 f2 then o1 else
      match au_fact f1 f2 with
      | Some g =>
          if fact_beq f1 g then o1 else
          if Nat.ltb (fact_size f1) (fact_size g) && Nat.leb (fact_size g) max_sexpr_size
          then Some g else None
      | None => None
      end
  | _, _ => None
  end.

End GENERALIZE.

Section AU_SOUND.

Context {F V: Type} (ge: Genv.t F V) (sp: val) (rs: regset).
Variables m1 m2: facts.

Lemma au_list_with_sound:
  forall (au: sexpr -> sexpr -> option sexpr),
  (forall e1 e2 e, au e1 e2 = Some e ->
     (exprs_hold ge sp rs m1 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs e1)
  /\ (exprs_hold ge sp rs m2 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs e2)) ->
  forall el1 el2 el, au_list_with au el1 el2 = Some el ->
     (exprs_hold ge sp rs m1 -> eval_sexprlist ge sp rs el = eval_sexprlist ge sp rs el1)
  /\ (exprs_hold ge sp rs m2 -> eval_sexprlist ge sp rs el = eval_sexprlist ge sp rs el2).
Proof.
  intros au AU. induction el1; destruct el2; simpl; intros; try discriminate.
- inv H; auto.
- destruct (au e e0) as [e1|] eqn:A; try discriminate.
  destruct (au_list_with au el1 el2) as [l1|] eqn:B; try discriminate.
  inv H. exploit AU; eauto. intros [P Q]. exploit IHel1; eauto. intros [R S].
  simpl. split; intros.
  rewrite P, R; auto.
  rewrite Q, S; auto.
Qed.

Lemma au_sound:
  forall n e1 e2 e, au m1 m2 n e1 e2 = Some e ->
     (exprs_hold ge sp rs m1 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs e1)
  /\ (exprs_hold ge sp rs m2 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs e2).
Proof.
  induction n; intros until e; simpl.
- destruct (sexpr_beq e1 e2) eqn:B; intros E; inv E.
  apply sexpr_beq_correct in B. subst; auto.
- destruct (sexpr_beq e1 e2) eqn:B.
  { intros E; inv E. apply sexpr_beq_correct in B. subst; auto. }
  assert (EXP1: forall r1 e1' e2,
            expr_fact m1 r1 = Some e1' -> au m1 m2 n e1' e2 = Some e ->
            (exprs_hold ge sp rs m1 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs (Sreg r1))
         /\ (exprs_hold ge sp rs m2 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs e2)).
  { intros. exploit IHn; eauto. intros [P Q]. split; intros; auto.
    rewrite P by auto. unfold expr_fact in H. destruct (m1!r1) as [[]|] eqn:M; inv H.
    simpl. apply H1; auto. }
  assert (EXP2: forall r2 e2' e1,
            expr_fact m2 r2 = Some e2' -> au m1 m2 n e1 e2' = Some e ->
            (exprs_hold ge sp rs m1 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs e1)
         /\ (exprs_hold ge sp rs m2 -> eval_sexpr ge sp rs e = eval_sexpr ge sp rs (Sreg r2))).
  { intros. exploit IHn; eauto. intros [P Q]. split; intros; auto.
    rewrite Q by auto. unfold expr_fact in H. destruct (m2!r2) as [[]|] eqn:M; inv H.
    simpl. apply H1; auto. }
  destruct e1 as [r1|op1 el1].
  + destruct (expr_fact m1 r1) as [e1'|] eqn:X1. intros; eapply EXP1; eauto.
    destruct e2 as [r2|op2 el2]; try discriminate.
    destruct (expr_fact m2 r2) as [e2'|] eqn:X2; try discriminate.
    intros; eapply EXP2; eauto.
  + destruct e2 as [r2|op2 el2].
    * destruct (expr_fact m2 r2) as [e2'|] eqn:X2; try discriminate.
      intros; eapply EXP2; eauto.
    * destruct (eq_operation op1 op2); try discriminate. subst op2.
      destruct (au_list_with (au m1 m2 n) el1 el2) as [el|] eqn:L; intros E; inv E.
      exploit au_list_with_sound. eexact IHn. eauto. intros [P Q].
      simpl. split; intros. rewrite P; auto. rewrite Q; auto.
Qed.

Lemma au_fact_sound:
  forall m f1 f2 g r,
  au_fact m1 m2 f1 f2 = Some g ->
     (facts_hold ge sp rs m m1 -> fact_holds ge sp rs m r f1 -> fact_holds ge sp rs m r g)
  /\ (facts_hold ge sp rs m m2 -> fact_holds ge sp rs m r f2 -> fact_holds ge sp rs m r g).
Proof.
  unfold au_fact; intros. destruct f1 as [e1|chunk1 addr1 el1], f2 as [e2|chunk2 addr2 el2]; try discriminate.
- destruct (au m1 m2 au_fuel e1 e2) as [e|] eqn:A; inv H.
  exploit au_sound; eauto. intros [P Q].
  simpl; split; intros.
  rewrite P; auto. eapply facts_exprs_hold; eauto.
  rewrite Q; auto. eapply facts_exprs_hold; eauto.
- destruct (chunk_eq chunk1 chunk2); try discriminate.
  destruct (eq_addressing addr1 addr2); try discriminate. subst.
  destruct (au_list_with (au m1 m2 au_fuel) el1 el2) as [el|] eqn:A; inv H.
  exploit au_list_with_sound. intros; eapply au_sound; eauto. eauto. intros [P Q].
  simpl; split; intros.
  rewrite P in H1 by (eapply facts_exprs_hold; eauto). eauto.
  rewrite Q in H1 by (eapply facts_exprs_hold; eauto). eauto.
Qed.

Lemma lub_fact_sound:
  forall m o1 o2 g r,
  lub_fact m1 m2 o1 o2 = Some g ->
     (facts_hold ge sp rs m m1 -> o1 = m1!r -> fact_holds ge sp rs m r g)
  /\ (facts_hold ge sp rs m m2 -> o2 = m2!r -> fact_holds ge sp rs m r g).
Proof.
  unfold lub_fact; intros. destruct o1 as [f1|]; destruct o2 as [f2|]; try discriminate.
  destruct (fact_beq f1 f2) eqn:B.
- inv H. apply fact_beq_correct in B. subst f2. split; intros; apply H; auto.
- destruct (au_fact m1 m2 f1 f2) as [g'|] eqn:A; try discriminate.
  exploit au_fact_sound; eauto. intros [P Q].
  destruct (fact_beq f1 g') eqn:B'.
  apply fact_beq_correct in B'. subst g'. inv H. split; intros. apply H; auto. apply Q; auto.
  destruct (Nat.ltb (fact_size f1) (fact_size g') && Nat.leb (fact_size g') max_sexpr_size); inv H.
  split; intros. apply P; auto. apply Q; auto.
Qed.

End AU_SOUND.

(** * The abstract domain *)

(** An abstract state is either [Bot] (unreachable program point)
  or a finite map from registers to facts.  Registers absent from the map
  have no known fact.  The ordering is semantic: [ge x y] holds if
  every concrete state satisfying [y] also satisfies [x].  The least upper
  bound keeps the facts common to both arguments, generalizing them
  if needed. *)

Module LFacts <: SEMILATTICE.

  Inductive t' : Type := Bot | Facts (m: facts).
  Definition t := t'.

  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).

  Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => true
    | Facts m1, Facts m2 => PTree.beq fact_beq m1 m2
    | _, _ => false
    end.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold eq; destruct x, y; simpl; intros; try discriminate; auto.
    f_equal. apply PTree.extensionality; intros i.
    rewrite PTree.beq_correct in H. specialize (H i).
    destruct (m!i), (m0!i); try contradiction; auto.
    f_equal; apply fact_beq_correct; auto.
  Qed.

  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, Facts _ => False
    | Facts m1, Facts m2 =>
        forall F V (g: Genv.t F V) sp rs m, facts_hold g sp rs m m2 -> facts_hold g sp rs m m1
    end.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq; intros; subst y. destruct x; simpl; auto.
  Qed.

  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; destruct x, y, z; auto. tauto.
  Qed.

  Definition bot : t := Bot.

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    destruct x; simpl; auto.
  Qed.

  (** The common case of equal arguments is tested first, to avoid
    rebuilding the map. *)

  Definition lub (x y: t) : t :=
    match x, y with
    | Bot, _ => y
    | _, Bot => x
    | Facts m1, Facts m2 =>
        if PTree.beq fact_beq m1 m2 then x
        else Facts (PTree.combine (lub_fact m1 m2) m1 m2)
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    destruct x, y; simpl; auto.
    destruct (PTree.beq fact_beq m m0); simpl; auto.
    intros; red; intros. rewrite PTree.gcombine in H0 by auto.
    exploit (lub_fact_sound g sp rs); eauto. intros [P Q]. apply P; auto.
  Qed.

  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    destruct x, y; simpl; auto.
    destruct (PTree.beq fact_beq m m0) eqn:B.
  - assert (E: Facts m = Facts m0) by (apply beq_correct; simpl; auto).
    injection E; intros <-. simpl; auto.
  - intros F V g sp rs mm H r f GET. rewrite PTree.gcombine in GET by auto.
    exploit (lub_fact_sound g sp rs); eauto. intros [P Q]. apply Q; auto.
  Qed.

End LFacts.

(** * The static analysis *)

(** Forgetting the old value of register [r], which is about to be assigned.
  Facts that mention [r] are rewritten by substituting the expression
  for [r], if known, or are removed. *)

Definition subst_for (r: reg) (mp: facts) : option sexpr :=
  match expr_fact mp r with
  | Some e => if sexpr_mentions r e then None else Some e
  | None => None
  end.

Definition kill_one (r: reg) (sub: option sexpr) (f: fact) : option fact :=
  if fact_mentions r f then
    match sub with
    | Some e =>
        let f' := subst_fact r e f in
        if Nat.leb (fact_size f') max_sexpr_size then Some f' else None
    | None => None
    end
  else Some f.

Definition kill_reg_full (r: reg) (mp: facts) : facts :=
  PTree.remove r (PTree.map_filter1 (kill_one r (subst_for r mp)) mp).

(** In the common case where [r] has no fact and no fact mentions [r],
  the facts are unchanged, and are returned without being copied. *)

Definition kill_reg (r: reg) (mp: facts) : facts :=
  match mp!r with
  | None =>
      if PTree.fold1 (fun b f => b && negb (fact_mentions r f)) mp true
      then mp
      else kill_reg_full r mp
  | Some _ => kill_reg_full r mp
  end.

(** [M] is a set of registers that contains all the registers mentioned
  by the facts (see [mentionable] below).  If [r] is not in [M], no fact
  mentions [r]. *)

Definition kill_reg_m (M: PTree.t unit) (r: reg) (mp: facts) : facts :=
  match M!r with
  | Some _ => kill_reg r mp
  | None => PTree.remove r mp
  end.

Definition kill_regs (M: PTree.t unit) (rl: list reg) (mp: facts) : facts :=
  fold_left (fun mp r => kill_reg_m M r mp) rl mp.

(** Record the fact [f] for register [r], which has just been assigned.
  The fact is expressed in terms of the values of registers before the
  assignment. *)

Definition set_fact (M: PTree.t unit) (r: reg) (f: fact) (mp: facts) : facts :=
  let mp' := kill_reg_m M r mp in
  match kill_one r (subst_for r mp) f with
  | Some f' => PTree.set r f' mp'
  | None => mp'
  end.

(** Forget all facts that depend on the memory state. *)

Definition is_expr_fact (f: fact) : bool :=
  match f with Fexpr _ => true | Fload _ _ _ => false end.

Definition kill_loads (mp: facts) : facts :=
  PTree.filter1 is_expr_fact mp.

(** Storing a value [v] with one of the following chunks then reading it back
  returns a value that is less defined than [v]. *)

Definition store_full (chunk: memory_chunk) : bool :=
  match chunk with
  | Mint32 | Mint64 | Mfloat32 | Mfloat64 | Many32 | Many64 => true
  | _ => false
  end.

(** To keep the abstract states small, expression facts are only recorded
  for the registers in [rel], which is meant to contain the registers that
  contribute to the computation of addresses (see [relevant_regs] below).
  Load facts are always recorded.  Dropping facts is always sound. *)

Definition transfer_op (rel M: PTree.t unit) (op: operation) (args: list reg) (res: reg)
                       (mp: facts) : facts :=
  match is_move_operation op args with
  | Some src =>
      match mp!src with
      | Some (Fload _ _ _ as f) => set_fact M res f mp
      | _ =>
          match rel!res with
          | Some _ => set_fact M res (Fexpr (Sreg src)) mp
          | None => kill_reg_m M res mp
          end
      end
  | None =>
      match rel!res with
      | Some _ =>
          if op_depends_on_memory op
          then kill_reg_m M res mp
          else set_fact M res (Fexpr (Sop op (sregs args))) mp
      | None => kill_reg_m M res mp
      end
  end.

Definition transfer_instr (rel M: PTree.t unit) (i: instruction) (mp: facts) : facts :=
  match i with
  | Inop _ | Icond _ _ _ _ | Ijumptable _ _ => mp
  | Iop op args res _ => transfer_op rel M op args res mp
  | Iload chunk addr args dst _ =>
      set_fact M dst (Fload chunk addr (sregs args)) mp
  | Istore chunk addr args src _ =>
      let mp' := kill_loads mp in
      if store_full chunk
      then PTree.set src (Fload chunk addr (sregs args)) mp'
      else mp'
  | Icall _ _ _ res _ => kill_reg_m M res (kill_loads mp)
  | Ibuiltin _ _ res _ => kill_regs M (params_of_builtin_res res) (kill_loads mp)
  | Itailcall _ _ _ | Ireturn _ => mp
  end.

Definition transfer (rel M: PTree.t unit) (f: function) (pc: node) (x: LFacts.t) : LFacts.t :=
  match x with
  | LFacts.Bot => LFacts.Bot
  | LFacts.Facts mp =>
      match f.(fn_code)!pc with
      | None => x
      | Some i => LFacts.Facts (transfer_instr rel M i mp)
      end
  end.

(** The relevant registers: the arguments of loads and stores, and,
  transitively, the arguments of the operations that define relevant
  registers (up to a fixed depth, which matches the depth of expansion
  used when comparing addresses). *)

Definition add_regs (rl: list reg) (u: PTree.t unit) : PTree.t unit :=
  fold_left (fun u r => PTree.set r tt u) rl u.

Definition relevant_step (c: code) (u: PTree.t unit) : PTree.t unit :=
  PTree.fold1
    (fun u i =>
       match i with
       | Iop op args res _ =>
           match u!res with Some _ => add_regs args u | None => u end
       | _ => u
       end)
    c u.

(** [relevant_iter c n u] computes [Nat.iter n (relevant_step c) u], stopping
  as soon as a fixpoint is reached.  [relevant_step] only adds registers,
  hence the test of the number of registers. *)

Definition unit_tree_size (t: PTree.t unit) : nat :=
  PTree.fold1 (fun n _ => S n) t O.

Fixpoint relevant_iter (c: code) (n: nat) (u: PTree.t unit) : PTree.t unit :=
  match n with
  | O => u
  | S n' =>
      let u' := relevant_step c u in
      if Nat.eqb (unit_tree_size u') (unit_tree_size u) then u else relevant_iter c n' u'
  end.

Definition relevant_regs (c: code) : PTree.t unit :=
  let r0 :=
    PTree.fold1
      (fun u i =>
         match i with
         | Iload _ _ args _ _ | Istore _ _ args _ _ => add_regs args u
         | _ => u
         end)
      c (PTree.empty unit) in
  relevant_iter c au_fuel r0.

(** The registers that can be mentioned by the facts: the arguments of
  loads and stores, and the arguments of the operations that define
  relevant registers. *)

Definition mention_regs (rel: PTree.t unit) (i: instruction) : list reg :=
  match i with
  | Iload _ _ args _ _ | Istore _ _ args _ _ => args
  | Iop op args res _ => match rel!res with Some _ => args | None => nil end
  | _ => nil
  end.

Definition mentionable (rel: PTree.t unit) (c: code) : PTree.t unit :=
  PTree.fold1 (fun u i => add_regs (mention_regs rel i) u) c (PTree.empty unit).

Module DS := Dataflow_Solver(LFacts)(NodeSetForward).

Definition empty_facts : LFacts.t := LFacts.Facts (PTree.empty fact).

(** As a safeguard against excessive compile times, functions that are
  too large (number of instructions times number of relevant registers)
  are not analyzed. *)

Definition tree_size {A: Type} (t: PTree.t A) : Z :=
  PTree.fold1 (fun n _ => Z.succ n) t 0.

Definition analysis_limit : Z := 20000000.

Definition too_big (f: function) (rel: PTree.t unit) : bool :=
  zlt analysis_limit (tree_size f.(fn_code) * (tree_size rel + 1)).

Definition analyze_rel (rel: PTree.t unit) (f: function) : PMap.t LFacts.t :=
  if too_big f rel then PMap.init empty_facts else
  match DS.fixpoint f.(fn_code) successors_instr
                    (transfer rel (mentionable rel f.(fn_code)) f)
                    f.(fn_entrypoint) empty_facts with
  | Some res => res
  | None => PMap.init empty_facts
  end.

Definition analyze (f: function) : PMap.t LFacts.t :=
  analyze_rel (relevant_regs f.(fn_code)) f.

(** * Insertion of moves to fresh registers *)

(** Expansion of registers by their defining expressions.  This is used
  to compute canonical keys for locations, and does not need to be proved
  correct. *)

Definition expand_list_with (ex: sexpr -> sexpr) : sexprlist -> sexprlist :=
  fix exl (el: sexprlist) : sexprlist :=
    match el with
    | Snil => Snil
    | Scons e el => Scons (ex e) (exl el)
    end.

Fixpoint expand (mp: facts) (n: nat) (e: sexpr) {struct n} : sexpr :=
  match n with
  | O => e
  | S n' =>
      match e with
      | Sreg r =>
          match expr_fact mp r with
          | Some e' => expand mp n' e'
          | None => e
          end
      | Sop op el => Sop op (expand_list_with (expand mp n') el)
      end
  end.

(** The symbolic location accessed by a load or a store. *)

Definition location_at (approx: PMap.t LFacts.t) (pc: node) (i: instruction) : option fact :=
  match i, approx!!pc with
  | Iload chunk addr args dst s, LFacts.Facts mp =>
      Some (Fload chunk addr (expand_list_with (expand mp au_fuel) (sregs args)))
  | Istore chunk addr args src s, LFacts.Facts mp =>
      if store_full chunk
      then Some (Fload chunk addr (expand_list_with (expand mp au_fuel) (sregs args)))
      else None
  | _, _ => None
  end.

(** A table associating fresh registers with locations.  It is a hash table
  indexed by the first register mentioned in the location. *)

Record locinfo : Type := mklocinfo {
  li_loc: fact;          (**r the location *)
  li_reg: reg;           (**r the fresh register associated with it *)
  li_loaded: bool;       (**r is it loaded somewhere? *)
  li_multi: bool         (**r is it accessed at least twice? *)
}.

Fixpoint sexpr_hash (e: sexpr) : positive :=
  match e with
  | Sreg r => r
  | Sop op el => sexprlist_hash el
  end
with sexprlist_hash (el: sexprlist) : positive :=
  match el with
  | Snil => 1%positive
  | Scons e el => sexpr_hash e
  end.

Definition loc_hash (l: fact) : positive :=
  match l with
  | Fexpr e => sexpr_hash e
  | Fload chunk addr el => sexprlist_hash el
  end.

Fixpoint update_bucket (b: list locinfo) (l: fact) (isload: bool) : option (list locinfo) :=
  match b with
  | nil => None
  | li :: b' =>
      if fact_beq li.(li_loc) l
      then Some (mklocinfo l li.(li_reg) (li.(li_loaded) || isload) true :: b')
      else match update_bucket b' l isload with
           | Some b'' => Some (li :: b'')
           | None => None
           end
  end.

Definition loctable := PTree.t (list locinfo).

Definition record_loc (st: reg * loctable) (isload: bool) (l: fact) : reg * loctable :=
  let (next, tbl) := st in
  let h := loc_hash l in
  let b := match tbl!h with Some b => b | None => nil end in
  match update_bucket b l isload with
  | Some b' => (next, PTree.set h b' tbl)
  | None => (Pos.succ next, PTree.set h (mklocinfo l next isload false :: b) tbl)
  end.

(** The locations accessed by the loads and stores of the code, computed
  once and for all, along with a flag indicating loads. *)

Definition locations (approx: PMap.t LFacts.t) (c: code) : PTree.t (bool * fact) :=
  PTree.fold
    (fun t pc i =>
       match location_at approx pc i with
       | Some l =>
           let isload := match i with Iload _ _ _ _ _ => true | _ => false end in
           PTree.set pc (isload, l) t
       | None => t
       end)
    c (PTree.empty _).

Definition build_table (locs: PTree.t (bool * fact)) (next: reg) : loctable :=
  snd (PTree.fold1 (fun st bl => record_loc st (fst bl) (snd bl))
                  locs (next, PTree.empty _)).

(** The register to be associated with the location accessed at each node,
  if any.  We only consider locations that are loaded at least once and
  accessed at least twice. *)

Definition choose_loc (tbl: loctable) (bl: bool * fact) : option reg :=
  let l := snd bl in
  match tbl!(loc_hash l) with
  | None => None
  | Some b =>
      match List.find (fun li => fact_beq li.(li_loc) l) b with
      | Some li => if li.(li_loaded) && li.(li_multi) then Some li.(li_reg) else None
      | None => None
      end
  end.

Definition choice_map (tbl: loctable) (locs: PTree.t (bool * fact)) : PTree.t reg :=
  PTree.map_filter1 (choose_loc tbl) locs.

Definition choice_of (cm: PTree.t reg) (pc: node) (i: instruction) : option reg :=
  cm!pc.

(** The insertion of moves proper.  This part is independent of the
  heuristic [choice] used to determine the fresh registers.  New nodes
  are numbered [maxpc + pc], where [pc] is the node of the load
  or store. *)

Section INSERT.

Variable choice: node -> instruction -> option reg.
Variable maxpc: positive.
Variable maxreg: positive.

Definition move_for (pc: node) (i: instruction) : option (reg * reg * node) :=
  match choice pc i with
  | Some t =>
      if plt maxreg t then
        match i with
        | Iload _ _ _ dst s => Some (dst, t, s)
        | Istore _ _ _ src s => Some (src, t, s)
        | _ => None
        end
      else None
  | None => None
  end.

Definition redirect (pc: node) (i: instruction) : instruction :=
  match move_for pc i with
  | Some _ =>
      match i with
      | Iload chunk addr args dst _ => Iload chunk addr args dst (Pos.add maxpc pc)
      | Istore chunk addr args src _ => Istore chunk addr args src (Pos.add maxpc pc)
      | _ => i
      end
  | None => i
  end.

Definition add_move (c: code) (pc: node) (i: instruction) : code :=
  match move_for pc i with
  | Some (x, t, s) => PTree.set (Pos.add maxpc pc) (Iop Omove (x :: nil) t s) c
  | None => c
  end.

Definition insert_code (c: code) : code :=
  PTree.fold add_move c (PTree.map redirect c).

End INSERT.

(** * Replacement of loads by moves *)

Definition match_load (mp: facts) (chunk: memory_chunk) (addr: addressing)
                      (el: sexprlist) (f: fact) : bool :=
  match f with
  | Fload chunk' addr' el' =>
      if chunk_eq chunk' chunk then if eq_addressing addr' addr then
        match au_list_with (au mp mp au_fuel) el' el with
        | Some _ => true
        | None => false
        end
      else false else false
  | Fexpr _ => false
  end.

(** Among the registers holding the value of the load, we choose the one
  with the smallest number.  This favors the registers of the original
  program over the fresh registers introduced by [insert_program],
  so that the latter are only used when needed (typically, across
  loop back-edges), keeping register pressure low. *)

Definition find_load (mp: facts) (chunk: memory_chunk) (addr: addressing)
                     (args: list reg) : option reg :=
  match List.filter (fun p => match_load mp chunk addr (sregs args) (snd p))
                    (PTree.elements mp) with
  | nil => None
  | p :: l => Some (fold_left (fun r q => Pos.min r (fst q)) l (fst p))
  end.

(** * The move insertion pass *)

(** Moves are first inserted for all candidate locations.  We then
  analyze the resulting code and keep only the fresh registers that
  would actually be used to replace a load, that is, at loads where the
  value is not already available in a register of the original
  function.  This typically happens across join points and loop
  back-edges.  Loads that are redundant within an extended basic block
  are left to CSE.  This avoids extending the live ranges of values
  needlessly, which increases register pressure. *)

Definition useful_regs (rel: PTree.t unit) (maxreg: reg) (f: function) : PTree.t unit :=
  let approx := analyze_rel rel f in
  PTree.fold
    (fun u pc i =>
       match i, approx!!pc with
       | Iload chunk addr args dst s, LFacts.Facts mp =>
           match find_load mp chunk addr args with
           | Some r => if plt maxreg r then PTree.set r tt u else u
           | None => u
           end
       | _, _ => u
       end)
    f.(fn_code) (PTree.empty unit).

Definition filter_choice (u: PTree.t unit) (choice: node -> instruction -> option reg)
                         (pc: node) (i: instruction) : option reg :=
  match choice pc i with
  | Some t => match u!t with Some _ => Some t | None => None end
  | None => None
  end.

(** The fresh registers that are worth inserting, given the locations
  [locs] accessed by [f].  The analysis of the code with all candidate
  moves reuses the relevant registers [rel] of [f]: the moves define fresh
  registers, which are never relevant, and use registers already in the
  code. *)

Definition useful_moves (f: function) (rel: PTree.t unit) (locs: PTree.t (bool * fact))
                        : PTree.t unit * (node -> instruction -> option reg) :=
  let maxreg := max_reg_function f in
  let maxpc := max_pc_function f in
  let cm := choice_map (build_table locs (Pos.succ maxreg)) locs in
  let choice := choice_of cm in
  let u :=
    match PTree.elements cm with
    | nil => PTree.empty unit
    | _ :: _ =>
        useful_regs rel maxreg
          (mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
             (insert_code choice maxpc maxreg f.(fn_code)) f.(fn_entrypoint))
    end in
  (u, choice).

Definition insert_function_with (f: function) (u: PTree.t unit)
                                (choice: node -> instruction -> option reg) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (insert_code (filter_choice u choice) (max_pc_function f) (max_reg_function f) f.(fn_code))
    f.(fn_entrypoint).

Definition insert_function (f: function) : function :=
  let rel := relevant_regs f.(fn_code) in
  let (u, choice) := useful_moves f rel (locations (analyze_rel rel f) f.(fn_code)) in
  insert_function_with f u choice.

Definition insert_fundef (fd: fundef) : fundef :=
  AST.transf_fundef insert_function fd.

Definition insert_program (p: program) : program :=
  transform_program insert_fundef p.

(** * The load replacement pass *)

Definition transf_instr (approx: PMap.t LFacts.t) (pc: node) (i: instruction) : instruction :=
  match i, approx!!pc with
  | Iload chunk addr args dst s, LFacts.Facts mp =>
      match find_load mp chunk addr args with
      | Some r => Iop Omove (r :: nil) dst s
      | None => i
      end
  | _, _ => i
  end.

Definition transf_function_with (approx: PMap.t LFacts.t) (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map (transf_instr approx) f.(fn_code))
    f.(fn_entrypoint).

Definition transf_function (f: function) : function :=
  transf_function_with (analyze f) f.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

(** * The two passes combined *)

(** [fwd_program p] computes [transf_program (insert_program p)] (see
  [fwd_program_eq] below), but avoids analyzing a function a second time
  when no move is inserted in it, which is the common case: the analysis
  of the function computed for the insertion of moves is then reused for
  the replacement of loads.  The replacement is computed before the
  analysis of the code with all candidate moves, so that the first
  analysis need not be kept in memory. *)

Definition fwd_function (f: function) : function :=
  let rel := relevant_regs f.(fn_code) in
  let approx := analyze_rel rel f in
  let tf := transf_function_with approx f in
  let (u, choice) := useful_moves f rel (locations approx f.(fn_code)) in
  match PTree.elements u with
  | nil => tf
  | _ :: _ => transf_function (insert_function_with f u choice)
  end.

Definition fwd_fundef (fd: fundef) : fundef :=
  AST.transf_fundef fwd_function fd.

Definition fwd_program (p: program) : program :=
  transform_program fwd_fundef p.

Lemma insert_code_nochoice:
  forall ch maxpc maxreg c,
  (forall pc i, ch pc i = None) ->
  insert_code ch maxpc maxreg c = c.
Proof.
  intros. unfold insert_code.
  assert (M: forall pc i, move_for ch maxreg pc i = None).
  { intros. unfold move_for. rewrite H; auto. }
  assert (A: forall l (c0: code), fold_left (fun a p => add_move ch maxpc maxreg a (fst p) (snd p)) l c0 = c0).
  { induction l; simpl; intros; auto. rewrite IHl. unfold add_move. rewrite M; auto. }
  rewrite PTree.fold_spec, A.
  apply PTree.extensionality; intros. rewrite PTree.gmap.
  destruct (c!i); simpl; auto. unfold redirect. rewrite M; auto.
Qed.

Lemma fwd_function_eq:
  forall f, fwd_function f = transf_function (insert_function f).
Proof.
  intros. unfold fwd_function, insert_function.
  destruct (useful_moves f (relevant_regs (fn_code f))
             (locations (analyze_rel (relevant_regs (fn_code f)) f) (fn_code f))) as [u choice].
  destruct (PTree.elements u) as [|x l] eqn:E; auto.
  assert (F: forall pc i, filter_choice u choice pc i = None).
  { intros. unfold filter_choice. destruct (choice pc i) as [t|]; auto.
    destruct (u!t) as [[]|] eqn:U; auto.
    apply PTree.elements_correct in U. rewrite E in U. contradiction. }
  unfold insert_function_with. rewrite insert_code_nochoice by auto.
  destruct f; reflexivity.
Qed.

Lemma fwd_program_eq:
  forall p, fwd_program p = transf_program (insert_program p).
Proof.
  intros. unfold fwd_program, transf_program, insert_program, transform_program; simpl.
  f_equal. rewrite map_map. apply map_ext. intros [id [fd|gv]]; simpl; auto.
  unfold transform_program_globdef. f_equal. f_equal.
  destruct fd; simpl; auto. rewrite fwd_function_eq; auto.
Qed.
