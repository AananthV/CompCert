(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Facts about induction variables, and the rewritings that they
  justify, for induction-variable widening ([IVwiden]).  These
  definitions are shared between the verified validator and the
  untrusted oracle ([IVwidenaux.ml]). *)

Require Import Coqlib Maps AST Integers Values Op Registers RTL IVop.

(** Facts about the values of registers at a program point. *)

Inductive fact : Type :=
  | Flin (x: reg) (b: option reg) (i: reg) (m d: int64)
      (**r [x = b + (long) i * m + d], where [i] is a 32-bit register,
           and [b] is absent or a 64-bit register (e.g. a pointer) *)
  | Fle (i: reg) (k: Z)
      (**r [i] is a 32-bit integer whose signed value is at most [k] *)
  | Fge (i: reg) (k: Z)
      (**r [i] is a 32-bit integer whose signed value is at least [k] *)
  | Feq (x y: reg).
      (**r [x] and [y] have the same value *)

Definition fact_eq (f1 f2: fact) : {f1 = f2} + {f1 <> f2}.
Proof.
  generalize peq Int64.eq_dec zeq (option_eq peq); intros. decide equality.
Defined.

Definition base_regs (b: option reg) : list reg :=
  match b with Some r => r :: nil | None => nil end.

Definition fact_regs (f: fact) : list reg :=
  match f with
  | Flin x b i _ _ => x :: i :: base_regs b
  | Fle i _ | Fge i _ => i :: nil
  | Feq x y => x :: y :: nil
  end.

Definition mentions (r: reg) (f: fact) : bool :=
  if In_dec peq r (fact_regs f) then true else false.

Definition kill (r: reg) (l: list fact) : list fact :=
  filter (fun f => negb (mentions r f)) l.

Definition kill_list (rl: list reg) (l: list fact) : list fact :=
  fold_right kill l rl.

(** [r] does not occur in [i] or [b]. *)

Definition fresh_for (r: reg) (b: option reg) (i: reg) : bool :=
  negb (peq i r) && negb (In_dec peq r (base_regs b)).

(** [l] implies the fact [f]. *)

Definition implied (l: list fact) (f: fact) : bool :=
  match f with
  | Flin _ _ _ _ _ | Feq _ _ => existsb (fun g => if fact_eq f g then true else false) l
  | Fle i k =>
      existsb (fun g => match g with Fle j k' => peq i j && zle k' k | _ => false end) l
  | Fge i k =>
      existsb (fun g => match g with Fge j k' => peq i j && zle k k' | _ => false end) l
  end.

(** Adding [n] to [a] does not overflow. *)

Definition no_overflow (l: list fact) (a: reg) (n: int) : bool :=
  if zle 0 (Int.signed n) then
    existsb (fun f => match f with
                      | Fle i k => peq i a && zle (k + Int.signed n) Int.max_signed
                      | _ => false end) l
  else
    existsb (fun f => match f with
                      | Fge i k => peq i a && zle Int.min_signed (k + Int.signed n)
                      | _ => false end) l.

(** Facts about [res = a + n] (32-bit), derived from a fact about [a]
  (in the absence of overflow). *)

Definition shift_fact (a res: reg) (n: int) (f: fact) : list fact :=
  match f with
  | Flin x b i m d =>
      if peq i a && negb (peq x res) && negb (In_dec peq res (base_regs b))
      then Flin x b res m (Int64.sub d (Int64.mul m (Int64.repr (Int.signed n)))) :: nil
      else nil
  | Fle i k => if peq i a then Fle res (k + Int.signed n) :: nil else nil
  | Fge i k => if peq i a then Fge res (k + Int.signed n) :: nil else nil
  | Feq _ _ => nil
  end.

(** Facts about [res = a], derived from a fact about [a]. *)

Definition move_fact (a res: reg) (f: fact) : list fact :=
  match f with
  | Flin x b i m d => if peq x a && fresh_for res b i then Flin res b i m d :: nil else nil
  | Fle i k => if peq i a then Fle res k :: nil else nil
  | Fge i k => if peq i a then Fge res k :: nil else nil
  | Feq _ _ => nil
  end.

(** Facts about [res = x + n] (64-bit), derived from a fact about [x]. *)

Definition addl_fact (x res: reg) (n: int64) (f: fact) : list fact :=
  match f with
  | Flin y b i m d =>
      if peq y x && fresh_for res b i then Flin res b i m (Int64.add d n) :: nil else nil
  | _ => nil
  end.

(** Facts about [res = x * sc + n] (64-bit), derived from a fact about [x]. *)

Definition scale_fact (x res: reg) (sc n: int64) (f: fact) : list fact :=
  match f with
  | Flin y None i m d =>
      if peq y x && negb (peq i res)
      then Flin res None i (Int64.mul m sc) (Int64.add (Int64.mul d sc) n) :: nil
      else nil
  | _ => nil
  end.

(** Facts about [res = x + (y * sc + n)] (64-bit), where [x] is a base. *)

Definition based_fact (x y res: reg) (sc n: int64) (f: fact) : list fact :=
  match f with
  | Flin z None i m d =>
      if peq z y && negb (peq x res) && negb (peq i res)
      then Flin res (Some x) i (Int64.mul m sc) (Int64.add (Int64.mul d sc) n) :: nil
      else nil
  | _ => nil
  end.

(** Facts about [res = x + y * sc + n] (64-bit), where [x] and [y] are
  linear in the same variable. *)

Definition sum_fact (l: list fact) (x y res: reg) (sc n: int64) (f: fact) : list fact :=
  match f with
  | Flin z None i m d =>
      if peq z x && negb (peq i res) then
        flat_map (fun g => match g with
                           | Flin z' None i' m' d' =>
                               if peq z' y && peq i' i
                               then Flin res None i (Int64.add m (Int64.mul m' sc))
                                         (Int64.add (Int64.add d (Int64.mul d' sc)) n) :: nil
                               else nil
                           | _ => nil
                           end) l
      else nil
  | _ => nil
  end.

Definition gen_op (l: list fact) (op: operation) (args: list reg) (res: reg) : list fact :=
  match op, args with
  | Omove, a :: nil =>
      (if peq a res then nil else Feq res a :: nil) ++ flat_map (move_fact a res) l
  | _, _ =>
  match classify_op op args with
  | OCaddimm a n =>
      if no_overflow l a n then flat_map (shift_fact a res n) l else nil
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
  end
  end.

Definition transfer_op (l: list fact) (op: operation) (args: list reg) (res: reg) : list fact :=
  gen_op l op args res ++ kill res l.

(** Facts established by the outcome of a comparison. *)

Definition cmp_bound (c: comparison) (a b: reg) (f: fact) : list fact :=
  match c, f with
  | Clt, Fle j k => if peq j b then Fle a (k - 1) :: nil else nil
  | Clt, Fge j k => if peq j a then Fge b (k + 1) :: nil else nil
  | Cle, Fle j k => if peq j b then Fle a k :: nil else nil
  | Cle, Fge j k => if peq j a then Fge b k :: nil else nil
  | Cgt, Fge j k => if peq j b then Fge a (k + 1) :: nil else nil
  | Cgt, Fle j k => if peq j a then Fle b (k - 1) :: nil else nil
  | Cge, Fge j k => if peq j b then Fge a k :: nil else nil
  | Cge, Fle j k => if peq j a then Fle b k :: nil else nil
  | _, _ => nil
  end.

Definition cmp_bounds (l: list fact) (c: comparison) (a b: reg) : list fact :=
  match c with
  | Clt => Fle a (Int.max_signed - 1) :: Fge b (Int.min_signed + 1) :: nil
  | Cgt => Fge a (Int.min_signed + 1) :: Fle b (Int.max_signed - 1) :: nil
  | _ => nil
  end ++ flat_map (cmp_bound c a b) l.

Definition cmpimm_bounds (c: comparison) (a: reg) (k: Z) : list fact :=
  match c with
  | Clt => Fle a (k - 1) :: nil
  | Cle => Fle a k :: nil
  | Cgt => Fge a (k + 1) :: nil
  | Cge => Fge a k :: nil
  | Ceq => Fle a k :: Fge a k :: nil
  | Cne => nil
  end.

(** The registers of which [x] is known to be the sign extension. *)

Definition sext_of (l: list fact) (x: reg) : list reg :=
  flat_map (fun f => match f with
                     | Flin y None i m d =>
                         if peq y x && Int64.eq m Int64.one && Int64.eq d Int64.zero
                         then i :: nil else nil
                     | _ => nil end) l.

Definition outcome (c: comparison) (b: bool) : comparison :=
  if b then c else negate_comparison c.

Definition cond_facts (l: list fact) (cond: condition) (args: list reg) (b: bool) : list fact :=
  match classify_cond cond args with
  | CCcmp c x y => cmp_bounds l (outcome c b) x y
  | CCcmpimm c x n => cmpimm_bounds (outcome c b) x (Int.signed n)
  | CCcmpl c x y =>
      flat_map (fun a => flat_map (fun a' => cmp_bounds l (outcome c b) a a') (sext_of l y))
               (sext_of l x)
  | CCcmplimm c x n =>
      flat_map (fun a => cmpimm_bounds (outcome c b) a (Int64.signed n)) (sext_of l x)
  | CCother => nil
  end.

Definition transfer_cond (l: list fact) (cond: condition) (args: list reg) (b: bool) : list fact :=
  cond_facts l cond args b ++ l.

(** Transfer function for the other instructions. *)

Definition transfer (l: list fact) (i: instruction) : list fact :=
  match i with
  | Iop op args res _ => transfer_op l op args res
  | Iload _ _ _ dst _ => kill dst l
  | Icall _ _ _ res _ => kill res l
  | Ibuiltin _ _ res _ => kill_list (params_of_builtin_res res) l
  | _ => l
  end.

(** Rewritings of instructions, guided by hints from the oracle. *)

Inductive hint : Type :=
  | Hrepl (y: reg) (b: option reg) (i: reg) (m d d': int64)
      (**r an operation that computes [b + (long) i * m + d] becomes
           [y + (d - d')], where [y = b + (long) i * m + d'] *)
  | Hcond (x y: reg)
      (**r a 32-bit comparison of [a] and [b] becomes a 64-bit comparison
           of [x = (long) a] and [y = (long) b] *)
  | Haddr (r y t: reg) (m d1 d2: int64)
      (**r index [r = (long) t * m + d1] of an addressing mode becomes
           [y = (long) t * m + d2] *)
  | Hbase (b r y t: reg) (m d1 d2: int64)
      (**r base [b] and index [r = (long) t * m + d1] of an addressing
           mode become [y = b + (long) t * m + d2] *)
  | Hbshift (r y: reg) (b: option reg) (t: reg) (m d1 d2: int64)
      (**r base [r = b + (long) t * m + d1] of an addressing mode becomes
           [y = b + (long) t * m + d2] *)
  | Hsubst (l: list (reg * reg)).
      (**r each argument [r] of an addressing mode is replaced by [y], for
           [(r, y)] in [l], where [r] and [y] are known to be equal *)

Fixpoint subst_reg (l: list (reg * reg)) (a: reg) : reg :=
  match l with
  | nil => a
  | (r, y) :: l' => if peq a r then y else subst_reg l' a
  end.

(** [r] and [y] are equal: [r = y], or both are [b + (long) t * m + d]. *)

Definition equal_regs (l: list fact) (r y: reg) : bool :=
  implied l (Feq r y)
  || existsb (fun f => match f with
                       | Flin r' b t m d => peq r' r && implied l (Flin y b t m d)
                       | _ => false
                       end) l.

Definition rewrite_instr (h: option hint) (i: instruction) : instruction :=
  match h, i with
  | Some (Hrepl y b t m d d'), Iop op args res s =>
      if Int64.eq d d' then Iop Omove (y :: nil) res s
      else match mk_addlimm (Int64.sub d d') with
           | Some op' => Iop op' (y :: nil) res s
           | None => i
           end
  | Some (Hcond x y), Icond cond args s1 s2 =>
      match classify_cond cond args with
      | CCcmp c _ _ =>
          match mk_cmpl c with
          | Some cond' => Icond cond' (x :: y :: nil) s1 s2
          | None => i
          end
      | CCcmpimm c _ n =>
          match mk_cmplimm c (Int64.repr (Int.signed n)) with
          | Some cond' => Icond cond' (x :: nil) s1 s2
          | None => i
          end
      | _ => i
      end
  | Some (Haddr r y t m d1 d2), Iload chunk addr args dst s =>
      match shift_addr addr args r y (Int64.sub d1 d2) with
      | Some (addr', args') => Iload chunk addr' args' dst s
      | None => i
      end
  | Some (Haddr r y t m d1 d2), Istore chunk addr args src s =>
      match shift_addr addr args r y (Int64.sub d1 d2) with
      | Some (addr', args') => Istore chunk addr' args' src s
      | None => i
      end
  | Some (Hbase b r y t m d1 d2), Iload chunk addr args dst s =>
      match rebase_addr addr args b r y (Int64.sub d1 d2) with
      | Some (addr', args') => Iload chunk addr' args' dst s
      | None => i
      end
  | Some (Hbase b r y t m d1 d2), Istore chunk addr args src s =>
      match rebase_addr addr args b r y (Int64.sub d1 d2) with
      | Some (addr', args') => Istore chunk addr' args' src s
      | None => i
      end
  | Some (Hbshift r y b t m d1 d2), Iload chunk addr args dst s =>
      match shift_base addr args r y (Int64.sub d1 d2) with
      | Some (addr', args') => Iload chunk addr' args' dst s
      | None => i
      end
  | Some (Hbshift r y b t m d1 d2), Istore chunk addr args src s =>
      match shift_base addr args r y (Int64.sub d1 d2) with
      | Some (addr', args') => Istore chunk addr' args' src s
      | None => i
      end
  | Some (Hsubst l), Iload chunk addr args dst s =>
      Iload chunk addr (map (subst_reg l) args) dst s
  | Some (Hsubst l), Istore chunk addr args src s =>
      Istore chunk addr (map (subst_reg l) args) src s
  | _, _ => i
  end.

(** The facts required by a rewriting. *)

Definition hint_ok (l: list fact) (i: instruction) (h: hint) : bool :=
  match h, i with
  | Hrepl y b t m d d', Iop op args res s =>
      negb (peq y res) && fresh_for res b t
      && implied (gen_op l op args res) (Flin res b t m d)
      && implied l (Flin y b t m d')
  | Hcond x y, Icond cond args _ _ =>
      match classify_cond cond args with
      | CCcmp _ a b =>
          implied l (Flin x None a Int64.one Int64.zero)
          && implied l (Flin y None b Int64.one Int64.zero)
      | CCcmpimm _ a _ => implied l (Flin x None a Int64.one Int64.zero)
      | _ => true
      end
  | Haddr r y t m d1 d2, (Iload _ _ _ _ _ | Istore _ _ _ _ _) =>
      implied l (Flin r None t m d1) && implied l (Flin y None t m d2)
  | Hbase b r y t m d1 d2, (Iload _ _ _ _ _ | Istore _ _ _ _ _) =>
      implied l (Flin r None t m d1) && implied l (Flin y (Some b) t m d2)
  | Hbshift r y b t m d1 d2, (Iload _ _ _ _ _ | Istore _ _ _ _ _) =>
      implied l (Flin r b t m d1) && implied l (Flin y b t m d2)
  | Hsubst sl, (Iload _ _ _ _ _ | Istore _ _ _ _ _) =>
      forallb (fun e => equal_regs l (fst e) (snd e)) sl
  | _, _ => true
  end.

(** Redirection of the successors of a node to chains of new nodes. *)

Fixpoint assoc_node (s: node) (l: list (node * node)) : node :=
  match l with
  | nil => s
  | (a, b) :: l' => if peq a s then b else assoc_node s l'
  end.

Definition redirect (redir: PTree.t (list (node * node))) (n s: node) : node :=
  match redir!n with
  | Some l => assoc_node s l
  | None => s
  end.

Definition map_succ (g: node -> node) (i: instruction) : instruction :=
  match i with
  | Inop s => Inop (g s)
  | Iop op args res s => Iop op args res (g s)
  | Iload chunk addr args dst s => Iload chunk addr args dst (g s)
  | Istore chunk addr args src s => Istore chunk addr args src (g s)
  | Icall sig ros args res s => Icall sig ros args res (g s)
  | Itailcall sig ros args => i
  | Ibuiltin ef args res s => Ibuiltin ef args res (g s)
  | Icond cond args ifso ifnot => Icond cond args (g ifso) (g ifnot)
  | Ijumptable arg tbl => Ijumptable arg (map g tbl)
  | Ireturn optarg => i
  end.

Definition transf_instr (redir: PTree.t (list (node * node))) (hints: PTree.t hint)
                        (n: node) (i: instruction) : instruction :=
  map_succ (redirect redir n) (rewrite_instr hints!n i).

(** Facts at each node, provided by the oracle. *)

Definition facts_at (fm: PTree.t (list fact)) (n: node) : list fact :=
  match fm!n with Some l => l | None => nil end.

Definition check_succ (fm: PTree.t (list fact)) (l: list fact) (s: node) : bool :=
  forallb (implied l) (facts_at fm s).

(** The facts are an inductive invariant of the code. *)

Definition check_node (fm: PTree.t (list fact)) (ni: node * instruction) : bool :=
  let l := facts_at fm (fst ni) in
  match snd ni with
  | Icond cond args s1 s2 =>
      check_succ fm (transfer_cond l cond args true) s1
      && check_succ fm (transfer_cond l cond args false) s2
  | i => forallb (check_succ fm (transfer l i)) (successors_instr i)
  end.
