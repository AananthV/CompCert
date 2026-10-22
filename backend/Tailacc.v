(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Accumulator tail-recursion elimination.

  A self-recursive function [f] whose recursive calls are of the form
<<
      res = f(args); d = res op y; return d;        (or d = y op res)
>>
  where [op] is an associative and commutative integer operation
  ([+], [*], [&], [|], [^], on [int] or [long]), is turned into a loop
  that carries an accumulator [acc]:
<<
  entry':  acc = unit(op);  goto entry
  call:    acc = acc op y;  params = args;  goto entry
  return r:  acc = acc op r;  return acc
>>
  The accumulator holds the combination of the right operands of all the
  recursive calls that are pending in the original program.  Returns are
  combined with it, which is why the value returned at the base cases must
  be a "normal" value for [op] (i.e. combining it with the neutral element
  does not change it); this is checked from the types of the operations that
  define the returned register.

  The function must not have a stack frame ([fn_stacksize = 0]): the
  frames of the pending recursive calls of the original program are then
  all mapped to the single frame of the loop.  It must not contain tail
  calls, and the operation must directly follow the recursive call.
  Only the recursive calls whose operation is that of the first one found
  are transformed; the others remain calls.

  The transformation is performed by a generator, and its result is
  checked by a validator ([check_function]), which is the only part
  relied upon in the proof. *)

Require Import Coqlib Maps Integers Floats AST Linking.
Require Import Values Op Registers RTL TailaccOp.

(** * Equality of functions, to recognize self-recursive calls *)

Definition builtin_arg_eq: forall (a b: builtin_arg reg), {a=b} + {a<>b}.
Proof.
  generalize Int.eq_dec Int64.eq_dec Float.eq_dec Float32.eq_dec Ptrofs.eq_dec
             chunk_eq ident_eq peq. intros. decide equality.
Defined.

Definition builtin_res_eq: forall (a b: builtin_res reg), {a=b} + {a<>b}.
Proof.
  generalize peq. intros. decide equality.
Defined.

Definition ros_eq: forall (a b: reg + ident), {a=b} + {a<>b}.
Proof.
  generalize peq. intros. decide equality.
Defined.

Definition instruction_eq: forall (a b: instruction), {a=b} + {a<>b}.
Proof.
  generalize eq_operation eq_addressing eq_condition chunk_eq signature_eq
             external_function_eq builtin_res_eq ros_eq peq
             (list_eq_dec peq) (list_eq_dec builtin_arg_eq) (option_eq peq).
  intros. decide equality.
Defined.

Definition function_beq (f g: function) : bool :=
     proj_sumbool (signature_eq f.(fn_sig) g.(fn_sig))
  && proj_sumbool (list_eq_dec peq f.(fn_params) g.(fn_params))
  && proj_sumbool (zeq f.(fn_stacksize) g.(fn_stacksize))
  && proj_sumbool (peq f.(fn_entrypoint) g.(fn_entrypoint))
  && PTree.beq (fun i j => proj_sumbool (instruction_eq i j)) f.(fn_code) g.(fn_code).

Lemma function_beq_sound:
  forall f g, function_beq f g = true -> f = g.
Proof.
  unfold function_beq; intros.
  rewrite ! andb_true_iff in H. destruct H as [[[[A B] C] D] E].
  assert (CODE: fn_code f = fn_code g).
  { apply PTree.extensionality. intros i.
    rewrite PTree.beq_correct in E. specialize (E i).
    destruct (fn_code f)!i, (fn_code g)!i; try contradiction; auto.
    destruct (instruction_eq i0 i1); simpl in E; congruence. }
  destruct (signature_eq (fn_sig f) (fn_sig g)); try discriminate.
  destruct (list_eq_dec peq (fn_params f) (fn_params g)); try discriminate.
  destruct (zeq (fn_stacksize f) (fn_stacksize g)); try discriminate.
  destruct (peq (fn_entrypoint f) (fn_entrypoint g)); try discriminate.
  destruct f, g; simpl in *. congruence.
Qed.

(** A call to [id] is a recursive call of [f] if [id] is defined as [f]
  in the current compilation unit. *)

Definition is_self (dm: defmap) (f: function) (id: ident) : bool :=
  match dm!id with
  | Some (Gfun (Internal g)) => function_beq g f
  | _ => false
  end.

(** * Recognition of recursive calls in accumulator position *)

(** The right operand of the accumulating operation: a register or a
  constant (for operations with an immediate argument). *)

Inductive accarg : Type :=
  | AAreg (r: reg)
  | AAimm (v: val).

Definition accarg_regs (acc: reg) (a: accarg) : list reg :=
  match a with
  | AAreg r => acc :: r :: nil
  | AAimm _ => acc :: nil
  end.

(** [site_of dm f i] recognizes [i] as a recursive call
  [res = f(args)] followed by [d = res op y; return d].  It returns the
  accumulating operation, the instruction [op], and the operand [y]. *)

Definition site_of (dm: defmap) (f: function) (i: instruction)
                   : option (accop * operation * accarg) :=
  match i with
  | Icall sg (inr id) args res s =>
      match f.(fn_code)!s with
      | Some (Iop op oargs d s2) =>
          match f.(fn_code)!s2 with
          | Some (Ireturn (Some d')) =>
              if peq d d'
              && Nat.eqb (length args) (length f.(fn_params))
              && is_self dm f id then
                match classify_accop op, oargs with
                | Some (k, None), r1 :: r2 :: nil =>
                    if peq r1 res && negb (peq r2 res) then Some (k, op, AAreg r2)
                    else if peq r2 res && negb (peq r1 res) then Some (k, op, AAreg r1)
                    else None
                | Some (k, Some c), r1 :: nil =>
                    if peq r1 res then Some (k, op, AAimm c) else None
                | _, _ => None
                end
              else None
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(** * Normal values at returns *)

(** A value [v] is normal for [k] if [accop_eval k (accop_unit k) v = v].
  Values of the following types are normal. *)

Definition accop_type_ok (k: accop) (ty: typ) : bool :=
  match k with
  | AOadd => proj_sumbool (typ_eq ty Tint)
  | AOaddl => proj_sumbool (typ_eq ty Tlong)
  | AOmul | AOand | AOor | AOxor => proj_sumbool (typ_eq ty Tint) && Archi.ptr64
  | AOmull | AOandl | AOorl | AOxorl => proj_sumbool (typ_eq ty Tlong) && negb Archi.ptr64
  end.

(** An instruction that produces a normal value. *)

Definition normal_def (k: accop) (i: instruction) : bool :=
  match i with
  | Iop Omove _ _ _ => false
  | Iop op _ _ _ => accop_type_ok k (snd (type_of_operation op))
  | _ => false
  end.

(** A register [r] always holds a normal value if it is not a parameter,
  and if all the instructions that define it produce normal values. *)

Definition ret_ok (k: accop) (f: function) (r: reg) : bool :=
  negb (In_dec peq r f.(fn_params))
  && PTree_Properties.for_all f.(fn_code)
       (fun pc i => match instr_defs i with
                    | Some r' => negb (peq r r') || normal_def k i
                    | None => true
                    end).

(** * The transformation *)

(** The first accumulating operation found in a recursive call. *)

Definition find_kind (dm: defmap) (f: function) : option accop :=
  PTree.fold
    (fun res pc i =>
       match res with
       | Some _ => res
       | None => match site_of dm f i with Some (k, _, _) => Some k | None => None end
       end)
    f.(fn_code) None.

(** The accumulator and the temporaries used for the parallel move of
  the arguments of a recursive call to the parameters. *)

Definition acc_reg (f: function) : reg := Pos.succ (max_reg_function f).

Fixpoint temps (r: reg) (n: nat) : list reg :=
  match n with
  | O => nil
  | S n' => Pos.succ r :: temps (Pos.succ r) n'
  end.

Definition call_moves (f: function) (args: list reg) : list (reg * reg) :=
  let tmps := temps (acc_reg f) (length f.(fn_params)) in
  combine args tmps ++ rev (combine tmps f.(fn_params)).

(** Generation of the transformed function. *)

Fixpoint gen_moves (moves: list (reg * reg)) (target: node) (c: code) (n: node)
                   : node * code * node :=
  match moves with
  | nil => (target, c, n)
  | (src, dst) :: ms =>
      let '(n1, c1, nx) := gen_moves ms target c (Pos.succ n) in
      (n, PTree.set n (Iop Omove (src :: nil) dst n1) c1, nx)
  end.

Definition gen_instr (dm: defmap) (f: function) (k: accop) (bop: operation)
                     (cn: code * node) (pc: node) (i: instruction) : code * node :=
  let '(c, n) := cn in
  let acc := acc_reg f in
  match site_of dm f i, i with
  | Some (k', op, a), Icall _ _ args _ _ =>
      if accop_eq k k' then
        let '(n1, c1, nx) := gen_moves (call_moves f args) f.(fn_entrypoint) c n in
        (PTree.set pc (Iop op (accarg_regs acc a) acc n1) c1, nx)
      else (c, n)
  | _, Ireturn (Some r) =>
      (PTree.set n (Ireturn (Some acc))
         (PTree.set pc (Iop bop (acc :: r :: nil) acc n) c), Pos.succ n)
  | _, _ => (c, n)
  end.

Definition gen_function (dm: defmap) (f: function) (k: accop) : option function :=
  match accop_binary k, accop_const k with
  | Some bop, Some cop =>
      let '(c, n) := PTree.fold (gen_instr dm f k bop) f.(fn_code)
                                (f.(fn_code), Pos.succ (max_pc_function f)) in
      Some (mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
              (PTree.set n (Iop cop nil (acc_reg f) f.(fn_entrypoint)) c) n)
  | _, _ => None
  end.

(** Validation of the transformed function. *)

Fixpoint check_moves (c: code) (n: node) (moves: list (reg * reg)) (target: node) : bool :=
  match moves with
  | nil => proj_sumbool (peq n target)
  | (src, dst) :: ms =>
      match c!n with
      | Some (Iop Omove (src' :: nil) dst' n') =>
          proj_sumbool (peq src src') && proj_sumbool (peq dst dst')
          && check_moves c n' ms target
      | _ => false
      end
  end.

Definition check_instr (dm: defmap) (f: function) (k: accop) (bop: operation)
                       (tc: code) (pc: node) (i: instruction) : bool :=
  let acc := acc_reg f in
  match site_of dm f i with
  | Some (k', op, a) =>
      if accop_eq k k' then
        match tc!pc, i with
        | Some (Iop op' args' res' n1), Icall _ _ args _ _ =>
            proj_sumbool (eq_operation op op')
            && proj_sumbool (list_eq_dec peq args' (accarg_regs acc a))
            && proj_sumbool (peq res' acc)
            && check_moves tc n1 (call_moves f args) f.(fn_entrypoint)
        | _, _ => false
        end
      else
        match tc!pc with Some i' => proj_sumbool (instruction_eq i i') | None => false end
  | None =>
      match i with
      | Ireturn (Some r) =>
          ret_ok k f r &&
          match tc!pc with
          | Some (Iop op' (a1 :: a2 :: nil) res' n) =>
              proj_sumbool (eq_operation op' bop)
              && proj_sumbool (peq a1 acc) && proj_sumbool (peq a2 r)
              && proj_sumbool (peq res' acc)
              && match tc!n with
                 | Some (Ireturn (Some r')) => proj_sumbool (peq r' acc)
                 | _ => false
                 end
          | _ => false
          end
      | Itailcall _ _ _ => false
      | _ =>
          match tc!pc with Some i' => proj_sumbool (instruction_eq i i') | None => false end
      end
  end.

Definition check_function (dm: defmap) (f: function) (k: accop) (tf: function) : bool :=
  match accop_binary k, accop_const k with
  | Some bop, Some cop =>
      proj_sumbool (signature_eq tf.(fn_sig) f.(fn_sig))
      && proj_sumbool (list_eq_dec peq tf.(fn_params) f.(fn_params))
      && proj_sumbool (zeq tf.(fn_stacksize) f.(fn_stacksize))
      && proj_sumbool (zeq f.(fn_stacksize) 0)
      && match tf.(fn_code)!(tf.(fn_entrypoint)) with
         | Some (Iop cop' nil res n) =>
             proj_sumbool (eq_operation cop' cop)
             && proj_sumbool (peq res (acc_reg f))
             && proj_sumbool (peq n f.(fn_entrypoint))
         | _ => false
         end
      && PTree_Properties.for_all f.(fn_code) (check_instr dm f k bop tf.(fn_code))
  | _, _ => false
  end.

Definition transf_function (dm: defmap) (f: function) : function :=
  if zeq f.(fn_stacksize) 0 then
    match find_kind dm f with
    | None => f
    | Some k =>
        match gen_function dm f k with
        | Some tf => if check_function dm f k tf then tf else f
        | None => f
        end
    end
  else f.

Definition transf_fundef (dm: defmap) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function dm) fd.

Definition transf_program (p: program) : program :=
  transform_program (transf_fundef (prog_defmap p)) p.
