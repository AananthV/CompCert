(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  This file is distributed under the terms of the INRIA              *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)

(** Induction-variable widening and strength reduction over the RTL
  intermediate language. *)

(** The 64-bit address of an array access [a[i]] with a 32-bit index [i]
  is computed from the sign extension [(long) i] of [i].  Since 32-bit
  arithmetic wraps around, [(long) (i + 1)] differs from [(long) i + 1]
  in general, so that the sign extension is recomputed at every
  iteration of a loop, constant offsets as in [a[i - 3]] cannot be folded
  into the addressing mode, and the address [b + (long) i * 8800] of a
  row [b[i]] of a 2-dimensional array is recomputed with a multiplication.

  This pass introduces, for an induction variable [i] of a loop, a
  64-bit register [li] that holds [(long) i] in the loop, and derived
  registers [p] that hold [b + (long) i * m], where [b] is invariant in
  the loop:
- [li = (long) i] and [p = b + li * m] are computed on the edges that
  enter the loop;
- [li = li + c] and [p = p + m * c] are computed after each increment
  [i = i + c];
- an operation of the loop that computes [b + (long) i * m + d], such as
  [r = (long) i], [r = (long) (i + d)], [r = (long) i * m] or
  [r = b + (long) i * m], becomes [r = p + d] or [r = p];
- a comparison [i < n] becomes a 64-bit comparison of [li] and
  [(long) n], so that [i] often becomes dead;
- the arguments of an addressing mode that are known to be equal to [p]
  plus a constant are replaced by [p], with the offset adjusted, and
  copies are propagated into addressing modes.

  The increment [li = li + c] is only correct if [i + c] does not
  overflow, which is the case if [i < n] or [i < N] was tested in the
  current iteration, with [c = 1] or [N + c - 1 <= max_int].

  An untrusted oracle ([IVwidenaux.ml]) chooses the induction variables,
  the new instructions (inserted on edges, as chains of new nodes that
  only write fresh registers and cannot fail), the rewritings, and the
  facts that justify them at every node: [x = b + (long) i * m + d],
  [x = y], and bounds on the signed values of 32-bit registers.  The
  validator below checks that the facts are an inductive invariant of
  the transformed code, and that they imply the correctness of every
  rewriting.  If the check fails, the function is left unchanged. *)

Require Import Coqlib Maps AST Integers Values Op Registers RTL LICMop IVop IVdomain.

(** The oracle returns the new nodes, the redirection of the successors
  of the nodes of the function, the rewriting hints and the facts. *)

Parameter iv_oracle:
  function -> list (node * instruction) * PTree.t (list (node * node))
              * PTree.t hint * PTree.t (list fact).

Definition add_instrs (c: code) (l: list (node * instruction)) : code :=
  fold_left (fun c pi => PTree.set (fst pi) (snd pi) c) l c.

Definition transf_code (f: function) (ghosts: list (node * instruction))
                       (redir: PTree.t (list (node * node))) (hints: PTree.t hint) : code :=
  add_instrs (PTree.map (transf_instr redir hints) f.(fn_code)) ghosts.

(** A path of new nodes, from [s'] to [s].  Each new node writes a fresh
  register with an operation that cannot fail. *)

Fixpoint ghost_path (c: code) (mr: reg) (fuel: nat) (s' s: node) {struct fuel} : bool :=
  if peq s' s then true else
  match fuel with
  | O => false
  | S fuel' =>
      match c!s' with
      | Some (Iop op args t s'') =>
          op_safe op (length args) && Pos.ltb mr t && ghost_path c mr fuel' s'' s
      | _ => false
      end
  end.

Definition check_function (f: function) (ghosts: list (node * instruction))
                          (redir: PTree.t (list (node * node))) (hints: PTree.t hint)
                          (fm: PTree.t (list fact)) (tc: code) : bool :=
  let mr := max_reg_function f in
  let fuel := S (length ghosts) in
  forallb (fun gi => match f.(fn_code)!(fst gi) with None => true | Some _ => false end)
          ghosts
  && forallb (fun ni => forallb (fun s => ghost_path tc mr fuel (redirect redir (fst ni) s) s)
                                (successors_instr (snd ni)))
             (PTree.elements f.(fn_code))
  && forallb (fun nh => match f.(fn_code)!(fst nh) with
                        | Some i => hint_ok (facts_at fm (fst nh)) i (snd nh)
                        | None => true
                        end)
             (PTree.elements hints)
  && forallb (check_node fm) (PTree.elements tc)
  && (match facts_at fm f.(fn_entrypoint) with nil => true | _ => false end).

Definition transf_function (f: function) : function :=
  let '(ghosts, redir, hints, fm) := iv_oracle f in
  let tc := transf_code f ghosts redir hints in
  if check_function f ghosts redir hints fm tc then
    mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize) tc f.(fn_entrypoint)
  else f.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
