(** Wrappers around the x86 [Asm.exec_instr] semantics, extracted to OCaml
  by [run.sh] and compared against the hardware by [check.ml].

  Each wrapper builds a register state and a memory with a single 8-byte
  block holding the memory operand, executes one instruction with the
  memory operand at [0(%rdi)], and returns the bits of the destination
  register (or [None] if the semantics is stuck or the result is not a
  number of the expected kind). *)

From Coq Require Import ZArith.
From compcert Require Import Coqlib Integers Floats Values Memory Globalenvs AST.
From compcert Require Import Asm.

Definition dummy_ge : genv := Genv.empty_genv fundef unit nil.
Definition dummy_fn : function := mkfunction signature_main nil.

Definition addr0 : addrmode := Addrmode (Some RDI) None (inl 0).

(** SSE form: [rd] is XMM0, holding the double whose bits are [x];
  the memory operand holds the 64 bits [mbits]. *)

Definition run_fm (mk: freg -> addrmode -> instruction) (x mbits: int64) : option int64 :=
  let (m1, b) := Mem.alloc Mem.empty 0 8 in
  match Mem.store Mint64 m1 b 0 (Vlong mbits) with
  | None => None
  | Some m2 =>
      let rs := (Pregmap.init Vundef) # XMM0 <- (Vfloat (Float.of_bits x))
                                      # RDI <- (Vptr b Ptrofs.zero) in
      match exec_instr dummy_ge dummy_fn (mk XMM0 addr0) rs m2 with
      | Next rs' _ =>
          match rs' XMM0 with Vfloat f => Some (Float.to_bits f) | _ => None end
      | Stuck => None
      end
  end.

(** Integer form: [rd] is RAX, holding the 32-bit integer [x];
  the memory operand holds the 32 bits [mbits]. *)

Definition run_rm (mk: ireg -> addrmode -> instruction) (x mbits: int) : option int :=
  let (m1, b) := Mem.alloc Mem.empty 0 8 in
  match Mem.store Mint32 m1 b 0 (Vint mbits) with
  | None => None
  | Some m2 =>
      let rs := (Pregmap.init Vundef) # RAX <- (Vint x)
                                      # RDI <- (Vptr b Ptrofs.zero) in
      match exec_instr dummy_ge dummy_fn (mk RAX addr0) rs m2 with
      | Next rs' _ =>
          match rs' RAX with Vint n => Some n | _ => None end
      | Stuck => None
      end
  end.

Definition sem_addsd := run_fm Paddd_fm.
Definition sem_subsd := run_fm Psubd_fm.
Definition sem_mulsd := run_fm Pmuld_fm.
Definition sem_divsd := run_fm Pdivd_fm.
Definition sem_addl := run_rm Paddl_rm.
Definition sem_xorl := run_rm Pxorl_rm.
Definition sem_andl := run_rm Pandl_rm.
Definition sem_orl := run_rm Porl_rm.

(** Conversions used by the OCaml driver. *)
Definition int64_of_Z (z: Z) : int64 := Int64.repr z.
Definition Z_of_int64 (n: int64) : Z := Int64.unsigned n.
Definition int_of_Z (z: Z) : int := Int.repr z.
Definition Z_of_int (n: int) : Z := Int.unsigned n.
