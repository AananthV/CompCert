(** Wrappers around the x86 [Asm.exec_instr] semantics, extracted to OCaml
  by [run.sh] and compared against the hardware by [check.ml].

  Each wrapper builds a register state and a memory with a single 8-byte
  block holding the memory operand, executes one instruction with the
  memory operand at [0(%rdi)], and returns the bits of the destination
  register (or [None] if the semantics is stuck or the result is not a
  number of the expected kind). *)

From Coq Require Import ZArith.
From compcert Require Import Coqlib Integers Floats Values Memory Globalenvs AST.
From compcert Require Import Asm Builtins.

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

(** * Register-only instructions (issues #10 and #11)

  [run_regs i inits r] executes the single instruction [i] from the
  register state where the registers of [inits] hold the given values
  (and all others are [Vundef]), with an empty memory, and returns the
  final value of register [r] ([None] if the semantics is stuck).
  The instruction is built by the OCaml driver ([check_regs.ml]) with
  the extracted constructors of [Asm.instruction]. *)

Definition run_regs (i: instruction) (inits: list (preg * val)) (r: preg) : option val :=
  let rs := fold_left (fun rs pv => rs # (fst pv) <- (snd pv)) inits (Pregmap.init Vundef) in
  match exec_instr dummy_ge dummy_fn i rs Mem.empty with
  | Next rs' _ => Some (rs' r)
  | Stuck => None
  end.

(** [sqrtsd] is produced by [Asmexpand] from the builtin [__builtin_fsqrt]
  ([Psqrtsd] itself is [Stuck] in [exec_instr], as are all instructions
  produced by the expander).  Its semantics is that of the builtin. *)

Definition sem_fsqrt (v: val) : option val :=
  builtin_function_sem (BI_standard BI_fsqrt) (v :: nil).

(** Values from and to unsigned integers (bit patterns). *)

Definition vint (z: Z) : val := Vint (Int.repr z).
Definition vlong (z: Z) : val := Vlong (Int64.repr z).
Definition vfloat_bits (z: Z) : val := Vfloat (Float.of_bits (Int64.repr z)).
Definition vsingle_bits (z: Z) : val := Vsingle (Float32.of_bits (Int.repr z)).

Inductive res : Type :=
  | RUndef
  | RInt (z: Z)        (**r [Vint]: unsigned 32 bits *)
  | RLong (z: Z)       (**r [Vlong]: unsigned 64 bits *)
  | RFloat (z: Z)      (**r [Vfloat]: its 64 bits *)
  | RSingle (z: Z)     (**r [Vsingle]: its 32 bits *)
  | RPtr.

Definition res_of_val (v: val) : res :=
  match v with
  | Vundef => RUndef
  | Vint n => RInt (Int.unsigned n)
  | Vlong n => RLong (Int64.unsigned n)
  | Vfloat f => RFloat (Int64.unsigned (Float.to_bits f))
  | Vsingle f => RSingle (Int.unsigned (Float32.to_bits f))
  | Vptr _ _ => RPtr
  end.
