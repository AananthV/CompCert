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
From Coq Require Import String.

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

(** [run_mem i inits base baseoff bytes r] is like [run_regs], with a
  memory made of one block of [bufsize] bytes, which holds the bytes
  [bytes] (a list of (offset, value)) and is pointed to by [base] at
  offset [baseoff]. *)

Definition bufsize : Z := 131072.

Fixpoint store_bytes (m: mem) (b: block) (l: list (Z * Z)) : option mem :=
  match l with
  | nil => Some m
  | (ofs, v) :: l' =>
      match Mem.store Mint8unsigned m b ofs (Vint (Int.repr v)) with
      | Some m' => store_bytes m' b l'
      | None => None
      end
  end.

Definition run_mem (i: instruction) (inits: list (preg * val)) (base: preg) (baseoff: Z)
                   (bytes: list (Z * Z)) (r: preg) : option val :=
  let (m1, b) := Mem.alloc Mem.empty 0 bufsize in
  match store_bytes m1 b bytes with
  | None => None
  | Some m2 =>
      let rs := fold_left (fun rs pv => rs # (fst pv) <- (snd pv)) inits (Pregmap.init Vundef) in
      match exec_instr dummy_ge dummy_fn i (rs # base <- (Vptr b (Ptrofs.repr baseoff))) m2 with
      | Next rs' _ => Some (rs' r)
      | Stuck => None
      end
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

(** * Unaligned 64-bit loads and stores (issue #13)

  [run_store i inits base baseoff bytes lo n] is like [run_mem] for a
  store instruction: it returns the [n] bytes at offsets [lo ...] of the
  block after the store (as [Mint8unsigned] loads; [Vundef] for a byte
  that cannot be read). *)

Fixpoint zrange (n: nat) (lo: Z) : list Z :=
  match n with O => nil | S n' => lo :: zrange n' (lo + 1) end.

Definition run_store (i: instruction) (inits: list (preg * val)) (base: preg) (baseoff: Z)
                     (bytes: list (Z * Z)) (lo: Z) (n: nat) : option (list val) :=
  let (m1, b) := Mem.alloc Mem.empty 0 bufsize in
  match store_bytes m1 b bytes with
  | None => None
  | Some m2 =>
      let rs := fold_left (fun rs pv => rs # (fst pv) <- (snd pv)) inits (Pregmap.init Vundef) in
      match exec_instr dummy_ge dummy_fn i (rs # base <- (Vptr b (Ptrofs.repr baseoff))) m2 with
      | Next _ m3 =>
          Some (map (fun ofs => match Mem.load Mint8unsigned m3 b ofs with
                                | Some v => v | None => Vundef end) (zrange n lo))
      | Stuck => None
      end
  end.

(** Unit tests of the memory model around [perm_limit] (issue #13):
  each test is expected to be [true]. *)

Definition is_some {A: Type} (o: option A) : bool := match o with Some _ => true | None => false end.

Local Open Scope string_scope.

Definition perm_limit_tests : list (string * bool) :=
  let (m1, b1) := Mem.alloc Mem.empty 0 Ptrofs.modulus in
  let (m2, b2) := Mem.alloc Mem.empty 0 perm_limit in
  let (m3, b3) := Mem.alloc Mem.empty 0 4096 in
  let (m4, b4) := Mem.alloc Mem.empty (-8) (perm_limit + 100) in
  ("huge block: byte at perm_limit-1 readable", is_some (Mem.load Mint8unsigned m1 b1 (perm_limit - 1))) ::
  ("huge block: byte at perm_limit not readable", negb (is_some (Mem.load Mint8unsigned m1 b1 perm_limit))) ::
  ("huge block: byte at 2^64-1 not readable", negb (is_some (Mem.load Mint8unsigned m1 b1 (Ptrofs.modulus - 1)))) ::
  ("huge block: Mint64u load at perm_limit-8", is_some (Mem.loadv Mint64u m1 (Vptr b1 (Ptrofs.repr (perm_limit - 8))))) ::
  ("huge block: no Mint64u load at perm_limit-7", negb (is_some (Mem.loadv Mint64u m1 (Vptr b1 (Ptrofs.repr (perm_limit - 7)))))) ::
  ("huge block: no Mint64u load at 2^64-4", negb (is_some (Mem.loadv Mint64u m1 (Vptr b1 (Ptrofs.repr (Ptrofs.modulus - 4)))))) ::
  ("huge block: Mint64u store at perm_limit-8", is_some (Mem.storev Mint64u m1 (Vptr b1 (Ptrofs.repr (perm_limit - 8))) (Vlong Int64.one))) ::
  ("huge block: no Mint64u store at perm_limit-7", negb (is_some (Mem.storev Mint64u m1 (Vptr b1 (Ptrofs.repr (perm_limit - 7))) (Vlong Int64.one)))) ::
  ("block [0,perm_limit): last byte readable", is_some (Mem.load Mint8unsigned m2 b2 (perm_limit - 1))) ::
  ("block [0,4096): byte 4095 readable", is_some (Mem.load Mint8unsigned m3 b3 4095)) ::
  ("block [0,4096): byte 4096 not readable", negb (is_some (Mem.load Mint8unsigned m3 b3 4096))) ::
  ("block [0,4096): byte -1 not readable", negb (is_some (Mem.load Mint8unsigned m3 b3 (-1)))) ::
  ("block [0,4096): Mint64u at 4088", is_some (Mem.load Mint64u m3 b3 4088)) ::
  ("block [0,4096): no Mint64u at 4089", negb (is_some (Mem.load Mint64u m3 b3 4089))) ::
  ("block [0,4096): Mint64u at 4081 (odd)", is_some (Mem.load Mint64u m3 b3 4081)) ::
  ("block [0,4096): no Mint64 at 4081 (aligned chunk)", negb (is_some (Mem.load Mint64 m3 b3 4081))) ::
  ("malloc-like block [-8,perm_limit+100): header at -8", is_some (Mem.store Mptr m4 b4 (-8) (Vlong Int64.one))) ::
  ("malloc-like block: byte at perm_limit-1 readable", is_some (Mem.load Mint8unsigned m4 b4 (perm_limit - 1))) ::
  ("malloc-like block: byte at perm_limit not readable", negb (is_some (Mem.load Mint8unsigned m4 b4 perm_limit))) ::
  ("Mem.perm at perm_limit is never granted (drop_perm fails)", negb (is_some (Mem.drop_perm m1 b1 perm_limit (perm_limit + 1) Readable))) ::
  nil.
