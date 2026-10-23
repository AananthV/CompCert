# asm_difftest: differential testing of Asm.v semantics against the CPU

`run.sh [COMPCERT_TREE] [N] [SEED] [GROUPS]` compares x86 instructions,
as printed by `TargetPrinter.ml`, run on this CPU with their `Asm.v`
semantics extracted to OCaml. The tree must be built (`make proof`).
`N` is the number of random tests per instruction (default 20000).
`GROUPS` is a comma-separated subset of the groups below (default: all):

| group    | issue | instructions |
|----------|-------|--------------|
| `loadop` | #5    | `Paddd_fm Psubd_fm Pmuld_fm Pdivd_fm Paddl_rm Pxorl_rm Pandl_rm Porl_rm` |
| `zx`     | #10   | `Psallzx_ri Pshrlzx_ri Pandlzx_ri` |
| `cvt`    | #10   | `Pcvtsi2sd_fr Pcvtsi2ss_fr Pcvtsl2sd_fr Pcvtsl2ss_fr Pcvtss2sd_ff Pcvtsd2ss_ff`, and `sqrtsd` (from `__builtin_fsqrt`), with the `xorpd`/`xorps` printed before them |
| `shift`  | #11   | `Psall_rcl Pshrl_rcl Psarl_rcl Psalq_rcl Pshrq_rcl Psarq_rcl`, whose count is masked in `Asm.v` since #11 |
| `zxload` | #25   | `Pmovzbq_rr Pmovzwq_rr Pmovzbq_rm Pmovzwq_rm` (8/16-bit zero extensions with a 64-bit result) |

For example, `run.sh . 20000 0x1 shift` runs only the shifts.
The script exits 1 if any group fails. Scratch files go to
`$ASM_DIFFTEST_OUT` (default: a fresh `mktemp -d`).

The reference is always the extracted Coq semantics (`Asm.exec_instr`,
`Val.*`, `Float.*`), not a reimplementation.

## Group `loadop`

- `Semantics.v` runs `Asm.exec_instr` on one instruction, with the
  register operand in `%xmm0`/`%eax` and the memory operand in a fresh
  `Mem.alloc`ed block at `0(%rdi)`.
- `hw.s` contains the same instructions. `hw.c` runs them on the special
  values (±0, ±inf, quiet/signaling NaNs with payloads, denormals,
  extremes; 0, ±1, INT_MIN, INT_MAX, ...), all pairs of them, and N random
  pairs per instruction.
- `check.ml` compares the hardware result bit for bit with the semantics.

## Groups `zx`, `cvt`, `shift`, `zxload` (register instructions)

- `gen_tests.py GROUPS SEED` writes `regs_tests.s`: one small body per
  instruction sequence, in the exact syntax of `TargetPrinter.ml` (and
  `Asmexpand.ml` for `sqrtsd`), including the `xorpd`/`xorps dst, dst`
  printed before the conversions. It uses several registers, including
  REX ones and, for `cvtss2sd`/`cvtsd2ss`/`sqrtsd`, `dst = src` (no clear
  printed). It also writes a table of the bodies.
  - `zx`: shift counts 0..63 (Asmgen emits 1..24 for `sall`, 1..31 for
    `shrl`; 32..63 are `Vundef` in the model). `andl` gets 15 special
    and 49 random immediates. The immediate is printed as a signed
    decimal, as `coqint` does.
  - `shift`: `%cl` takes every count 0..255; bits 8..63 of `%rcx` are
    zero or garbage.
  - `zxload`: the source register, or the byte/halfword in memory, takes
    every 8-bit value (16 times) or every 16-bit value. A register source
    has garbage in bits 8..63 or 16..63, and the old destination holds
    garbage. The memory forms use several addressing modes
    (`disp(%base)` and `disp(%base,%index,scale)`), with a random effective
    address in a 64 KiB buffer of random bytes and a random index.
- `regs_frame.s` (`hw_run`) loads a complete random register state (all
  GPRs except `%rsp`, all 128 bits of `%xmm0`-`%xmm15`, and CF PF AF ZF SF
  OF), calls the body, and saves the complete state. `hw_regs.c` builds
  the states. The destination holds garbage, or a value with garbage in
  its upper 32 bits. The sources are special or random values. Then
  it prints one line per test.
- `check_regs.ml` runs `Semantics.run_regs` (one `exec_instr` step) on the
  values the compiler would have in the registers: a `Vint` of the low
  32 bits, a `Vlong`, a `Vsingle`/`Vfloat` of the low lane. For the memory
  forms, `Semantics.run_mem` builds a memory block holding the bytes at
  the effective address, and sets the base register to a pointer into it
  and the index register to a `Vlong`. The model computes the address
  itself from these registers. `sqrtsd`
  uses the semantics of the builtin `__builtin_fsqrt`, because `Psqrtsd`
  is `Stuck` in `exec_instr`. Each test is classified as
  - **match**: the model is defined and equals the hardware result,
    which is all 64 bits for the `zx` and `zxload` groups and the 64-bit shifts, the
    low 32 bits for the 32-bit shifts, and the low lane for `cvt`;
  - **MISMATCH**: the model is defined and differs from the hardware
    (failure);
  - **undef**: the model gives `Vundef`, so there is no constraint.

  For `shift`, `Asm.v` masks the count since #11
  (`Val.shl rd (Val.and rcx 31)`, ...), so the model must be defined on
  every test: an undef result is a failure there.
  A test also fails (`regs` column) if any register other than the
  destination changed. For `cvt`, whose semantics uses `nextinstr`, it
  also fails if a flag changed. The `wrong-kind:undef` column runs the
  model on inputs the compiler does not produce (a `Vlong` for a 32-bit
  operation, `Vundef`, a float, ...) and counts how many give `Vundef`.
  The `info` column reports facts that are not modelled: the upper 32 bits
  are zeroed by 32-bit operations, and the upper XMM lanes are zero after
  the clear.

## Adding an instruction

For `loadop`, add a `sem_*` wrapper in `Semantics.v`, a function in `hw.s`,
and a case in `hw.c`/`check.ml`. For a register-only instruction, add
its printed form to `gen_tests.py`. Then add a case to `instr`,
`model_inputs` and `names` in `check_regs.ml`.
