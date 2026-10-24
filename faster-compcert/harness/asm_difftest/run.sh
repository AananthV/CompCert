#!/bin/bash
# Differential test of the x86 Asm.v semantics against the hardware.
# See README.md.
# usage: run.sh [COMPCERT_TREE] [N_RANDOM_PER_INSTR] [SEED] [GROUPS]
#   GROUPS: comma-separated subset of loadop,zx,cvt,shift,zxload,unal (default: all)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
TREE=$(cd "${1:-$HERE/../../..}" && pwd)
N=${2:-20000}
SEED=${3:-0x9e3779b97f4a7c15}
GROUPS_=${4:-loadop,zx,cvt,shift,zxload,unal}
OUT=${ASM_DIFFTEST_OUT:-$(mktemp -d)}
mkdir -p "$OUT"
cp "$HERE"/Semantics.v "$HERE"/Extract.v "$HERE"/check.ml "$HERE"/hw.c "$HERE"/hw.s \
   "$HERE"/check_regs.ml "$HERE"/hw_regs.c "$HERE"/regs_frame.s \
   "$HERE"/check_unal.ml "$HERE"/hw_unal.c "$HERE"/unal_frame.s "$OUT"
cd "$OUT"
# Load paths of the CompCert tree, made absolute.
FLAGS=$(sed -e "s|-R \([^ ]*\) |-R $TREE/\1 |g" "$TREE/_CoqProject")
if command -v rocq >/dev/null; then COQC="rocq compile"; else COQC=coqc; fi
$COQC $FLAGS -R . "" Semantics.v
$COQC $FLAGS -R . "" Extract.v > /dev/null
build_checker() {   # build_checker OUTPUT MAIN.ml
  ocamlfind ocamlopt -w -a difftest_sem.mli difftest_sem.ml "$2" -o "$1" >/dev/null 2>&1 \
    || ocamlopt -w -a difftest_sem.mli difftest_sem.ml "$2" -o "$1"
}
status=0
# Load-op instructions (#5).
if [[ ,$GROUPS_, == *,loadop,* ]]; then
  echo "== loadop"
  build_checker check check.ml
  gcc -O1 -o hw hw.c hw.s
  ./hw "$N" "$SEED" > hw.txt
  ./check < hw.txt || status=1
fi
# Register and memory instructions (#10: zx, cvt; #11: shift; #25: zxload).
REGS=$(echo "$GROUPS_" | tr ',' '\n' | grep -E '^(zx|cvt|shift|zxload)$' | paste -sd, -)
if [ -n "$REGS" ]; then
  echo "== $REGS"
  python3 -I "$HERE"/gen_tests.py "$REGS" "$SEED" > regs_tests.s
  build_checker check_regs check_regs.ml
  gcc -O1 -o hw_regs hw_regs.c regs_frame.s regs_tests.s
  ./hw_regs "$N" "$SEED" > hw_regs.txt
  ./check_regs < hw_regs.txt || status=1
fi
# Unaligned 64-bit loads and stores, and the memory model bound (#13).
if [[ ,$GROUPS_, == *,unal,* ]]; then
  echo "== unal"
  build_checker check_unal check_unal.ml
  gcc -O1 -o hw_unal hw_unal.c unal_frame.s
  ./hw_unal "$N" "$SEED" > hw_unal.txt
  ./check_unal < hw_unal.txt || status=1
fi
exit $status
