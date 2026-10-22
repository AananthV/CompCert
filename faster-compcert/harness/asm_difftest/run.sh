#!/bin/bash
# Differential test of the x86 Asm.v semantics of the load-op
# instructions against the hardware.  See README.md.
# usage: run.sh [COMPCERT_TREE] [N_RANDOM_PER_INSTR] [SEED]
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
TREE=$(cd "${1:-$HERE/../../..}" && pwd)
N=${2:-20000}
SEED=${3:-0x9e3779b97f4a7c15}
OUT=${ASM_DIFFTEST_OUT:-$(mktemp -d)}
mkdir -p "$OUT"
cp "$HERE"/Semantics.v "$HERE"/Extract.v "$HERE"/check.ml "$HERE"/hw.c "$HERE"/hw.s "$OUT"
cd "$OUT"
# Load paths of the CompCert tree, made absolute.
FLAGS=$(sed -e "s|-R \([^ ]*\) |-R $TREE/\1 |g" "$TREE/_CoqProject")
if command -v rocq >/dev/null; then COQC="rocq compile"; else COQC=coqc; fi
$COQC $FLAGS -R . "" Semantics.v
$COQC $FLAGS -R . "" Extract.v > /dev/null
ocamlfind ocamlopt -w -a difftest_sem.mli difftest_sem.ml check.ml -o check >/dev/null 2>&1 \
  || ocamlopt -w -a difftest_sem.mli difftest_sem.ml check.ml -o check
gcc -O1 -o hw hw.c hw.s
./hw "$N" "$SEED" > hw.txt
./check < hw.txt
