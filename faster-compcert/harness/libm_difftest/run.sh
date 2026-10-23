#!/bin/bash
# Differential test of the C library's sqrt and fabs against their models
# under -ftrust-libm, extracted from Coq.  See README.md.
# usage: run.sh [COMPCERT_TREE] [N_RANDOM] [SEED]
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
TREE=$(cd "${1:-$HERE/../../..}" && pwd)
N=${2:-10000000}
SEED=${3:-0x9e3779b97f4a7c15}
OUT=${LIBM_DIFFTEST_OUT:-$(mktemp -d)}
mkdir -p "$OUT"
cp "$HERE"/Semantics.v "$HERE"/Extract.v "$HERE"/check.ml "$HERE"/hw.c "$OUT"
cd "$OUT"
# Load paths of the CompCert tree, made absolute.
FLAGS=$(sed -e "s|-R \([^ ]*\) |-R $TREE/\1 |g" "$TREE/_CoqProject")
if command -v rocq >/dev/null; then COQC="rocq compile"; else COQC=coqc; fi
$COQC $FLAGS -R . "" Semantics.v
$COQC $FLAGS -R . "" Extract.v > /dev/null
ocamlfind ocamlopt -w -a libm_sem.mli libm_sem.ml check.ml -o check >/dev/null 2>&1 \
  || ocamlopt -w -a libm_sem.mli libm_sem.ml check.ml -o check
gcc -O1 -fno-builtin -o hw hw.c -lm
ldd ./hw | grep libm || true
./hw "$N" "$SEED" | ./check
