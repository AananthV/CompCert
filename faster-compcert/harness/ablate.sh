#!/bin/bash
# Leave-one-family-out ablation of GCC optimizations, starting from
# gcc -O2 restricted to CompCert's semantic model.  Writes abl-<family>.json.
# usage: ablate.sh [core]
H=$(dirname "$0")
CORE=${1:-8}
REF="-O2 -fwrapv -fno-strict-aliasing -fno-tree-vectorize -ffp-contract=off"
declare -A F=(
 [nobuiltin]="-fno-builtin"
 [noinline]="-fno-inline-functions -fno-inline-small-functions -fno-inline-functions-called-once -fno-early-inlining -fno-partial-inlining -fno-ipa-cp -fno-ipa-sra -fno-ipa-icf -fno-ipa-ra -fno-ipa-vrp -fno-ipa-bit-cp -fno-ipa-pure-const -fno-ipa-modref"
 [nolicm]="-fno-tree-loop-im -fno-move-loop-invariants"
 [noivopts]="-fno-ivopts -fno-tree-slsr -fno-tree-scev-cprop"
 [nolooprot]="-fno-tree-ch"
 [noifconv]="-fno-if-conversion -fno-if-conversion2 -fno-tree-loop-if-convert -fno-ssa-phiopt"
 [nopre]="-fno-tree-pre -fno-gcse -fno-code-hoisting -fno-tree-fre"
 [nosched]="-fno-schedule-insns2"
 [novrp]="-fno-tree-vrp"
 [nosra]="-fno-tree-sra"
 [nothread]="-fno-thread-jumps -fno-tree-dominator-opts"
 [noreassoc]="-fno-tree-reassoc"
 [nolayout]="-fno-reorder-blocks -fno-reorder-blocks-and-partition -fno-align-functions -fno-align-jumps -fno-align-loops -fno-align-labels"
)
for k in "${!F[@]}"; do
  python3 "$H/bench.py" --core "$CORE" --extra "abl-$k=gcc $REF ${F[$k]}" "abl-$k" > "abl-$k.json"
done
