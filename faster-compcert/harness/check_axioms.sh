#!/bin/bash
# Print the names of the axioms and parameters that CompCert's end-to-end
# correctness theorems depend on, for a built CompCert tree.
# usage: check_axioms.sh [compcert-tree]      (default: this repository)
# Compare with: diff ../results/axioms-master.txt <(check_axioms.sh)
TREE=${1:-$(dirname "$0")/../..}
cd "$TREE" || exit 1
F=$(mktemp --suffix=.v)
trap 'rm -f "$F"' EXIT
cat > "$F" <<'V'
From compcert.driver Require Import Compiler Complements.
Print Assumptions transf_c_program_correct.
Print Assumptions transf_c_program_preservation.
V
if command -v rocq >/dev/null; then REPL="rocq repl"; else REPL=coqtop; fi
$REPL $(tr '\n' ' ' < _CoqProject) -batch -load-vernac-source "$F" 2>&1 \
  | grep -E '^[A-Za-z]' | awk '{print $1}' | grep -v '^Axioms:$' | sort -u
