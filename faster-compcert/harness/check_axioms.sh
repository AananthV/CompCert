#!/bin/bash
# Print the names of the axioms and parameters that CompCert's end-to-end
# correctness theorems depend on, for a built CompCert tree.
# usage: check_axioms.sh [compcert-tree]      (default: this repository)
# Compare with: diff ../results/axioms-master.txt <(check_axioms.sh)
# Exits with an error (and prints nothing on stdout) if Rocq/Coq is not
# available or the theorems cannot be loaded, so that a failed run is never
# mistaken for an empty or short list of assumptions.
set -o pipefail
TREE=${1:-$(dirname "$0")/../..}
cd "$TREE" || exit 1
if command -v rocq >/dev/null; then REPL="rocq repl"
elif command -v coqtop >/dev/null; then REPL=coqtop
else echo "check_axioms.sh: neither rocq nor coqtop found in PATH" >&2; exit 1; fi
F=$(mktemp --suffix=.v)
OUT=$(mktemp)
trap 'rm -f "$F" "$OUT"' EXIT
cat > "$F" <<'V'
From compcert.driver Require Import Compiler Complements.
Print Assumptions transf_c_program_correct.
Print Assumptions transf_c_program_preservation.
V
$REPL $(tr '\n' ' ' < _CoqProject) -batch -load-vernac-source "$F" > "$OUT" 2>&1
if ! grep -q '^Axioms:' "$OUT"; then
  echo "check_axioms.sh: could not print the assumptions; output was:" >&2
  head -20 "$OUT" >&2
  exit 1
fi
grep -E '^[A-Za-z]' "$OUT" | awk '{print $1}' | grep -v '^Axioms:$' | sort -u
