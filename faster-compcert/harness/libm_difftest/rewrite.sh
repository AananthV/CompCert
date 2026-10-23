#!/bin/bash
# Check which calls to sqrt and fabs -ftrust-libm turns into builtins.
# Each rewrite/*.c file states the expected result in its first line,
# "EXPECT sqrt=R fabs=R", where R is
#   builtin: compiled to sqrtsd / andpd, with no call to the function;
#   call:    still a call (or tail call) to the function;
#   none:    neither.
# A line "OPTIONS ..." gives extra options.  Each file is also compiled
# without -ftrust-libm, where no builtin may appear.
# usage: rewrite.sh CCOMP [RUNTIME]
HERE=$(cd "$(dirname "$0")" && pwd)
CCOMP=$1
RUNTIME=${2:-$(dirname "$CCOMP")/runtime}
OUT=$(mktemp -d)
classify() {   # classify ASM FUNCTION
  local pat insn
  if [ "$2" = sqrt ]; then insn='sqrtsd'; else insn='__absd_mask'; fi
  if grep -Eq "^\s*(call|jmp)\s+$2\b" "$1"; then echo call
  elif grep -q "$insn" "$1"; then echo builtin
  else echo none; fi
}
fail=0; n=0
for f in "$HERE"/rewrite/*.c; do
  opts=$(sed -n 's|.*OPTIONS \(.*\) \*/|\1|p' "$f")
  for flag in -ftrust-libm -fno-trust-libm; do
    n=$((n + 1))
    s="$OUT/$(basename "$f" .c)$flag.s"
    if ! "$CCOMP" -stdlib "$RUNTIME" $opts $flag -S "$f" -o "$s"; then
      echo "FAIL $(basename "$f") $flag: does not compile"; fail=1; continue
    fi
    got="sqrt=$(classify "$s" sqrt) fabs=$(classify "$s" fabs)"
    want=$(sed -n '1s|.*EXPECT \(.*\) \*/|\1|p' "$f")
    [ "$flag" = -fno-trust-libm ] && want=${want//builtin/call}
    if [ "$got" = "$want" ]; then res=ok; else res=FAIL; fail=1; fi
    printf '%-4s %-18s %-15s %s\n' "$res" "$(basename "$f")" "$flag" "$got"
  done
done
rm -rf "$OUT"
[ $fail = 0 ] && echo "OK: $n compilations as expected" || echo FAILED
exit $fail
