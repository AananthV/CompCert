#!/bin/bash
# Check which declarations -ftrust-libm treats as pure libm functions
# (issue #12, phase 2).  Each decl/*.c file states in its first line
# "EXPECT on=N off=M": the number of direct calls (call or jmp) to the 50
# listed functions in the assembly, with and without -ftrust-libm.  The
# files call functions twice on the same arguments, so that a pure function
# is called once.  A line "OPTIONS ..." gives extra options.
# usage: decl.sh CCOMP [RUNTIME]
HERE=$(cd "$(dirname "$0")" && pwd)
CCOMP=$1
RUNTIME=${2:-$(dirname "$CCOMP")/runtime}
OUT=$(mktemp -d)
F='floor|ceil|trunc|round|sin|cos|tan|asin|acos|atan|sinh|cosh|tanh|exp|exp2|expm1|log|log2|log10|log1p|cbrt|pow|atan2|fmod|hypot'
F="$F|lgamma|frexp|fmin"
count() { grep -cE "^\s*(call|jmp)\s+(($F)f?)(@PLT)?\s*$" "$1"; }
fail=0; n=0
for f in "$HERE"/decl/*.c; do
  opts=$(sed -n 's|.*OPTIONS \(.*\) \*/|\1|p' "$f")
  got=""
  for flag in -ftrust-libm -fno-trust-libm; do
    n=$((n + 1))
    s="$OUT/$(basename "$f" .c)$flag.s"
    if ! "$CCOMP" -stdlib "$RUNTIME" $opts $flag -S "$f" -o "$s" 2>/dev/null; then
      echo "FAIL $(basename "$f") $flag: does not compile"; fail=1; continue
    fi
    if [ $flag = -ftrust-libm ]; then got="on=$(count "$s")"; else got="$got off=$(count "$s")"; fi
  done
  want=$(sed -n '1s|.*EXPECT \(.*\) \*/|\1|p' "$f")
  if [ "$got" = "$want" ]; then res=ok; else res=FAIL; fail=1; fi
  printf '%-4s %-18s %s\n' "$res" "$(basename "$f")" "$got"
done
rm -rf "$OUT"
[ $fail = 0 ] && echo "OK: $n compilations as expected" || echo FAILED
exit $fail
