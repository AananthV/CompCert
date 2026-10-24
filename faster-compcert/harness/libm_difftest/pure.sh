#!/bin/bash
# Purity of the C library functions that -ftrust-libm treats as pure
# (issue #12, phase 2).  See README.md.
# usage: pure.sh [N_RANDOM] [SEED...]
# Each seed is run with the default ifunc selection of glibc, and with the
# FMA and AVX2 variants disabled (GLIBC_TUNABLES=glibc.cpu.hwcaps=-AVX2,-FMA,
# the spelling of glibc 2.33 and later).
HERE=$(cd "$(dirname "$0")" && pwd)
N=${1:-1000000}; shift
SEEDS=${*:-1 2 3}
OUT=${LIBM_DIFFTEST_OUT:-$(mktemp -d)}
mkdir -p "$OUT"
gcc -O1 -fno-builtin -o "$OUT/det" "$HERE/det.c" -lm || exit 1
fail=0
for seed in $SEEDS; do
  for v in default noavx2fma; do
    if [ $v = default ]; then tun=; else tun=glibc.cpu.hwcaps=-AVX2,-FMA; fi
    tag="seed=$seed $v"
    GLIBC_TUNABLES=$tun "$OUT/det" "$N" "$seed" > "$OUT/out" 2> "$OUT/err"
    rc=$?
    # Silence: no output other than the expected lines, nothing on stderr.
    extra=$(grep -cvE '^(fn |summary )' "$OUT/out")
    errbytes=$(wc -c < "$OUT/err")
    echo "$tag: $(tail -1 "$OUT/out") other_stdout_lines $extra stderr_bytes $errbytes"
    if [ $rc != 0 ] || [ "$extra" != 0 ] || [ "$errbytes" != 0 ]; then fail=1; fi
    cp "$OUT/out" "$OUT/out-$seed-$v"
  done
  # Per-function errno counts, and whether the two selections agree.
  paste <(grep '^fn ' "$OUT/out-$seed-default") <(grep '^fn ' "$OUT/out-$seed-noavx2fma") |
    awk '{ printf "%s:%s%s ", $2, $6, ($8 == $16 ? "" : "(selections differ)") } END { print "" }' |
    fold -s -w 100 | sed "s/^/  seed=$seed errno_set /"
done
[ $fail = 0 ] && echo "OK" || echo FAILED
exit $fail
