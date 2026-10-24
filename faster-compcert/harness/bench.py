#!/usr/bin/env python3
"""Compile a benchmark suite with several compilers, check each program's
result, and report the minimum wall-clock time of each program.

Each run is pinned to one core.  For each program, the configs are run in
interleaved rounds (one run of each config per round, in rotating order), so
that load from other users of the machine affects all configs alike.  Rounds
continue until every config has at least N runs and 1.5s of total run time.

Suites: `c` (test/c, the default), `big` (raytracer, spass, compression) and
`polybench` (PolyBench/C 4.2.1, see fetch_polybench.sh); see suites.py.

usage: bench.py [--suite S] [-n N] [--core C] [--progs p1,p2] [--extra NAME=CMD ...] CONFIG...
Output: JSON {config: {program: seconds, or null if the result was wrong}}.
"""
import argparse, json, os, subprocess, sys, time

import suites

ROOT = suites.ROOT
SRC = os.path.join(ROOT, 'test', 'c')
PROGS = ('fib integr qsort fft fftsp fftw sha1 sha3 aes almabench lists '
         'binarytrees fannkuch knucleotide mandelbrot nbody nsieve nsievebits '
         'spectral vmach bisect chomp perlin siphash24').split()

# GCC restricted to what CompCert's semantics allow: wrapping signed
# arithmetic, no type-based alias analysis, no SIMD, no FMA contraction.
CCMODEL = ['-fwrapv', '-fno-strict-aliasing', '-fno-tree-vectorize', '-ffp-contract=off']

CONFIGS = {
    'gcc-O0': ['gcc', '-O0'],
    'gcc-O1': ['gcc', '-O1'],
    'gcc-O2': ['gcc', '-O2'],
    'gcc-O3': ['gcc', '-O3'],
    'gcc-O2-ccmodel': ['gcc', '-O2'] + CCMODEL,
    'gcc-O3-ccmodel': ['gcc', '-O3'] + CCMODEL,
    'ccomp': [os.path.join(ROOT, 'ccomp'), '-stdlib', os.path.join(ROOT, 'runtime')],
}


def test_c():
    def check(prog):
        expected = open(os.path.join(SRC, 'Results', prog), 'rb').read()
        return lambda w, out: out[0] == expected
    return [suites.Bench(p, [os.path.join(SRC, p + '.c')],
                         steps=lambda exe, w: [([exe], None, SRC)], check=check(p))
            for p in PROGS]


def run_once(bench, exe, workdir, core):
    """One timed run of a program; None if it fails or its result is wrong."""
    outs = []
    t = time.perf_counter()
    for argv, stdin, cwd in bench.steps(exe, workdir):
        with open(stdin, 'rb') if stdin else open(os.devnull, 'rb') as f:
            r = subprocess.run(['taskset', '-c', str(core)] + argv, stdin=f,
                               capture_output=True, cwd=cwd)
        if r.returncode:
            return None
        outs.append(r.stdout)
    dt = time.perf_counter() - t
    return dt if bench.check(workdir, outs) else None


def run_interleaved(bench, exes, n, core):
    """Minimum run time of each config, timed in interleaved rounds.
    exes: {config: (exe, workdir)}.  A config whose run fails gets None."""
    best = {c: float('inf') for c in exes}
    total = {c: 0.0 for c in exes}
    alive = list(exes)
    k = 0
    while alive and (k < n or any(total[c] < 1.5 for c in alive)):
        order = alive[k % len(alive):] + alive[:k % len(alive)]
        for c in order:
            dt = run_once(bench, exes[c][0], exes[c][1], core)
            if dt is None:
                best[c] = None
                alive.remove(c)
                continue
            best[c], total[c] = min(best[c], dt), total[c] + dt
        k += 1
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('configs', nargs='+')
    ap.add_argument('--suite', choices=['c', 'big', 'polybench'], default='c')
    ap.add_argument('--polybench', default=os.environ.get('POLYBENCH_DIR'),
                    help='PolyBench/C directory (see fetch_polybench.sh)')
    ap.add_argument('-n', type=int, default=7, help='minimum number of runs')
    ap.add_argument('--core', type=int, default=8, help='CPU core used for timing')
    ap.add_argument('--progs', help='comma-separated subset of the suite')
    ap.add_argument('--extra', action='append', default=[],
                    help='add a config, e.g. "mine=/path/ccomp -stdlib /path/runtime"')
    ap.add_argument('--out', default='/tmp/faster-compcert-bench', help='directory for binaries')
    a = ap.parse_args()
    for e in a.extra:
        k, v = e.split('=', 1)
        CONFIGS[k] = v.split()
    benches = {'c': test_c, 'big': suites.big,
               'polybench': lambda: suites.polybench(a.polybench)}[a.suite]()
    if a.progs:
        wanted = a.progs.split(',')
        benches = [b for b in benches if b.name in wanted]
    res = {c: {} for c in a.configs}
    for b in benches:
        exes = {}
        for c in a.configs:
            workdir = os.path.join(a.out, a.suite, c)
            os.makedirs(workdir, exist_ok=True)
            try:
                exes[c] = (b.build(CONFIGS[c], workdir), workdir)
            except RuntimeError as e:
                print(f'[{c}] {e}', file=sys.stderr)
                res[c][b.name] = None
        for c, t in run_interleaved(b, exes, a.n, a.core).items():
            res[c][b.name] = t
    print(json.dumps(res, indent=1))


if __name__ == '__main__':
    main()
