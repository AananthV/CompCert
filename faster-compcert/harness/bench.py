#!/usr/bin/env python3
"""Compile a benchmark suite with several compilers, check each program's
result, and report the minimum wall-clock time of each program.

Each run is pinned to one core.  A program is run at least N times and until
at least 1.5s of total run time has been accumulated.

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


def run(bench, exe, workdir, n, core):
    best, total, k = float('inf'), 0.0, 0
    while k < n or total < 1.5:
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
        if not bench.check(workdir, outs):
            return None
        best, total, k = min(best, dt), total + dt, k + 1
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
    res = {}
    for c in a.configs:
        res[c] = {}
        for b in benches:
            workdir = os.path.join(a.out, a.suite, c)
            os.makedirs(workdir, exist_ok=True)
            try:
                exe = b.build(CONFIGS[c], workdir)
            except RuntimeError as e:
                print(f'[{c}] {e}', file=sys.stderr)
                res[c][b.name] = None
                continue
            res[c][b.name] = run(b, exe, workdir, a.n, a.core)
    print(json.dumps(res, indent=1))


if __name__ == '__main__':
    main()
