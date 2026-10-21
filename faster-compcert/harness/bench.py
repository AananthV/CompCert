#!/usr/bin/env python3
"""Compile the test/c benchmarks with several compilers, check their output
against test/c/Results, and report the minimum wall-clock time of each run.

Each run is pinned to one core.  A program is run at least N times and until
at least 1.5s of total run time has been accumulated.

usage: bench.py [-n N] [--core C] [--progs p1,p2] [--extra NAME=CMD ...] CONFIG...
Output: JSON {config: {program: seconds, or null if the output was wrong}}.
"""
import argparse, json, os, subprocess, sys, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
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

def build(name, cmd, outdir, progs):
    os.makedirs(outdir, exist_ok=True)
    for p in progs:
        r = subprocess.run(cmd + ['-o', os.path.join(outdir, p), os.path.join(SRC, p + '.c'), '-lm'],
                           capture_output=True, text=True)
        if r.returncode:
            print(f'[{name}] cannot compile {p}: {r.stderr[:300]}', file=sys.stderr)

def run(exe, prog, n, core):
    expected = open(os.path.join(SRC, 'Results', prog), 'rb').read()
    best, total, k = float('inf'), 0.0, 0
    while k < n or total < 1.5:
        t = time.perf_counter()
        r = subprocess.run(['taskset', '-c', str(core), exe], capture_output=True, cwd=SRC)
        dt = time.perf_counter() - t
        if r.stdout != expected:
            return None
        best, total, k = min(best, dt), total + dt, k + 1
    return best

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('configs', nargs='+')
    ap.add_argument('-n', type=int, default=7, help='minimum number of runs')
    ap.add_argument('--core', type=int, default=8, help='CPU core used for timing')
    ap.add_argument('--progs', default=','.join(PROGS))
    ap.add_argument('--extra', action='append', default=[],
                    help='add a config, e.g. "mine=/path/ccomp -stdlib /path/runtime"')
    ap.add_argument('--out', default='/tmp/faster-compcert-bench', help='directory for binaries')
    a = ap.parse_args()
    for e in a.extra:
        k, v = e.split('=', 1)
        CONFIGS[k] = v.split()
    progs = a.progs.split(',')
    res = {}
    for c in a.configs:
        build(c, CONFIGS[c], os.path.join(a.out, c), progs)
        res[c] = {p: run(os.path.join(a.out, c, p), p, a.n, a.core) for p in progs}
    print(json.dumps(res, indent=1))

if __name__ == '__main__':
    main()
