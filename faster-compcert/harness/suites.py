"""Benchmark suites beyond test/c, used by bench.py --suite.

Each benchmark is described by a `Bench`: how to compile it, how to run it
(a list of steps, all timed together) and how to check its result.

- `big`: the larger programs of the CompCert test suite (raytracer, spass,
  and the three compression programs).
- `polybench`: the 30 PolyBench/C 4.2.1 kernels, fetched separately with
  fetch_polybench.sh.  These were not used to tune any faster-compcert
  heuristic, so they measure how well the results generalize.
"""
import filecmp, os, re, shutil, subprocess

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
TEST = os.path.join(ROOT, 'test')


def is_ccomp(cmd):
    return os.path.basename(cmd[0]).startswith('ccomp')


def compile_c(cmd, sources, exe):
    r = subprocess.run(cmd + ['-w', '-o', exe] + sources + ['-lm'], capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(f'cannot compile {os.path.basename(exe)}: {r.stderr[:400]}')
    return exe


class Bench:
    """name: benchmark name.
    sources: C files.  flags: extra flags, as {'ccomp': [...], 'gcc': [...]}.
    steps(exe, workdir): list of (argv, stdin_path, cwd) run in sequence.
    check(workdir, outputs): True if the result is correct; `outputs` is the
    list of stdouts of the steps."""

    def __init__(self, name, sources, steps, check, flags=None):
        self.name, self.sources, self.steps, self.check = name, sources, steps, check
        self.flags = flags or {}

    def build(self, cmd, outdir):
        extra = self.flags.get('ccomp' if is_ccomp(cmd) else 'gcc', [])
        return compile_c(cmd + extra, self.sources, os.path.join(outdir, self.name))


# ---------------------------------------------------------------- big

def _raytracer():
    d = os.path.join(TEST, 'raytracer')
    objs = ('memory gmllexer gmlparser eval arrays vector matrix object '
            'intersect surface light simplify render main').split()
    return Bench('raytracer', [os.path.join(d, o + '.c') for o in objs],
                 steps=lambda exe, w: [([exe], os.path.join(d, 'kal.gml'), w)],
                 check=lambda w, out: filecmp.cmp(os.path.join(w, 'kal.ppm'),
                                                  os.path.join(d, 'Results', 'kal.ppm'),
                                                  shallow=False),
                 flags={'ccomp': ['-fstruct-passing']})


def _spass_reference_trace(out):
    # Drop the timing lines; keep the whole proof-search trace.
    return [l for l in out.decode(errors='replace').splitlines()
            if '0:00:' not in l and 'spent' not in l]


def _spass():
    d = os.path.join(TEST, 'spass')
    mk = open(os.path.join(d, 'Makefile')).read()
    srcs = re.findall(r'[\w-]+\.c', mk.split('SRCS=')[1].split('all:')[0])
    expected = {}

    def check(w, out):
        trace = _spass_reference_trace(out[0])
        if 'reference' not in expected:
            expected['reference'] = _reference_spass(srcs, d)
        return 'SPASS beiseite: Proof found.' in trace and trace == expected['reference']

    return Bench('spass', [os.path.join(d, s) for s in srcs],
                 steps=lambda exe, w: [([exe, 'problem.dfg'], None, d)],
                 check=check, flags={'ccomp': ['-fstruct-passing']})


def _reference_spass(srcs, d):
    """The trace of spass compiled with gcc -O0, computed once and cached."""
    cache = os.path.join(_cache_dir(), 'spass.trace')
    if not os.path.exists(cache):
        exe = compile_c(['gcc', '-O0'], [os.path.join(d, s) for s in srcs],
                        os.path.join(_cache_dir(), 'spass.ref'))
        out = subprocess.run([exe, 'problem.dfg'], cwd=d, capture_output=True).stdout
        open(cache, 'w').write('\n'.join(_spass_reference_trace(out)))
    return open(cache).read().split('\n')


def _compression_input():
    """A deterministic ~1 MB text file: the SPASS sources, repeated."""
    path = os.path.join(_cache_dir(), 'compression-input.txt')
    if not os.path.exists(path):
        d = os.path.join(TEST, 'spass')
        text = b''.join(open(os.path.join(d, f), 'rb').read()
                        for f in sorted(os.listdir(d)) if f.endswith(('.c', '.h')))
        with open(path, 'wb') as f:
            while f.tell() < 1024 * 1024:
                f.write(text)
    return path


def _compression(name, objs):
    d = os.path.join(TEST, 'compression')
    inp = _compression_input()

    def steps(exe, w):
        c, x = os.path.join(w, name + '.compressed'), os.path.join(w, name + '.expanded')
        return [([exe, '-c', '-i', inp, '-o', c], None, w),
                ([exe, '-d', '-i', c, '-o', x], None, w)]

    return Bench(name, [os.path.join(d, o + '.c') for o in ['optlist', 'bitfile'] + objs],
                 steps=steps,
                 check=lambda w, out: filecmp.cmp(inp, os.path.join(w, name + '.expanded'),
                                                  shallow=False),
                 flags={'ccomp': ['-U__GNUC__']})


def big():
    return [_raytracer(), _spass(),
            _compression('arcode', ['arcode', 'armain']),
            _compression('lzw', ['lzwencode', 'lzwdecode', 'lzwmain']),
            _compression('lzss', ['lzvars', 'lzhash', 'lzencode', 'lzdecode', 'lzssmain'])]


# ---------------------------------------------------------------- polybench

# Dataset used for timing each kernel: the largest standard size for which
# CompCert 3.18 runs in roughly 0.1-6 s on the reference machine.
POLYBENCH_DATASET = {
    'atax': 'EXTRALARGE', 'bicg': 'EXTRALARGE', 'mvt': 'EXTRALARGE',
    'gemver': 'EXTRALARGE', 'gesummv': 'EXTRALARGE', 'trisolv': 'EXTRALARGE',
    'durbin': 'EXTRALARGE', 'jacobi-1d': 'EXTRALARGE',
    'cholesky': 'MEDIUM', 'lu': 'MEDIUM', 'ludcmp': 'MEDIUM',
    'floyd-warshall': 'MEDIUM', 'adi': 'MEDIUM', 'heat-3d': 'MEDIUM',
    'seidel-2d': 'MEDIUM',
}


class PolyBench(Bench):
    """A PolyBench kernel.  The timed binary uses the dataset above; the
    result is checked by a second binary, built with the same compiler at
    MEDIUM size with -DPOLYBENCH_DUMP_ARRAYS, whose dump must equal the one
    of gcc -O0."""

    def __init__(self, root, rel):
        name = os.path.splitext(os.path.basename(rel))[0]
        self.root, self.dir = root, os.path.join(root, os.path.dirname(rel))
        src = [os.path.join(root, 'utilities', 'polybench.c'), os.path.join(self.dir, name + '.c')]
        super().__init__(name, src, steps=lambda exe, w: [([exe], None, w)], check=self._check)

    def _cmd(self, cmd, dataset, dump):
        return (cmd + ['-I', os.path.join(self.root, 'utilities'), '-I', self.dir,
                       f'-D{dataset}_DATASET'] + (['-DPOLYBENCH_DUMP_ARRAYS'] if dump else []))

    def build(self, cmd, outdir):
        self.check_exe = compile_c(self._cmd(cmd, 'MEDIUM', True), self.sources,
                                   os.path.join(outdir, self.name + '.check'))
        return compile_c(self._cmd(cmd, POLYBENCH_DATASET.get(self.name, 'LARGE'), False),
                         self.sources, os.path.join(outdir, self.name))

    def _dump(self, exe):
        return subprocess.run([exe], capture_output=True).stderr

    def _check(self, w, out):
        ref = os.path.join(_cache_dir(), f'polybench-{self.name}.dump')
        if not os.path.exists(ref):
            exe = compile_c(self._cmd(['gcc', '-O0'], 'MEDIUM', True), self.sources,
                            os.path.join(_cache_dir(), f'polybench-{self.name}.ref'))
            open(ref, 'wb').write(self._dump(exe))
        return self._dump(self.check_exe) == open(ref, 'rb').read()


def polybench(root):
    if not root or not os.path.isdir(os.path.join(root, 'utilities')):
        raise SystemExit('PolyBench not found: run fetch_polybench.sh DIR and pass --polybench DIR')
    rels = [l.strip()[2:] for l in open(os.path.join(root, 'utilities', 'benchmark_list')) if l.strip()]
    return [PolyBench(root, r) for r in rels]


# ---------------------------------------------------------------- utilities

def _cache_dir():
    d = os.environ.get('FASTER_COMPCERT_CACHE', '/tmp/faster-compcert-cache')
    os.makedirs(d, exist_ok=True)
    return d
