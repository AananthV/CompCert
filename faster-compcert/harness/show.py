#!/usr/bin/env python3
"""Pretty-print one or more bench.py JSON files side by side.
The last line is the geometric mean relative to the first config."""
import json, math, sys

d = {}
for f in sys.argv[1:]:
    d.update(json.load(open(f)))
cs = list(d)
base = d[cs[0]]
print('prog'.ljust(12), *[c[:16].rjust(16) for c in cs])
for p in base:
    print(p.ljust(12), *[('%.4f' % d[c][p] if d[c].get(p) else 'FAIL').rjust(16) for c in cs])
def gm(c):
    ps = [p for p in base if d[c].get(p) and base[p]]
    if not ps:
        return 'n/a'
    return '%.3f' % math.exp(sum(math.log(d[c][p] / base[p]) for p in ps) / len(ps))
print(('geomean/' + cs[0])[:12].ljust(12), *[gm(c).rjust(16) for c in cs])
