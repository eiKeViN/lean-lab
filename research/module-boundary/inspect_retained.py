#!/usr/bin/env python3
"""Read-only structural diagnostics; never changes the production comparator."""
import gzip, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
E = ROOT / 'reports/evidence/module-rollout'
CHILDREN = {'app': (1,2), 'lam': (3,4), 'forall': (3,4), 'let': (2,3,4), 'proj': (3,), 'proof': (1,)}
def load(path):
    nodes, roots = {}, {}
    with gzip.open(path, 'rt') as f:
        for line in f:
            tag, *fields = line.rstrip('\n').split('\t')
            if tag == 'NODE': nodes[int(fields[0])] = json.loads(fields[1])
            if tag == 'TYPE': roots[fields[0]] = int(fields[2])
    return nodes, roots
def differences(a, b, ia, ib, path=()):
    x, y = a[ia], b[ib]
    children = CHILDREN.get(x[0], ())
    if x[0] != y[0] or len(x) != len(y): return [{'path': path, 'old': x, 'new': y}]
    found = []
    for i in range(len(x)):
        if i in children: found += differences(a,b,int(x[i]),int(y[i]),path+(i,))
        elif x[i] != y[i]: found.append({'path':path+(i,), 'old':x[i], 'new':y[i]})
    return found
oldpath = E/'final-validation/migrated-types.tsv.gz'
newpath = E/'rejected-131/migrated-types.tsv.gz'
a, ar = load(oldpath); b, br = load(newpath)
name = 'OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1'
print(json.dumps({'old':str(oldpath.relative_to(ROOT)), 'new':str(newpath.relative_to(ROOT)), 'name':name, 'leaf_differences':differences(a,b,ar[name],br[name])},indent=2))
