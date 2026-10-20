#!/usr/bin/env python3
"""Validate this experiment without relaxing pristine-baseline checks."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

exp = Path(__file__).resolve().parent
root = exp.parents[1]
base = root/'experiments/kl'
module = 'OAI.RepresentationTheory.KazhdanLusztig.DihedralIntervals'
source = Path(module.replace('.', '/')+'.lean')
parser = argparse.ArgumentParser()
parser.add_argument('--measure', action='store_true', help='also time direct elaboration sequentially')
args = parser.parse_args()
output = root/'results/signed-ranks'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
output.mkdir(parents=True)

def require(condition, message):
    if not condition:
        raise SystemExit(message)

def run(command, cwd=exp):
    subprocess.run(command, cwd=cwd, check=True)

def measured(label, command, cwd=exp):
    log = output/(label+'.log')
    run([sys.executable, str(root/'scripts/measure.py'), str(log), *command], cwd)
    return log.read_text()

run([sys.executable, str(root/'scripts/verify.py')], root)
for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
    require((exp/name).read_bytes() == (base/name).read_bytes(), 'Changed configuration: '+name)
original = {p.relative_to(base) for p in (base/'OAI').rglob('*.lean')}
actual = {p.relative_to(exp) for p in (exp/'OAI').rglob('*.lean')}
require(actual == original, 'Changed OAI source file set')
changed = {p for p in original if (base/p).read_bytes() != (exp/p).read_bytes()}
require(changed == {source}, 'Unexpected changed-source set: '+str(changed))
require(not re.search(r'\b(sorry|admit|axiom|unsafe)\b', (exp/source).read_text()),
        'Forbidden proof bypass keyword in changed source')
# Check baseline readiness before copying artifacts or accepting any build cost.
measured('baseline-ready', ['lake', '--no-build', 'build', 'OAI'], base)
(exp/'.lake').mkdir(exist_ok=True)
packages = exp/'.lake/packages'
if not packages.exists():
    packages.symlink_to(base/'.lake/packages', target_is_directory=True)
require(packages.resolve() == (base/'.lake/packages').resolve(), 'Unexpected dependency cache path')
if not (exp/'.lake/build').exists():
    run(['cp', '-a', '--reflink=auto', str(base/'.lake/build'), str(exp/'.lake/build')])
measured('mathlib-ready', ['lake', '--no-build', 'build', 'Mathlib'])
if args.measure:
    measured('direct-before', ['lake', 'env', 'lean', str(source)], base)
    measured('direct-after', ['lake', 'env', 'lean', str(source)])
measured('module', ['lake', 'build', module])
measured('boundaries', ['lake', 'env', 'lean', 'BoundaryChecks.lean'])
measured('downstream', ['lake', 'build', 'OAI'])
audit = measured('audit', ['lake', 'env', 'lean', 'Audit.lean'])
prefix = 'OAI.KLInvariance.'
expected = {prefix+'SignedDihedral.'+n for n in (
    'arrowAfter_pair', 'arrowAfter_pair_below', 'countAfter_base',
    'countAfter_pos_formula', 'countAfter_neg_formula', 'countAfter_difference')}
expected |= {prefix+'TitsSpace.PlaneBasis.laterCount_difference', prefix+'combinatorial_invariance'}
closures = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit):
    require(name not in closures, 'Duplicate axiom closure: '+name)
    closures[name] = sorted({a.strip() for a in axioms.split(',') if a.strip()})
for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
    require(name not in closures, 'Duplicate axiom closure: '+name)
    closures[name] = []
require(set(closures) == expected, 'Missing or unexpected axiom output')
for name, axioms in closures.items():
    require(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Disallowed axioms: '+name)

# Intern constructor tuples across both dumps: exact DAG equality, not hashes.
intern = {}
child_fields = {'app': (1, 2), 'lam': (3, 4), 'forall': (3, 4),
                'let': (2, 3, 4), 'proj': (3,)}

def types(label, cwd):
    dump = output/(label+'.types')
    measured(label, ['env', 'LEAN_TYPES_OUT='+str(dump), 'lake', 'env', 'lean',
                     '--root='+str(exp), str(exp/'PublicTypes.lean')], cwd)
    nodes, rows, modules = {}, {}, set()
    for line in dump.open():
        line = line.rstrip('\n')
        if line.startswith('MODULE\t'):
            modules.add(line.split('\t', 1)[1])
        if line.startswith('NODE\t'):
            _, number, payload = line.split('\t', 2)
            fields = json.loads(payload)
            require(fields[0] in {'bvar', 'sort', 'const', 'app', 'lam', 'forall', 'let', 'lit', 'proj'},
                    'Unknown expression constructor')
            for i in child_fields.get(fields[0], ()):
                fields[i] = nodes[int(fields[i])]
            key = tuple(fields)
            nodes[int(number)] = intern.setdefault(key, len(intern))
        elif line.startswith('TYPE\t'):
            _, name, levels, node = line.split('\t')
            require(name not in rows, 'Duplicate public type: '+name)
            rows[name] = (json.loads(levels), nodes[int(node)])
    require(modules == {str(p.with_suffix('')).replace('/', '.') for p in original},
            'Missing module type coverage')
    require(rows, 'No public types exported')
    return rows

before = types('types-before', base)
after = types('types-after', exp)
require(all(after.get(name) == value for name, value in before.items()), 'Existing public type changed')
added = {prefix+'SignedDihedral.arrowAfter_pair', prefix+'SignedDihedral.arrowAfter_pair_below'}
require(set(after)-set(before) == added, 'Unexpected new public declarations')
measured('warm', ['lake', 'build', 'OAI'])
run([sys.executable, str(root/'scripts/verify.py')], root)
summary = dict(public_types_preserved=len(before), new_public_declarations=sorted(added), axioms=closures)
(output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps(summary, indent=2))
print('Evidence:', output.relative_to(root))
