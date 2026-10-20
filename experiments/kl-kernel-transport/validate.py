#!/usr/bin/env python3
"""Validate kernel API relocation against a frozen, unchanged signed-ranks reference."""
import json
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

if len(sys.argv) != 1:
    raise SystemExit('Usage: bash experiments/kl-kernel-transport/check.sh')

exp = Path(__file__).resolve().parent
root = exp.parents[1]
ref = root / 'experiments/kl-signed-ranks'
base = root / 'experiments/kl'
manifest = json.loads((exp / 'api-manifest.json').read_text())
pin = '7225842219ed3844b2fbd9cf3d95f9b65bec862c'
bott = 'OAI.RepresentationTheory.KazhdanLusztig.BottSamelson'
generic, compat = manifest['added_modules']
names = ('kernelSourceEquiv', 'kernelTargetEquiv', 'kernelMixedEquiv')
output = root / 'results/kernel-transport' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
output.mkdir(parents=True)


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def run(command, cwd=exp):
    subprocess.run(command, cwd=cwd, check=True)


def measured(label, command, cwd=exp):
    log = output / (label + '.log')
    run([sys.executable, str(root / 'scripts/measure.py'), str(log), *command], cwd)
    return log.read_text()


def path(module):
    return Path(module.replace('.', '/') + '.lean')


def identity():
    require(manifest['reference_commit'] == pin, 'Unexpected reference pin')
    protected = ['experiments/kl', 'experiments/kl-signed-ranks', 'scripts', 'provenance']
    tracked = subprocess.check_output(
        ['git', 'ls-tree', '-r', '--name-only', pin, '--', *protected], cwd=root, text=True).splitlines()
    require(tracked, 'Missing protected reference files')
    for name in tracked:
        expected = subprocess.check_output(['git', 'show', pin + ':' + name], cwd=root)
        require((root / name).read_bytes() == expected, 'Protected file changed: ' + name)
    extra = subprocess.check_output(
        ['git', 'ls-files', '--others', '--exclude-standard', '--', *protected], cwd=root, text=True)
    require(not extra.strip(), 'Unexpected protected files: ' + extra)
    run([sys.executable, str(root / 'scripts/verify.py')], root)
    for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
        require((exp / name).read_bytes() == (ref / name).read_bytes(), 'Configuration changed: ' + name)
    expected = {path(m) for m in manifest['reference_modules']}
    require(len(expected) == 34, 'Expected 34 reference modules')
    require({p.relative_to(ref) for p in (ref / 'OAI').rglob('*.lean')} == expected,
            'Reference source set changed')
    additions = {path(generic), path(compat)}
    require({p.relative_to(exp) for p in (exp / 'OAI').rglob('*.lean')} == expected | additions,
            'Experiment source set differs from allowlist')
    changed = {p for p in expected if (exp / p).read_bytes() != (ref / p).read_bytes()}
    require(changed == {path(bott)}, 'Unexpected changed-source set: ' + str(changed))
    require((exp / 'BoundaryChecks.lean').read_bytes() == (ref / 'BoundaryChecks.lean').read_bytes(),
            'Inherited signed boundary checks changed')
    original = (ref / path(bott)).read_text()
    remaining = original
    for name in names:
        hit = remaining.index('def ' + name)
        start = remaining.rfind('\nsection\n', 0, hit)
        end = remaining.index('\nend KLInvariance\n\nend\n', hit) + len('\nend KLInvariance\n\nend\n')
        remaining = remaining[:start] + remaining[end:]
        # Preserve each complete implementation body byte-for-byte.
        def body(source):
            start = source.index(' where', source.index('def ' + name))
            return source[start:source.index('\nend ', start)]
        require(body(original) == body((exp / path(generic)).read_text()),
                'Implementation body changed: ' + name)
    remaining = remaining.replace('import OAI.RepresentationTheory.KazhdanLusztig.Frobenius\n',
                                  'import OAI.RepresentationTheory.KazhdanLusztig.Frobenius\nimport ' + compat + '\n', 1)
    require((exp / path(bott)).read_text() == remaining, 'Bott changed beyond exact relocation/import')
    for module in (generic, compat):
        require(not re.search(r'\b(sorry|admit|axiom|unsafe)\b', (exp / path(module)).read_text()),
                'Proof bypass keyword: ' + module)
    return sorted(str(p) for p in changed | additions)


changed_files = identity()
measured('versions', ['bash', '-c', 'set -e; lean --version; lake --version'])
measured('reference-mathlib-ready', ['lake', '--no-build', 'build', 'Mathlib'], ref)
measured('reference-ready', ['lake', '--no-build', 'build', 'OAI'], ref)
(exp / '.lake').mkdir(exist_ok=True)
packages = exp / '.lake/packages'
if not packages.exists():
    packages.symlink_to(base / '.lake/packages', target_is_directory=True)
require(packages.resolve() == (base / '.lake/packages').resolve(), 'Unexpected dependency cache')
build = exp / '.lake/build'
if not build.exists():
    run(['cp', '-a', '--reflink=auto', str(ref / '.lake/build'), str(build)])
require(not build.is_symlink() and build.resolve() != (ref / '.lake/build').resolve(),
        'Build directory must be independent')
for item in (ref / '.lake/build').rglob('*'):
    other = build / item.relative_to(ref / '.lake/build')
    if item.is_file() and other.exists():
        require(not os.path.samefile(item, other), 'Shared writable artifact: ' + str(other))
measured('mathlib-ready', ['lake', '--no-build', 'build', 'Mathlib'])
measured('generic', ['lake', 'build', generic])
measured('compat', ['lake', 'build', compat])
measured('independent-import', ['lake', 'env', 'lean', 'KernelChecks.lean'])
measured('compat-import', ['lake', 'env', 'lean', 'CompatChecks.lean'])
measured('bott-clients', ['lake', 'build', bott])
measured('signed-boundaries', ['lake', 'env', 'lean', 'BoundaryChecks.lean'])
measured('downstream', ['lake', 'build', 'OAI'])

audit = measured('audit', ['lake', 'env', 'lean', 'Audit.lean'])
prefix = 'OAI.KLInvariance.'
expected_audits = {prefix + 'SignedDihedral.' + n for n in (
    'arrowAfter_pair', 'arrowAfter_pair_below', 'countAfter_base',
    'countAfter_pos_formula', 'countAfter_neg_formula', 'countAfter_difference')}
expected_audits |= {
    prefix + 'TitsSpace.PlaneBasis.laterCount_difference', prefix + 'combinatorial_invariance'}
expected_audits |= {p + n for p in (prefix, 'OAI.LinearEquiv.') for n in names}
expected_audits |= {prefix + 'TitsSpace.' + n for n in ('bottHeadKernelEquiv', 'bottHeadRightKernelEquiv')}
closures = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit):
    require(name not in closures, 'Duplicate axiom closure: ' + name)
    closures[name] = sorted({a.strip() for a in axioms.split(',') if a.strip()})
for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
    require(name not in closures, 'Duplicate axiom closure: ' + name)
    closures[name] = []
require(set(closures) == expected_audits, 'Missing or unexpected axiom output')
for name, axioms in closures.items():
    require(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Disallowed axioms: ' + name)

# Shared exact constructor interning, including binder names/info and universes.
intern = {}
children = {'app': (1, 2), 'lam': (3, 4), 'forall': (3, 4), 'let': (2, 3, 4), 'proj': (3,)}


def types(label, cwd, expected_modules):
    dump = output / (label + '.types')
    measured(label, ['env', 'LEAN_TYPES_OUT=' + str(dump), 'lake', 'env', 'lean',
                     '--root=' + str(exp), str(exp / 'PublicTypes.lean')], cwd)
    nodes, rows, modules, owners, excluded = {}, {}, set(), {}, {}
    owner = None
    for line in dump.open():
        fields = line.rstrip('\n').split('\t')
        if fields[0] == 'MODULE':
            owner = fields[1]
            require(owner not in modules, 'Duplicate module: ' + owner)
            modules.add(owner)
        elif fields[0] == 'NODE':
            _, number, payload = fields
            key = json.loads(payload)
            require(key[0] in {'bvar', 'sort', 'const', 'app', 'lam', 'forall', 'let', 'lit', 'proj'},
                    'Unknown expression constructor')
            for i in children.get(key[0], ()):
                key[i] = nodes[int(key[i])]
            require(int(number) not in nodes, 'Duplicate expression node')
            nodes[int(number)] = intern.setdefault(tuple(key), len(intern))
        elif fields[0] == 'TYPE':
            _, name, levels, node, kind = fields
            require(owner is not None and name not in rows, 'Duplicate/unowned type: ' + name)
            rows[name] = (json.loads(levels), nodes[int(node)], kind)
            owners[name] = owner
        elif fields[0] == 'EXCLUDED':
            _, module, private, internal = fields
            require(module not in excluded, 'Duplicate exclusion count')
            excluded[module] = dict(private=int(private), internal=int(internal))
        else:
            raise SystemExit('Unknown dump row: ' + fields[0])
    require(modules == set(expected_modules), 'Module coverage mismatch: ' + label)
    require(set(excluded) == modules, 'Missing compiler exclusion counts')
    return rows, owners, excluded


before, owners_before, excluded_before = types('types-before', ref, manifest['reference_modules'])
after, owners_after, excluded_after = types(
    'types-after', exp, manifest['reference_modules'] + manifest['added_modules'])
require(len(before) == manifest['reference_public_count'], 'Unexpected reference public count: ' + str(len(before)))
bad = [name for name, value in before.items() if after.get(name) != value]
require(not bad, 'Existing public type/kind changed: ' + str(bad))
require(set(after) - set(before) == set(manifest['new_declarations']), 'Unexpected new public API')
require(len(after) == manifest['final_public_count'], 'Unexpected final public count: ' + str(len(after)))
moves = {name: owners_after[name] for name in before if owners_after[name] != owners_before[name]}
require(moves == manifest['moved_declarations'], 'Unexpected owner changes: ' + str(moves))
for name, owner in manifest['new_declarations'].items():
    require(owners_after[name] == owner and after[name][2] == 'def', 'Wrong new API owner/kind: ' + name)
    old = name.replace('OAI.LinearEquiv.', prefix, 1)
    require(after[name] == before[old], 'Relocated implementation type/kind changed: ' + name)
measured('warm', ['lake', 'build', 'OAI'])
identity()
summary = dict(reference_commit=pin, changed_sources=changed_files,
               reference_public_count=len(before), final_public_count=len(after),
               new_declarations=manifest['new_declarations'], moved_declarations=moves,
               excluded_before=excluded_before, excluded_after=excluded_after, axioms=closures,
               module_counts=dict(reference=len(manifest['reference_modules']),
                                  experiment=len(manifest['reference_modules']) + len(manifest['added_modules'])),
               type_dump_sha256={label: hashlib.sha256((output / (label + '.types')).read_bytes()).hexdigest()
                                 for label in ('types-before', 'types-after')})
(output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('Validated:', len(before), 'existing public declarations;', len(after), 'total.')
print('Evidence:', output.relative_to(root))
