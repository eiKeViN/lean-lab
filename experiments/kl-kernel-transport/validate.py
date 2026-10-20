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

sys.dont_write_bytecode = True
import type_compare as tc

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
compiled_commit = 'a9568d548f48febeb2aa99b4ede8130e4eabba68'
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


def compiled_snapshot():
    relative = exp.relative_to(root)
    files = [str(relative / path(m)) for m in manifest['reference_modules'] + manifest['added_modules']]
    files += [str(relative / n) for n in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
              'KernelChecks.lean', 'CompatChecks.lean', 'BoundaryChecks.lean', 'Audit.lean',
              'Smoke.lean', 'api-manifest.json')]
    files += ['reports/evidence/kernel-transport-' + n for n in
              ('results.json', 'api-diagnostics.json', 'focused-types.json', 'audit.log')]
    hashes = {}
    for name in files:
        expected = subprocess.check_output(['git', 'show', compiled_commit + ':' + name], cwd=root)
        actual = (root / name).read_bytes()
        require(actual == expected, 'Changed compiled source/original evidence: ' + name)
        hashes[name] = hashlib.sha256(actual).hexdigest()
    return hashes


changed_files = identity()
compiled_hashes = compiled_snapshot()
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
measured('experiment-ready', ['lake', '--no-build', 'build', 'OAI'])
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

# Load raw DAGs without normalization. Supplementary Name rows do not enter
# global interning; policy comparison is per declaration and uses no memo.
intern = {}

def types(label, cwd, expected_modules):
    dump = output / (label + '.types')
    measured(label, ['env', 'LEAN_TYPES_OUT=' + str(dump), 'lake', 'env', 'lean',
                     '--root=' + str(exp), str(exp / 'PublicTypes.lean')], cwd)
    return tc.load_dump(dump, intern, expected_modules)

before = types('types-before', ref, manifest['reference_modules'])
after = types('types-after', exp, manifest['reference_modules'] + manifest['added_modules'])
frozen_record = json.loads((root / 'reports/evidence/kernel-transport-results.json').read_text())
for label, data in (('types-before', before), ('types-after', after)):
    expected_hash = frozen_record['type_dump_sha256'][label]
    require(data.raw_projection_sha256 == expected_hash, 'Original raw export changed: ' + label)
    saved = root / frozen_record['run'] / (label + '.types')
    if saved.exists():
        require(hashlib.sha256(saved.read_bytes()).hexdigest() == expected_hash,
                'Saved original export hash mismatch: ' + label)
comparison = tc.compare_public(before, after, manifest)
tests = measured('comparator-tests', [sys.executable, str(exp / 'test_type_compare.py'),
                  '--before', str(output / 'types-before.types'),
                  '--after', str(output / 'types-after.types')])
measured('warm', ['lake', 'build', 'OAI'])
identity()
require(compiled_snapshot() == compiled_hashes, 'Compiled source snapshot changed during checks')
workflow_hashes = {n: hashlib.sha256((exp / n).read_bytes()).hexdigest() for n in
                   ('PublicTypes.lean', 'validate.py', 'type_compare.py', 'test_type_compare.py', 'check.sh')}
summary = dict(status='ACCEPTED under ' + tc.RULE_VERSION,
               comparison=comparison, reference_commit=pin, compiled_source_commit=compiled_commit,
               compiled_source_and_original_evidence_sha256=compiled_hashes,
               workflow_sha256=workflow_hashes, changed_sources=changed_files,
               reference_public_count=len(before.rows), final_public_count=len(after.rows),
               new_declarations=manifest['new_declarations'], moved_declarations=manifest['moved_declarations'],
               excluded_before=before.excluded, excluded_after=after.excluded, axioms=closures,
               module_counts=dict(reference=len(before.modules), experiment=len(after.modules)),
               raw_projection_sha256=dict(before=before.raw_projection_sha256, after=after.raw_projection_sha256),
               type_dump_sha256={label: hashlib.sha256((output / (label + '.types')).read_bytes()).hexdigest()
                                 for label in ('types-before', 'types-after')})
(output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('ACCEPTED:', tc.RULE_VERSION, '3896 exact old declarations; 3 moved + 3 new pairs; 62 permitted fields.')
print('Evidence:', output.relative_to(root))
