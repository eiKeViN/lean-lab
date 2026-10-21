#!/usr/bin/env python3
"""Verify facts of this dated review against its matching checkout and base Git tree.

Not a semantic/proof review and not an ongoing architecture freeze. This optional
historical receipt check needs the recorded base Git object; it never fetches.
"""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[3]
PROJECT = ROOT / 'experiments/kl-for-mathlib'
RECORD = json.loads(Path(__file__).with_name('module-review.json').read_text())
migration = json.loads((PROJECT / 'migration.json').read_text())
fixed = {'ForMathlib.LinearAlgebra.KernelTransport', 'OAI.KL.Compatibility.KernelTransport'}
expected = set(migration['modules']) | fixed
rows = RECORD['current_review']
if len(rows) != len(expected) or {x['module'] for x in rows} != expected:
    raise RuntimeError('Current implementation coverage differs from this review')
for row in rows:
    data = (ROOT / row['path']).read_bytes()
    if hashlib.sha256(data).hexdigest() != row['source_sha256']:
        raise RuntimeError('Changed reviewed implementation: ' + row['module'])
    if row['imports'] != migration['modules'].get(row['module'], {}).get('imports', []):
        raise RuntimeError('Changed implementation imports: ' + row['module'])
base = RECORD['base']
base_migration = json.loads(subprocess.check_output(
    ['git', 'show', base + ':experiments/kl-for-mathlib/migration.json'], cwd=ROOT))
base_rows = RECORD['base_review']
if len(base_rows) != 192 or {x['module'] for x in base_rows} != set(base_migration['modules']) | fixed:
    raise RuntimeError('Incomplete base review inventory')
for row in base_rows:
    path = 'experiments/kl-for-mathlib/' + row['module'].replace('.', '/') + '.lean'
    data = subprocess.check_output(['git', 'show', base + ':' + path], cwd=ROOT)
    if hashlib.sha256(data).hexdigest() != row['source_sha256']:
        raise RuntimeError('Wrong base source receipt: ' + row['module'])
if {d for row in base_rows for d in row['destinations']} != expected:
    raise RuntimeError('Incomplete original-to-current destination coverage')
compat = RECORD['compatibility_review']
if len(compat) != len(migration['legacy_shims']) or {x['module'] for x in compat} != set(migration['legacy_shims']):
    raise RuntimeError('Incomplete compatibility-entry review')
for row in compat:
    data = (PROJECT / (row['module'].replace('.', '/') + '.lean')).read_bytes()
    if hashlib.sha256(data).hexdigest() != row['source_sha256'] or row['imports'] != migration['legacy_shims'][row['module']]:
        raise RuntimeError('Changed compatibility receipt: ' + row['module'])
for key in ('units', 'unit_partitions', 'source_hashes', 'fixed', 'instance_annotations'):
    if migration[key] != base_migration[key]:
        raise RuntimeError('Changed mathematical source allocation policy: ' + key)
fixed_imports = {'ForMathlib.LinearAlgebra.KernelTransport': [],
                 'OAI.KL.Compatibility.KernelTransport': ['ForMathlib.LinearAlgebra.KernelTransport']}
def reachable_units(data, name, seen=None):
    seen = set() if seen is None else seen
    if name == 'Mathlib' or name in seen:
        return set()
    seen.add(name)
    if name in data['modules']:
        item = data['modules'][name]
    elif name in fixed_imports:
        item = dict(units=['fixed:' + name], imports=fixed_imports[name])
    else:
        item = dict(units=[], imports=data['legacy_shims'][name])
    result = set(item['units'])
    for dependency in item['imports']:
        result |= reachable_units(data, dependency, seen)
    return result
for row in compat:
    name = row['module']
    if reachable_units(base_migration, name) - reachable_units(migration, name):
        raise RuntimeError('Compatibility entry lost original source exports: ' + name)
print(json.dumps(dict(base_implementations=len(base_rows), current_implementations=len(rows),
                     compatibility_entries=len(compat), source_records_unchanged=True,
                     compatibility_source_units_preserved=True,
                     original_to_current_coverage_complete=True, passed=True), indent=2))
