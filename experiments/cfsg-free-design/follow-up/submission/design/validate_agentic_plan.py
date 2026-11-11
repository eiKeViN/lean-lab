"""Validate design bookkeeping and supplied source hashes only; never invoke Lean.

Run from any cwd: python3 /work/design/validate_agentic_plan.py
Writes /work/design/validation-report.json; exits nonzero on a failed check.
Historical files under /work/previous are read-only inputs and are never modified.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/work')
REPORT = ROOT / 'design/validation-report.json'
errors: list[str] = []
checks: dict[str, object] = {}


def require(condition: bool, message: str) -> None:
    if not condition:
        errors.append(message)


def read_json(relative: str):
    return json.loads((ROOT / relative).read_text(encoding='utf-8'))


def inspect() -> None:
    original = read_json('previous/design/obligations.json')
    workplan = read_json('design/agentic-workplan.json')
    old = {p['id']: p for p in original['packages']}
    packages = workplan['packages']
    by_id = {p['id']: p for p in packages}
    require(len(packages) == len(by_id) == 50, 'Expected exactly 50 unique parent packages')
    require(set(old) == set(by_id), 'Parent package ID set differs from historical ledger')
    for key in ('target', 'mathlib_rev', 'tauceti_rev'):
        require(workplan.get(key) == original[key], f'Changed fixed metadata: {key}')
    for key, p in by_id.items():
        if key not in old:
            continue
        prior = old[key]
        for field in ('stream', 'title', 'acceptance', 'owner_role'):
            require(p.get(field) == prior[field], f'Changed original {key}.{field}')
        require(p.get('reference_depends_on') == prior['depends_on'],
                f'Historical dependency list changed: {key}')
        require('depends_on' not in p, f'{key}: coarse dependencies must be reference_depends_on')
        require(p.get('status') == 'proposed_unverified', f'{key}: status overstates verification')
        require(bool(p.get('reference_dependency_semantics')), f'{key}: missing coarse-DAG explanation')
        require(p.get('runtime_dispatch', {}).get('unit') == 'theorem_card', f'{key}: not card dispatch')
        require(p.get('runtime_dispatch', {}).get('status') == 'proposed_unverified',
                f'{key}: runtime status overstates verification')
        sequence = [step.get('mode') for step in p.get('implementation_order', [])]
        require(sequence == ['audit_reuse', 'adapt', 'new_proof'], f'{key}: wrong implementation order')
        duties = p.get('execution_responsibilities', {})
        require(all(duties.get(r, {}).get('duty') for r in ('executor', 'reviewer', 'consumer')),
                f'{key}: missing executor/reviewer/consumer responsibilities')
        require(bool(p.get('scheduling_refinement')), f'{key}: missing dispatch refinement')
    checks['original_parent_packages_preserved'] = len(by_id)

    # All edges are historical coverage edges, not runtime barriers or proved dependencies.
    visited: set[str] = set()
    active: set[str] = set()
    order: list[str] = []

    def visit(key: str) -> None:
        if key not in by_id:
            errors.append(f'Unknown historical dependency: {key}')
            return
        if key in active:
            errors.append(f'Historical reference dependency cycle: {key}')
            return
        if key in visited:
            return
        active.add(key)
        for dependency in by_id[key]['reference_depends_on']:
            visit(dependency)
        active.remove(key)
        visited.add(key)
        order.append(key)

    visit('Z02')
    final_ancestors = set(visited)
    require(final_ancestors == set(by_id), 'Parent packages disconnected from final Z02 delivery')
    for key in by_id:
        visit(key)
    checks['reference_dependency_graph_acyclic'] = not any('cycle:' in e for e in errors)
    checks['all_parents_reachable_as_final_dependencies'] = final_ancestors == set(by_id)
    checks['reference_topological_order'] = order
    checks['runtime_dependency_graph_verified'] = False

    organization = workplan['organization']
    pods = organization['math_pods']
    services = organization['shared_services']
    pod_ids = {p['id'] for p in pods}
    service_ids = {s['id'] for s in services}
    all_units = pod_ids | service_ids
    require(len(pods) == len(pod_ids) == 24, 'Expected 24 unique math pods')
    require(len(services) == len(service_ids) == 6, 'Expected 6 unique shared service pools')
    require(not pod_ids.intersection(service_ids), 'Pod/shared IDs overlap')
    require(all(p['concurrent_slots'] == sum(p['roles'].values()) == 8 for p in pods),
            'Each mathematical pod must have exactly 8 role slots')
    math_slots = sum(p['concurrent_slots'] for p in pods)
    shared_slots = sum(s['concurrent_slots'] for s in services)
    require(math_slots == 192 and shared_slots == 64, 'Expected 192 math + 64 shared slots')
    require(organization['steady_slots'] == math_slots + shared_slots == 256,
            'Steady concurrency arithmetic mismatch')
    require(organization['pilot_math_pods'] * 8 + organization['pilot_shared_slots'] ==
            organization['pilot_slots'] == 64, 'Pilot concurrency arithmetic mismatch')
    assigned: set[str] = set()
    for key, p in by_id.items():
        units = set(p.get('owning_units', []))
        require(bool(units) and units <= all_units, f'{key}: missing/unknown owning units')
        assigned.update(units)
        if key in ('E00', 'E01'):
            require(units <= service_ids, f'{key}: engineering package must belong to shared services')
        for role in ('executor', 'reviewer', 'consumer'):
            assigned_units = set(p['execution_responsibilities'][role].get('units', []))
            require(assigned_units <= all_units, f'{key}: unknown {role} units')
        consumers = p['execution_responsibilities']['consumer'].get('parent_packages', [])
        require(set(consumers) <= set(by_id), f'{key}: unknown parent consumers')
    require(pod_ids <= assigned, 'Some of the 24 mathematical pods have no package responsibility')
    checks['organization'] = {'math_pods': len(pods), 'math_slots': math_slots,
                              'shared_slots': shared_slots, 'total_slots': math_slots + shared_slots,
                              'numbers_are_planning_assumptions': True}

    source_root = ROOT / 'sources'
    index = (source_root / 'TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean').read_text()
    lie_block = index.split('inductive LieTypeIndex where', 1)[1].split('deriving DecidableEq', 1)[0]
    sporadic_block = index.split('inductive SporadicName where', 1)[1].split('deriving DecidableEq', 1)[0]
    lie = set(re.findall(r'^  \| (\w+)', lie_block, re.M))
    sporadic = set(re.findall(r'\|\s*(\w+)', sporadic_block))
    require(len(lie) == 17 and len(sporadic) == 26, 'Pinned source constructor count mismatch')
    for key, source_names, count, dispatch_key in (
        ('lie_family_owner', lie, 17, 'lie_family_dispatch'),
        ('sporadic_owner', sporadic, 26, 'sporadic_dispatch'),
    ):
        mapping = workplan[key]
        require(mapping == original[key], f'Changed original {key} exact mapping')
        require(set(mapping) == source_names and len(mapping) == count,
                f'{key}: does not match pinned source constructors')
        dispatch = workplan[dispatch_key]
        require(set(dispatch) == source_names, f'{dispatch_key}: constructor coverage mismatch')
        for name, parent in mapping.items():
            require(parent in by_id, f'{key}/{name}: unknown owner {parent}')
            require(dispatch[name]['parent_package'] == parent, f'{dispatch_key}/{name}: wrong parent')
            require(set(dispatch[name]['units']) <= all_units, f'{dispatch_key}/{name}: unknown unit')
            require(dispatch[name]['status'] == 'proposed_unverified',
                    f'{dispatch_key}/{name}: status overstates verification')
    checks['lie_constructors_covered'] = len(lie)
    checks['sporadic_constructors_covered'] = len(sporadic)

    manifest = read_json('sources/source-manifest.json')
    require(len(manifest) == 90, 'Expected 90 supplied source manifest entries')
    require(len({row['path'] for row in manifest}) == len(manifest), 'Duplicate manifest source paths')
    verified = 0
    for row in manifest:
        path = source_root / row['path']
        if not path.is_file():
            errors.append(f'Missing pinned source: {row["path"]}')
            continue
        data = path.read_bytes()
        size_ok = len(data) == row['bytes']
        hash_ok = hashlib.sha256(data).hexdigest() == row['sha256']
        require(size_ok, f'Source byte mismatch: {row["path"]}')
        require(hash_ok, f'Source SHA-256 mismatch: {row["path"]}')
        verified += int(size_ok and hash_ok)
    checks['source_manifest_entries_verified'] = verified
    checks['mathlib_inventory_paths'] = len((source_root / 'mathlib-paths.txt').read_text().splitlines())

    required = workplan['required_design_deliverables']
    expected = {'AGENTIC_PLAN.zh-CN.md', 'reviews/MATH_REVIEW.zh-CN.md',
                'reviews/OPERATING_MODEL.zh-CN.md', 'reviews/ASSURANCE.zh-CN.md',
                'design/agentic-workplan.json', 'design/validate_agentic_plan.py',
                'design/validation-report.json'}
    require(set(required) == expected, 'Design deliverable manifest differs from expected files')
    checks['required_design_deliverables'] = required
    for relative in required:
        path = ROOT / relative
        if path == REPORT:
            continue  # This run generates the report, even on validation failure.
        require(path.is_file() and path.stat().st_size > 0, f'Missing/empty deliverable: {relative}')
    for key in ('K00', 'A00', 'A01', 'A02', 'N00'):
        require(bool(by_id[key]['scheduling_refinement'].get('split_axes')),
                f'{key}: required fine-grained scheduling axes missing')
    require(bool(by_id['T07'].get('operational_acceptance')),
            'T07 must clarify that residual parameter families are not assumed finite exceptions')


def main() -> int:
    try:
        inspect()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        errors.append(f'Validation could not complete: {type(exc).__name__}: {exc}')
    report = {
        'schema_version': 1,
        'generated_at_utc': datetime.now(timezone.utc).isoformat(),
        'root': str(ROOT),
        'status': 'passed' if not errors else 'failed',
        'check_scope': 'design bookkeeping, exact historical coverage, local pinned source hashes, deliverable presence only',
        'design_only': True,
        'lean_executable_invoked': False,
        'lean_kernel_checked': False,
        'mathematical_route_verified': False,
        'future_cfsg_implementation_acquired_or_audited': False,
        'performance_or_cost_assumptions_empirically_validated': False,
        'checks': checks,
        'errors': errors,
    }
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    summary = {k: v for k, v in report.items() if k != 'checks'}
    summary['counts'] = {k: checks.get(k) for k in ('original_parent_packages_preserved',
        'lie_constructors_covered', 'sporadic_constructors_covered', 'source_manifest_entries_verified')}
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0 if not errors else 1


if __name__ == '__main__':
    sys.exit(main())
