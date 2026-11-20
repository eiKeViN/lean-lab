#!/usr/bin/env python3
"""Record freshly run checks and source identities, without replaying frozen evidence."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import subprocess

root = Path(__file__).resolve().parents[1]

def run(*args):
    return subprocess.check_output(args, cwd=root, text=True).strip()

axioms = json.loads((root / 'evidence/axioms.json').read_text())
assert axioms['status'] == 'PASS'
assert os.environ.get('GIAL_CHECK_STARTED_AT'), 'Run this recorder through check.sh'
for name, expected in axioms['source_sha256'].items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == expected, name
result = {
    'status': 'PASS',
    'check_started_at_utc': os.environ['GIAL_CHECK_STARTED_AT'],
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean': run('lean', '--version'),
    'base_repository_commit': run('git', 'rev-parse', 'origin/main'),
    'dependencies': {name: run('git', '-C', f'.lake/packages/{name}', 'rev-parse', 'HEAD')
                     for name in ['mathlib', 'Physlib']},
    'checks': ['lake build Giallar', 'tests/*.lean fresh elaboration',
               'mathlib lint-style', 'mathlibStandardSet and autoImplicit=false on every module',
               'Lean.collectAxioms on every exported declaration', 'source structure and hashes'],
    'library_modules': len(axioms['audited_modules']),
    'exported_declarations': axioms['declaration_count'],
    'safe_logical_declarations': axioms['safe_logical_declaration_count'],
    'generated_runtime_helpers': axioms['generated_runtime_helper_count'],
    'allowed_axioms': axioms['allowed_axioms'],
    'source_manifest_sha256': hashlib.sha256((root / 'evidence/sources.json').read_bytes()).hexdigest(),
    'trust_scope': 'Fresh project elaboration with pinned cached dependencies; no independent full dependency rebuild',
}
(root / 'evidence/acceptance.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['status', 'library_modules', 'exported_declarations']}))
