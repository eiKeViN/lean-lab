#!/usr/bin/env python3
"""Verify the published frozen originals and accepted bridge source baseline."""
from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
baseline = json.loads((root / 'history/source-baselines.json').read_text())
for row in baseline['files']:
    rel = Path(row['path'])
    assert not rel.is_absolute() and '..' not in rel.parts
    path = root.parent / rel
    assert path.is_file() and not path.is_symlink(), rel
    assert hashlib.sha256(path.read_bytes()).hexdigest() == row['sha256'], rel
assert len(baseline['files']) == 20
print('PASS: 14 published historical files and 6 accepted bridge sources match SHA-256 baselines')
print('Scope: published source identity; private transfer archive and ignored logs are not required')
