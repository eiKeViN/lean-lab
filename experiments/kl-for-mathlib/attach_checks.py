"""Strict ordinary modern API comparison for the three new producers."""
import json,sys,hashlib
from pathlib import Path
from compare_types import load,compare
HERE=Path(__file__).resolve().parent
raw=(HERE/'attach-module-types.json').read_bytes()
EXPECTED_SHA='eb5657d0d3d2faa00ddce096030c4bcf3fc4e29dabce267c4b7ce5a64919d96e'
if hashlib.sha256(raw).hexdigest()!=EXPECTED_SHA:raise RuntimeError('Changed three-module public expectation')
r=compare(json.loads(raw),load(sys.argv[1],93))
print(json.dumps(r,indent=2))
if not r['passed'] or r['relocated']:raise SystemExit(1)
