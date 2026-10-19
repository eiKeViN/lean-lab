#!/usr/bin/env python3
"""Cheap failure-path regressions; no Lean build or network access."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
(root/'results').mkdir(exist_ok=True)
audit = (root/'scripts/check.sh').read_text().split("<<'PY'\n", 1)[1].split('\nPY', 1)[0]

def run(args, optimized, expected):
    env = dict(os.environ, PYTHONOPTIMIZE=str(optimized))
    result = subprocess.run([sys.executable, *args], env=env, capture_output=True, text=True)
    if (result.returncode == 0) != expected:
        raise SystemExit(f'Unexpected status {result.returncode}: {args}\n{result.stdout}{result.stderr}')

with tempfile.TemporaryDirectory(dir=root/'results') as temp:
    fixture = Path(temp)
    log = fixture/'audit.log'
    name = "'OAI.KLInvariance.combinatorial_invariance'"
    for optimized in (0, 1):
        for text, expected in [
            (name+' depends on axioms: [propext, Quot.sound, Classical.choice]', True),
            (name+' depends on axioms: [sorryAx]', False),
            (name+' depends on axioms: [Other.axiom]', False),
            ("'Other.theorem' depends on axioms: [propext]", False),
            ('', False),
        ]:
            log.write_text(text)
            run(['-c', audit, str(log)], optimized, expected)
    (fixture/'scripts').mkdir()
    shutil.copy(root/'scripts/verify.py', fixture/'scripts/verify.py')
    shutil.copytree(root/'provenance', fixture/'provenance')
    project = fixture/'experiments/kl'
    project.mkdir(parents=True)
    shutil.copytree(root/'experiments/kl/OAI', project/'OAI')
    for name in ('lean-toolchain', 'lake-manifest.json'):
        shutil.copy(root/'experiments/kl'/name, project/name)
    verify = str(fixture/'scripts/verify.py')
    source = next((project/'OAI').rglob('*.lean'))
    original = source.read_bytes()
    manifest = project/'lake-manifest.json'
    lock = manifest.read_text()
    for optimized in (0, 1):
        run([verify], optimized, True)
        source.write_bytes(original+b'\n')
        run([verify], optimized, False)
        source.write_bytes(original)
        (project/'lean-toolchain').write_text('leanprover/lean4:v0.0.0\n')
        run([verify], optimized, False)
        shutil.copy(root/'experiments/kl/lean-toolchain', project/'lean-toolchain')
        data = json.loads(lock)
        next(d for d in data['packages'] if d['name']=='mathlib')['rev'] = '0'*40
        manifest.write_text(json.dumps(data))
        run([verify], optimized, False)
        manifest.write_text(lock)
    bin_dir = fixture/'bin'
    bin_dir.mkdir()
    calls = fixture/'calls.log'
    (bin_dir/'lake').write_text("""#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$MOCK_CALLS"
if [[ "$*" == '--no-build build Mathlib' ]]; then exit "$MOCK_READY"; fi
if [[ "$*" == 'exe cache get Mathlib' ]]; then exit "$MOCK_DOWNLOAD"; fi
exit 99
""")
    (bin_dir/'curl').write_text('#!/usr/bin/env bash\necho unexpected-network >> "$MOCK_CALLS"\nexit 97\n')
    for command in bin_dir.iterdir():
        command.chmod(0o755)
    for ready, download, expected in [(0, 99, True), (1, 22, False), (1, 0, False)]:
        calls.write_text('')
        env = dict(os.environ, PATH=str(bin_dir)+':'+os.environ['PATH'],
                   MOCK_CALLS=str(calls), MOCK_READY=str(ready), MOCK_DOWNLOAD=str(download))
        env.pop('CACHE_PROBE_URL', None)
        result = subprocess.run(['bash', str(root/'scripts/cache.sh')], env=env,
                                capture_output=True, text=True)
        if (result.returncode == 0) != expected:
            raise SystemExit('Cache guard returned unexpected status: '+result.stdout+result.stderr)
        if ready != 0 and download != 0 and result.returncode != download:
            raise SystemExit('Cache download failure status was not propagated')
        if ready == 0 and calls.read_text().splitlines() != ['--no-build build Mathlib']:
            raise SystemExit('Warm cache attempted network access')
        if 'unexpected-network' in calls.read_text():
            raise SystemExit('Cache guard made an unsolicited probe')
    calls.write_text('')
    env.update(MOCK_READY='1', CACHE_PROBE_URL='https://cache.example.invalid/artifact')
    result = subprocess.run(['bash', str(root/'scripts/cache.sh')], env=env,
                            capture_output=True, text=True)
    if result.returncode != 97 or 'exe cache get Mathlib' in calls.read_text():
        raise SystemExit('Denied diagnostic probe did not stop cache work')
print('Passed: axiom/source rejection with PYTHONOPTIMIZE=0/1; warm cache skips network; failed or incomplete cache fails closed.')
