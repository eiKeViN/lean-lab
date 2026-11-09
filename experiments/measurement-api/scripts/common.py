from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def environment():
    env = os.environ.copy()
    env['PATH'] = str(ROOT / 'toolchain/lean-4.35.0-linux/bin') + os.pathsep + env['PATH']
    env['XDG_CACHE_HOME'] = str(ROOT / '.cache')
    env['LAKE_CACHE_DIR'] = str(ROOT / '.cache/lake')
    env['MATHLIB_CACHE_DIR'] = str(ROOT / '.cache/mathlib')
    env['LEAN_NUM_THREADS'] = '2'
    env['GIT_LFS_SKIP_SMUDGE'] = '1'
    return env


def logged(args, label):
    results = ROOT / 'results'
    results.mkdir(exist_ok=True)
    started = time.monotonic()
    path = results / (label + '.log')
    with path.open('w') as log:
        proc = subprocess.run(args, cwd=ROOT, env=environment(), stdout=log,
                              stderr=subprocess.STDOUT)
    result = dict(command=args, exit_code=proc.returncode,
                  seconds=round(time.monotonic() - started, 3),
                  log=str(path.relative_to(ROOT)), sha256=sha(path))
    (results / (label + '.json')).write_text(json.dumps(result, indent=2) + '\n')
    print(label, 'exit', proc.returncode, 'log:', result['log'], flush=True)
    if proc.returncode:
        print('\n'.join(path.read_text().splitlines()[-18:]))
        raise RuntimeError(f'{label} failed; preserve {path}')
    return result


def source_identity():
    pins = json.loads((ROOT / 'provenance/upstream.json').read_text())
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    package_heads = {}
    for package in manifest['packages']:
        if package['name'] == 'mathlib' and package['rev'] != pins['mathlib']:
            raise RuntimeError('Mathlib manifest differs from the reviewed pin')
        path = ROOT / '.lake/packages' / package['name']
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path,
                                       text=True).strip()
        if head != package['rev']:
            raise RuntimeError(f'Package identity differs: {package["name"]}')
        if subprocess.run(['git', 'diff', '--quiet', 'HEAD'], cwd=path).returncode:
            raise RuntimeError(f'Local dependency edits need review: {package["name"]}')
        package_heads[package['name']] = head
    physlib = ROOT / 'vendor/physlib'
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=physlib,
                                   text=True).strip()
    if head != pins['physlib']:
        raise RuntimeError('Physlib checkout differs from the reviewed pin')
    files = json.loads((ROOT / 'provenance/physlib-sources.json').read_text())
    for path, digest in files.items():
        if sha(physlib / path) != digest:
            raise RuntimeError(f'Physlib source changed: {path}')
    actual = {str(p.relative_to(physlib)) for p in (physlib / 'QuantumInfo').rglob('*.lean')}
    if (physlib / 'QuantumInfo.lean').exists():
        actual.add('QuantumInfo.lean')
    if actual != set(files):
        raise RuntimeError('Unrecorded or missing Physlib QuantumInfo source')
    if sha(ROOT / pins['bridge_source']) != pins['bridge_sha256']:
        raise RuntimeError('Shared PMF bridge source changed; review adaptation before proceeding')
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:' + pins['lean']:
        raise RuntimeError('Lean toolchain declaration differs from the reviewed pin')
    return dict(physlib=head, physlib_source_files=len(files), packages=package_heads,
                shared_bridge_sha256=pins['bridge_sha256'])
