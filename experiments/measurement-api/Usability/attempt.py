#!/usr/bin/env python3
"""Log isolated learner Lean attempts against frozen resources; no solution logic."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True)
    parser.add_argument('--audit', action='store_true')
    parser.add_argument('--decl', action='append', default=[])
    args = parser.parse_args()
    freeze = json.loads((ROOT / 'Usability/freeze.json').read_text())
    case = (dict(problem='_harness', resources='extended',
                 source='results/usability-harness/Input.lean') if args.case == '_harness'
            else freeze['cases'][args.case])
    for relative, expected in freeze['library_sources_sha256'].items():
        if digest((ROOT / relative).read_bytes()) != expected:
            raise RuntimeError('Frozen library source changed: ' + relative)
    source = ROOT / case['source']
    text = source.read_text()
    imports = []
    for line in text.splitlines():
        match = re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)', line)
        if match:
            imports.extend(match.group(1).split('--')[0].split())
    allowed = {'Mathlib', 'QuantumInfo', 'PMFBridgeDraft', 'Lean', 'Batteries'}
    if case['resources'] == 'extended':
        allowed.add('MeasurementAPI')
    denied = [name for name in imports if name.split('.')[0] not in allowed]
    if denied:
        raise RuntimeError('Imports outside assigned resources: ' + ', '.join(denied))
    if args.audit and not args.decl:
        parser.error('audit requires at least one --decl')
    if any(not re.fullmatch(r"[\w.']+", name) for name in args.decl):
        parser.error('declarations must be qualified Lean names')
    directory = ROOT / 'results/usability' / args.case
    directory.mkdir(parents=True, exist_ok=True)
    existing = sorted(directory.glob('Attempt*.json'))
    number = len(existing) + 1
    stem = f'Attempt{number:03d}'
    original = directory / (stem + '.source.lean.txt')
    original.write_text(text)
    executable = text
    if args.audit:
        executable += '\n' + '\n'.join('#check @' + n for n in args.decl) + '\n'
        executable += '\n'.join('#print axioms ' + n for n in args.decl) + '\n'
    compiled = directory / (stem + '.lean')
    compiled.write_text(executable)
    env = os.environ.copy()
    env['PATH'] = str(ROOT / 'toolchain/lean-4.35.0-linux/bin') + os.pathsep + env['PATH']
    env['XDG_CACHE_HOME'] = str(ROOT / '.cache')
    env['LAKE_CACHE_DIR'] = str(ROOT / '.cache/lake')
    env['MATHLIB_CACHE_DIR'] = str(ROOT / '.cache/mathlib')
    env['LEAN_NUM_THREADS'] = '1'
    command = ['lake', 'env', 'lean', str(compiled.relative_to(ROOT)),
               '-o', str((directory / (stem + '.olean')).relative_to(ROOT))]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    monotonic = time.monotonic()
    timed_out = False
    try:
        proc = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True, timeout=120)
        output, exit_code = proc.stdout, proc.returncode
    except subprocess.TimeoutExpired as error:
        value = error.stdout or b''
        output = value.decode(errors='replace') if isinstance(value, bytes) else value
        output += '\n[recorder: Lean wall timeout after 120 seconds]\n'
        exit_code, timed_out = None, True
    status = 'timeout' if timed_out else ('compiled' if exit_code == 0 else 'failed')
    axioms = {name: [x.strip() for x in body.split(',') if x.strip()]
              for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",
                                          output, re.DOTALL)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        axioms[name] = []
    if args.audit and status == 'compiled':
        status = ('verified' if set(args.decl) <= set(axioms) and
                  all(set(axioms[n]) <= STANDARD for n in args.decl) else 'audit_rejected')
    if 'declaration uses `sorry`' in output or 'declaration uses sorry' in output:
        status = 'sorry_rejected'
    log = directory / (stem + '.log')
    log.write_text(output)
    metadata = dict(case=args.case, mode='audit' if args.audit else 'compile',
                    started_utc=started, elapsed_seconds=round(time.monotonic() - monotonic, 3),
                    timeout_seconds=120, lean_threads=1, command=command,
                    lean_exit_code=exit_code, status=status,
                    source=case['source'], source_sha256=digest(text.encode()),
                    source_snapshot=str(original.relative_to(ROOT)),
                    log=str(log.relative_to(ROOT)), log_sha256=digest(output.encode()),
                    declarations=args.decl, axioms=axioms, imports=imports,
                    options=re.findall(r'^.*set_option.*$', text, re.MULTILINE),
                    library_commit=freeze['library_commit'],
                    observed_git_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                                              cwd=ROOT, text=True).strip(),
                    is_exercise=args.case != '_harness',
                    problem_sha256=freeze['problems_sha256'].get(case['problem'], 'HARNESS_ONLY'))
    (directory / (stem + '.json')).write_text(json.dumps(metadata, indent=2, ensure_ascii=False) + '\n')
    print(f'{args.case} {stem}: {status}; Lean exit={exit_code}; '
          f'{metadata["elapsed_seconds"]} seconds; log={metadata["log"]}')
    print('\n'.join(output.splitlines()[-70:]))
    return 0 if status in {'compiled', 'verified'} else (124 if timed_out else (exit_code or 1))


if __name__ == '__main__':
    raise SystemExit(main())
