#!/usr/bin/env python3
"""Replay archived learner proofs, keeping original and later-library results distinct."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_archive(case_id, case, freeze, round_id):
    """Use tracked records, not the original machine's ignored working logs."""
    directory = ROOT / 'Usability/records'
    if round_id == 'round2':
        directory /= 'round2'
    path = directory / (case_id + '.json')
    record = json.loads(path.read_text())
    assert record['case'] == case_id
    assert record['library_commit'] == freeze['library_commit']
    assert record['problem_sha256'] == freeze['problems_sha256'][case['problem']]
    assert record['final_source'] == case['source']
    assert sha((ROOT / case['source']).read_bytes()) == record['final_source_sha256']
    for attempt in record['attempts']:
        assert attempt['case'] == case_id
        assert attempt['library_commit'] == freeze['library_commit']
        assert attempt['problem_sha256'] == record['problem_sha256']
        assert sha(attempt['source_text'].encode()) == attempt['source_sha256']
        assert sha(attempt['compiler_output'].encode()) == attempt['log_sha256']
    return record, path


def main():
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT,
                        help='experiment directory to replay (allows the current reviewer on a frozen checkout)')
    parser.add_argument('--round', choices=['round1', 'round2'], default='round1')
    parser.add_argument('--allow-library-drift', action='store_true',
                        help='explicit regression on a later library, never a fresh first-round result')
    parser.add_argument('--verify-archives-only', action='store_true',
                        help='check all archived source/output hashes without invoking Lean')
    parser.add_argument('--record', action='store_true',
                        help='intentionally refresh the compact tracked review; default writes only results/')
    args = parser.parse_args()
    ROOT = args.root.resolve()
    freeze_name = 'freeze.json' if args.round == 'round1' else 'freeze-round2.json'
    freeze = json.loads((ROOT / 'Usability' / freeze_name).read_text())
    changed = [p for p, d in freeze['library_sources_sha256'].items()
               if not (ROOT / p).exists() or sha((ROOT / p).read_bytes()) != d]
    actual_lean = [ROOT / 'MeasurementAPI.lean', *sorted((ROOT / 'MeasurementAPI').glob('*.lean'))]
    changed += ['added:' + str(p.relative_to(ROOT)) for p in actual_lean
                if str(p.relative_to(ROOT)) not in freeze['library_sources_sha256']]
    if changed and not args.allow_library_drift:
        raise RuntimeError('Frozen library differs: ' + ', '.join(changed))
    for problem, expected in freeze['problems_sha256'].items():
        if sha((ROOT / 'Usability/problems' / (problem + '.md')).read_bytes()) != expected:
            raise RuntimeError('Frozen problem differs: ' + problem)
    archives = {case_id: read_archive(case_id, case, freeze, args.round)
                for case_id, case in freeze['cases'].items()}
    if args.verify_archives_only:
        count = sum(len(record['attempts']) for record, _ in archives.values())
        print(f'{args.round}: {len(archives)} archives, {count} source/output pairs verified; no Lean run.')
        return
    env = os.environ.copy()
    env['PATH'] = str(ROOT / 'toolchain/lean-4.35.0-linux/bin') + os.pathsep + env['PATH']
    env['XDG_CACHE_HOME'] = str(ROOT / '.cache')
    env['LAKE_CACHE_DIR'] = str(ROOT / '.cache/lake')
    env['MATHLIB_CACHE_DIR'] = str(ROOT / '.cache/mathlib')
    env['LEAN_NUM_THREADS'] = '1'
    output_dir = ROOT / 'results/usability-parent' / args.round
    output_dir.mkdir(parents=True, exist_ok=True)
    kind = ('later_library_regression' if changed else
            ('frozen_round1_parent_review' if args.round == 'round1' else
             'same_task_iteration_round2_parent_review'))
    report = dict(kind=kind, round=args.round,
                  started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  library_commit=freeze['library_commit'], changed_library_files=changed,
                  reviewer_sha256=sha(Path(__file__).read_bytes()),
                  observed_library_sha256={str(p.relative_to(ROOT)): sha(p.read_bytes())
                                            for p in actual_lean}, cases={})
    for case_id, case in freeze['cases'].items():
        source = ROOT / case['source']
        final = source.read_text()
        names = re.findall(r'^(?:@\[[^\]]+\]\s+)?(?:def|theorem|abbrev)\s+(\w+)', final, re.MULTILINE)
        names = [case_id + '.' + name for name in names]
        archive, archive_path = archives[case_id]
        first = next(m for m in archive['attempts']
                     if m['mode'] == 'compile' and m['lean_exit_code'] == 0)
        first_text = first['source_text']
        variants = {'first_compiling_source': first_text, 'final_source': final}
        results = {}
        for variant, body in variants.items():
            path = output_dir / (case_id + '_' + variant + '.lean')
            appended = '\nset_option pp.fullNames true\n'
            appended += '\n'.join('#check @' + n for n in names) + '\n'
            appended += '\n'.join('#print axioms ' + n for n in names) + '\n'
            path.write_text(body + appended)
            started = time.monotonic()
            proc = subprocess.run(['lake', 'env', 'lean', str(path.relative_to(ROOT))],
                                  cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, text=True, timeout=120)
            log = output_dir / (path.stem + '.log')
            log.write_text(proc.stdout)
            axioms = {n: [x.strip() for x in b.split(',') if x.strip()]
                      for n, b in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",
                                            proc.stdout, re.DOTALL)}
            for n in re.findall(r"'([^']+)' does not depend on any axioms", proc.stdout):
                axioms[n] = []
            passed = proc.returncode == 0 and set(names) <= set(axioms)
            passed = passed and all(set(axioms[n]) <= STANDARD for n in names)
            results[variant] = dict(source_sha256=sha(body.encode()), lean_exit_code=proc.returncode,
                                    passed=passed, axioms=axioms,
                                    seconds=round(time.monotonic() - started, 3),
                                    log=str(log.relative_to(ROOT)), log_sha256=sha(proc.stdout.encode()))
            print(case_id, variant, 'passed' if passed else 'FAILED', flush=True)
            if not passed:
                print(proc.stdout[-10000:])
                raise RuntimeError(case_id + ' failed parent review')
        report['cases'][case_id] = dict(declarations=names, variants=results,
                                       archive=str(archive_path.relative_to(ROOT)),
                                       archive_sha256=sha(archive_path.read_bytes()),
                                       first_compiling_attempt=first['source_snapshot'])
    filename = ('regression-review.json' if changed else
                ('parent-review.json' if args.round == 'round1' else 'round2-parent-review.json'))
    report_dir = ROOT / 'Usability' if args.record else output_dir
    (report_dir / filename).write_text(json.dumps(report, indent=2) + '\n')
    print('All learner source variants checked with fully qualified printed names.')


if __name__ == '__main__':
    main()
