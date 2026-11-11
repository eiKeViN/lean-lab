"""Launch the registered 36M pair against an already prepared and tested runtime."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from prepare_rooms import HERE, PACKET, SHEAF, SHEAF_SETTINGS

ROOM_NOTE = """
Long builds can be submitted with start_shell_job and polled later with
shell_job_status. Each run has its own compile lane for top-level Lean/Lake
commands. The direct shell has a 120 s maximum and a 30 s default. Long
jobs allow 600 s. The supervisor stops the run at 36,000,000 aggregate
weighted units or one hour. No other run can see your workspace.
"""


def run(base, study):
    if subprocess.check_output(['git', '-C', str(base/'sheaf-upstream'), 'rev-parse', 'HEAD'], text=True).strip() != SHEAF:
        raise ValueError('Unexpected SHEAF revision')
    study.mkdir(exist_ok=False)
    rows = []
    for name, arm, cpus in [('birch', 'SHEAF', '0,1'), ('larch', 'free', '2,3')]:
        room = study/'rooms'/name
        room.mkdir(parents=True)
        if arm == 'SHEAF':
            subprocess.run(['git', '-C', str(base/'sheaf-upstream'), 'checkout-index', '-a', '--prefix', str(room)+'/'], check=True)
        for file in PACKET.iterdir():
            shutil.copy2(file, room/file.name)
        with (room/'ENVIRONMENT.md').open('a') as f:
            f.write(ROOM_NOTE)
        project = room/'project'
        shutil.copytree(HERE/'lean-project', project/'lean', ignore=shutil.ignore_patterns('.lake', '__pycache__'))
        if arm == 'SHEAF':
            for file in ('source.md', 'acceptance.md', 'ENVIRONMENT.md'):
                shutil.copy2(room/file, project/file)
        prompt = (room/'task.txt').read_text() + ('\n'+SHEAF_SETTINGS if arm == 'SHEAF' else '')
        (study/(name+'.prompt')).write_text(prompt)
        (study/(name+'.lock')).touch()
        rows.append(dict(id=name, arm=arm, cpus=cpus, prompt_sha256=hashlib.sha256(prompt.encode()).hexdigest()))
    (study/'runs.json').write_text(json.dumps(rows, indent=2))
    children = []
    try:
        for row in rows:
            name = row['id']
            cmd = ['taskset','-c',row['cpus'],sys.executable,str(HERE/'runner.py'),
                   '--extended','--room',str(study/'rooms'/name),'--evidence',str(study/'evidence'/name),
                   '--prompt',str(study/(name+'.prompt')),'--seconds','3600','--units','36000000']
            env = dict(os.environ, HGP_RUNTIME_ROOT=str(base), HGP_EXTENDED_ROOM='1',
                       HGP_LEAN_LOCK=str(study/(name+'.lock')))
            with (study/(name+'.log')).open('x') as out:
                row['start'] = time.time()
                children.append(subprocess.Popen(cmd,env=env,stdout=out,stderr=subprocess.STDOUT))
        (study/'start.json').write_text(json.dumps(rows,indent=2))
        statuses = {row['id']: p.wait() for row,p in zip(rows,children)}
        (study/'exit.json').write_text(json.dumps(statuses,indent=2))
        return int(any(statuses.values()))
    finally:
        for child in children:
            if child.poll() is None:
                child.terminate()


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('base',type=Path)
    p.add_argument('study',type=Path)
    args = p.parse_args()
    raise SystemExit(run(args.base.resolve(), args.study.resolve()))
