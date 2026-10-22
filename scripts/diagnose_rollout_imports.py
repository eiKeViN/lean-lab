#!/usr/bin/env python3
"""Scope shake's no-build preflight to the ready focused modules; never force/fix."""
from pathlib import Path
import subprocess,sys,json
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'experiments/kl-for-mathlib'
sys.path.insert(0,str(P))
from module_rollout import narrow_plan
modules=[path[:-5].replace('/','.') for path in narrow_plan()['files']]
config=P/'lakefile.toml';before=config.read_bytes()
try:
 text=before.decode();old='defaultTargets = ["ForMathlib", "OAI"]'
 if text.count(old)!=1:raise RuntimeError('Unexpected default target configuration')
 config.write_text(text.replace(old,'defaultTargets = '+json.dumps(modules)))
 subprocess.run(['lake','--no-build','build',*modules],cwd=P,check=True)
 # Exit 1 can mean proposed changes. Raw status/output remain explicit.
 result=subprocess.run(['lake','shake',*modules],cwd=P)
 print('Scoped read-only shake status:',result.returncode)
 if result.returncode not in (0,1):raise RuntimeError('Unexpected shake diagnostic failure')
finally:
 config.write_bytes(before)
assert config.read_bytes()==before
