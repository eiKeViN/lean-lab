#!/usr/bin/env python3
"""Pinned small reproducers with expected failure controls and per-command evidence."""
import hashlib, json, os, resource, shutil, subprocess, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SRC=Path(__file__).resolve().parent
LEAN=ROOT/'.cache/lean-4.34.1-linux/bin/lean'
out=Path(sys.argv[1]).resolve()
if out.exists():raise SystemExit('Use a fresh output directory')
out.mkdir(parents=True)
version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
assert '5045d0056413266e57c625dcd7c365b10e377c52' in version
inputs={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in SRC.rglob('*') if p.is_file()}
(out/'inputs.json').write_text(json.dumps({'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'version':version,'inputs':inputs},indent=2)+'\n')
records=[]
def run(label,source,expected=0,needle=None,compile=False,folder=None):
    target=out/(folder or 'single');target.mkdir(exist_ok=True)
    dest=target/source.name;shutil.copyfile(source,dest)
    cmd=[str(LEAN),'-R',str(target)]
    if compile:cmd+=['-o',str(dest.with_suffix('.olean'))]
    cmd+=[str(dest)]
    env=os.environ.copy();env['LEAN_PATH']=str(target);env['LEAN_NUM_THREADS']='4'
    start=time.monotonic();p=subprocess.run(cmd,env=env,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (out/(label+'.log')).write_text(p.stdout)
    record={'label':label,'command':cmd,'environment':{'LEAN_PATH':str(target),'LEAN_NUM_THREADS':'4'},'source_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'exit_code':p.returncode,'expected_exit':expected,'wall_seconds':time.monotonic()-start,'max_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'expected_diagnostic':needle,'pass':p.returncode==expected and (needle is None or needle in p.stdout)}
    records.append(record);(out/'runs.json').write_text(json.dumps(records,indent=2)+'\n')
    if not record['pass']:raise SystemExit('Unexpected result: '+label+'\n'+p.stdout)
run('private-exposed',SRC/'PrivateBoundary.lean',1,'would need to be public')
for name in ['InferenceBoundary','InferenceExact']:
    run(name,SRC/(name+'.lean'),1,'tactic execution is stuck, goal contains metavariables')
for name in ['InferenceExplicit','InferenceUnexposed','InferenceTerm','InferencePublicProof']:
    run(name,SRC/(name+'.lean'))
for name in ['Unexposed','Inline','PublicHelper']:
    run(name,SRC/'private'/(name+'.lean'),compile=True,folder='private')
run('UnexposedConsumer',SRC/'private/UnexposedConsumer.lean',1,'definition is not exposed',folder='private')
for name in ['InlineConsumer','PublicHelperConsumer']:
    run(name,SRC/'private'/(name+'.lean'),folder='private')
for name in ['Common','Legacy','Modern','Realizer']:
    run(name,SRC/'generated'/(name+'.lean'),compile=True,folder='generated')
run('Audit',SRC/'generated/Audit.lean',needle='owner=some (Realizer)',folder='generated')
for name in ['LegacyMatcher','ModernMatcher']:
    run(name,SRC/'matcher'/(name+'.lean'),compile=True,folder='matcher')
run('LegacyConsumer',SRC/'matcher/LegacyConsumer.lean',folder='matcher')
run('ModernConsumer',SRC/'matcher/Consumer.lean',1,'Unknown constant `Boundary.ext.match_1_1`',folder='matcher')
run('ImplementationConsumer',SRC/'matcher/ImplementationConsumer.lean',folder='matcher')
print(json.dumps({'passed':len(records),'total_wall_seconds':sum(r['wall_seconds'] for r in records)},indent=2))
