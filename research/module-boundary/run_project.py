#!/usr/bin/env python3
"""Bounded project replay. Requires setup.sh official cache; never builds Mathlib."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; SRC=Path(__file__).resolve().parent
PROJECT=ROOT/'experiments/kl-for-mathlib'; LEAN=ROOT/'.cache/lean-4.34.1-linux/bin/lean'; LAKE=LEAN.with_name('lake')
out=Path(sys.argv[1]).resolve()
if out.exists():raise SystemExit('Use a fresh output directory')
out.mkdir(parents=True)
records=[]
def run(label,cmd,expected=0,env=None,files=(),cwd=PROJECT):
    log=out/(label+'.log')
    identity={'command':list(map(str,cmd)), 'cwd':str(cwd),'environment':{k:(env or os.environ).get(k) for k in ['LEAN_PATH','STALK_JSON_OUT','OLD_STALK_JSON','NEW_STALK_JSON','LEAN_NUM_THREADS']},'files':{str(p):hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in files}}
    (out/(label+'.inputs.json')).write_text(json.dumps(identity,indent=2)+'\n')
    status=subprocess.call([sys.executable,str(ROOT/'scripts/measure.py'),str(log),*map(str,cmd)],cwd=cwd,env=env)
    metrics=json.loads(log.with_suffix('.json').read_text());metrics['expected_exit']=expected;metrics['pass']=status==expected;records.append(metrics)
    (out/'runs.json').write_text(json.dumps(records,indent=2)+'\n')
    if status!=expected:raise SystemExit('Unexpected result: '+label)
# Refuse source fallback before even focused local builds.
run('mathlib-ready',[LAKE,'--no-build','build','Mathlib'])
run('focused-dependencies',[LAKE,'build','ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs'])
path=subprocess.check_output([str(LAKE),'env','printenv','LEAN_PATH'],cwd=PROJECT,text=True).strip()
def environment(*prefixes,**extra):
    e=os.environ.copy();e.update(LEAN_PATH=os.pathsep.join([*map(str,prefixes),path]),LEAN_NUM_THREADS='4',**extra);return e
for stem,expected in [('AttachGeneric',1),('AttachGenericExplicit',0),('AttachGenericUnexposed',0),('AttachComparison',0)]:
    file=SRC/(stem+'.lean');run(stem,[LEAN,file],expected,environment(),[file])
shadow=out/'shadow'
run('prepare-shadow',[sys.executable,SRC/'prepare_shadow.py',shadow],cwd=ROOT)
codec=out/'codec';codec.mkdir()
run('codec',[LEAN,'-R',SRC,'-o',codec/'StalkCodec.olean',SRC/'StalkCodec.lean'],files=[SRC/'StalkCodec.lean'],cwd=ROOT)
for rel in ['ForMathlib/Combinatorics/MomentGraph/Sheaf/Basic.lean','ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Defs.lean']:
    f=shadow/rel;run('shadow-'+f.stem,[LEAN,'-R',shadow,'-o',f.with_suffix('.olean'),f],env=environment(shadow),files=[f])
f=SRC/'AttachBottomExplicit.lean';run('attach-bottom',[LEAN,f],env=environment(shadow),files=[f])
for label,prefixes in [('old',(codec,)),('new',(codec,shadow))]:
    f=SRC/'CaptureStalkJson.lean';run('capture-'+label,[LEAN,f],env=environment(*prefixes,STALK_JSON_OUT=str(out/(label+'.json'))),files=[f,SRC/'StalkCodec.lean'])
f=SRC/'CheckStalkJson.lean';run('check-stalk',[LEAN,f],env=environment(codec,shadow,OLD_STALK_JSON=str(out/'old.json'),NEW_STALK_JSON=str(out/'new.json')),files=[f,out/'old.json',out/'new.json'])
print('All bounded project controls passed.')
