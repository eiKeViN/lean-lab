"""Bounded header/exposure-only transport for three graph/sheaf producers."""
from pathlib import Path
import gzip,hashlib,json,subprocess,tempfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='7e28e636991b2205d14199377f33bd025b348b2d'
PATHS=tuple('ForMathlib/Combinatorics/MomentGraph/'+s+'.lean' for s in ('Bruhat/Basic','Sheaf/Duality','GradedSheaf/Reindex'))
OWNERS=tuple(s[:-5].replace('/','.') for s in PATHS)
PLAN_SHA='ef2537574fc266985e13d75e95c65eaa3f261d07a8c53dda8fa5889ddc49ae86'
TYPES_SHA='0279ca1caa3cb055c6859a691ea942f792ff782833523f5c5285c56b396e4489'
def sha(b):return hashlib.sha256(b).hexdigest()
def baseline(p):return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+p],cwd=ROOT)
def plan():
    raw=(HERE/'module-next.json').read_bytes()
    if sha(raw)!=PLAN_SHA:raise RuntimeError('Changed next-module scope or source transport')
    d=json.loads(raw)
    if d['base_commit']!=BASE or set(d['files'])!=set(PATHS):raise RuntimeError('Changed three-module scope')
    return d

def convert(path,data):
    item=plan()['files'][path]
    if sha(data)!=item['before_sha256']:raise RuntimeError('Changed next-module input: '+path)
    s=data.decode()
    for e in sorted(item['edits'],key=lambda e:e['start'],reverse=True):
        i=e['start']
        if s[i:i+len(e['old'])]!=e['old']:raise RuntimeError('Next-module edit mismatch')
        s=s[:i]+e['new']+s[i+len(e['old']):]
    if sha(s.encode())!=item['after_sha256']:raise RuntimeError('Changed next-module output')
    return s.encode()

def legacy_source(path,data):
    if path not in PATHS:return data
    old=baseline(path)
    if data==old:return old
    if data!=convert(path,old):raise RuntimeError('Unapproved next-module header/body edit: '+path)
    return old

def overlay(files):
    for p in PATHS:files[p]=convert(p,files[p])
    return files

def policy():
    for p in PATHS:convert(p,baseline(p))
    expected_types()

def expected_types():
    raw=(HERE/'module-next-types.json').read_bytes()
    if sha(raw)!=TYPES_SHA:raise RuntimeError('Changed next-module public expectation')
    d=json.loads(raw)
    if len(d)!=61 or {v['module'] for v in d.values()}!=set(OWNERS):raise RuntimeError('Changed public scope')
    return d

def compare_public(path):
    from compare_types import load,compare
    r=compare(expected_types(),load(path,61))
    if not r['passed'] or r['relocated']:raise RuntimeError('Next-module ordinary public types changed: '+json.dumps(r))
    return r

def compare_full(path):
    from compare_types import load,compare
    rel='reports/evidence/attach-module/stages/migrated-types.tsv.gz'
    raw=(ROOT/rel).read_bytes()
    if raw!=subprocess.check_output(['git','show',BASE+':'+rel],cwd=ROOT):raise RuntimeError('Changed accepted main export')
    with tempfile.NamedTemporaryFile() as f:
        f.write(gzip.decompress(raw));f.flush();old=load(f.name,3947)
    r=compare(old,load(path,3947))
    if not r['passed'] or r['relocated']:raise RuntimeError('New unaccepted complete-record difference: '+json.dumps(r))
    return r

def generated_checks():
    import attach_module
    prefix,body=attach_module.generated_checks()['ModernAttachTypes.lean'].split('run_elab do\n  let env ← getEnv',1)
    a=prefix.index('private def rolloutOwners :');b=prefix.index('\nprivate def rolloutOriginalKind',a)
    prefix=prefix[:a]+'private def rolloutOwners : Array Name := #['+', '.join('`'+n for n in OWNERS)+']'+prefix[b:]
    a=prefix.index('module\n');b=prefix.index('import Lean\n',a)
    prefix=prefix[:a]+'module\n'+''.join('import '+n+'\n' for n in OWNERS)+prefix[b:]
    body=body.replace('attach-module-types.json','module-next-types.json').replace('93','61')
    return {'ModernNextTypes.lean':prefix+'run_elab do\n  let env ← getEnv'+body}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--compare-full');p.add_argument('--compare-public');a=p.parse_args();policy()
    if a.compare_full:print(json.dumps(compare_full(a.compare_full),indent=2))
    if a.compare_public:print(json.dumps(compare_public(a.compare_public),indent=2))
