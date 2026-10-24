"""Three-file source transport and one explicitly authorized equation representation."""
from pathlib import Path
import gzip,hashlib,json,subprocess,tempfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='bc7cc147e9742f8f6c77a53785813dbdd6960311'
PATHS=('ForMathlib/Combinatorics/MomentGraph/Sheaf/Basic.lean','ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Defs.lean','ForMathlib/Combinatorics/MomentGraph/GradedSheaf/AttachBottom.lean')
OWNERS=tuple(p[:-5].replace('/','.') for p in PATHS)
PLAN_SHA='940ff903f46a0a7061d1f094d6f5b9f4cd4af16f054e68912b3d07dcc8ff18e5'
COMPAT_SHA='c3b90ce64206d1f621978b0c3c3b68314ed24ca25983e76960ea575919922454';WITNESS_SHA='c625c7423c89cba3c5342290ae0edc7bb39a9c4441a6db3e516a4b974a6f0c8e'
def sha(b):return hashlib.sha256(b).hexdigest()
def baseline(path):return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def plan():
    raw=(HERE/'attach-module.json').read_bytes()
    if sha(raw)!=PLAN_SHA:raise RuntimeError('Changed three-file source plan')
    d=json.loads(raw)
    if d['base_commit']!=BASE or set(d['files'])!=set(PATHS):raise RuntimeError('Changed AttachBottom scope')
    return d

def convert(path,data):
    item=plan()['files'][path]
    if sha(data)!=item['before_sha256']:raise RuntimeError('Changed attach-module input: '+path)
    s=data.decode()
    for e in sorted(item['edits'],key=lambda e:e['start'],reverse=True):
        i=e['start']
        if s[i:i+len(e['old'])]!=e['old']:raise RuntimeError('Attach-module edit mismatch')
        s=s[:i]+e['new']+s[i+len(e['old']):]
    if sha(s.encode())!=item['after_sha256']:raise RuntimeError('Changed attach-module output')
    return s.encode()

def legacy_source(path,data):
    if path not in PATHS:return data
    before=baseline(path)
    if data==before:return data
    if data!=convert(path,before):raise RuntimeError('Unrecorded attach-module body/header change: '+path)
    return before

def overlay(files):
    for p in PATHS:files[p]=convert(p,files[p])
    return files

def policy():
    d=plan()
    for p in PATHS:
        if sha(baseline(p))!=d['files'][p]['before_sha256']:raise RuntimeError('Changed AttachBottom baseline')
        convert(p,baseline(p))
    compatibility()
    return d

def compatibility():
    raw=(HERE/'stalk-equation-compat.json').read_bytes()
    if sha(raw)!=COMPAT_SHA:raise RuntimeError('Changed single-equation authorization')
    c=json.loads(raw)
    if sha((HERE/'stalk-equation-old.json').read_bytes())!=c['old_dag_sha256']:raise RuntimeError('Changed historical equation/proofs')
    if sha((HERE/c['witness']).read_bytes())!=WITNESS_SHA:raise RuntimeError('Changed ordinary compatibility witness')
    if (HERE/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Changed equation toolchain')
    lock=json.loads((HERE/'lake-manifest.json').read_text())
    if next(x['rev'] for x in lock['packages'] if x['name']=='mathlib')!=c['mathlib_commit']:raise RuntimeError('Changed equation Mathlib pin')
    return c

def accept_change(raw):
    """Keep raw failures intact; accept exactly this version-bound pair after live Lean checks."""
    c=compatibility();changes=raw.get('changed',[])
    if raw.get('missing') or raw.get('added') or len(changes)!=1:raise RuntimeError('Non-authorized API difference: '+json.dumps(raw))
    x=changes[0]
    if x['name']!=c['name'] or x['field']!='type':raise RuntimeError('Wrong accepted equation/field')
    for side,key in [('old','old_type'),('new','new_type')]:
        if x[side]['type']!=c[key] or x[side]['levels']!=c['levels'] or x[side]['kind']!=c['kind']:
            raise RuntimeError('Unbound equation representation: '+json.dumps(x))
    if x['new']['module']!=c['current_owner']:raise RuntimeError('Equation owner changed')
    v=subprocess.check_output(['lean','--version'],cwd=HERE,text=True)
    if c['lean_commit'] not in v:raise RuntimeError('Wrong compiler for equation witness')
    subprocess.run(['lake','env','lean',c['witness']],cwd=HERE,check=True)
    return {'name':c['name'],'old_type':c['old_type'],'new_type':c['new_type'],'witness':c['witness'],'policy_sha256':COMPAT_SHA,'raw_difference_retained':True}

def compare_full(path):
    from compare_types import load,compare
    frozen=ROOT/'reports/evidence/imports-safe-region/final-stages/migrated-types.tsv.gz'
    data=frozen.read_bytes()
    original=subprocess.check_output(['git','show',BASE+':'+str(frozen.relative_to(ROOT))],cwd=ROOT)
    if data!=original:raise RuntimeError('Changed accepted 3947-record starting export')
    with tempfile.NamedTemporaryFile() as f:
        f.write(gzip.decompress(data));f.flush();old=load(f.name,3947)
    from module_all import load_prior_view
    actual=load_prior_view(path);raw=compare(old,actual)
    if raw['relocated']:raise RuntimeError('Current producer/realizer owner changed')
    from module_final import accept_known
    remaining,batch_accepted=accept_known(raw)
    accepted=accept_change(remaining)
    return {**__import__('module_all').contract_summary(),'raw':raw,'accepted_representation_changes':[accepted]+batch_accepted,'passed':True}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--compare-full');a=p.parse_args();policy()
    if a.compare_full:print(json.dumps(compare_full(a.compare_full),indent=2))

# Reuse the inherited finite proof-alias rules; no new broad normalizer.
def generated_checks():
    import module_rollout
    s=module_rollout.modern_exporter()
    prefix,body=s.split('run_elab do\n  let env ← getEnv',1)
    a=prefix.index('private def rolloutOwners :');b=prefix.index('\nprivate def rolloutOriginalKind',a)
    prefix=prefix[:a]+'private def rolloutOwners : Array Name := #['+', '.join('`'+n for n in OWNERS)+']'+prefix[b:]
    a=prefix.index('module\n');b=prefix.index('import Lean\n',a)
    prefix=prefix[:a]+'module\nimport '+OWNERS[-1]+'\n'+prefix[b:]
    body=body.replace('"module-rollout-types.json"','"attach-module-types.json"').replace('1196','93')
    return {'ModernAttachTypes.lean':prefix+'run_elab do\n  let env ← getEnv'+body}
