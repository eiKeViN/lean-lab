"""Exact 25-module transport and finite evidence-bound representation acceptance."""
from pathlib import Path
import gzip,hashlib,json,subprocess,tempfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='0917d25afb52e46cae4233d3056020ed6f881fa3'
PATHS=('ForMathlib/Algebra/Algebra/ReflectionFrobenius/Basic.lean', 'ForMathlib/Algebra/Module/Localization/FiniteCharacters.lean', 'ForMathlib/Combinatorics/MomentGraph/OrderedGraph/VertexDeletion.lean', 'ForMathlib/GroupTheory/Coxeter/Bruhat/DiamondClosure.lean', 'ForMathlib/GroupTheory/Coxeter/Bruhat/Diamonds.lean', 'ForMathlib/GroupTheory/Coxeter/Dihedral/Diamonds.lean', 'ForMathlib/GroupTheory/Coxeter/Dihedral/IntervalTransport.lean', 'ForMathlib/GroupTheory/Coxeter/Dihedral/PlaneSystem.lean', 'ForMathlib/GroupTheory/Coxeter/Dihedral/SignedWords.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/Basic.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/DihedralOrder.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/LaterCount.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/Order.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/PlaneBasis.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/PlaneLength.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/PlaneSubgroup.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/PlaneTransport.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/RatioOrder.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/ReflectionLabels.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/Splines.lean', 'ForMathlib/LinearAlgebra/Avoidance.lean', 'ForMathlib/RepresentationTheory/Hecke/DyerPaths/Adapted.lean', 'ForMathlib/RepresentationTheory/Hecke/DyerPaths/PlaneCoordinates.lean', 'OAI/RepresentationTheory/KazhdanLusztig/Sheaves.lean', 'OAI/RepresentationTheory/KazhdanLusztig/Tits.lean')
OWNERS=tuple(s[:-5].replace('/','.') for s in PATHS)
PLAN_SHA='ecab6ec6b61ae651ea6e83ff92da4d513e83595403255fa145ab370e0af21b40'
TYPES_SHA='c2bd9473688a07d0885e05c62947eab0c8d30f97a998670d1f82394e20891e28'
def sha(b):return hashlib.sha256(b).hexdigest()
def baseline(p):return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+p],cwd=ROOT)
def plan():
    raw=(HERE/'module-final.json').read_bytes()
    if sha(raw)!=PLAN_SHA:raise RuntimeError('Changed final-module scope or source transport')
    d=json.loads(raw)
    if d['base_commit']!=BASE or set(d['files'])!=set(PATHS):raise RuntimeError('Changed 25-module scope')
    return d

def convert(path,data):
    item=plan()['files'][path]
    if sha(data)!=item['before_sha256']:raise RuntimeError('Changed final-module input: '+path)
    s=data.decode()
    for e in sorted(item['edits'],key=lambda e:e['start'],reverse=True):
        i=e['start']
        if s[i:i+len(e['old'])]!=e['old']:raise RuntimeError('Next-module edit mismatch')
        s=s[:i]+e['new']+s[i+len(e['old']):]
    if sha(s.encode())!=item['after_sha256']:raise RuntimeError('Changed final-module output')
    return s.encode()

def legacy_source(path,data):
    if path not in PATHS:return data
    old=baseline(path)
    if data==old:return old
    if data!=convert(path,old):raise RuntimeError('Source edit outside approved final-module header/body transport: '+path)
    return old

def overlay(files):
    for p in PATHS:files[p]=convert(p,files[p])
    return files

def policy():
    for p in PATHS:convert(p,baseline(p))
    expected_types()
    compatibility()

def expected_types():
    raw=(HERE/'module-final-types.json').read_bytes()
    if sha(raw)!=TYPES_SHA:raise RuntimeError('Changed final-module public expectation')
    d=json.loads(raw)
    if len(d)!=661 or not {v['module'] for v in d.values()} <= set(OWNERS):raise RuntimeError('Changed public scope')
    return d

COMPAT_SHA='29b24e59e5fe235dba35cab3256d55d3bc77346838fbf3c7590e60359cbaee2a'

def compatibility():
    raw=(HERE/'module-final-compat.json').read_bytes()
    if sha(raw)!=COMPAT_SHA:raise RuntimeError('Changed finite batch compatibility policy')
    c=json.loads(raw)
    for file,key in [('module-final-old.json','old_dag_sha256'),('module-final-current.json','current_dag_sha256'),('ModernFinalCompat.lean','witness_sha256'),('ModernFinalTypes.lean','public_witness_sha256'),('module-final-attributes.json','old_attributes_sha256')]:
        if sha((HERE/file).read_bytes())!=c[key]:raise RuntimeError('Changed actual expression or witness: '+file)
    if (HERE/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Changed compiler pin')
    lock=json.loads((HERE/'lake-manifest.json').read_text())
    if next(x['rev'] for x in lock['packages'] if x['name']=='mathlib')!=c['mathlib_commit']:raise RuntimeError('Changed batch Mathlib pin')
    if len(c['full'])!=8 or len(c['ordinary'])!=9:raise RuntimeError('Changed finite evidence scope')
    return c

def _partition(raw, pairs):
    import copy
    if raw.get('missing') or raw.get('added') or raw.get('relocated'):raise RuntimeError('Name/owner change is not a representation pair: '+json.dumps(raw))
    residual=copy.deepcopy(raw);residual['changed']=[];accepted=[]
    bound={x['name']:x for x in pairs}
    for x in raw['changed']:
        if x['name'] not in bound:residual['changed'].append(x);continue
        if x!=bound[x['name']]:raise RuntimeError('Wrong exact old/new batch pair: '+x['name'])
        accepted.append({'name':x['name'],'old_type':x['old']['type'],'new_type':x['new']['type'],'policy_sha256':COMPAT_SHA,'witness':'ModernFinalCompat.lean','raw_difference_retained':True})
    residual['passed']=not residual['changed']
    return residual,accepted

def accept_known(raw,view='full'):
    c=compatibility()
    v=subprocess.check_output(['lean','--version'],cwd=HERE,text=True)
    if c['lean_commit'] not in v:raise RuntimeError('Wrong actual compiler for batch')
    residual,accepted=_partition(raw,c[view])
    if accepted:subprocess.run(['lake','env','lean',c['witness']],cwd=HERE,check=True)
    return residual,accepted

def compare_public(path):
    from compare_types import load,compare
    raw=compare(expected_types(),load(path,661));left,accepted=accept_known(raw,'ordinary')
    if not left['passed']:raise RuntimeError('Unaccepted ordinary producer change: '+json.dumps(raw))
    return {'raw':raw,'accepted_representation_changes':accepted,'passed':True}

def compare_full(path):
    from compare_types import load,compare
    rel='reports/evidence/module-next/stages/migrated-types.tsv.gz'
    raw=(ROOT/rel).read_bytes()
    if raw!=subprocess.check_output(['git','show',BASE+':'+rel],cwd=ROOT):raise RuntimeError('Changed accepted 131-module export')
    with tempfile.NamedTemporaryFile() as f:
        f.write(gzip.decompress(raw));f.flush();old=load(f.name,3947)
    raw=compare(old,load(path,3947));left,accepted=accept_known(raw)
    if not left['passed']:raise RuntimeError('Unaccepted complete batch change: '+json.dumps(raw))
    return {'raw':raw,'accepted_representation_changes':accepted,'passed':True}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--compare-full');p.add_argument('--compare-public');a=p.parse_args();policy();compatibility()
    if a.compare_full:print(json.dumps(compare_full(a.compare_full),indent=2))
    if a.compare_public:print(json.dumps(compare_public(a.compare_public),indent=2))
