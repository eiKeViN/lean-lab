"""Final105 exact source transport; eight explicit generated-name contract removals.

prior_view is ONLY an input adapter for the inherited156 checks. It restores
historical records for names intentionally removed by the separately mandatory
complete raw interface audit. It does not claim those names remain usable.
"""
from pathlib import Path
import copy,gzip,hashlib,json,subprocess,tempfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='382d29d94aaa8e32bcdeb24633f070d29695dcc3'
PLAN_SHA='b80932b3e50f7b705000c0452aa800579af1910f518c4b880ac9b92db56dbd66'
REGISTRY_SHA='f0259259bb74b5cac131c4079eac544f94d4fa935130ea4f52caeaa60ece4182'
PATHS=('ForMathlib.lean', 'ForMathlib/Algebra/Algebra/ReflectionFrobenius/Basis.lean', 'ForMathlib/Algebra/Module/CoefficientChange/Basic.lean', 'ForMathlib/Algebra/Module/CoefficientChange/Dual.lean', 'ForMathlib/Algebra/Module/Cover/Local.lean', 'ForMathlib/Algebra/Module/Graded/DualAndShift.lean', 'ForMathlib/Algebra/Module/Graded/ModuleData/CoefficientChange.lean', 'ForMathlib/Algebra/Module/Graded/ModuleData/CoefficientChange/Basic.lean', 'ForMathlib/Algebra/Module/Graded/ModuleData/MinimalCover.lean', 'ForMathlib/Algebra/Module/Projective/Transport.lean', 'ForMathlib/Algebra/Module/ReflectionPair/TensorDescent.lean', 'ForMathlib/Algebra/Module/ReflectionPair/TensorKernel.lean', 'ForMathlib/Algebra/Module/ReflectionPair/Twist.lean', 'ForMathlib/Combinatorics/MomentGraph/Boundary/Basic.lean', 'ForMathlib/Combinatorics/MomentGraph/Boundary/Extension.lean', 'ForMathlib/Combinatorics/MomentGraph/Boundary/Hom.lean', 'ForMathlib/Combinatorics/MomentGraph/Boundary/Models.lean', 'ForMathlib/Combinatorics/MomentGraph/Boundary/Summand.lean', 'ForMathlib/Combinatorics/MomentGraph/Boundary/Uniqueness.lean', 'ForMathlib/Combinatorics/MomentGraph/Bruhat/DihedralModel.lean', 'ForMathlib/Combinatorics/MomentGraph/Bruhat/PlaneModel.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Basic.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Character.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Duality.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Extension.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Hilbert.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Hom.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Models.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Properties.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/StalkMaps.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Uniqueness.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/BaseChange.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Extension.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/FlowDown.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Hom.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Iso.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Isomorphism.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Localization.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Models.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Pi.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Products.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Pullback.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Restriction.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/ScaledImages.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Structure.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Uniqueness.lean', 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Zero.lean', 'ForMathlib/GroupTheory/Coxeter/Roots/ReflectionOrder.lean', 'ForMathlib/LinearAlgebra/Dual/Frobenius.lean', 'ForMathlib/LinearAlgebra/KernelCoordinates.lean', 'ForMathlib/RepresentationTheory/BottSamelson/TitsWords.lean', 'ForMathlib/RepresentationTheory/Hecke/DyerPaths/LexicographicOrder.lean', 'ForMathlib/RepresentationTheory/Hecke/DyerPaths/Wall.lean', 'OAI/Architecture.lean', 'OAI/KL.lean', 'OAI/KL/BottSamelson/AdjointSheaf.lean', 'OAI/KL/BottSamelson/CanonicalPairing.lean', 'OAI/KL/BottSamelson/Character.lean', 'OAI/KL/BottSamelson/CharacterDecomposition.lean', 'OAI/KL/BottSamelson/Flabby.lean', 'OAI/KL/BottSamelson/Pairings.lean', 'OAI/KL/BottSamelson/StalkCharacter.lean', 'OAI/KL/BottSamelson/Stalks.lean', 'OAI/KL/BottSamelson/Support.lean', 'OAI/KL/BottSamelson/UpperSections.lean', 'OAI/KL/Comparison/Propagation.lean', 'OAI/KL/Comparison/SuffixFreeness.lean', 'OAI/KL/Comparison/Transport.lean', 'OAI/KL/Invariance/Finite.lean', 'OAI/KL/Invariance/Main.lean', 'OAI/KL/Localization/Ambient.lean', 'OAI/KL/Localization/Edge.lean', 'OAI/KL/Localization/GraphEmbedding.lean', 'OAI/KL/Localization/Plane.lean', 'OAI/KL/Localization/TerminalImages.lean', 'OAI/KL/Sheaves/Boundary.lean', 'OAI/KL/Sheaves/FreeModel.lean', 'OAI/KL/Sheaves/LowerCharacter.lean', 'OAI/KL/Sheaves/Reciprocity.lean', 'OAI/KL/Sheaves/StalkReciprocity.lean', 'OAI/KL/Sheaves/Support.lean', 'OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean', 'OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean', 'OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean', 'OAI/RepresentationTheory/KazhdanLusztig/Decomposition.lean', 'OAI/RepresentationTheory/KazhdanLusztig/DihedralIntervals.lean', 'OAI/RepresentationTheory/KazhdanLusztig/DyerPaths.lean', 'OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean', 'OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean', 'OAI/RepresentationTheory/KazhdanLusztig/GradedModules.lean', 'OAI/RepresentationTheory/KazhdanLusztig/GradedSheaves.lean', 'OAI/RepresentationTheory/KazhdanLusztig/HilbertSeries.lean', 'OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean', 'OAI/RepresentationTheory/KazhdanLusztig/Invariance.lean', 'OAI/RepresentationTheory/KazhdanLusztig/MinimalExtensions.lean', 'OAI/RepresentationTheory/KazhdanLusztig/ModuleAlgebra.lean', 'OAI/RepresentationTheory/KazhdanLusztig/PlaneLocalization.lean', 'OAI/RepresentationTheory/KazhdanLusztig/PositiveTransfer.lean', 'OAI/RepresentationTheory/KazhdanLusztig/ReflectionOrders.lean', 'OAI/RepresentationTheory/KazhdanLusztig/ReflectionSchedules.lean', 'OAI/RepresentationTheory/KazhdanLusztig/SheafMorphisms.lean', 'OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean', 'OAI/RepresentationTheory/KazhdanLusztig/Support.lean', 'OAI/RepresentationTheory/KazhdanLusztig/TerminalKernels.lean')
OWNERS=tuple(p[:-5].replace('/','.') for p in PATHS)
def sha(b):return hashlib.sha256(b).hexdigest()
def baseline(p):return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+p],cwd=ROOT)
def plan():
    b=(HERE/'module-all.json').read_bytes()
    if sha(b)!=PLAN_SHA:raise RuntimeError('Changed final105 source policy')
    d=json.loads(b)
    if d['base_commit']!=BASE or set(d['files'])!=set(PATHS):raise RuntimeError('Changed final105 scope')
    return d

def convert(path,data):
    d=plan()['files'][path]
    if sha(data)!=d['before_sha256']:raise RuntimeError('Changed final105 input: '+path)
    s=data.decode()
    for e in sorted(d['edits'],key=lambda e:e['start'],reverse=True):
        i=e['start']
        if s[i:i+len(e['old'])]!=e['old']:raise RuntimeError('Invalid exact source edit')
        s=s[:i]+e['new']+s[i+len(e['old']):]
    if sha(s.encode())!=d['after_sha256']:raise RuntimeError('Changed final105 output')
    return s.encode()
def legacy_source(path,data):
    if path not in PATHS:return data
    old=baseline(path)
    if data not in (old,convert(path,old)):raise RuntimeError('Source outside final105 transport: '+path)
    return old

def overlay(files):
    for p in PATHS:files[p]=convert(p,files[p])
    return files

def registry():
    b=(HERE/'module-all-interface.json').read_bytes()
    if sha(b)!=REGISTRY_SHA:raise RuntimeError('Changed explicit generated interface contract')
    c=json.loads(b)
    if len(c['removed'])!=8 or len(c['generated_added'])!=1:raise RuntimeError('Changed exact generated-name scope')
    if (HERE/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Changed toolchain')
    lock=json.loads((HERE/'lake-manifest.json').read_text())
    if next(x['rev'] for x in lock['packages'] if x['name']=='mathlib')!=c['mathlib_commit']:raise RuntimeError('Changed Mathlib')
    for f,h in c['evidence_files'].items():
        if sha((HERE/f).read_bytes())!=h:raise RuntimeError('Changed final105 evidence: '+f)
    return c

def policy():
    for p in PATHS:convert(p,baseline(p))
    registry()

def baseline_types():
    from compare_types import load
    p='reports/evidence/module-final/accepted-25/migrated-types.tsv.gz'
    b=(ROOT/p).read_bytes()
    if b!=subprocess.check_output(['git','show',BASE+':'+p],cwd=ROOT):raise RuntimeError('Changed accepted156 raw export')
    with tempfile.NamedTemporaryFile() as f:
        f.write(gzip.decompress(b));f.flush();return load(f.name,3947)

def prior_view(actual):
    """Validate exact name/owner change; adapt ONLY for inherited checks."""
    old=baseline_types();c=registry()
    if set(old)-set(actual)!=set(c['removed']) or set(actual)-set(old)!=set(c['generated_added']):raise RuntimeError('Unapproved name change')
    for n,v in c['removed'].items():
        if old[n]!=v:raise RuntimeError('Unbound removed generated declaration: '+n)
    for n,v in c['generated_added'].items():
        if actual[n]!=v:raise RuntimeError('Changed generated addition: '+n)
    for n in old.keys()&actual.keys():
        if actual[n]['module']!=old[n]['module']:raise RuntimeError('Unapproved owner change: '+n)
    view={n:v for n,v in actual.items() if n not in c['generated_added']}
    view.update(c['removed'])
    return view

def contract_summary():
    c=registry()
    return {'actual_export_count':3940,'prior_contract_view_count':3947,
      'comparison_view':'retained declarations plus historical records ONLY for the eight explicitly retired names; not an availability assertion',
      'explicit_generated_contract_breaks':c['removed'],
      'classified_generated_additions':c['generated_added'],
      'actual_raw_audit':'final105-full-records','fully_source_compatible':False}

def load_prior_view(path):
    from compare_types import load
    return prior_view(load(path,3940))

def witness():
    c=registry()
    if c['lean_commit'] not in subprocess.check_output(['lean','--version'],cwd=HERE,text=True):raise RuntimeError('Wrong running Lean')
    subprocess.run(['lake','env','lean','ModernAllCompat.lean'],cwd=HERE,check=True)

def accept_type(raw):
    c=registry();pair=c['type_pair'];left=copy.deepcopy(raw);left['changed']=[];accepted=[]
    for x in raw['changed']:
        if x['name']!=pair['name']:left['changed'].append(x);continue
        if x!=pair:raise RuntimeError('Unbound Tits public type expression')
        witness();accepted.append({'name':x['name'],'old_type':x['old']['type'],'new_type':x['new']['type'],'witness':'ModernAllCompat.lean','raw_difference_retained':True})
    left['passed']=not(left['missing'] or left['added'] or left['changed'])
    return left,accepted

def compare_full(path):
    from compare_types import load,compare
    actual=load(path,3940);old=baseline_types();raw=compare(old,actual)
    view=prior_view(actual);r=compare(old,view);left,accepted=accept_type(r)
    if not left['passed'] or left['relocated']:raise RuntimeError('New unaccepted final105 difference: '+json.dumps(raw))
    return {'raw':raw,'explicit_generated_contract_breaks':registry()['removed'],'classified_generated_additions':registry()['generated_added'],'accepted_representation_changes':accepted,'passed':True,'fully_source_compatible':False}

def compare_public(path):
    from compare_types import load,compare
    c=registry();old=json.loads((HERE/'module-all-types.json').read_text());actual=load(path,3940)
    raw=compare(old,actual)
    if raw['missing'] or raw['added'] or raw['relocated']:raise RuntimeError('Ordinary name/owner change: '+json.dumps(raw))
    if raw['changed']!=c['ordinary_pairs']:raise RuntimeError('Unbound ordinary type expression difference: '+json.dumps(raw))
    subprocess.run(['lake','env','lean','ModernOrdinaryAllCompat.lean'],cwd=HERE,check=True)
    subprocess.run(['lake','env','lean','ModernFinalCompat.lean'],cwd=HERE,check=True)
    return {'raw':raw,'accepted_representation_changes':c['ordinary_pairs'],'actual_old_types_rechecked':115,'retained_matcher_value_rechecked':True,'prior_two_view_pairs_witness':'ModernFinalCompat.lean','passed':True}

if __name__=='__main__':
    import sys
    policy();print(json.dumps(compare_full(sys.argv[1]),indent=2))
