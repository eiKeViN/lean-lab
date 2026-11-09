"""Round 4: graded/reflection operation families with exact source/type boundaries.
The prior round stays frozen; inverse views feed only its historical checks.
"""
from pathlib import Path
import hashlib,json,subprocess,gzip,tempfile,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='a797fbc1300142c56c18ebfaa0ae84b357bc4b3d'
SOURCE_SHA='86bdcb4267e385d669649cab49c0778b1552ab30d5be81154d25ff82d99d2ea7'
TYPES_SHA='7a3bfd411066f2b45a92eca69c8582d616308171ae4763d33e2bc480bc02fcb9'
NAMES=tuple('OAI.KLInvariance.'+n for n in ('Graded.ModuleData.rangeMap_val', 'Graded.ModuleData.rangeMap_projection', 'Graded.ModuleData.rangeProjection_val', 'Graded.ModuleData.rangeInclusion_apply', 'Graded.ModuleData.range_fixed', 'MomentGraph.GradedSheaf.Hom.comp_vertex_apply', 'MomentGraph.GradedSheaf.Hom.comp_edge_apply', 'MomentGraph.GradedSheaf.Hom.sectionMap_comp', 'MomentGraph.GradedSheaf.Hom.sectionMap_id', 'MomentGraph.GradedSheaf.SplitIn.projection_comp_inclusion', 'MomentGraph.GradedSheaf.SplitIn.projector_apply_vertex', 'MomentGraph.GradedSheaf.SplitIn.projector_apply_edge', 'ReflectionPairTranslation.Twist.val_add', 'ReflectionPairTranslation.Twist.val_smul', 'ReflectionPairTranslation.mem_lattice_iff', 'ReflectionPairTranslation.left_apply', 'ReflectionPairTranslation.kernelMap_snd_val', 'ReflectionPairTranslation.twistMap_val', 'ReflectionPairTranslation.right_apply', 'ReflectionPairTranslation.rightKernelMap_fst', 'ReflectionPairTranslation.tensorFirst_natural', 'ReflectionPairTranslation.tensorSecond_natural'))
GENERATED=()
def sha(b):return hashlib.sha256(b).hexdigest()
def before(path,commit=BASE):return subprocess.check_output(['git','show',commit+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def plan():
 b=(HERE/'api-reflection-source.json').read_bytes()
 if sha(b)!=SOURCE_SHA:raise RuntimeError('Changed round-4 exact source policy')
 d=json.loads(b)
 if d['base_commit']!=BASE or len(d['files'])!=6:raise RuntimeError('Changed round-4 source scope')
 return d
def apply(path,b):
 r=plan()['files'][path]
 if sha(b)!=r['before_sha256']:raise RuntimeError('Unexpected families input: '+path)
 s=b.decode()
 for e in reversed(r['edits']):
  i=e['start']
  if s[i:i+len(e['old'])]!=e['old']:raise RuntimeError('Invalid exact families edit')
  s=s[:i]+e['new']+s[i+len(e['old']):]
 if sha(s.encode())!=r['after_sha256']:raise RuntimeError('Unexpected families output')
 return s.encode()
def prior_source(path,b):
 b=__import__('api_support').prior_source(path,b)
 if path not in plan()['files']:return b
 old=before(path);new=apply(path,old)
 if b==new:return old
 if b==old or b in (before(path,'31f05da2d4ff1d80f2ceed3f8e1f3ac86fcb933b'),before(path,'178ccf2a9fa1f0bff04d6b029db1361f881fef33')):return b
 raise RuntimeError('Unreviewed families source: '+path)
def overlay(files):
 for p in plan()['files']:files[p]=apply(p,files[p])
 return files
def registry():
 b=(HERE/'api-reflection-types.json').read_bytes()
 if sha(b)!=TYPES_SHA:raise RuntimeError('Changed families type registry')
 d=json.loads(b)
 if set(d['mathematical'])!=set(NAMES) or set(d['generated'])!=set(GENERATED):raise RuntimeError('Unlisted families declaration')
 if any(v['kind']!='theorem' for v in d['mathematical'].values()):raise RuntimeError('Expected theorem APIs')
 return d
def additions():
 d=registry();return {**d['mathematical'],**d['generated']}
def strip_additions(records):
 records=__import__('api_support').strip_additions(records)
 added=additions()
 for n,r in added.items():
  if records.get(n)!=r:raise RuntimeError('Missing/changed families API: '+n)
 return {n:r for n,r in records.items() if n not in added}
def compare(path):
 from compare_types import load,compare as cmp
 rel='reports/evidence/mathematical-api-families/accepted/migrated-types.tsv.gz'
 b=(ROOT/rel).read_bytes()
 if b!=subprocess.check_output(['git','show',BASE+':'+rel],cwd=ROOT):raise RuntimeError('Changed third-round evidence')
 with tempfile.NamedTemporaryFile() as f:
  f.write(gzip.decompress(b));f.flush();old=load(f.name,3967)
 complete=load(path);new=__import__('api_support').strip_additions(complete);raw=cmp(old,new)
 strip_additions(complete)
 if raw['missing'] or raw['changed'] or raw['relocated'] or set(raw['added'])!=set(additions()):raise RuntimeError('Unapproved families: '+json.dumps(raw))
 return dict(raw=raw,registry=registry(),passed=True)
def check_axioms(text):
 expected=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(HERE/'GradedReflectionChecks.lean').read_text(),re.M)
 found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
 if not set(NAMES)<=set(expected) or len(found)!=len(expected) or {n for n,_ in found}!=set(expected):raise RuntimeError('Missing families axiom closures')
 for n,axs in found:
  if not set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axs))<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('New axiom: '+n)
if __name__=='__main__':
 import sys
 print(json.dumps(compare(sys.argv[1]),indent=2))
