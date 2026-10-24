"""Round 6: graded morphisms, range functoriality and image/corner laws with exact source/type boundaries.
The prior round stays frozen; inverse views feed only its historical checks.
"""
from pathlib import Path
import hashlib,json,subprocess,gzip,tempfile,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='78cdaf405dbf1dcf07eed5490469b7a8704c93f0'
SOURCE_SHA='bcfb94f7fb0887cade8d97f63fadc08bb157bd3e85aa4294bdf90939478cdd44'
TYPES_SHA='8c8d8c83bc43ad025bd7402c7c131d4cdf659046d3a6b820a611c0e88acdcca0'
NAMES=('OAI.KLInvariance.Graded.ModuleData.rangeMap_id', 'OAI.KLInvariance.Graded.ModuleData.rangeMap_comp', 'OAI.KLInvariance.Graded.ModuleData.rangeInclusion_comp_rangeMap', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_assoc', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.id_comp', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_id', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.inverse_comp', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_inverse', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageInclusion_comp_imageProjection', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionMap_val', 'OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSplit_projector', 'OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.downEnd_comp', 'OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd_downEnd')
GENERATED=()
# Exact historical views required by inherited checks; never arbitrary source bypasses.
HISTORICAL_INPUTS={'ForMathlib/Algebra/Module/Graded/ModuleData/Range.lean': [('178ccf2a9fa1f0bff04d6b029db1361f881fef33', '06c7253b3cf539042a8d2ee5a1ff67470ba8c8153efb217f320f2f6a2333a60f')], 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean': [('178ccf2a9fa1f0bff04d6b029db1361f881fef33', '9a968f525ebb1e24916ab6e9eb2bca24ffaf3d77a1c162e9d2946c9ad2d52ac6'), ('d655bbdf5d09ddc26324f997e4f9a1987309a6a7', 'fbf00a7a1032c4c424977f4d1fa88353aa35d776435eed89b96db17f389939c7')]}
def sha(b):return hashlib.sha256(b).hexdigest()
def before(path,commit=BASE):return subprocess.check_output(['git','show',commit+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def plan():
 b=(HERE/'api-saturation-source.json').read_bytes()
 if sha(b)!=SOURCE_SHA:raise RuntimeError('Changed round-6 exact source policy')
 d=json.loads(b)
 if d['base_commit']!=BASE or len(d['files'])!=2:raise RuntimeError('Changed round-6 source scope')
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
 if path not in plan()['files']:return b
 for commit,digest in HISTORICAL_INPUTS.get(path,()):
  if sha(b)==digest:
   if b!=before(path,commit):raise RuntimeError('Changed historical source identity')
   return b
 old=before(path);new=apply(path,old)
 if b==new:return old
 if b==old:return b
 raise RuntimeError('Unreviewed families source: '+path)
def overlay(files):
 for p in plan()['files']:files[p]=apply(p,files[p])
 return files
def registry():
 b=(HERE/'api-saturation-types.json').read_bytes()
 if sha(b)!=TYPES_SHA:raise RuntimeError('Changed families type registry')
 d=json.loads(b)
 if set(d['mathematical'])!=set(NAMES) or set(d['generated'])!=set(GENERATED):raise RuntimeError('Unlisted families declaration')
 if any(v['kind']!='theorem' for v in d['mathematical'].values()):raise RuntimeError('Expected theorem APIs')
 return d
def additions():
 d=registry();return {**d['mathematical'],**d['generated']}
def strip_additions(records):
 added=additions()
 for n,r in added.items():
  if records.get(n)!=r:raise RuntimeError('Missing/changed families API: '+n)
 return {n:r for n,r in records.items() if n not in added}
def compare(path):
 from compare_types import load,compare as cmp
 rel='reports/evidence/support-sections-api/accepted/migrated-types.tsv.gz'
 b=(ROOT/rel).read_bytes()
 if b!=subprocess.check_output(['git','show',BASE+':'+rel],cwd=ROOT):raise RuntimeError('Changed fifth-round evidence')
 with tempfile.NamedTemporaryFile() as f:
  f.write(gzip.decompress(b));f.flush();old=load(f.name,4001)
 new=load(path,4001+len(additions()));raw=cmp(old,new)
 strip_additions(new)
 if raw['missing'] or raw['changed'] or raw['relocated'] or set(raw['added'])!=set(additions()):raise RuntimeError('Unapproved families: '+json.dumps(raw))
 return dict(raw=raw,registry=registry(),passed=True)
def check_axioms(text):
 expected=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(HERE/'ApiSaturationChecks.lean').read_text(),re.M)
 found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
 if not set(NAMES)<=set(expected) or len(found)!=len(expected) or {n for n,_ in found}!=set(expected):raise RuntimeError('Missing families axiom closures')
 for n,axs in found:
  if not set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axs))<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('New axiom: '+n)
if __name__=='__main__':
 import sys
 print(json.dumps(compare(sys.argv[1]),indent=2))
