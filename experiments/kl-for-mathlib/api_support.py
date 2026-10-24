"""Round 5: supported sections, costalk duality and split operations with exact source/type boundaries.
The prior round stays frozen; inverse views feed only its historical checks.
"""
from pathlib import Path
import hashlib,json,subprocess,gzip,tempfile,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='d655bbdf5d09ddc26324f997e4f9a1987309a6a7'
SOURCE_SHA='e467768868ec7b21f7ddaaef50aef49190def87c7933444af022a54a4863bea6'
TYPES_SHA='ab154b65507c29aba29486aef7f2313ab13127b203840d19c3f514011ed6b151'
NAMES=tuple('OAI.KLInvariance.'+n for n in ('MomentGraph.Sheaf.singleSupportEquivDual_pairing', 'MomentGraph.Sheaf.singleSupportEquivDual_symm_pairing', 'MomentGraph.Sheaf.singleStalkEquivSupport_val', 'MomentGraph.Sheaf.singleStalkEquivSupport_apply_self', 'MomentGraph.Sheaf.singleStalkEquivSupport_symm_val', 'MomentGraph.Sheaf.kernelEquivSingleStalk_val', 'MomentGraph.GradedSheaf.singleSupportEquivDual_symm_homogeneous', 'MomentGraph.GradedSheaf.Hom.imageSectionEquiv_val', 'MomentGraph.GradedSheaf.SplitIn.liftEnd_vertex_apply', 'MomentGraph.GradedSheaf.SplitIn.liftEnd_edge_apply', 'MomentGraph.GradedSheaf.SplitIn.compress_liftEnd', 'MomentGraph.GradedSheaf.SplitIn.liftEnd_id'))
GENERATED=()
# Exact pre-module Propagation input reused by inherited proof-evolution tests.
HISTORICAL_INPUT=('8a7352034c8fa8155e41e45c6047a40357fbcef7','c330d6b7bca3c86579e1ebd2db9cefbf968a28bf6644387235cac7ef4e256cbf')
def sha(b):return hashlib.sha256(b).hexdigest()
def before(path,commit=BASE):return subprocess.check_output(['git','show',commit+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def plan():
 b=(HERE/'api-support-source.json').read_bytes()
 if sha(b)!=SOURCE_SHA:raise RuntimeError('Changed round-5 exact source policy')
 d=json.loads(b)
 if d['base_commit']!=BASE or len(d['files'])!=7:raise RuntimeError('Changed round-5 source scope')
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
 if path=='OAI/KL/Comparison/Propagation.lean' and sha(b)==HISTORICAL_INPUT[1]:
  if b!=before(path,HISTORICAL_INPUT[0]):raise RuntimeError('Changed historical Propagation input')
  return b
 old=before(path);new=apply(path,old)
 if b==new:return old
 if b==old or b in (before(path,'31f05da2d4ff1d80f2ceed3f8e1f3ac86fcb933b'),before(path,'178ccf2a9fa1f0bff04d6b029db1361f881fef33')):return b
 raise RuntimeError('Unreviewed families source: '+path)
def overlay(files):
 for p in plan()['files']:files[p]=apply(p,files[p])
 return files
def registry():
 b=(HERE/'api-support-types.json').read_bytes()
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
 rel='reports/evidence/graded-reflection-api/accepted/migrated-types.tsv.gz'
 b=(ROOT/rel).read_bytes()
 if b!=subprocess.check_output(['git','show',BASE+':'+rel],cwd=ROOT):raise RuntimeError('Changed fourth-round evidence')
 with tempfile.NamedTemporaryFile() as f:
  f.write(gzip.decompress(b));f.flush();old=load(f.name,3989)
 new=load(path,3989+len(additions()));raw=cmp(old,new)
 strip_additions(new)
 if raw['missing'] or raw['changed'] or raw['relocated'] or set(raw['added'])!=set(additions()):raise RuntimeError('Unapproved families: '+json.dumps(raw))
 return dict(raw=raw,registry=registry(),passed=True)
def check_axioms(text):
 expected=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(HERE/'SupportSectionsChecks.lean').read_text(),re.M)
 found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
 if not set(NAMES)<=set(expected) or len(found)!=len(expected) or {n for n,_ in found}!=set(expected):raise RuntimeError('Missing families axiom closures')
 for n,axs in found:
  if not set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axs))<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('New axiom: '+n)
if __name__=='__main__':
 import sys
 print(json.dumps(compare(sys.argv[1]),indent=2))
