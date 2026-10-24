"""Round 3: four related operation families with exact source/type boundaries.
The prior round stays frozen; inverse views feed only its historical checks.
"""
from pathlib import Path
import hashlib,json,subprocess,gzip,tempfile,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='bdbca7ff639bc32f94a85647c88cb16d9e80b294'
SOURCE_SHA='701ce877f749910d95455ca84bc371c732d0ca05fe8ea5595cb0f9ebbe8c7d9b'
TYPES_SHA='db107aacfcbe766fd86d0444790eff71a7a92117c6b1980ad947c3424971b2d2'
NAMES=tuple('OAI.KLInvariance.MomentGraph.Sheaf.'+n for n in ('Iso.assignments_apply', 'Iso.assignments_symm_apply', 'Iso.sections_val_apply', 'Iso.boundary_apply', 'mem_upwardKernel_iff', 'upwardKernel_univ', 'pi_stalkMap_apply', 'prod_stalkMap_apply', 'prod_compatible_iff', 'restrict_extendAssignment', 'restrict_compatible_iff'))
GENERATED=()
# Two immutable pre-module inputs used by the inherited proof-evolution tests.
# The final product check still requires the current seven-file overlay exactly.
HISTORICAL_INPUTS={
 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Models.lean':
  ('382d29d94aaa8e32bcdeb24633f070d29695dcc3','af6f21aad2f674a0d658e9d72b4245c37a72516e1cd7d2418b2e2d79a8c2b42c'),
 'ForMathlib/Combinatorics/MomentGraph/Sheaf/Pullback.lean':
  ('382d29d94aaa8e32bcdeb24633f070d29695dcc3','22ee33c3051530b5581c66b929e45f55a3716047c3be6c9a2bac64d6efd3e38a')}
def sha(b):return hashlib.sha256(b).hexdigest()
def before(path,commit=BASE):return subprocess.check_output(['git','show',commit+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def plan():
 b=(HERE/'api-families-source.json').read_bytes()
 if sha(b)!=SOURCE_SHA:raise RuntimeError('Changed round-3 exact source policy')
 d=json.loads(b)
 if d['base_commit']!=BASE or len(d['files'])!=7:raise RuntimeError('Changed round-3 source scope')
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
 if path in HISTORICAL_INPUTS:
  commit,digest=HISTORICAL_INPUTS[path]
  if sha(b)==digest:
   if b!=before(path,commit):raise RuntimeError('Changed historical input identity')
   return b
 old=before(path);new=apply(path,old)
 if b==new:return old
 if b==old or b in (before(path,'31f05da2d4ff1d80f2ceed3f8e1f3ac86fcb933b'),before(path,'178ccf2a9fa1f0bff04d6b029db1361f881fef33')):return b
 raise RuntimeError('Unreviewed families source: '+path)
def overlay(files):
 for p in plan()['files']:files[p]=apply(p,files[p])
 return files
def registry():
 b=(HERE/'api-families-types.json').read_bytes()
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
 rel='reports/evidence/coefficient-api-evolution/accepted/migrated-types.tsv.gz'
 b=(ROOT/rel).read_bytes()
 if b!=subprocess.check_output(['git','show',BASE+':'+rel],cwd=ROOT):raise RuntimeError('Changed second-round evidence')
 with tempfile.NamedTemporaryFile() as f:
  f.write(gzip.decompress(b));f.flush();old=load(f.name,3956)
 new=load(path,3956+len(additions()));raw=cmp(old,new)
 strip_additions(new)
 if raw['missing'] or raw['changed'] or raw['relocated'] or set(raw['added'])!=set(additions()):raise RuntimeError('Unapproved families: '+json.dumps(raw))
 return dict(raw=raw,registry=registry(),passed=True)
def check_axioms(text):
 expected=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(HERE/'ApiFamiliesChecks.lean').read_text(),re.M)
 found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
 if not set(NAMES)<=set(expected) or len(found)!=len(expected) or {n for n,_ in found}!=set(expected):raise RuntimeError('Missing families axiom closures')
 for n,axs in found:
  if not set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axs))<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('New axiom: '+n)
if __name__=='__main__':
 import sys
 print(json.dumps(compare(sys.argv[1]),indent=2))
