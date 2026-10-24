"""Round 2: six exact source changes, individually registered mathematical API.
The prior round stays frozen; inverse views feed only its historical checks.
"""
from pathlib import Path
import hashlib,json,subprocess,gzip,tempfile,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='31f05da2d4ff1d80f2ceed3f8e1f3ac86fcb933b'
SOURCE_SHA='5cf15dd23d5aee52f6355d0c449093944bcf28199ad8024010813f971344830f'
TYPES_SHA='6cd8ca9f18c2f845c5ce8cdd83ef4c9e5efb2f2e94c2f542c2d2d6e6d038fd85'
NAMES=tuple('OAI.KLInvariance.'+n for n in (
 'CoefficientChange.val_zero','CoefficientChange.val_smul','CoefficientChange.val_mapEquiv',
 'Graded.ModuleData.val_changeHom','MomentGraph.GradedSheaf.coefficientChange_lower_val',
 'MomentGraph.GradedSheaf.coefficientChange_upper_val','MomentGraph.GradedSheaf.coefficientChange_compatibleOn_iff',
 'MomentGraph.GradedSheaf.coefficientChangeSections_symm_val_apply',
 'MomentGraph.GradedSheaf.PerfectPairing.coefficientChange_apply'))
GENERATED=()
def sha(b):return hashlib.sha256(b).hexdigest()
def before(path,commit=BASE):return subprocess.check_output(['git','show',commit+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def plan():
 b=(HERE/'api-evolution-source.json').read_bytes()
 if sha(b)!=SOURCE_SHA:raise RuntimeError('Changed round-2 exact source policy')
 d=json.loads(b)
 if d['base_commit']!=BASE or len(d['files'])!=6:raise RuntimeError('Changed round-2 source scope')
 return d
def apply(path,b):
 r=plan()['files'][path]
 if sha(b)!=r['before_sha256']:raise RuntimeError('Unexpected evolution input: '+path)
 s=b.decode()
 for e in reversed(r['edits']):
  i=e['start']
  if s[i:i+len(e['old'])]!=e['old']:raise RuntimeError('Invalid exact evolution edit')
  s=s[:i]+e['new']+s[i+len(e['old']):]
 if sha(s.encode())!=r['after_sha256']:raise RuntimeError('Unexpected evolution output')
 return s.encode()
def prior_source(path,b):
 if path not in plan()['files']:return b
 old=before(path);new=apply(path,old)
 if b==new:return old
 if b==old or b==before(path,'178ccf2a9fa1f0bff04d6b029db1361f881fef33'):return b
 raise RuntimeError('Unreviewed evolution source: '+path)
def overlay(files):
 for p in plan()['files']:files[p]=apply(p,files[p])
 return files
def registry():
 b=(HERE/'api-evolution-types.json').read_bytes()
 if sha(b)!=TYPES_SHA:raise RuntimeError('Changed evolution type registry')
 d=json.loads(b)
 if set(d['mathematical'])!=set(NAMES) or set(d['generated'])!=set(GENERATED):raise RuntimeError('Unlisted evolution declaration')
 if any(v['kind']!='theorem' for v in d['mathematical'].values()):raise RuntimeError('Expected theorem APIs')
 return d
def additions():
 d=registry();return {**d['mathematical'],**d['generated']}
def strip_additions(records):
 added=additions()
 for n,r in added.items():
  if records.get(n)!=r:raise RuntimeError('Missing/changed evolution API: '+n)
 return {n:r for n,r in records.items() if n not in added}
def compare(path):
 from compare_types import load,compare as cmp
 rel='reports/evidence/semantic-api/accepted/migrated-types.tsv.gz'
 b=(ROOT/rel).read_bytes()
 if b!=subprocess.check_output(['git','show',BASE+':'+rel],cwd=ROOT):raise RuntimeError('Changed first-round evidence')
 with tempfile.NamedTemporaryFile() as f:
  f.write(gzip.decompress(b));f.flush();old=load(f.name,3947)
 new=load(path,3947+len(additions()));raw=cmp(old,new)
 strip_additions(new)
 if raw['missing'] or raw['changed'] or raw['relocated'] or set(raw['added'])!=set(additions()):raise RuntimeError('Unapproved evolution: '+json.dumps(raw))
 return dict(raw=raw,registry=registry(),passed=True)
def check_axioms(text):
 expected=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(HERE/'ApiEvolutionChecks.lean').read_text(),re.M)
 found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
 if not set(NAMES)<=set(expected) or len(found)!=len(expected) or {n for n,_ in found}!=set(expected):raise RuntimeError('Missing evolution axiom closures')
 for n,axs in found:
  if not set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axs))<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('New axiom: '+n)
if __name__=='__main__':
 import sys
 print(json.dumps(compare(sys.argv[1]),indent=2))
