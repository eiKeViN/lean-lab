"""Bounded semantic API experiment over the accepted module migration.

Only seven exact producer/client sources may change. Historical checking views
undo these reviewed edits; current products must match the new exact bytes.
Added mathematical declarations are checked separately, never ignored by prefix.
"""
from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
TYPES_SHA='b846764299030f7aff842fe3ea8fbe4d5cc8466c6f5883e530c6ed5c1102f3f0'
BASE='178ccf2a9fa1f0bff04d6b029db1361f881fef33'
SOURCE_SHA='88e9c102e53ada3a698c0961844acce2d9c317d688da518ee60c8b143f7c9ab1'
def sha(b):return hashlib.sha256(b).hexdigest()
def plan():
    b=(HERE/'semantic-api-source.json').read_bytes()
    if sha(b)!=SOURCE_SHA:raise RuntimeError('Changed bounded semantic API source policy')
    d=json.loads(b)
    if d['base_commit']!=BASE or len(d['files'])!=7:raise RuntimeError('Changed semantic API scope')
    return d

def original(p):return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+p],cwd=ROOT)
def apply(p,b):
    r=plan()['files'][p]
    if sha(b)!=r['before_sha256']:raise RuntimeError('Unexpected semantic API input: '+p)
    s=b.decode()
    for e in reversed(r['edits']):
        i=e['start']
        if s[i:i+len(e['old'])]!=e['old']:raise RuntimeError('Invalid semantic API edit')
        s=s[:i]+e['new']+s[i+len(e['old']):]
    if sha(s.encode())!=r['after_sha256']:raise RuntimeError('Unexpected semantic API output')
    return s.encode()
def prior_source(p,b):
    r=plan()['files'].get(p)
    if r is None:return b
    old=original(p);new=apply(p,old)
    if b==new:return old
    if b==old:return b  # immutable reconstruction and inherited mutation controls
    raise RuntimeError('Unreviewed semantic API source: '+p)
def overlay(files):
    for p in plan()['files']:files[p]=apply(p,files[p])
    return files

def added_types():
    b=(HERE/'semantic-api-types.json').read_bytes()
    if sha(b)!=TYPES_SHA:raise RuntimeError('Changed semantic API type policy')
    d=json.loads(b)
    if len(d)!=6 or any(r['kind']!='theorem' for r in d.values()):
        raise RuntimeError('Expected exactly six added theorems')
    return d

GENERATED_SHA='9aa202f4a1ae1a6674db0d0cb9d12307cbfcce3321e79924c1e8e759ee48a1bd'
def generated_types():
    b=(HERE/'semantic-api-generated.json').read_bytes()
    if sha(b)!=GENERATED_SHA:raise RuntimeError('Changed generated congruence policy')
    d=json.loads(b)
    if set(d)!={'OAI.KLInvariance.LocalCover.splitEquiv.congr_simp'} or any(r['kind']!='theorem' for r in d.values()):
        raise RuntimeError('Unexpected generated addition')
    return d

def prior_export(path,expected_count):
    from compare_types import load
    records=__import__('api_evolution').strip_additions(load(path))
    additions={**added_types(),**generated_types()}
    if len(records)!=expected_count+len(additions):raise RuntimeError('Unexpected semantic API count')
    for n,r in additions.items():
        if records.get(n)!=r:raise RuntimeError('Changed semantic API declaration: '+n)
    return {n:r for n,r in records.items() if n not in additions}

def check_axioms(text):
    import re
    expected=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(HERE/'SemanticApiChecks.lean').read_text(),re.M)
    found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
    if len(expected)!=14 or len(found)!=14 or {n for n,_ in found}!=set(expected):
        raise RuntimeError('Missing semantic API axiom closure')
    for n,axs in found:
        if not set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axs))<={'propext','Quot.sound','Classical.choice'}:
            raise RuntimeError('New axiom: '+n)

HIDDEN=()
def modern_exporter(destination):
    # Round 2 restores the exposed computation interface: use the frozen audit.
    return str(HERE/'ModernAllTypes.lean')

def compare_main(path):
    import gzip,tempfile
    from compare_types import load,compare
    relative='reports/evidence/module-completion/accepted/migrated-types.tsv.gz'
    b=(ROOT/relative).read_bytes()
    if b!=subprocess.check_output(['git','show',BASE+':'+relative],cwd=ROOT):
        raise RuntimeError('Changed accepted main evidence')
    with tempfile.NamedTemporaryFile() as f:
        f.write(gzip.decompress(b));f.flush();old=load(f.name,3940)
    current=__import__('api_evolution').strip_additions(load(path));raw=compare(old,current);additions={**added_types(),**generated_types()}
    if raw['missing'] or raw['changed'] or raw['relocated'] or set(raw['added'])!=set(additions):
        raise RuntimeError('Unapproved change from accepted main: '+json.dumps(raw))
    if any(current[n]!=r for n,r in additions.items()):raise RuntimeError('Changed new API')
    return dict(raw=raw,mathematical_additions=added_types(),generated_additions=generated_types(),hidden_definitions=HIDDEN,passed=True)

if __name__=='__main__':
    import sys
    print(json.dumps(compare_main(sys.argv[1]),indent=2))
