"""Hash-bound 226-node dependency-closed compatibility rollout (223 new modules)."""
from pathlib import Path
from functools import lru_cache
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BASE='45cc0cfcf699b7acd17a48d867c5f28bdb30bc5d'
PLAN_SHA='35a8935693cc4326dd02e906bbe222ea86f99c99fdd051c1fdfdc93fe0c6bc7f'
TYPES_SHA='1a37df0fcfd3658f1d28f66cf31ea06673587931308d883dddd48e1e9fd52048'
def sha(b):return hashlib.sha256(b).hexdigest()
def plan():
    data=(HERE/'module-rollout.json').read_bytes()
    if sha(data)!=PLAN_SHA:raise RuntimeError('Changed rollout allowlist')
    d=json.loads(data)
    if d['base_commit']!=BASE or len(d['files'])!=223 or len(d['selected'])!=226:
        raise RuntimeError('Changed rollout scope')
    return d
@lru_cache(None)
def baseline(path):
    return subprocess.check_output(['git','show',BASE+':experiments/kl-for-mathlib/'+path],cwd=ROOT)
def convert(path,data):
    item=plan()['files'][path]
    if sha(data)!=item['before_sha256']:raise RuntimeError('Changed rollout input: '+path)
    text=data.decode()
    for e in sorted(item['edits'],key=lambda e:e['start'],reverse=True):
        if text[e['start']:e['start']+len(e['old'])]!=e['old']:raise RuntimeError('Rollout edit mismatch')
        text=text[:e['start']]+e['new']+text[e['start']+len(e['old']):]
    if sha(text.encode())!=item['after_sha256']:raise RuntimeError('Changed rollout output')
    return text.encode()
def legacy_source(path,data):
    items=plan()['files']
    if path not in items or not data.startswith(b'module\n'):return data
    delta=0;undo=[]
    for e in sorted(items[path]['edits'],key=lambda e:e['start']):
        undo.append((e['start']+delta,e['new'],e['old']))
        delta+=len(e['new'])-len(e['old'])
    text=data.decode()
    for start,new,old in reversed(undo):
        if text[start:start+len(new)]!=new:raise RuntimeError('Unapproved rollout syntax: '+path)
        text=text[:start]+old+text[start+len(new):]
    return text.encode()
def overlay(files):
    for path,item in plan()['files'].items():
        if files[path]!=baseline(path):raise RuntimeError('Pre-rollout source differs: '+path)
        files[path]=convert(path,files[path])
    return files

def policy():
    d=plan();selected=set(d['selected'])
    for path,item in d['files'].items():
        if sha(baseline(path))!=item['before_sha256']:raise RuntimeError('Changed baseline binding')
        convert(path,baseline(path))
        if any(n.startswith(('OAI.','ForMathlib.')) and n not in selected for n in item['imports']):
            raise RuntimeError('Not a dependency-closed module region: '+path)
    raw=(HERE/'module-rollout-types.json').read_bytes()
    if sha(raw)!=TYPES_SHA:raise RuntimeError('Changed rollout type/name allowlist')
    return d

def expected_types():
    policy();return json.loads((HERE/'module-rollout-types.json').read_text())

def generated_checks():
    from module_integration import PUBLIC_THEOREMS
    selected=plan()['selected']
    imports=''.join('import all '+n+'\n' for n in selected)
    # Explicit implementation access is confined to this independent audit root.
    full='import OAI.Architecture\n'+imports
    exporter=(HERE/'PublicTypes.lean').read_text().replace('import OAI.Architecture','import ImplementationImports',1)
    corpus=(HERE/'SemanticCorpus.lean').read_text().replace('import OAI.Architecture','import ImplementationImports',1)
    return {'ImplementationImports.lean':full,'ImplementationPublicTypes.lean':exporter,
            'ImplementationSemanticCorpus.lean':corpus}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--apply',action='store_true');p.add_argument('--write-checks',action='store_true');a=p.parse_args()
    policy()
    if a.apply:
        for path in plan()['files']:(HERE/path).write_bytes(convert(path,baseline(path)))
    if a.write_checks:
        for path,text in generated_checks().items():(HERE/path).write_text(text)
