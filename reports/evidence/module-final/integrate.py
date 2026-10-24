from pathlib import Path
import json,hashlib
h=Path('experiments/kl-for-mathlib');r=Path('results/module-final');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
full=json.loads((r/'retained-comparison.json').read_text())['changed'];ordinary=json.loads((r/'final-public-v2-comparison.json').read_text())['changed'];assert len(full)==8 and len(ordinary)==9
cfg=dict(schema=1,lean_commit='5045d0056413266e57c625dcd7c365b10e377c52',mathlib_commit='d13f23b723b8a846827a245b89c10fc7d3f11612',full=full,ordinary=ordinary,old_dag_sha256=sha(h/'module-final-old.json'),current_dag_sha256=sha(h/'module-final-current.json'),witness='ModernFinalCompat.lean',witness_sha256=sha(h/'ModernFinalCompat.lean'),public_witness_sha256=sha(h/'ModernFinalTypes.lean'),scope='Exactly these eight complete/equation and nine ordinary type-expression pairs. All raw comparisons retained. No matcher/name exception or general defeq rule.')
(h/'module-final-compat.json').write_text(json.dumps(cfg,indent=2)+'\n')
s=(h/'module_next.py').read_text();s=s[:s.index('def compare_public')];s=s.replace('Bounded header/exposure-only transport for three graph/sheaf producers.','Exact 25-module transport and finite evidence-bound representation acceptance.')
s=s.replace("BASE='7e28e636991b2205d14199377f33bd025b348b2d'","BASE='0917d25afb52e46cae4233d3056020ed6f881fa3'")
a=s.index('PATHS=');b=s.index('OWNERS=',a);paths=tuple(json.loads((h/'module-final.json').read_text())['files']);s=s[:a]+'PATHS='+repr(paths)+'\n'+s[b:]
s=s.replace('module-next.json','module-final.json').replace('module-next-types.json','module-final-types.json').replace("PLAN_SHA='ef2537574fc266985e13d75e95c65eaa3f261d07a8c53dda8fa5889ddc49ae86'","PLAN_SHA="+repr(sha(h/'module-final.json'))).replace("TYPES_SHA='0279ca1caa3cb055c6859a691ea942f792ff782833523f5c5285c56b396e4489'","TYPES_SHA="+repr(sha(h/'module-final-types.json'))).replace('len(d)!=61','len(d)!=661').replace('three-module','25-module').replace('next-module','final-module')
s+='''COMPAT_SHA=COMPAT_HASH

def compatibility():
    raw=(HERE/'module-final-compat.json').read_bytes()
    if sha(raw)!=COMPAT_SHA:raise RuntimeError('Changed finite batch compatibility policy')
    c=json.loads(raw)
    for file,key in [('module-final-old.json','old_dag_sha256'),('module-final-current.json','current_dag_sha256'),('ModernFinalCompat.lean','witness_sha256'),('ModernFinalTypes.lean','public_witness_sha256')]:
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
'''.replace('COMPAT_HASH',repr(sha(h/'module-final-compat.json')))
# Source policy also binds the finite acceptance fixtures, not just the transport.
s=s.replace('    expected_types()\n','    expected_types()\n    compatibility()\n');(h/'module_final.py').write_text(s)
# Compose source transport and inverse before all prior layers.
p=h/'migrate.py';s=p.read_text().replace(' from module_next import overlay as next_modules',' from module_next import overlay as next_modules\n from module_final import overlay as final_modules').replace(' return next_modules(attach(rollout(modules(overlay(pristine_products())))))',' return final_modules(next_modules(attach(rollout(modules(overlay(pristine_products()))))))');p.write_text(s)
p=h/'module_integration.py';s=p.read_text();s=s.replace('    from module_next import legacy_source as next_legacy','    from module_final import legacy_source as final_legacy\n    data=final_legacy(path,data)\n    from module_next import legacy_source as next_legacy');s=s.replace('    next_policy()','    next_policy()\n    from module_final import PATHS as final_paths, policy as final_policy\n    final_policy()');s=s.replace('or path in next_paths):','or path in next_paths or path in final_paths):');needle='        if path in next_paths:';s=s.replace(needle,'''        if path in final_paths:
            if any(e['all'] or e['meta'] or not e['public'] for e in record['imports']):raise RuntimeError('Changed final-module import flags')
            if (HERE/path).read_bytes()!=__import__('module_final').convert(path,__import__('module_final').baseline(path)):raise RuntimeError('Changed final-module source')
            continue
'''+needle);p.write_text(s)
# Comparisons retain their original raw result and compose exact finite pairs.
p=h/'proof_evolution.py';s=p.read_text();s=s.replace("    try:accepted=[] if result['passed'] else [accept_change(result)]","    from module_final import accept_known\n    remaining,accepted=accept_known(result)\n    try:accepted += [] if remaining['passed'] else [accept_change(remaining)]");p.write_text(s)
p=h/'attach_module.py';s=p.read_text().replace('    accepted=accept_change(raw)\n    return',"    from module_final import accept_known\n    remaining,batch_accepted=accept_known(raw)\n    accepted=accept_change(remaining)\n    return").replace("'accepted_representation_changes':[accepted]","'accepted_representation_changes':[accepted]+batch_accepted");p.write_text(s)
p=h/'module_next.py';s=p.read_text();needle="    if not r['passed'] or r['relocated']:raise RuntimeError('New unaccepted complete-record difference: '+json.dumps(r))\n    return r";assert needle in s;s=s.replace(needle,"    from module_final import accept_known\n    left,accepted=accept_known(r)\n    if not left['passed']:raise RuntimeError('New unaccepted complete-record difference: '+json.dumps(r))\n    return {'raw':r,'accepted_representation_changes':accepted,'passed':True}");p.write_text(s)
# Existing source guards now recognize the exact additive scope.
for n in ['test_module_integration.py','test_module_rollout.py']:
 p=h/n;s=p.read_text();s=s.replace("| set(__import__('module_next').OWNERS)","| set(__import__('module_next').OWNERS) | set(__import__('module_final').OWNERS)").replace("- set(__import__('module_next').OWNERS)","- set(__import__('module_next').OWNERS) - set(__import__('module_final').OWNERS)");p.write_text(s)
p=h/'validate.py';s=p.read_text();s=s.replace("'ModernNextConsumer'","'ModernNextConsumer','ModernFinalCompat'");s=s.replace("run('next-regressions',[sys.executable,'test_module_next.py'])","run('next-regressions',[sys.executable,'test_module_next.py'])\n run('final-full-records',[sys.executable,'module_final.py','--compare-full',str(OUT/'migrated-types.tsv')])\n run('final-modern-types',['lake','env','lean','ModernFinalTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'final-modern-types.tsv')))\n run('final-modern-comparison',[sys.executable,'module_final.py','--compare-public',str(OUT/'final-modern-types.tsv')])\n run('final-regressions',[sys.executable,'test_module_final.py'])")
# Static harness allowlist/policy are adapted after inspecting their exact location.
p.write_text(s)
