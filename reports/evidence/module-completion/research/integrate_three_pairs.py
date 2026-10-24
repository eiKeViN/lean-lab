from pathlib import Path
import json,hashlib,re
h=Path('experiments/kl-for-mathlib');r=Path('results/matcher-compat');sha=lambda b:hashlib.sha256(b).hexdigest()
(h/'module-all-ordinary-old.json').write_bytes((r/'ordinary-old-batch.json').read_bytes());(h/'module-all-ordinary-current.json').write_bytes((r/'ordinary-current-expressions-complete.json').read_bytes());(h/'module-all-onhom-attributes.json').write_bytes((r/'onhom-old-attribute-values.json').read_bytes())
s=(r/'OrdinaryCompleteHistorical.lean').read_text().replace('../../results/matcher-compat/ordinary-old-batch.json','module-all-ordinary-old.json').replace('../../results/matcher-compat/onhom-old-attribute-values.json','module-all-onhom-attributes.json');s=s.replace('  IO.FS.writeFile "../../results/matcher-compat/ordinary-current-expressions-complete.json" ((toJson current).compress)','''  let bound ← ofExcept (Json.parse (← IO.FS.readFile "module-all-ordinary-current.json"))
  unless toJson current == bound do throwError "Unbound ordinary actual current expressions"''');(h/'ModernOrdinaryAllCompat.lean').write_text(s);(h/'ModernAllConsumer.lean').write_bytes((r/'AllConsumer-v3.lean').read_bytes())
p=h/'module-all-interface.json';c=json.loads(p.read_text());c['type_pairs']=json.loads((r/'complete-raw-diff.json').read_text())['changed'];c.pop('type_pair');c['ordinary_pairs']=json.loads((r/'ordinary-complete-raw-diff.json').read_text())['changed'];c['actual_old_types_checked']=120;c['actual_old_helpers_checked']=53;c['directed_rw_simp_checked']=10
for f in ['module-all-ordinary-old.json','module-all-ordinary-current.json','module-all-onhom-attributes.json','ModernOrdinaryAllCompat.lean','ModernAllConsumer.lean']:c['evidence_files'][f]=sha((h/f).read_bytes())
p.write_text(json.dumps(c,indent=2)+'\n')
p=h/'module_all.py';s=p.read_text();s=re.sub(r"REGISTRY_SHA='[0-9a-f]+'",'REGISTRY_SHA='+repr(sha((h/'module-all-interface.json').read_bytes())),s)
s=s.replace("    subprocess.run(['lake','env','lean','ModernAllCompat.lean'],cwd=HERE,check=True)","    subprocess.run(['lake','env','lean','ModernAllCompat.lean'],cwd=HERE,check=True)\n    subprocess.run(['lake','env','lean','ModernOrdinaryAllCompat.lean'],cwd=HERE,check=True)")
a=s.index('def accept_type(');b=s.index('\ndef compare_full(',a)
s=s[:a]+'''def accept_type(raw):
    c=registry();bound={p['name']:p for p in c['type_pairs']}
    left=copy.deepcopy(raw);left['changed']=[];accepted=[]
    for x in raw['changed']:
        if x['name'] not in bound:left['changed'].append(x);continue
        if x!=bound[x['name']]:raise RuntimeError('Unbound exact final105 type expression')
        accepted.append({'name':x['name'],'old_type':x['old']['type'],'new_type':x['new']['type'],'witness':'ModernOrdinaryAllCompat.lean','raw_difference_retained':True})
    if accepted:witness()
    left['passed']=not(left['missing'] or left['added'] or left['changed'])
    return left,accepted
''' +s[b:]
s=s.replace("'actual_old_types_rechecked':115","'actual_old_types_rechecked':120");s=s.replace("    if len(c['removed'])!=8 or len(c['generated_added'])!=1:","    if len(c['removed'])!=8 or len(c['generated_added'])!=1 or len(c['type_pairs'])!=3 or len(c['ordinary_pairs'])!=12:")
p.write_text(s)
p=h/'module_final.py';s=p.read_text().replace("pairs += [copy.deepcopy(registry()['type_pair'])]","pairs += copy.deepcopy(registry()['type_pairs'])").replace("if any(x['name']==registry()['type_pair']['name'] for x in accepted):witness()","if any(x['name'] in {p['name'] for p in registry()['type_pairs']} for x in accepted):witness()")
# Avoid running the old25 witness solely because a new105 pair was accepted.
s=s.replace("    accepted=new_accepted+accepted\n    if accepted:subprocess.run(['lake','env','lean',c['witness']],cwd=HERE,check=True)\n    return residual,accepted","    if accepted:subprocess.run(['lake','env','lean',c['witness']],cwd=HERE,check=True)\n    return residual,new_accepted+accepted")
p.write_text(s)
p=h/'test_module_final.py';s=p.read_text().replace("+[__import__('module_all').registry()['type_pair']]","+__import__('module_all').registry()['type_pairs']").replace('old_count=9,new_count=9','old_count=11,new_count=11').replace('relocated=9,passed=False','relocated=11,passed=False').replace("left['relocated'],9","left['relocated'],11").replace('len(accepted),9','len(accepted),11').replace("raw['relocated'],9","raw['relocated'],11");p.write_text(s)
p=h/'test_module_all.py';s=p.read_text().replace("p=m.registry()['type_pair']","p=m.registry()['type_pairs'][0]").replace('test_one_full_type_pair_has_no_wildcard','test_exact_full_type_pair_has_no_wildcard');p.write_text(s)
print('three full and twelve ordinary pairs bound to120 actual old types and53 helper values')
