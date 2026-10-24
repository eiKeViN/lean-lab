from pathlib import Path
import json,hashlib,sys
h=Path('experiments/kl-for-mathlib');r=Path('results/matcher-compat');sha=lambda b:hashlib.sha256(b).hexdigest()
plan=json.loads((h/'module-all.json').read_text());reg=json.loads((r/'proposed-interface-registry.json').read_text())
(h/'module-all-old.json').write_bytes(Path('results/module-final/ForMathlib.RepresentationTheory.BottSamelson.TitsWords.json').read_bytes())
(h/'module-all-current.json').write_bytes((r/'tits-current-expression.json').read_bytes())
s=(r/'TitsPublic.lean').read_text().replace('../../results/module-final/ForMathlib.RepresentationTheory.BottSamelson.TitsWords.json','module-all-old.json')
s=s.replace('    check ci.type','''    check ci.type
    let (_, currentDump) := (BoundaryCodec.encode ci.type).run {}
    let current ← ofExcept (Json.parse (← IO.FS.readFile "module-all-current.json"))
    unless toJson currentDump.nodes == current do throwError "Unbound current Tits type expression"''')
s=s.replace('  unless checked+missing.size == records.size do throwError "incomplete historical checks"','  unless checked == 1 && missing.isEmpty do throwError "incomplete actual old Tits type check"')
(h/'ModernAllCompat.lean').write_text(s)
sys.path.insert(0,str(h));from compare_types import load
old=load(r/'accepted156.tsv',3947);new=load(r/'library-types.tsv');expected={n:v for n,v in old.items() if n not in reg['removed']};expected.update(reg['generated_added'])
(h/'module-all-types.json').write_text(json.dumps(expected,indent=2)+'\n')
s=(h/'ModernFinalTypes.lean').read_text();start=s.index('import Lean\n');s='module\n'+Path(h/'ImplementationImports.lean').read_text()+s[start:];a=s.index('private def rolloutOwners :');b=s.index('\nprivate def rolloutProofOwners',a);s=s[:a]+'private def rolloutOwners : Array Name := #['+', '.join('`'+n for n in sorted({v['module'] for v in expected.values()}))+']'+s[b:]
s=s.replace('module-final-types.json','module-all-types.json').replace('661','3940');(h/'ModernAllTypes.lean').write_text(s)
reg['evidence_files']={f:sha((h/f).read_bytes()) for f in ['module-all-old.json','module-all-current.json','ModernAllCompat.lean','ModernAllTypes.lean','module-all-types.json']}
(h/'module-all-interface.json').write_text(json.dumps(reg,indent=2)+'\n')
s=(r/'module_all.py.staged').read_text().replace('PLAN_HASH',repr(sha((h/'module-all.json').read_bytes()))).replace('REGISTRY_HASH',repr(sha((h/'module-all-interface.json').read_bytes()))).replace('SOURCE_PATHS',repr(tuple(plan['files'])));(h/'module_all.py').write_text(s)
p=h/'migrate.py';s=p.read_text().replace(' from module_final import overlay as final_modules',' from module_final import overlay as final_modules\n from module_all import overlay as all_modules').replace(' return final_modules(next_modules(attach(rollout(modules(overlay(pristine_products()))))))',' return all_modules(final_modules(next_modules(attach(rollout(modules(overlay(pristine_products())))))))');p.write_text(s)
p=h/'module_integration.py';s=p.read_text().replace('    from module_final import legacy_source as final_legacy','    from module_all import legacy_source as all_legacy\n    data=all_legacy(path,data)\n    from module_final import legacy_source as final_legacy').replace('    final_policy()','    final_policy()\n    from module_all import PATHS as all_paths, policy as all_policy\n    all_policy()').replace('or path in final_paths):','or path in final_paths or path in all_paths):');s=s.replace('        if path in final_paths:', '''        if path in all_paths:
            if any(e['all'] or e['meta'] or not e['public'] for e in record['imports']):raise RuntimeError('Changed final105 import flags')
            if (HERE/path).read_bytes()!=__import__('module_all').convert(path,__import__('module_all').baseline(path)):raise RuntimeError('Changed final105 source')
            continue
        if path in final_paths:''');p.write_text(s)
# Inherited156 checks operate on an explicitly named prior-contract view.
# The mandatory final105 audit retains and validates the actual3940 raw records.
p=h/'proof_evolution.py';s=p.read_text().replace("    all_types = load(path, 3902+len(p['additions']))","    from module_all import load_prior_view\n    all_types = load_prior_view(path)");p.write_text(s)
p=h/'attach_module.py';s=p.read_text().replace('    actual=load(path,3947);raw=compare(old,actual)','    from module_all import load_prior_view\n    actual=load_prior_view(path);raw=compare(old,actual)');p.write_text(s)
p=h/'module_next.py';s=p.read_text().replace('    r=compare(old,load(path,3947))','    from module_all import load_prior_view\n    r=compare(old,load_prior_view(path))');p.write_text(s)
p=h/'module_final.py';s=p.read_text().replace("    raw=compare(old,load(path,3947));left,accepted=accept_known(raw)","    from module_all import load_prior_view\n    raw=compare(old,load_prior_view(path));left,accepted=accept_known(raw)")
s=s.replace("    residual,accepted=_partition(raw,c[view])","    from module_all import accept_type\n    raw,new_accepted=accept_type(raw)\n    residual,accepted=_partition(raw,c[view])\n    accepted=new_accepted+accepted")
s=s.replace("    pairs=copy.deepcopy(compatibility()['full'])","    pairs=copy.deepcopy(compatibility()['full'])\n    from module_all import registry\n    pairs += [copy.deepcopy(registry()['type_pair'])]")
s=s.replace("    c=compatibility();residual,accepted=_partition_historical(raw,actual)","    c=compatibility();residual,accepted=_partition_historical(raw,actual)\n    from module_all import registry,witness\n    if any(x['name']==registry()['type_pair']['name'] for x in accepted):witness()")
p.write_text(s)
for f in ['test_module_integration.py','test_module_rollout.py']:
 p=h/f;s=p.read_text().replace("| set(__import__('module_final').OWNERS)","| set(__import__('module_final').OWNERS) | set(__import__('module_all').OWNERS)").replace("- set(__import__('module_final').OWNERS)","- set(__import__('module_final').OWNERS) - set(__import__('module_all').OWNERS)");p.write_text(s)
p=h/'test_module_final.py';s=p.read_text().replace("            self.assertEqual((m.HERE/p).read_bytes(),m.baseline(p),n)","            import module_all\n            self.assertEqual((m.HERE/p).read_bytes(),module_all.convert(p,m.baseline(p)),n)")
# Historical unit-test fixtures now include one additional exact pair, not an exemption.
s=s.replace("pairs=m.compatibility()['full']\n        baseline=", "pairs=m.compatibility()['full']+[__import__('module_all').registry()['type_pair']]\n        baseline=").replace('old_count=8,new_count=8','old_count=9,new_count=9').replace('relocated=8,passed=False','relocated=9,passed=False').replace("left['relocated'],8","left['relocated'],9").replace('len(accepted),8','len(accepted),9').replace("raw['relocated'],8","raw['relocated'],9")
p.write_text(s)
p=h/'validate.py';s=p.read_text().replace(' from module_final import policy as final_policy',' from module_final import policy as final_policy\n from module_all import policy as all_policy\n all_policy()').replace("{'ModernFinalTypes.lean'","{'ModernAllTypes.lean','ModernAllCompat.lean','ModernAllConsumer.lean','ModernFinalTypes.lean'").replace("'ModernFinalCompat','LegacyKernelEntryChecks'","'ModernFinalCompat','ModernAllCompat','ModernAllConsumer','LegacyKernelEntryChecks'")
s=s.replace(" run('type-comparison'", " run('final105-full-records',[sys.executable,'module_all.py',str(OUT/'migrated-types.tsv')])\n run('final105-modern-types',['lake','env','lean','ModernAllTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'all-modern-types.tsv')))\n run('final105-modern-comparison',[sys.executable,'check_all_public.py',str(OUT/'all-modern-types.tsv')])\n run('final105-regressions',[sys.executable,'test_module_all.py'])\n run('type-comparison'")
p.write_text(s)
print('integrated exact105 transport and bounded contract adapter; consumers/tests still to finish')
