"""Finite acceptance/source regressions; never run a baseline refresh."""
import copy,json,unittest
from pathlib import Path
import module_final as m

class FinalPolicyTests(unittest.TestCase):
    def test_exact_transport_and_body_identity(self):
        import re
        self.assertEqual(len(m.PATHS),25)
        for p in m.PATHS:
            old=m.baseline(p);new=m.convert(p,old)
            self.assertEqual(m.legacy_source(p,new),old)
            stripped=new.decode().removeprefix('module\n').replace('public import ','import ').replace('\n\npublic section','').replace('@[expose] ','').replace(', expose]',']')
            self.assertEqual(stripped.encode(),old,p)
            with self.assertRaises(RuntimeError):m.legacy_source(p,new+b'\n-- unapproved\n')

    def test_finite_pairs_reject_mutations(self):
        c=m.compatibility()
        for view,count in [('full',8),('ordinary',9)]:
            pairs=c[view];self.assertEqual(len(pairs),count)
            raw=dict(old_count=3947,new_count=3947,missing=[],added=[],relocated=0,changed=copy.deepcopy(pairs),passed=False)
            left,accepted=m._partition(raw,pairs)
            self.assertTrue(left['passed']);self.assertEqual(len(accepted),count)
            self.assertEqual(raw['changed'],pairs)
            for field in ['type','kind','levels','module']:
                bad=copy.deepcopy(raw);bad['changed'][0]['new'][field]+='tampered'
                with self.assertRaises(RuntimeError):m._partition(bad,pairs)
            for key in ['missing','added','relocated']:
                bad=copy.deepcopy(raw);bad[key]=1 if key=='relocated' else ['unapproved']
                with self.assertRaises(RuntimeError):m._partition(bad,pairs)
            bad=copy.deepcopy(raw);bad['changed'][0]['name']='Unapproved.eq_1'
            left,accepted=m._partition(bad,pairs)
            self.assertFalse(left['passed']);self.assertEqual(len(accepted),count-1)

    def test_preexisting_historical_transport_does_not_allow_new_owners(self):
        from unittest.mock import patch
        pairs=m.compatibility()['full']+__import__('module_all').registry()['type_pairs']
        baseline={x['name']:x['old'] for x in pairs}
        actual={x['name']:x['new'] for x in pairs}
        original={n:{**v,'module':'Original.Historical'} for n,v in baseline.items()}
        changes=[{**x,'old':original[x['name']]} for x in pairs]
        raw=dict(old_count=11,new_count=11,missing=[],added=[],changed=changes,relocated=11,passed=False)
        with patch.object(m,'baseline_types',return_value=baseline),patch('compare_types.load_snapshot',return_value=original):
            left,accepted=m._partition_historical(raw,actual)
            self.assertTrue(left['passed']);self.assertEqual(left['relocated'],11);self.assertEqual(len(accepted),11)
            bad=copy.deepcopy(actual);bad[next(iter(bad))]['module']='Unapproved.NewOwner'
            with self.assertRaises(RuntimeError):m._partition_historical(raw,bad)
            bad=copy.deepcopy(raw);bad['relocated']=7
            with self.assertRaises(RuntimeError):m._partition_historical(bad,actual)
            bad=copy.deepcopy(raw);bad['changed'][0]['old']['module']='Wrong.Historical'
            with self.assertRaises(RuntimeError):m._partition_historical(bad,actual)
        self.assertEqual(raw['relocated'],11)

    def test_held_sources_and_existing_policy(self):
        c=m.plan();held=set(c['held_structure_closure'])|set(c['held_matcher_closure'])
        for n in held:
            p=n.replace('.','/')+'.lean'
            import module_all
            self.assertEqual(__import__('semantic_api').prior_source(p,__import__('api_evolution').prior_source(p,(m.HERE/p).read_bytes())),module_all.convert(p,m.baseline(p)),n)
        for p in ['stalk-equation-compat.json','stalk-equation-old.json','StalkEquationCompat.lean','compare_types.py','reference-public-types.json','additional-types.json','module-next-types.json']:
            self.assertEqual((m.HERE/p).read_bytes(),m.baseline(p),p)

if __name__=='__main__':unittest.main()
