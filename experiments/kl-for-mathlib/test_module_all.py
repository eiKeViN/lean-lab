"""Fail-closed source/name/type boundaries for the final105 migration."""
import copy,json,re,unittest
from unittest.mock import patch
import module_all as m
from compare_types import compare
class AllPolicyTests(unittest.TestCase):
 def test_exact105_body_transport(self):
  self.assertEqual(len(m.PATHS),105)
  for p in m.PATHS:
   old=m.baseline(p);new=m.convert(p,old)
   self.assertEqual(m.legacy_source(p,new),old)
   stripped=new.decode().removeprefix('module\n').replace('public import ','import ').replace('\n\npublic section','').replace('@[expose] ','').replace(', expose]',']')
   if p.endswith('/Sheaf/Structure.lean'):
    inline='((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap)'
    self.assertEqual(stripped.count(inline),2)
    stripped=stripped.replace(inline,'(quotientLinear α e)')
    self.assertIn('private def quotientLinear',stripped)
   self.assertEqual(stripped.encode(),old,p)
   with self.assertRaises(RuntimeError):m.legacy_source(p,new+b'\n-- unapproved\n')
 def test_exact_eight_names_and_one_generated_addition(self):
  old=m.baseline_types();c=m.registry();actual={n:v for n,v in old.items() if n not in c['removed']};actual.update(c['generated_added'])
  self.assertEqual(len(actual),3940);self.assertEqual(m.prior_view(actual),old)
  for action in ['missing','extra','restore_removed','generated_type','generated_owner','retained_owner']:
   bad=copy.deepcopy(actual)
   if action=='missing':bad.pop(next(n for n in bad if n not in c['generated_added']))
   if action=='extra':bad['Unexpected.match_999']=next(iter(bad.values()))
   if action=='restore_removed':n=next(iter(c['removed']));bad[n]=c['removed'][n]
   if action.startswith('generated_'):
    n=next(iter(c['generated_added']));bad[n]['type' if action=='generated_type' else 'module']='changed'
   if action=='retained_owner':n=next(n for n in bad if n not in c['generated_added']);bad[n]['module']='Other'
   with self.assertRaises(RuntimeError):m.prior_view(bad)
 def test_exact_full_type_pair_has_no_wildcard(self):
  self.assertEqual(len(m.registry()['type_pairs']),3)
  for p in m.registry()['type_pairs']:
   r=dict(old_count=3947,new_count=3947,missing=[],added=[],changed=[copy.deepcopy(p)],relocated=0,passed=False)
   with patch.object(m,'witness'):
    left,accepted=m.accept_type(r);self.assertTrue(left['passed']);self.assertEqual(len(accepted),1)
    for side in ['old','new']:
     for key in ['type','kind','levels','module']:
      bad=copy.deepcopy(r);bad['changed'][0][side][key]='changed'
      with self.assertRaises(RuntimeError):m.accept_type(bad)
    bad=copy.deepcopy(r);bad['changed'][0]['name']='Different.eq_1';left,accepted=m.accept_type(bad);self.assertFalse(left['passed']);self.assertFalse(accepted)
   self.assertEqual(r['changed'],[p])
 def test_exact_twelve_ordinary_pairs_reject_other_changes(self):
  c=m.registry();self.assertEqual(len(c['ordinary_pairs']),12)
  expected=json.loads((m.HERE/'module-all-types.json').read_text());actual=copy.deepcopy(expected)
  for p in c['ordinary_pairs']:actual[p['name']]=p['new']
  with patch('compare_types.load',return_value=actual),patch('subprocess.run'),patch('subprocess.check_output',return_value=c['lean_commit']):
   self.assertTrue(m.compare_public('unused')['passed'])
  for p in c['ordinary_pairs']:
   for field in ['type','kind','levels','module']:
    bad=copy.deepcopy(actual);bad[p['name']][field]='changed'
    with patch('compare_types.load',return_value=bad),self.assertRaises(RuntimeError):m.compare_public('unused')
  for action in ['drop_pair','missing','extra']:
   bad=copy.deepcopy(actual);n=c['ordinary_pairs'][0]['name']
   if action=='drop_pair':bad[n]=expected[n]
   if action=='missing':bad.pop(n)
   if action=='extra':bad['Unapproved.match_99']=bad[n]
   with patch('compare_types.load',return_value=bad),self.assertRaises(RuntimeError):m.compare_public('unused')

 def test_ordinary_exporter_retains_exact_alias_guard(self):
  old=(m.HERE/'ModernFinalTypes.lean').read_text();new=(m.HERE/'ModernAllTypes.lean').read_text()
  line=lambda s,n:next(x for x in s.splitlines() if x.startswith('private def '+n+' :'))
  self.assertEqual(line(old,'rolloutProofAliases'),line(new,'rolloutProofAliases'))
  self.assertEqual(len(re.findall(r'`[A-Za-z0-9_.]+',line(new,'rolloutProofAliases'))),150)
  self.assertEqual(len(re.findall(r'`[A-Za-z0-9_.]+',line(new,'rolloutProofOwners'))),261)
  self.assertIn('getOriginalConstKind? env n == some .thm',new)
  self.assertIn('owned && rolloutProofAliases.contains n',new)
  self.assertNotIn('import all ',new)
  self.assertNotIn('startsWith "_private.ForMathlib."',new)
 def test_no_compatibility_patch_or_old_policy_refresh(self):
  for p in m.PATHS:
   self.assertNotIn('kernel-checked public copies',(m.HERE/p).read_text())
  for p in ['compare_types.py','reference-public-types.json','additional-types.json','stalk-equation-compat.json','StalkEquationCompat.lean','module-final-compat.json','module-final-old.json','module-final-current.json']:
   self.assertEqual((m.HERE/p).read_bytes(),m.baseline(p),p)
if __name__=='__main__':unittest.main()
