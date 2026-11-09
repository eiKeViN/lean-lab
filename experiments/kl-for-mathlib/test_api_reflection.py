"""Regression checks for bounded round-2 source and declaration policies."""
import copy,unittest
from unittest.mock import patch
import api_reflection as a
class EvolutionPolicy(unittest.TestCase):
 def test_exact_source_roundtrip(self):
  for p in a.plan()['files']:
   old=a.before(p);new=a.apply(p,old)
   self.assertEqual(__import__('api_support').prior_source(p,(a.HERE/p).read_bytes()),new)
   self.assertEqual(a.prior_source(p,new),old)
   with self.assertRaises(RuntimeError):a.prior_source(p,new+b'\n')
   with self.assertRaises(RuntimeError):a.apply(p,old+b'\n')
 @patch('api_support.strip_additions',side_effect=lambda r:r)
 def test_exact_registry(self,_):
  records=a.additions();self.assertEqual(a.strip_additions(records),{})
  for n in records:
   changed=copy.deepcopy(records);changed[n]['type']+=' mutation'
   with self.assertRaises(RuntimeError):a.strip_additions(changed)
   missing=dict(records);del missing[n]
   with self.assertRaises(RuntimeError):a.strip_additions(missing)
  extra=dict(records);extra['Unexpected.public.declaration']={'type':'Nat'}
  self.assertIn('Unexpected.public.declaration',a.strip_additions(extra))
if __name__=='__main__':unittest.main()
