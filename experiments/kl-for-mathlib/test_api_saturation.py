"""Regression checks for bounded round-6 source and declaration policies."""
import copy,unittest
from unittest.mock import patch
import api_saturation as a
class EvolutionPolicy(unittest.TestCase):
 def test_exact_source_roundtrip(self):
  for p in a.plan()['files']:
   old=a.before(p);new=a.apply(p,old)
   self.assertEqual((a.HERE/p).read_bytes(),new)
   self.assertEqual(a.prior_source(p,new),old)
   with self.assertRaises(RuntimeError):a.prior_source(p,new+b'\n')
   with self.assertRaises(RuntimeError):a.apply(p,old+b'\n')
 def test_exact_historical_inputs(self):
  for p,inputs in a.HISTORICAL_INPUTS.items():
   for commit,digest in inputs:
    old=a.before(p,commit)
    self.assertEqual(a.sha(old),digest)
    self.assertEqual(a.prior_source(p,old),old)
    with self.assertRaises(RuntimeError):a.apply(p,old)
    with self.assertRaises(RuntimeError):a.prior_source(p,old+b'\n')
 def test_exact_registry(self):
  records=a.additions();self.assertEqual(a.strip_additions(records),{})
  for n in records:
   changed=copy.deepcopy(records);changed[n]['type']+=' mutation'
   with self.assertRaises(RuntimeError):a.strip_additions(changed)
   missing=dict(records);del missing[n]
   with self.assertRaises(RuntimeError):a.strip_additions(missing)
  extra=dict(records);extra['Unexpected.public.declaration']={'type':'Nat'}
  self.assertIn('Unexpected.public.declaration',a.strip_additions(extra))
if __name__=='__main__':unittest.main()
