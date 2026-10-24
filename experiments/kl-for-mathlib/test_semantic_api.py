"""Reject changes outside the finite experiment and its exact added types."""
import json,tempfile,unittest
from unittest.mock import patch
import semantic_api as a

class BoundedApi(unittest.TestCase):
    def test_source_roundtrip_and_mutations(self):
        for p in a.plan()['files']:
            old=a.original(p);new=a.apply(p,old)
            self.assertEqual(a.prior_source(p,new),old)
            self.assertEqual(a.prior_source(p,old),old)
            for bad in (new+b'\n',new.replace(b'theorem ',b'axiom ',1)):
                if bad!=new:
                    with self.assertRaises(RuntimeError):a.prior_source(p,bad)
            with self.assertRaises(RuntimeError):a.apply(p,old+b'\n')
        self.assertEqual(a.prior_source('Elsewhere.lean',b'arbitrary'),b'arbitrary')

    def test_added_records_exact(self):
        additions={**a.added_types(),**a.generated_types()}
        old={'historical':{'type':'old'}}
        records={**old,**additions}
        with patch('api_evolution.strip_additions',side_effect=lambda r:r),patch('compare_types.load',return_value=records):
            self.assertEqual(a.prior_export('unused',1),old)
        for n in additions:
            bad={**records,n:{**records[n],'kind':'axiom'}}
            with patch('api_evolution.strip_additions',side_effect=lambda r:r),patch('compare_types.load',return_value=bad):
                with self.assertRaises(RuntimeError):a.prior_export('unused',1)
        for bad in ({**records,'unlisted':{}},dict(list(records.items())[:-1])):
            with patch('api_evolution.strip_additions',side_effect=lambda r:r),patch('compare_types.load',return_value=bad):
                with self.assertRaises(RuntimeError):a.prior_export('unused',1)

if __name__=='__main__':unittest.main()
