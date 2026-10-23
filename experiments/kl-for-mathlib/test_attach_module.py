"""Adversarial guards for the exact three-file and single-equation authorization."""
import copy,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import attach_module as a

class AttachChecks(unittest.TestCase):
    def good(self):
        c=a.compatibility()
        old={'levels':c['levels'],'kind':'theorem','type':c['old_type'],'module':'historical'}
        new={**old,'type':c['new_type'],'module':c['current_owner']}
        return dict(missing=[],added=[],changed=[dict(name=c['name'],field='type',old=old,new=new)],passed=False)
    def test_exact_source_and_inverse(self):
        a.policy()
        for p in a.PATHS:
            old=a.baseline(p);new=a.convert(p,old)
            self.assertEqual((a.HERE/p).read_bytes(),new)
            self.assertEqual(a.legacy_source(p,new),old)
            with self.assertRaises(RuntimeError):a.legacy_source(p,new+b'\n')
            with self.assertRaises(RuntimeError):a.convert(p,old+b'\n')
        self.assertIn("map_add' b c := by ext e",(a.HERE/a.PATHS[0]).read_text())
        self.assertNotIn('import all',(a.HERE/'StalkEquationCompat.lean').read_text())
    def test_exact_pair_requires_live_witness_and_retains_raw_failure(self):
        raw=self.good();snapshot=copy.deepcopy(raw)
        with patch.object(a.subprocess,'check_output',return_value=a.compatibility()['lean_commit']),patch.object(a.subprocess,'run') as run:
            accepted=a.accept_change(raw)
            run.assert_called_once();self.assertTrue(accepted['raw_difference_retained'])
        self.assertEqual(raw,snapshot);self.assertFalse(raw['passed'])
    def test_reject_other_names_fields_levels_kinds_hashes_owners_and_coverage(self):
        cases=[]
        for field in ['name','field']:
            r=self.good();r['changed'][0][field]='OTHER';cases.append(r)
        for side in ['old','new']:
            for field in ['levels','kind','type']:
                r=self.good();r['changed'][0][side][field]='OTHER';cases.append(r)
        r=self.good();r['changed'][0]['new']['module']='OTHER';cases.append(r)
        for key in ['missing','added']:
            r=self.good();r[key]=['OTHER'];cases.append(r)
        r=self.good();r['changed']*=2;cases.append(r)
        for r in cases:
            with patch.object(a.subprocess,'run') as run,self.assertRaises(RuntimeError):a.accept_change(r)
            run.assert_not_called()
    def test_policy_or_proof_data_tampering_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td)
            for f in ['stalk-equation-compat.json','stalk-equation-old.json','StalkEquationCompat.lean']:
                (d/f).write_bytes((a.HERE/f).read_bytes())
            (d/'stalk-equation-old.json').write_bytes(b'{}')
            with patch.object(a,'HERE',d),self.assertRaisesRegex(RuntimeError,'historical'):a.compatibility()
            (d/'stalk-equation-compat.json').write_bytes(b'{}')
            with patch.object(a,'HERE',d),self.assertRaisesRegex(RuntimeError,'authorization'):a.compatibility()

if __name__=='__main__':unittest.main()
