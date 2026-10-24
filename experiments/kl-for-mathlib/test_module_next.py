import copy,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import module_next as m

class NextChecks(unittest.TestCase):
    def test_exact_header_transport_and_no_body_edit(self):
        m.policy()
        import re
        for p in m.PATHS:
            old=m.baseline(p);new=m.convert(p,old)
            self.assertEqual(__import__('api_support').prior_source(p,(m.HERE/p).read_bytes()),new)
            self.assertEqual(m.legacy_source(p,new),old)
            strip=lambda b:re.sub(rb'(?m)^public import ',b'import ',b).replace(b'module\n',b'',1).replace(b'public section\n\n',b'',1).replace(b'@[expose] ',b'')
            self.assertEqual(strip(new),old)
            with self.assertRaises(RuntimeError):m.legacy_source(p,new+b'\n')
            with self.assertRaises(RuntimeError):m.convert(p,old+b'\n')
    def test_public_scope_is_strict(self):
        wanted=m.expected_types()
        with patch('compare_types.load',return_value=wanted):self.assertTrue(m.compare_public('unused')['passed'])
        for mutate in ['missing','added','type','kind','levels','owner']:
            d=copy.deepcopy(wanted);n=next(iter(d))
            if mutate=='missing':d.pop(n)
            elif mutate=='added':d['EXTRA']=d[n]
            else:d[n]['module' if mutate=='owner' else mutate]='OTHER'
            with patch('compare_types.load',return_value=d),self.assertRaises(RuntimeError):m.compare_public('unused')
    def test_vertex_and_single_equation_policy_remain_bound(self):
        import subprocess
        p='ForMathlib/Combinatorics/MomentGraph/OrderedGraph/VertexDeletion.lean'
        self.assertEqual((m.HERE/p).read_bytes(),__import__('module_final').convert(p,__import__('module_final').baseline(p)))
        old_attach=subprocess.check_output(['git','show',m.BASE+':experiments/kl-for-mathlib/attach_module.py'],cwd=m.ROOT).decode()
        current_attach=(m.HERE/'attach_module.py').read_text()
        part=lambda s:s[s.index('def accept_change('):s.index('def compare_full(')]
        self.assertEqual(part(current_attach),part(old_attach))
        for f in ['stalk-equation-compat.json','stalk-equation-old.json','StalkEquationCompat.lean','compare_types.py']:
            self.assertEqual((m.HERE/f).read_bytes(),subprocess.check_output(['git','show',m.BASE+':experiments/kl-for-mathlib/'+f],cwd=m.ROOT))

if __name__=='__main__':unittest.main()
