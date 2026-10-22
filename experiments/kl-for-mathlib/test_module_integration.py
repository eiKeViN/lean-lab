#!/usr/bin/env python3
"""Adversarial checks for the bounded syntax layer and split public audit."""
import copy,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import module_integration as m

class ModuleIntegrationChecks(unittest.TestCase):
    def test_exact_roundtrip(self):
        m.policy()
        for path in m.SPEC:
            old=m.baseline(path);new=m.convert(path,old)
            self.assertEqual(m.legacy_source(path,new),old)
            self.assertEqual((m.HERE/path).read_bytes(),new)
        self.assertEqual(sum(len(s['expose']) for s in m.SPEC.values()),6)

    def test_reject_other_headers_and_expose_changes(self):
        for path in m.SPEC:
            new=m.convert(path,m.baseline(path))
            for changed in [new.replace(b'public import',b'import',1),
                            new.replace(b'public section',b'public section\npublic section',1)]:
                # Extra public sections survive inversion and are rejected by the
                # exact pre-module hash; they are never treated as harmless syntax.
                try: legacy=m.legacy_source(path,changed)
                except RuntimeError:continue
                self.assertNotEqual(legacy,m.baseline(path))
            if path!=m.S:
                with self.assertRaisesRegex(RuntimeError,'expose'):
                    m.legacy_source(path,new.replace(b'@[expose] def',b'def',1))

    def test_proof_and_statement_edits_not_erased(self):
        old=m.baseline(m.S);new=m.convert(m.S,old)
        for changed in [new.replace(b'(hm : m t=1)',b'(hm : m t=2)',1),
                        new.replace(b'  ring\n',b'  apply id\n  ring\n',1),
                        new+b'\nprivate axiom hidden : False\n']:
            self.assertNotEqual(m.legacy_source(m.S,changed),old)
        untouched='ForMathlib/Algebra/Polynomial/ScaledReciprocity.lean'
        self.assertEqual(m.legacy_source(untouched,new),new)

    def test_manifest_cannot_expand_or_rebind(self):
        original=json.loads((m.HERE/'module-integration.json').read_text())
        for mutate in [lambda d:d['files'].update({'Extra.lean':{}}),
                       lambda d:d['files'][m.S].update(imports=['Mathlib']),
                       lambda d:d['files'][m.K].update(after_sha256='0'*64),
                       lambda d:d.update(base_commit='0'*40)]:
            data=copy.deepcopy(original);mutate(data)
            with tempfile.TemporaryDirectory() as temp:
                root=Path(temp);(root/'module-integration.json').write_text(json.dumps(data))
                with patch.object(m,'HERE',root),self.assertRaises(RuntimeError):m.policy()

    def test_import_flags_and_source_positions(self):
        r=m.imports('/- comment -/\nmodule\npublic meta import A.B\nimport all C.D\n\nnamespace N\n')
        self.assertTrue(r['module'])
        self.assertEqual(r['imports'],[
            dict(module='A.B',public=True,meta=True,all=False,line=3),
            dict(module='C.D',public=False,meta=False,all=True,line=4)])
        self.assertFalse(m.imports('import Mathlib\n')['module'])

    def test_exactly_three_module_nodes(self):
        g=m.graph()
        self.assertEqual({n.replace('.','/')+'.lean' for n,r in g.items() if r['module']},set(m.SPEC))
        self.assertEqual(g['OAI.KL.Compatibility.KernelTransport']['imports'][0]['module'],
                         'ForMathlib.LinearAlgebra.KernelTransport')
        self.assertTrue(g['OAI.KL.Compatibility.KernelTransport']['imports'][0]['public'])

    def test_public_comparator_rejects_missing_extra_kind_and_type(self):
        from compare_types import load_snapshot
        wanted={**load_snapshot(m.HERE/'reference-public-types.json'),
                **json.loads((m.HERE/'additional-types.json').read_text())}
        good={n:wanted[n] for n in m.PUBLIC_THEOREMS+m.PUBLIC_DEFS}
        with patch('compare_types.load',return_value=good):self.assertTrue(m.compare_public('unused')['passed'])
        bad=copy.deepcopy(good);bad.pop(m.PUBLIC_THEOREMS[0])
        extra={**good,'Extra':next(iter(good.values()))}
        for data in [bad,extra]:
            with patch('compare_types.load',return_value=data),self.assertRaises(RuntimeError):m.compare_public('unused')
        for field,value in [('kind','axiom'),('type','0'*64)]:
            data=copy.deepcopy(good);data[m.PUBLIC_THEOREMS[0]][field]=value
            with patch('compare_types.load',return_value=data),self.assertRaises(RuntimeError):m.compare_public('unused')

if __name__=='__main__':unittest.main()
