#!/usr/bin/env python3
"""Source/scope/representation regressions for the large closed region."""
from pathlib import Path
import json,unittest,tempfile,copy
from unittest.mock import patch
import module_rollout as m
class RolloutTests(unittest.TestCase):
    def test_exact_complete_region_roundtrips(self):
        d=m.policy();self.assertEqual(len(d['selected']),125);self.assertEqual(len(d['held']),136)
        for path in d['files']:
            before=m.baseline(path);after=m.convert(path,before)
            self.assertEqual((m.HERE/path).read_bytes(),after)
            self.assertEqual(m.legacy_source(path,after),before)
    def test_hashbound_plan_rejects_scope_or_body_changes(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td);raw=(m.HERE/'module-rollout.json').read_bytes();(p/'module-rollout.json').write_bytes(raw+b' ')
            with patch.object(m,'HERE',p),self.assertRaisesRegex(RuntimeError,'allowlist'):m.plan()
        path=next(iter(m.plan()['files']));before=m.baseline(path)
        with self.assertRaises(RuntimeError):m.convert(path,before+b'\n')
        after=m.convert(path,before)
        with self.assertRaises(RuntimeError):m.legacy_source(path,after.replace(b'public import',b'import',1))
    def test_no_private_escape_in_production(self):
        import module_integration as pilot
        g=pilot.graph();self.assertEqual({n for n,r in g.items() if r['module']},set(m.plan()['selected']) | set(__import__('attach_module').OWNERS))
        for n in m.plan()['selected']:
            self.assertFalse(any(e['all'] for e in g[n]['imports']))
        for p in m.plan()['files']:
            self.assertNotIn('backward.privateInPublic',(m.HERE/p).read_text())
    def test_held_boundaries_unchanged(self):
        for name in set(m.plan()['held']) - set(__import__('attach_module').OWNERS):
            path=name.replace('.','/')+'.lean'
            self.assertEqual((m.HERE/path).read_bytes(),m.baseline(path))
    def test_public_policy_is_finite_and_strict(self):
        wanted=m.expected_types();self.assertEqual(len(wanted),1196)
        with patch('compare_types.load',return_value=wanted):self.assertTrue(m.compare_public('unused')['passed'])
        for data in [dict(list(wanted.items())[1:]),{**wanted,'EXTRA':next(iter(wanted.values()))}]:
            with patch('compare_types.load',return_value=data),self.assertRaises(RuntimeError):m.compare_public('unused')
        bad=copy.deepcopy(wanted);n=next(iter(bad));bad[n]['kind']='axiom'
        with patch('compare_types.load',return_value=bad),self.assertRaises(RuntimeError):m.compare_public('unused')
    def test_imports_only_batch_cannot_change_old_headers_or_module_scope(self):
        original=m.narrow_plan();region=m.plan()
        for mutation in ('old_header','module_scope'):
            data=copy.deepcopy(original)
            if mutation=='old_header':
                first=next(iter(m.original_narrow_plan()['files']))
                data['files'][first]['imports'].append('Mathlib')
            else:data['imports_only_batch']['module_scope_unchanged']=126
            raw=(json.dumps(data,indent=2)+'\n').encode()
            with tempfile.TemporaryDirectory() as td:
                root=Path(td);(root/'module-rollout-imports.json').write_bytes(raw)
                with patch.object(m,'HERE',root),patch.object(m,'NARROW_SHA',m.sha(raw)),patch.object(m,'plan',return_value=region):
                    with self.assertRaises(RuntimeError):m.narrow_plan()

    def test_original_implementation_serializer_is_not_changed(self):
        src=(m.HERE/'PublicTypes.lean').read_text()
        full=m.generated_checks()['ImplementationPublicTypes.lean']
        self.assertEqual(full,src.replace('import OAI.Architecture','import ImplementationImports',1))
        modern=m.modern_exporter()
        self.assertIn('rolloutProofAliases.contains n',modern)
        self.assertIn('getOriginalConstKind? env n == some .thm',modern)
        self.assertNotIn('startsWith "_private.ForMathlib."',modern)
if __name__=='__main__':unittest.main()
