#!/usr/bin/env python3
"""Adversarial source/API evolution checks; inherited DAG-reader tests stay intact."""
from pathlib import Path
import copy,json,tempfile,unittest
from unittest.mock import patch
import proof_evolution as ev
import compare_types as types
from migrate import pristine_products

REAL=ev.HERE
PRISTINE=pristine_products()
OLD=types.load_snapshot(REAL/'reference-public-types.json')
ADDED=json.loads((REAL/'additional-types.json').read_text())

class EvolutionChecks(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        for name in ['lemma-pilot.json','proof-evolution.json','proof-evolution.patch','additional-types.json']:
            (self.root/name).write_bytes((REAL/name).read_bytes())
        for path in ev.policy()['pristine_files']:
            target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((REAL/path).read_bytes())
        for name,value in [('HERE',self.root),('POLICY',self.root/'lemma-pilot.json'),('MANIFEST',self.root/'proof-evolution.json')]:
            p=patch.object(ev,name,value);p.start();self.addCleanup(p.stop)

    def bind_sources(self):
        record=json.loads(ev.MANIFEST.read_text());chunks=[]
        for path,item in record['files'].items():
            active=(self.root/path).read_bytes();item['active_sha256']=ev.sha(active)
            chunks.append(ev.difference(path,PRISTINE[path],active))
        delta=''.join(chunks).encode();(self.root/'proof-evolution.patch').write_bytes(delta)
        record['diff_sha256']=ev.sha(delta);ev.MANIFEST.write_text(json.dumps(record))

    def compare_mock(self,current):
        with patch.object(types,'load',return_value=current),patch.object(types,'load_snapshot',return_value=OLD):
            return ev.compare_export('unused.tsv')

    def test_accept_current_explicit_evolution(self):
        ev.overlay(dict(PRISTINE));self.assertTrue(self.compare_mock({**OLD,**ADDED})['passed'])

    def test_reject_unrecorded_source_edit(self):
        path=next(iter(ev.policy()['pristine_files']));f=self.root/path;f.write_text(f.read_text()+'\n')
        with self.assertRaisesRegex(RuntimeError,'Unrecorded active'):ev.overlay(dict(PRISTINE))

    def test_reject_rebound_first_round_source(self):
        path=next(iter(ev.policy()['prior_active_files']));f=self.root/path
        f.write_text(f.read_text()+'\n');self.bind_sources()
        with self.assertRaisesRegex(RuntimeError,'frozen first-round'):ev.overlay(dict(PRISTINE))

    def test_reject_rebound_first_round_type(self):
        f=self.root/'additional-types.json';data=json.loads(f.read_text())
        data[next(iter(data))]['type']='0'*64;f.write_text(json.dumps(data))
        record=json.loads(ev.MANIFEST.read_text());record['additional_types_sha256']=ev.sha(f.read_bytes());ev.MANIFEST.write_text(json.dumps(record))
        with self.assertRaisesRegex(RuntimeError,'retained first-round added types'):
            self.compare_mock({**OLD,**ADDED})

    def test_reject_unlisted_file(self):
        r=json.loads(ev.MANIFEST.read_text());r['files']['Extra.lean']={};ev.MANIFEST.write_text(json.dumps(r))
        with self.assertRaisesRegex(RuntimeError,'allowlist'):ev.overlay(dict(PRISTINE))

    def test_reject_changed_pristine_hash(self):
        data=dict(PRISTINE);path=next(iter(ev.policy()['pristine_files']));data[path]+=b'\n'
        with self.assertRaisesRegex(RuntimeError,'Pristine reconstruction'):ev.overlay(data)

    def test_reject_truncated_diff(self):
        f=self.root/'proof-evolution.patch';f.write_bytes(f.read_bytes()[:-1])
        with self.assertRaisesRegex(RuntimeError,'diff'):ev.overlay(dict(PRISTINE))

    def test_reject_rebound_old_statement(self):
        f=self.root/'ForMathlib/Algebra/BigOperators/SingleCoordinate.lean';text=f.read_text()
        self.assertIn('(hm : m t=1)',text);f.write_text(text.replace('(hm : m t=1)','(hm : m t=2)',1));self.bind_sources()
        with patch.object(ev,'edit_scope',return_value=None), patch.object(ev,'check_prior_source',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'Changed old theorem statement'):ev.overlay(dict(PRISTINE))

    def test_reject_rebound_unsampled_proof_edit(self):
        f=self.root/'ForMathlib/Algebra/BigOperators/SingleCoordinate.lean';text=f.read_text()
        self.assertIn("exact sub_le_sub hp hp'.ge",text)
        f.write_text(text.replace("exact sub_le_sub hp hp'.ge","simpa using sub_le_sub hp hp'.ge",1));self.bind_sources()
        with patch.object(ev,'check_prior_source',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'outside approved'):ev.overlay(dict(PRISTINE))

    def test_reject_rebound_expansion_unsampled_proof(self):
        f=self.root/'ForMathlib/LinearAlgebra/Dual/IntegralSupport.lean';text=f.read_text()
        self.assertIn('simp [h]',text)
        f.write_text(text.replace('simp [h]','simpa [h]',1));self.bind_sources()
        with self.assertRaisesRegex(RuntimeError,'outside approved'):ev.overlay(dict(PRISTINE))

    def test_reject_rebound_expansion_statement(self):
        f=self.root/'ForMathlib/LinearAlgebra/Reflection/Plane.lean';text=f.read_text()
        needle='(hfg : LinearIndependent k ![f, g]) :\n    LinearMap.range'
        self.assertIn(needle,text)
        f.write_text(text.replace(needle,'(hfg : LinearIndependent k ![g, f]) :\n    LinearMap.range',1));self.bind_sources()
        with patch.object(ev,'edit_scope',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'Changed old theorem statement'):ev.overlay(dict(PRISTINE))

    def test_reject_rebound_private_axiom(self):
        path=next(iter(ev.policy()['pristine_files']));f=self.root/path;f.write_text(f.read_text()+'\nprivate axiom hidden : False\n');self.bind_sources()
        with patch.object(ev,'edit_scope',return_value=None), patch.object(ev,'check_prior_source',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'proof-bypass'):ev.overlay(dict(PRISTINE))

    def test_reject_new_global_attribute(self):
        path=next(iter(ev.policy()['pristine_files']));f=self.root/path;f.write_text(f.read_text()+'\nattribute [simp] Nat.add_comm\n');self.bind_sources()
        with patch.object(ev,'edit_scope',return_value=None), patch.object(ev,'check_prior_source',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'attributes'):ev.overlay(dict(PRISTINE))

    def test_reject_missing_old_api(self):
        current={**OLD,**ADDED};current.pop(next(iter(OLD)))
        with self.assertRaisesRegex(RuntimeError,'Missing old API'):self.compare_mock(current)

    def test_reject_unlisted_addition(self):
        current={**OLD,**ADDED,'Unlisted':next(iter(ADDED.values()))}
        with self.assertRaisesRegex(RuntimeError,'unlisted'):self.compare_mock(current)

    def test_reject_changed_old_type(self):
        current=copy.deepcopy({**OLD,**ADDED});current[next(iter(OLD))]['type']='0'*64
        with self.assertRaisesRegex(RuntimeError,'Old API'):self.compare_mock(current)

    def test_reject_changed_new_type_or_kind(self):
        for field,value in [('type','0'*64),('kind','axiom')]:
            current=copy.deepcopy({**OLD,**ADDED});current[next(iter(ADDED))][field]=value
            with self.assertRaisesRegex(RuntimeError,'explicit added types'):self.compare_mock(current)

    def test_reject_unbound_new_snapshot(self):
        f=self.root/'additional-types.json';f.write_text(f.read_text()+' ')
        with self.assertRaisesRegex(RuntimeError,'Unbound'):self.compare_mock({**OLD,**ADDED})

    def test_reject_empty_and_truncated_exports(self):
        for text in ['', 'FORMAT\tkl-public-types-v3\n']:
            f=self.root/'bad.tsv';f.write_text(text)
            with self.assertRaises(ValueError):ev.compare_export(f)

    def test_reject_missing_or_extra_axiom_records(self):
        p=ev.policy();good=''.join("'"+n+"' depends on axioms: [propext]\n" for n in p['additions']+p['changed_declarations'])
        ev.check_pilot_axioms(good)
        with self.assertRaises(RuntimeError):ev.check_pilot_axioms('')
        with self.assertRaises(RuntimeError):ev.check_pilot_axioms(good+good.splitlines()[0]+'\n')
        with self.assertRaises(RuntimeError):ev.check_pilot_axioms(good.replace('propext','badAxiom',1))

if __name__=='__main__':unittest.main()
