#!/usr/bin/env python3
"""Small adversarial checks of the actual type-DAG comparator."""
from pathlib import Path
import copy,json,tempfile,unittest
from compare_types import load,compare

def dump(path,sort='Level.zero',binder='BinderInfo.implicit',body=0,kind='theorem',name='Example',offset=0,constant=None):
 rows=[f'MODULE\tOAI.Old',f'NODE\t{offset}\t'+json.dumps(['sort',sort]),f'NODE\t{offset+1}\t'+json.dumps(['bvar',str(body)])]
 if constant is not None:rows[1]=f'NODE\t{offset}\t'+json.dumps(['const',constant,'[]'])
 rows += [f'NODE\t{offset+2}\t'+json.dumps(['forall','_',binder,str(offset),str(offset+1)]),f'TYPE\t{name}\t"[]"\t{offset+2}\t{kind}']
 path.write_text('\n'.join(rows)+'\n')

class ComparatorTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.a=Path(self.tmp.name)/'a';self.b=Path(self.tmp.name)/'b';dump(self.a)
 def accepted(self,**kwargs):
  dump(self.b,**kwargs);return compare(load(self.a),load(self.b))['passed']
 def test_interning_ids_do_not_matter(self):self.assertTrue(self.accepted(offset=91))
 def test_module_relocation_is_not_type_change(self):
  dump(self.b);self.b.write_text(self.b.read_text().replace('OAI.Old','OAI.New'));self.assertTrue(compare(load(self.a),load(self.b))['passed'])
 def test_explicit_implicit_change_fails(self):self.assertFalse(self.accepted(binder='BinderInfo.default'))
 def test_universe_change_fails(self):self.assertFalse(self.accepted(sort='Level.succ Level.zero'))
 def test_bound_variable_change_fails(self):self.assertFalse(self.accepted(body=1))
 def test_constant_change_fails(self):self.assertFalse(self.accepted(constant='Other'))
 def test_kind_change_fails(self):self.assertFalse(self.accepted(kind='axiom'))
 def test_missing_and_added_names_fail(self):self.assertFalse(self.accepted(name='Other'))
 def test_duplicate_name_fails(self):
  dump(self.b);self.b.write_text(self.b.read_text()+self.b.read_text().splitlines()[-1]+'\n')
  with self.assertRaises(ValueError):load(self.b)
if __name__=='__main__':unittest.main()
