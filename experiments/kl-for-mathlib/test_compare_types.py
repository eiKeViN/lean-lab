#!/usr/bin/env python3
"""Small adversarial checks of the actual type-DAG comparator."""
from pathlib import Path
import copy,json,tempfile,unittest
from compare_types import load,load_snapshot,compare,FORMAT

def dump(path,sort='Level.zero',binder='BinderInfo.implicit',body=0,kind='theorem',name='Example',offset=0,constant=None):
 rows=['FORMAT\t'+FORMAT,f'MODULE\tOAI.Old',f'NODE\t{offset}\t'+json.dumps(['sort',sort]),f'NODE\t{offset+1}\t'+json.dumps(['bvar',str(body)])]
 if constant is not None:rows[2]=f'NODE\t{offset}\t'+json.dumps(['const',constant,'[]'])
 rows += [f'NODE\t{offset+2}\t'+json.dumps(['forall','_',binder,str(offset),str(offset+1)]),f'TYPE\t{name}\t"[]"\t{offset+2}\t{kind}']
 rows+=['PRIVATE_SUMMARY\t0\t0\t0\t0','SUMMARY\t1\t0\t0']
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
 def test_constant_change_fails(self):
  dump(self.a,constant='Original');self.assertFalse(self.accepted(constant='Other'))
 def test_kind_change_fails(self):self.assertFalse(self.accepted(kind='axiom'))
 def test_missing_and_added_names_fail(self):self.assertFalse(self.accepted(name='Other'))
 def test_duplicate_name_fails(self):
  dump(self.b);text=self.b.read_text();row=next(x for x in text.splitlines() if x.startswith('TYPE\t'));self.b.write_text(text.replace('PRIVATE_SUMMARY','MODULE\tOAI.Old\n'+row+'\nPRIVATE_SUMMARY',1))
  with self.assertRaises(ValueError):load(self.b)
 def proof_dump(self,path,proposition='P',binder='kernel',share=False):
  nodes=[['const',proposition,'[]'],['bvar','0'],['forall','_',binder,'0','1'],['proof','2'],['const','F','[]'],['app','4','3']]
  if share:nodes.append(['app','5','2'])
  rows=['FORMAT\t'+FORMAT,'MODULE\tOAI.Test']+[f'NODE\t{i}\t'+json.dumps(v) for i,v in enumerate(nodes)]
  rows.append(f'TYPE\tExample\t"[]"\t{len(nodes)-1}\ttheorem');rows+=['PRIVATE_SUMMARY\t0\t0\t0\t0','SUMMARY\t1\t0\t0'];path.write_text('\n'.join(rows)+'\n')
 def test_proof_proposition_change_fails(self):
  self.proof_dump(self.a,'P');self.proof_dump(self.b,'Q');self.assertFalse(compare(load(self.a),load(self.b))['passed'])
 def test_proof_context_is_accepted(self):
  self.proof_dump(self.a);self.proof_dump(self.b);self.assertTrue(compare(load(self.a),load(self.b))['passed'])
 def test_noncanonical_proof_binder_fails(self):
  self.proof_dump(self.b,binder='BinderInfo.implicit')
  with self.assertRaises(ValueError):load(self.b)
 def test_shared_node_context_leak_fails(self):
  self.proof_dump(self.b,share=True)
  with self.assertRaises(ValueError):load(self.b)
 def test_public_kernel_metadata_fails(self):
  dump(self.b,binder='kernel')
  with self.assertRaises(ValueError):load(self.b)
 def reject_text(self,text):
  self.b.write_text(text)
  with self.assertRaises((ValueError,KeyError)):load(self.b)
 def test_empty_input_fails(self):self.reject_text('')
 def test_two_empty_dictionaries_fail(self):self.assertFalse(compare({},{})['passed'])
 def test_empty_complete_export_fails(self):self.reject_text('FORMAT\t'+FORMAT+'\nPRIVATE_SUMMARY\t0\t0\t0\t0\nSUMMARY\t0\t0\t0\n')
 def test_missing_summary_fails(self):self.reject_text(self.a.read_text().rsplit('SUMMARY\t1',1)[0])
 def test_truncated_summary_fails(self):self.reject_text(self.a.read_text().replace('SUMMARY\t1\t0\t0','SUMMARY\t1\t0'))
 def test_missing_type_fails(self):self.reject_text('\n'.join(x for x in self.a.read_text().splitlines() if not x.startswith('TYPE\t'))+'\n')
 def test_wrong_public_count_fails(self):self.reject_text(self.a.read_text().replace('SUMMARY\t1\t0\t0','SUMMARY\t2\t0\t0'))
 def test_wrong_copy_count_fails(self):self.reject_text(self.a.read_text().replace('SUMMARY\t1\t0\t0','SUMMARY\t1\t1\t0'))
 def test_wrong_proof_alias_count_fails(self):self.reject_text(self.a.read_text().replace('SUMMARY\t1\t0\t0','SUMMARY\t1\t0\t1'))
 def test_records_after_summary_fail(self):self.reject_text(self.a.read_text()+'NODE\t99\t["bvar","0"]\n')
 def test_missing_format_fails(self):self.reject_text('\n'.join(self.a.read_text().splitlines()[1:])+'\n')
 def test_orphan_module_fails(self):self.reject_text(self.a.read_text().replace('PRIVATE_SUMMARY','MODULE\tOAI.Other\nPRIVATE_SUMMARY',1))
 def test_unknown_record_fails(self):self.reject_text(self.a.read_text().replace('PRIVATE_SUMMARY','UNKNOWN\t0\nPRIVATE_SUMMARY',1))
 def test_independent_coverage_fails(self):
  with self.assertRaises(ValueError):load(self.a,expected_count=3902)
 def test_reference_snapshot_count_checked(self):
  obj={'schema':3,'public_count':1,'private_canonical_rewrites':[],'types':load(self.a)};self.b.write_text(json.dumps(obj));self.assertEqual(load_snapshot(self.b,1),obj['types'])
  with self.assertRaises(ValueError):load_snapshot(self.b)
 def test_empty_reference_snapshot_fails(self):
  self.b.write_text(json.dumps({'schema':3,'public_count':3902,'private_canonical_rewrites':[],'types':{}}))
  with self.assertRaises(ValueError):load_snapshot(self.b)
 def test_nonempty_private_rewrite_fails(self):
  text=self.a.read_text().replace('PRIVATE_SUMMARY\t0\t0\t0\t0','PRIVATE_CANONICAL\t_private.OAI.X.0.P\tP\nPRIVATE_SUMMARY\t1\t0\t0\t0')
  self.reject_text(text)
if __name__=='__main__':unittest.main()
