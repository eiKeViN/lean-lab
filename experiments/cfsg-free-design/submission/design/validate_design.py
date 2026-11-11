"""Check this proposal's bookkeeping and local source hashes, never Lean correctness."""
import hashlib
import json
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
SOURCES=ROOT/'sources'
ledger=json.loads((ROOT/'design/obligations.json').read_text())
packages=ledger['packages']; by_id={p['id']:p for p in packages}
assert len(by_id)==len(packages), 'Duplicate package IDs'
visited=set(); active=set(); order=[]
def visit(i):
 assert i in by_id, f'Unknown dependency {i}'
 assert i not in active, f'Cycle at {i}'
 if i in visited: return
 active.add(i)
 for dep in by_id[i]['depends_on']: visit(dep)
 active.remove(i); visited.add(i); order.append(i)
visit('Z02')
assert len(visited)==len(packages), 'Packages disconnected from final delivery'
index=(SOURCES/'TauCeti/GroupTheory/SpecificGroups/CFSG/Index.lean').read_text()
lie_block=index.split('inductive LieTypeIndex where',1)[1].split('deriving DecidableEq',1)[0]
lie=set(re.findall(r'^  \| (\w+)',lie_block,re.M))
sporadic_block=index.split('inductive SporadicName where',1)[1].split('deriving DecidableEq',1)[0]
sporadics=set(re.findall(r'\|\s*(\w+)',sporadic_block))
assert lie==set(ledger['lie_family_owner']), 'Lie constructor coverage mismatch'
assert sporadics==set(ledger['sporadic_owner']), 'Sporadic constructor coverage mismatch'
for owner in [*ledger['lie_family_owner'].values(),*ledger['sporadic_owner'].values()]:
 assert owner in by_id
manifest=json.loads((SOURCES/'source-manifest.json').read_text())
for row in manifest:
 p=SOURCES/row['path']; assert p.is_file(), f'Missing {p}'
 data=p.read_bytes()
 assert len(data)==row['bytes'], f'Byte count mismatch: {p}'
 assert hashlib.sha256(data).hexdigest()==row['sha256'], f'Hash mismatch: {p}'
assert (ROOT/'PLAN.zh-CN.md').is_file(), 'Missing requested proposal'
bib=(SOURCES/'bibliography.bib').read_text()
report=dict(check_scope='proposal bookkeeping and supplied source hashes only; no Lean executable invoked',
 work_packages=len(packages),all_reachable_from_final=True,dependency_graph_acyclic=True,
 lie_constructors_covered=len(lie),sporadic_constructors_covered=len(sporadics),
 source_manifest_entries_verified=len(manifest),mathlib_inventory_paths=len((SOURCES/'mathlib-paths.txt').read_text().splitlines()),
 bibliography_entries=len(re.findall(r'@\w+\s*\{',bib)),topological_order=order,
 mathematical_route_verified=False,lean_kernel_checked=False)
(ROOT/'design/review-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='topological_order'},ensure_ascii=False,indent=2))
