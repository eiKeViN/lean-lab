#!/usr/bin/env python3
"""Reproduce the staging inventory and dependency evidence, without Lean builds."""
from pathlib import Path
import json,re,statistics
from source_partitions import expand_units
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"scripts"))
from baseline import snapshot
HERE=Path(__file__).resolve().parent
m=json.loads((HERE/'migration.json').read_text())
a=json.loads((HERE/'upstream-assessment.json').read_text())
from proof_evolution import active_modules
from module_integration import graph
import_graph=graph()
(HERE/'module-import-graph.json').write_text(json.dumps(import_graph,indent=2)+'\n')
g={n:x['imports'] for n,x in active_modules(m['modules']).items()}
for name in ['ForMathlib.LinearAlgebra.KernelTransport','OAI.KL.Compatibility.KernelTransport']:
 g[name]=[e['module'] for e in import_graph[name]['imports'] if e['module'].startswith(('OAI.','ForMathlib.'))]
candidate={n for n in g if n.startswith('ForMathlib.')};project=set(g)-candidate
bad=[(n,d) for n in candidate for d in g[n] if d not in candidate]
if bad:raise RuntimeError('Candidate-to-project dependency: '+repr(bad))
lengths={n:len((HERE/(n.replace('.','/')+'.lean')).read_text().splitlines()) for n in g}
metrics=dict(previous_semantic_modules=len(a['modules']),transported_units=len(m['units']),allocated_source_pieces=len(expand_units(m['units'],m.get('unit_partitions',{}),snapshot('transport').read_text)),implementation_modules=len(g),candidate_modules=len(candidate),project_modules_including_kernel_wrapper=len(project),compatibility_import_entries=len(m['legacy_shims']),aggregate_entries=2+len(m.get('entrypoints',{})),total_product_modules=len(g)+len(m['legacy_shims'])+2+len(m.get('entrypoints',{})),core_direct_import_edges=sum(map(len,g.values())),candidate_to_project_edges=bad,physical_implementation_lines=sum(lengths.values()),median_implementation_lines=statistics.median(lengths.values()),module_lines=lengths)
(HERE/'layout-metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
lines=['# Current-content upstream assessment','','All 193 prior semantic modules are indexed below; the generic kernel module is','also staged, while its three-name compatibility wrapper remains project-owned.','These are current dependency-compatible candidates, not accepted or PR-ready','Mathlib additions. Mathematical suitability and present integration are separate.','No future interface extraction is performed. See README and the report for the','official criteria, limitations and family-level reasoning.','','Original source references name the pinned kl-architecture Git tree; declaration names','and line references are evidence for inspecting the actual statements, not a','claim that the first three names exhaust each module. Full spans: MIGRATION.md.','','| Prior semantic module | New home | Current category | Declaration evidence (prior line) |','| --- | --- | --- | --- |']
for x in sorted(a['modules'],key=lambda x:x['module']):
 names=', '.join('`'+d['name']+'`:'+str(d['line']) for d in x['declarations'][:3]) or '(see source spans)'
 lines.append('| [`'+x['module']+'`](https://github.com/eiKeViN/lean-lab/blob/'+a['checkpoint']+'/'+x['source']+') | '+', '.join('`'+n+'`' for n in x['destination'])+' | '+x['classification']+' | '+names+' |')
lines+=['','The full machine-readable inventory, current basis and candidate preparation','items are in `upstream-assessment.json`. ForMathlib → OAI dependencies: **0**.','The 34 original KL import entrypoints plus two kernel import entrypoints are','wrappers, not additional proposed upstream mathematics. Published ForMathlib paths retired by later responsibility refinements also remain compatibility imports; see the current whole-library report.']
(HERE/'CLASSIFICATION.md').write_text('\n'.join(lines)+'\n')
lines=['digraph Staging {','graph [rankdir=LR, label="Imported module → consumer; candidate layer may not import project layer", labelloc=t];','node [shape=box, style=filled, fontsize=9];']
for n in sorted(g):lines.append(json.dumps(n)+' [fillcolor="'+('#dbeafe' if n in candidate else '#fee2e2')+'", label='+json.dumps(n)+'];')
for n,ds in sorted(g.items()):
 for d in ds:
  edge=next(e for e in import_graph[n]['imports'] if e['module']==d)
  flags=', '.join(k for k in ('public','meta','all') if edge[k]) or ('module import' if import_graph[n]['module'] else 'legacy import')
  lines.append(json.dumps(d)+' -> '+json.dumps(n)+' [label='+json.dumps(flags)+'];')
lines.append('}');(HERE/'DEPENDENCIES.dot').write_text('\n'.join(lines)+'\n')
# A current-path guide complements CLASSIFICATION's historical source index.
lines=['# Current module guide','','Use `import OAI.KL` for the application theorem. Use a focused `ForMathlib.*`',
 'module for reusable mathematics. `ForMathlib` imports all candidates and',
 '`OAI.Architecture` imports all implementations for auditing; neither is the',
 'minimal project entrypoint. Compatibility paths are listed separately below.','',
 'The declaration anchors are navigation examples, not an exhaustive API export.',
 'Public-type validation preserves all 3902 baseline declarations and checks every additional type in additional-types.json. Source spans: MIGRATION.md.','']
groups={}
for n in sorted(g):
 group='Application / compatibility implementation' if n.startswith('OAI.') else n.split('.')[1]
 groups.setdefault(group,[]).append(n)
for group,names in groups.items():
 lines+=['## '+group,'','| Current implementation | Declaration anchors |','| --- | --- |']
 for n in names:
  path=n.replace('.','/')+'.lean';text=(HERE/path).read_text()
  anchors=re.findall(r'^\s*(?:@\[expose\]\s+)?(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|lemma|abbrev|instance|structure|class)\s+([^\s:({]+)',text,re.M)
  lines.append('| [`'+n+'`]('+path+') | '+', '.join('`'+a+'`' for a in anchors[:3])+' |')
lines+=['','## Published compatibility imports','','These files contain imports only; implementations use current homes directly.','',
 '| Compatibility path | Current imports |','| --- | --- |']
for n,ds in sorted(m['legacy_shims'].items()):
 lines.append('| [`'+n+'`]('+n.replace('.','/')+'.lean) | '+', '.join('`'+d+'`' for d in ds)+' |')
(HERE/'MODULES.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({k:v for k,v in metrics.items() if k!='module_lines'},indent=2))
