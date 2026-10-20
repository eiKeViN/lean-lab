#!/usr/bin/env python3
"""Reproduce module-size, dependency-closure evidence and the exact core DOT graph."""
from pathlib import Path
import collections,json,re,statistics,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
m=json.loads((HERE/'migration.json').read_text());ref=ROOT/m['reference'];old={}
for p in (ref/'OAI').rglob('*.lean'):
 n=p.relative_to(ref).with_suffix('').as_posix().replace('/','.')
 old[n]=re.findall(r'^import (OAI\..+)$',p.read_text(),re.M)
new={n:x['imports'] for n,x in m['modules'].items()}
for n in ('OAI.LinearAlgebra.KernelTransport','OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat'):new[n]=old[n]
consumers=collections.defaultdict(list)
for n,ds in new.items():
 for d in ds:consumers[d].append(n)
def closure(g,n):
 seen=set();todo=[n]
 while todo:
  x=todo.pop()
  if x not in seen:seen.add(x);todo+=g.get(x,[])
 return sorted(seen)
lengths={n:len((HERE/(n.replace('.','/')+'.lean')).read_text().splitlines()) for n in m['modules']}
cases=[]
for a,b in [('BottSamelson','OAI.Algebra.Module.CoefficientChange.Basic'),('CharacterReciprocity','OAI.Combinatorics.MomentGraph.Sheaf.Models'),('Tits','OAI.GroupTheory.Coxeter.Realization.Tits'),('CanonicalKL','OAI.Data.Polynomial.LowPart'),('PlaneLocalization','OAI.LinearAlgebra.SymmetricAlgebra.Quotient')]:
 a='OAI.RepresentationTheory.KazhdanLusztig.'+a
 cases.append(dict(old_entry=a,new_entry=b,old_OAI_closure=closure(old,a),new_OAI_closure=closure(new,b)))
metrics=dict(semantic_modules=len(lengths),stable_modules=2,legacy_shims=len(m['legacy_shims']),transported_units=len(m['units']),physical_lines=sum(lengths.values()),median_lines=statistics.median(lengths.values()),minimum_lines=min(lengths.values()),maximum_lines=max(lengths.values()),below_40_lines=sum(x<40 for x in lengths.values()),below_60_lines=sum(x<60 for x in lengths.values()),below_100_lines=sum(x<100 for x in lengths.values()),original_direct_OAI_edges=sum(map(len,old.values())),semantic_core_direct_OAI_edges=sum(map(len,new.values())),closure_examples=cases,small_modules=[dict(module=n,lines=l,direct_semantic_consumers=consumers[n]) for n,l in sorted(lengths.items(),key=lambda p:p[1]) if l<60])
(HERE/'architecture-metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
colors={'OAI.Algebra':'#dbeafe','OAI.LinearAlgebra':'#dbeafe','OAI.Data':'#dbeafe','OAI.RingTheory':'#dbeafe','OAI.Order':'#dbeafe','OAI.GroupTheory':'#dcfce7','OAI.Combinatorics':'#fef3c7','OAI.RepresentationTheory.Hecke':'#ede9fe','OAI.RepresentationTheory.BottSamelson':'#fce7f3','OAI.RepresentationTheory.KazhdanLusztig':'#fee2e2'}
lines=['digraph KL {','graph [rankdir=LR, bgcolor="white", nodesep=0.18, ranksep=0.45, label="KL semantic core: imported module → consumer (193 migrated + 2 stable modules)", labelloc=t, fontsize=20];','node [shape=box, style="rounded,filled", fontname="sans-serif", fontsize=9];','edge [color="#94a3b8", arrowsize=0.5];']
for n in sorted(new):
 parts=n.split('.')[1:];cut=max(1,len(parts)-2);label='/'.join(parts[:cut])+'\n'+'/'.join(parts[cut:]);color=next((v for k,v in reversed(list(colors.items())) if n.startswith(k)),'#f1f5f9')
 lines.append(json.dumps(n)+' [label='+json.dumps(label)+', fillcolor='+json.dumps(color)+', tooltip='+json.dumps(n)+'];')
for n,ds in sorted(new.items()):
 for d in ds:lines.append(json.dumps(d)+' -> '+json.dumps(n)+';')
lines.append('}');(HERE/'DEPENDENCIES.dot').write_text('\n'.join(lines)+'\n')
print(json.dumps({k:v for k,v in metrics.items() if k not in ('closure_examples','small_modules')},indent=2))
