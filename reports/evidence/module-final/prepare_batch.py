from pathlib import Path
import json,re,hashlib,difflib,subprocess
root=Path.cwd();here=root/'experiments/kl-for-mathlib';G=json.loads((here/'module-import-graph.json').read_text());held={'ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure'}
while True:
 h=held|{n for n,d in G.items() if any(e['module'] in held for e in d['imports'])}
 if h==held:break
 held=h
selected=sorted(n for n,d in G.items() if not d['module'] and n not in held)
plan={'schema':1,'base_commit':'0917d25afb52e46cae4233d3056020ed6f881fa3','held_structure_closure':sorted(held),'files':{}}
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
for n in selected:
 p=n.replace('.','/')+'.lean';f=here/p;s=subprocess.check_output(['git','show','0917d25:experiments/kl-for-mathlib/'+p],text=True);t=re.sub(r'(?m)^import ', 'public import ',s)
 end=list(re.finditer(r'(?m)^public import [^\n]+',t))[-1].end();t=t[:end]+'\n\npublic section'+t[end:]
 t=re.sub(r'(?m)^([ \t]*)(?=(?:(?:noncomputable|protected|unsafe)\s+)*def\s)',r'\1@[expose] ',t)
 # Keep existing instance_reducible attribute and expose in the same group.
 t=re.sub(r'@\[([^\]\n]+)\]\s*\n([ \t]*)@\[expose\]',lambda m:'@['+m[1]+', expose]\n'+m[2],t)
 t=re.sub(r'@\[([^\]\n]+)\] (?=(?:(?:noncomputable|protected|unsafe)\s+)*def\s)',lambda m:'@['+m[1]+(', expose' if 'expose' not in m[1] else '')+'] ',t)
 t='module\n'+t
 sl=s.splitlines(keepends=True);tl=t.splitlines(keepends=True)
 edits=[dict(start=sum(map(len,sl[:i])),old=''.join(sl[i:j]),new=''.join(tl[a:b])) for op,i,j,a,b in difflib.SequenceMatcher(None,sl,tl,autojunk=False).get_opcodes() if op!='equal']
 plan['files'][p]={'before_sha256':sha(s),'after_sha256':sha(t),'edits':edits}
 f.write_text(t)
(here/'module-final.json').write_text(json.dumps(plan,indent=2)+'\n')
(root/'results/module-final/first-scope.json').write_text(json.dumps(plan,indent=2)+'\n')
# Separate the candidate roots from the downstream integration build.
roots=[n for n in selected if n.startswith('ForMathlib.')];(root/'results/module-final/roots.json').write_text(json.dumps(roots,indent=2)+'\n')
print('candidate',len(selected),'first library roots',len(roots),'held',len(held))
