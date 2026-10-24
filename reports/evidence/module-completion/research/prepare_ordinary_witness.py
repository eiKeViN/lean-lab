from pathlib import Path
import json
r=Path('results/matcher-compat');groups={p.name.removesuffix('.ordinary-old.json'):json.loads(p.read_text()) for p in r.glob('*.ordinary-old.json')}
def name(a):return '' if not a else (name(a[0])+'.' if a[0] else '')+str(a[1])
aux={name(a[0]):[o,i] for o,d in groups.items() for i,a in enumerate(d['aux'])};order=[];seen=set();active=set();ch={'app':(1,2),'lam':(2,3),'forall':(2,3),'let':(2,3,4),'proj':(3,)}
def visit(n):
 if n in seen:return
 if n in active:raise RuntimeError('helper dependency cycle')
 active.add(n);o,i=aux[n];d=groups[o];todo=[d['aux'][i][2],d['aux'][i][3]];ids=set();deps=set()
 while todo:
  j=todo.pop()
  if j in ids:continue
  ids.add(j);v=d['nodes'][j]
  if v[0]=='const' and name(v[1]) in aux:deps.add(name(v[1]))
  todo.extend(v[k] for k in ch.get(v[0],()))
 for k in sorted(deps):visit(k)
 active.remove(n);seen.add(n);order.append([o,i])
for n in aux:visit(n)
(r/'ordinary-old-batch.json').write_text(json.dumps({'groups':groups,'helpers':groups,'order':order},separators=(',',':')))
s=Path('results/module-final/BatchCompat.lean').read_text();s=s[:s.index('run_elab do')]+Path('results/module-final/prepare_old_data.py').read_text().split("p=r/'BatchCompat.lean';s=p.read_text();s=s[:s.index('run_elab do')]+'''",1)[1].split("''';p.write_text(s)",1)[0]
s=s.replace('import ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic','import ForMathlib')
# Retain ordinary imports; never import all.
s=s.replace('../../results/module-final/batch-old.json','../../results/matcher-compat/ordinary-old-batch.json').replace('BatchOld','AllOld').replace('HistoricalBatchUse','AllHistoricalUse')
s=s.replace('    unless (← ofExcept a[4]!.getStr?) == "theorem" do throwError "unexpected helper kind"\n    addDecl <| .thmDecl {', '    let kind ← ofExcept a[4]!.getStr?\n    if kind == "theorem" then addDecl <| .thmDecl {')
needle='''      value := rename es[vi]!
    }
  for (_, old)'''
s=s.replace(needle,'''      value := rename es[vi]!
    }
    else addDecl <| .defnDecl {
      name := `AllOld ++ n
      levelParams := us
      type := rename es[ti]!
      value := rename es[vi]!
      hints := .opaque
      safety := .safe }
  let mut checked := 0
  let mut current : Array Json := #[]
  for (_, old)''')
s=s.replace('      if user.toString.contains "match_" then continue','      unless toJson (ciDummy := true) == toJson true do pure ()') if False else s
s=s.replace('      if user.toString.contains "match_" then continue\n','')
s=s.replace('      let ci ← getConstInfo n','''      let ci ← getConstInfo n
      unless toJson (ci.levelParams.map nameJson) == a[1]! do throwError "changed universe parameters {user}"
      let (_, dump) := (BoundaryCodec.encode ci.type).run {}
      current := current.push (Json.mkObj [("name",toJson user.toString),("nodes",toJson dump.nodes)])''')
s=s.replace('      addDecl <| .thmDecl {\n        name := historical','      if ← isProp oldType then addDecl <| .thmDecl {\n        name := historical')
s=s.replace('''        value := .const n (ci.levelParams.map .param)
      }
      let axioms''','''        value := .const n (ci.levelParams.map .param)
      }
      else addDecl <| .defnDecl {
        name := historical
        levelParams := ci.levelParams
        type := oldType
        value := .const n (ci.levelParams.map .param)
        hints := .opaque
        safety := .safe }
      checked := checked+1
      let axioms''')
s += '''\n  unless checked == 115 do throwError "incomplete historical ordinary checks"
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative defeq control failed"
  IO.FS.writeFile "../../results/matcher-compat/ordinary-current-expressions.json" ((toJson current).compress)
  logInfo m!"Checked {checked} actual historical types in ordinary modern imports."
'''
(r/'OrdinaryHistorical.lean').write_text(s)
print('old groups',len(groups),'helpers',len(order))
