from pathlib import Path
import json
r=Path('results/module-final');groups=json.loads((r/'retained-old-expressions.json').read_text());old={o:json.loads((r/(o+'.first.json')).read_text()) for o in groups}
def name(a):return '' if not a else (name(a[0])+'.' if a[0] else '')+str(a[1])
aux={name(a[0]):[o,i] for o,d in groups.items() for i,a in enumerate(d['aux'])};order=[];seen=set()
def deps(o,i):
 nodes=groups[o]['nodes'];a=groups[o]['aux'][i];todo=[a[2],a[3]];visited=set();found=set();ch={'app':(1,2),'lam':(2,3),'forall':(2,3),'let':(2,3,4),'proj':(3,)}
 while todo:
  j=todo.pop()
  if j in visited:continue
  visited.add(j);n=nodes[j]
  if n[0]=='const':found.add(name(n[1]))
  todo.extend(n[k] for k in ch.get(n[0],()))
 return found&aux.keys()
def visit(n):
 if n in seen:return
 seen.add(n);o,i=aux[n]
 for k in sorted(deps(o,i)):visit(k)
 order.append([o,i])
for n in aux:visit(n)
(r/'batch-old.json').write_text(json.dumps(dict(groups=old,helpers=groups,order=order),separators=(',',':')));print('actual helpers',len(order))
p=r/'BatchCompat.lean';s=p.read_text();s=s[:s.index('run_elab do')]+'''run_elab do
  let all ← ofExcept (Json.parse (← IO.FS.readFile "../../results/module-final/batch-old.json"))
  let oldGroups ← ofExcept (← ofExcept (all.getObjVal? "groups")).getObj?
  let helperGroups ← ofExcept (← ofExcept (all.getObjVal? "helpers")).getObj?
  let order ← ofExcept (all.getObjValAs? (Array Json) "order")
  let mut helperNames : Array Name := #[]
  for row in order do
    let row ← ofExcept row.getArr?
    let group ← ofExcept row[0]!.getStr?
    let i : Nat ← ofExcept (fromJson? row[1]!)
    let d := helperGroups[group]!
    let a ← ofExcept (← ofExcept (d.getObjValAs? (Array Json) "aux"))[i]!.getArr?
    helperNames := helperNames.push (← ofExcept (readName a[0]!))
  let rename := fun (e : Expr) => e.replace fun e => match e with
    | .const n us => if helperNames.contains n then some (.const (`BatchOld ++ n) us) else none
    | _ => none
  for row in order do
    let row ← ofExcept row.getArr?
    let group ← ofExcept row[0]!.getStr?
    let i : Nat ← ofExcept (fromJson? row[1]!)
    let d := helperGroups[group]!
    let es ← ofExcept (decode (← ofExcept (d.getObjValAs? (Array Json) "nodes")))
    let a ← ofExcept (← ofExcept (d.getObjValAs? (Array Json) "aux"))[i]!.getArr?
    let n ← ofExcept (readName a[0]!)
    let us ← (← ofExcept a[1]!.getArr?).toList.mapM fun x => ofExcept (readName x)
    let ti : Nat ← ofExcept (fromJson? a[2]!)
    let vi : Nat ← ofExcept (fromJson? a[3]!)
    unless (← ofExcept a[4]!.getStr?) == "theorem" do throwError "unexpected helper kind"
    addDecl <| .thmDecl {
      name := `BatchOld ++ n
      levelParams := us
      type := rename es[ti]!
      value := rename es[vi]!
    }
  for (_, old) in oldGroups.toArray do
    let es ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))
    let records ← ofExcept (old.getObjValAs? (Array Json) "records")
    for r in records do
      let a ← ofExcept r.getArr?
      let user ← ofExcept (readName a[0]!)
      if user.toString.contains "match_" then continue
      let n ← realizeGlobalConstNoOverload (mkIdent user)
      let ci ← getConstInfo n
      let i : Nat ← ofExcept (fromJson? a[2]!)
      let oldType := rename es[i]!
      check oldType
      check ci.type
      unless ← isDefEq oldType ci.type do throwError "not defeq: {user}"
      let historical := `HistoricalBatchUse ++ user
      addDecl <| .thmDecl {
        name := historical
        levelParams := ci.levelParams
        type := oldType
        value := .const n (ci.levelParams.map .param)
      }
      let axioms ← collectAxioms historical
      unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
        throwError "unexpected axiom: {user} {axioms}"
      logInfo m!"PASS actual historical type/kernel/defeq/axioms: {user}; actual={n}"
  for n in helperNames do
    let axioms ← collectAxioms (`BatchOld ++ n)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected helper axiom {n}"
  logInfo m!"Kernel checked {helperNames.size} actual old helper type/value pairs under fresh names"
''';p.write_text(s)
