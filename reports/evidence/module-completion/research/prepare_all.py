from pathlib import Path
import re,json,hashlib,subprocess,difflib
root=Path.cwd();h=root/'experiments/kl-for-mathlib';r=root/'results/matcher-compat';G=json.loads((h/'module-import-graph.json').read_text());selected=sorted(n for n,d in G.items() if not d['module']);assert len(selected)==105
names=json.loads((r/'names.json').read_text());owners={names[0]:'ForMathlib.Algebra.Module.CoefficientChange.Basic',names[1]:'ForMathlib.Algebra.Module.Cover.Local',names[2]:'ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties',names[3]:'ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties',names[4]:'ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis',names[5]:'ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis',names[6]:'ForMathlib.Algebra.Module.ReflectionPair.Twist',names[7]:'ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder'}
plan={'schema':1,'base_commit':'382d29d94aaa8e32bcdeb24633f070d29695dcc3','files':{},'compatibility_pairs':[[n,n.replace('match_3','match_6') if n==names[1] else n] for n in names]};sha=lambda b:hashlib.sha256(b).hexdigest()
for n in selected:
 p=n.replace('.','/')+'.lean';old=subprocess.check_output(['git','show',plan['base_commit']+':experiments/kl-for-mathlib/'+p],text=True);assert (h/p).read_text()==old
 t=re.sub(r'(?m)^import ','public import ',old);end=list(re.finditer(r'(?m)^public import [^\n]+',t))[-1].end();t=t[:end]+'\n\npublic section'+t[end:]
 t=re.sub(r'(?m)^([ \t]*)(?=(?:(?:noncomputable|protected|unsafe)\s+)*def\s)',r'\1@[expose] ',t)
 t=re.sub(r'@\[([^\]\n]+)\]\s*\n([ \t]*)@\[expose\] ',lambda m:'@['+m[1]+', expose]\n'+m[2],t)
 t=re.sub(r'@\[([^\]\n]+)\] (?=(?:(?:noncomputable|protected|unsafe)\s+)*def\s)',lambda m:'@['+m[1]+(', expose' if 'expose' not in m[1] else '')+'] ',t)
 t='module\n'+t
 if n=='ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure':
  assert t.count('(quotientLinear α e)')==2;t=t.replace('(quotientLinear α e)','((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap)')
 pairs=[(a,b) for a,b in plan['compatibility_pairs'] if owners[a]==n]
 if pairs:
  t+='''
-- Preserve the pinned historical matcher API with kernel-checked public copies.
-- The producer's proof still uses its compiler-generated private matcher.
open Lean Elab Command in
run_elab do
  let pairs : Array (Name × Name) := #[PAIRS]
  for (publicName, sourceName) in pairs do
    if ((← getEnv).setExporting true).contains publicName then
      throwError "Historical matcher already public: {publicName}"
    let actual ← withoutExporting <| realizeGlobalConstNoOverload (mkIdent sourceName)
    let ci ← withoutExporting <| getConstInfo actual
    let .defnInfo info := ci | throwError "Matcher source is not a definition: {actual}"
    unless info.safety == .safe do throwError "Unsafe matcher source: {actual}"
    let some matcherInfo ← withoutExporting <| Lean.Meta.getMatcherInfo? actual |
      throwError "Missing matcher metadata: {actual}"
    let decl := Declaration.defnDecl { info with name := publicName }
    withExporting (isExporting := true) do
      addDecl decl (forceExpose := true)
      setReducibilityStatus publicName .instanceReducible
      Lean.Meta.Match.addMatcherInfo publicName matcherInfo
      compileDecl decl
'''.replace('PAIRS',', '.join('(`'+a+', `'+b+')' for a,b in pairs))
 sl=old.splitlines(keepends=True);tl=t.splitlines(keepends=True);edits=[dict(start=sum(map(len,sl[:i])),old=''.join(sl[i:j]),new=''.join(tl[a:b])) for op,i,j,a,b in difflib.SequenceMatcher(None,sl,tl,autojunk=False).get_opcodes() if op!='equal']
 plan['files'][p]={'before_sha256':sha(old.encode()),'after_sha256':sha(t.encode()),'edits':edits}
 (h/p).write_text(t)
(h/'module-all.json').write_text(json.dumps(plan,indent=2)+'\n');(r/'initial-plan.json').write_text(json.dumps(plan,indent=2)+'\n');roots=[n for n in selected if n=='ForMathlib' or n.startswith('ForMathlib.')];(r/'roots.json').write_text(json.dumps(roots,indent=2)+'\n');print('candidate105; initial roots',len(roots))
