from pathlib import Path
import json,subprocess
r=Path('results/module-final');roots=set(json.loads((r/'retained-roots.json').read_text()));groups=json.loads((r/'retained-old-expressions.json').read_text())
for owner in groups:
 p=r/(owner+'.lean');s=p.read_text().replace('ci.value? |','ci.value? (allowOpaque := true) |');p.write_text(s)
 out=r/(owner+'.json');(r/(owner+'.first.json')).write_bytes(out.read_bytes())
 with (r/(owner+'.helpers.log')).open('w') as log:code=subprocess.call(['lake','env','lean',str(p.resolve())],cwd='experiments/kl-for-mathlib',stdout=log,stderr=subprocess.STDOUT)
 print(owner,code,flush=True)
 if code:print((r/(owner+'.helpers.log')).read_text()[-2000:]);raise SystemExit(code)
 groups[owner]=json.loads(out.read_text())
(r/'retained-old-expressions.json').write_text(json.dumps(groups,separators=(',',':')))
