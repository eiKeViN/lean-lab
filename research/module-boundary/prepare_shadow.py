#!/usr/bin/env python3
"""Create exactly two diagnostic module fixtures; never write production sources."""
import gzip, hashlib, json, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PROJECT=ROOT/'experiments/kl-for-mathlib'
plan=json.load(gzip.open(ROOT/'reports/evidence/module-rollout/rejected-131/module-rollout.json.gz','rt'))
out=Path(sys.argv[1]).resolve()
records=[]
for rel in ['ForMathlib/Combinatorics/MomentGraph/Sheaf/Basic.lean', 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Defs.lean']:
    data=(PROJECT/rel).read_bytes(); item=plan['files'][rel]
    assert hashlib.sha256(data).hexdigest()==item['before_sha256']
    text=data.decode()
    for e in sorted(item['edits'],key=lambda e:e['start'],reverse=True):
        i=e['start']; assert text[i:i+len(e['old'])]==e['old']
        text=text[:i]+e['new']+text[i+len(e['old']):]
    assert hashlib.sha256(text.encode()).hexdigest()==item['after_sha256']
    target=out/rel;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():raise SystemExit('Refusing overwrite: '+str(target))
    target.write_text(text)
    records.append({'path':rel,'before':item['before_sha256'],'after':item['after_sha256']})
(out/'ForMathlib/Algebra').symlink_to(PROJECT/'.lake/build/lib/lean/ForMathlib/Algebra', target_is_directory=True)
(out/'sources.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
