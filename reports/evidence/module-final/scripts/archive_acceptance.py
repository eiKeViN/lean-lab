from pathlib import Path
import json,gzip,shutil,hashlib
root=Path.cwd();src=root/'results/module-final';out=root/'results/module-final/accepted-25';stages=root/'results/for-mathlib'
m=json.loads((src/'checks-acceptance.json').read_text());assert m['exit_code']==0
ss=json.loads((stages/'stages.json').read_text());assert len(ss)==59 and all(x['exit_code']==0 for x in ss)
i=json.loads((src/'checks-acceptance.inputs.json').read_text());bad=[p for p,h in i['files'].items() if not (root/p).is_file() or hashlib.sha256((root/p).read_bytes()).hexdigest()!=h];assert not bad,bad
out.mkdir(parents=True,exist_ok=True)
(out/'input-match-at-completion.json').write_text(json.dumps(dict(checkpoint=i['git_head'],checked_inputs=len(i['files']),changed_inputs=bad),indent=2)+'\n')
for p in [src/'checks-acceptance.log',src/'checks-acceptance.json',src/'checks-acceptance.inputs.json',stages/'stages.json']:
 target=out/p.name
 if p.name.endswith('.inputs.json'):target=target.with_name(target.name+'.gz');target.write_bytes(gzip.compress(p.read_bytes(),mtime=0))
 else:shutil.copyfile(p,target)
for stage in ss:shutil.copyfile(stages/(stage['label']+'.log'),out/(stage['label']+'.log'))
for label in ('baseline-types','migrated-types','attach-modern-types','next-modern-types','final-modern-types','modern-public-types','rollout-public-types'):
 p=stages/(label+'.tsv');(out/(label+'.tsv.gz')).write_bytes(gzip.compress(p.read_bytes(),mtime=0))
for label,key in [('type-comparison','old_api'),('full-record-compatibility','raw'),('next-full-records','raw'),('final-full-records','raw'),('final-modern-comparison','raw')]:
 s=(out/(label+'.log')).read_text();data=json.loads(s[s.index('{\n  "'+key+'"'):]);(out/(label+'-result.json')).write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(dict(stages=len(ss),inputs=len(i['files']),metrics=m),indent=2))
