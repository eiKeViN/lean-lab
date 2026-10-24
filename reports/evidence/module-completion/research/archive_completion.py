from pathlib import Path
import hashlib,json,gzip,shutil
root=Path.cwd();src=root/'results/matcher-compat';dest=root/'results/module-completion-archive';dest.mkdir(exist_ok=True)
manifest={}
def save(p,relative):
 b=p.read_bytes();compress=p.suffix in ('.json','.tsv') or len(b)>400000
 out=dest/relative
 if compress:out=out.with_name(out.name+'.gz');stored=gzip.compress(b,mtime=0)
 else:stored=b
 out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(stored)
 manifest[str(out.relative_to(dest))]={'sha256':hashlib.sha256(stored).hexdigest(),'original_sha256':hashlib.sha256(b).hexdigest(),'original_bytes':len(b),'encoding':'gzip' if compress else 'identity'}
for p in sorted(src.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:save(p,Path('research')/p.relative_to(src))
stages=root/'results/for-mathlib';metrics=json.loads((stages/'stages.json').read_text());assert metrics and all(x['exit_code']==0 for x in metrics)
save(stages/'stages.json',Path('accepted/stages.json'))
for x in metrics:save(stages/(x['label']+'.log'),Path('accepted')/(x['label']+'.log'))
for s in ['baseline-types.tsv','migrated-types.tsv','all-modern-types.tsv','attach-modern-types.tsv','next-modern-types.tsv','final-modern-types.tsv','modern-public-types.tsv','rollout-public-types.tsv']:
 save(stages/s,Path('accepted')/s)
(dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('archived files',len(manifest),'stored bytes',sum((dest/p).stat().st_size for p in manifest))
