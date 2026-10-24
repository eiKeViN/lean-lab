from pathlib import Path
import json,gzip,shutil,hashlib,subprocess
root=Path.cwd();r=root/'results/module-final';out=root/'reports/evidence/module-final';out.mkdir(parents=True,exist_ok=True)
def copy(p,q):
 q.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.tsv' or p.name.endswith('.inputs.json'):
  q=q.with_name(q.name+'.gz');q.write_bytes(gzip.compress(p.read_bytes(),mtime=0))
 else:shutil.copyfile(p,q)
for p in r.iterdir():
 if p.is_file() and p.suffix in ('.json','.log','.lean','.py','.txt'):copy(p,out/p.name)
for folder in ['accepted-25','failed-full-1','decisions','scripts']:
 for p in (r/folder).rglob('*'):
  if p.is_file() and p.suffix in ('.json','.log','.lean','.py','.txt','.md','.gz','.sh'):copy(p,out/folder/p.relative_to(r/folder))
base='0917d25afb52e46cae4233d3056020ed6f881fa3';source=json.loads((root/'reports/evidence/module-next/source-identity.json').read_text());records=[]
for a in source['records']:
 p=a['path'];old=subprocess.check_output(['git','show',base+':'+p]);new=(root/p).read_bytes();records.append(dict(path=p,before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=hashlib.sha256(new).hexdigest(),unchanged=old==new))
changed=[a['path'] for a in records if not a['unchanged']];assert len(changed)==25
protected=['reference-public-types.json','compare_types.py','additional-types.json','stalk-equation-compat.json','stalk-equation-old.json','StalkEquationCompat.lean','lean-toolchain','lakefile.toml','lake-manifest.json']
for p in protected:assert (root/'experiments/kl-for-mathlib'/p).read_bytes()==subprocess.check_output(['git','show',base+':experiments/kl-for-mathlib/'+p])
m=root/'experiments/kl-for-mathlib/.lake/packages/mathlib';mh=subprocess.check_output(['git','-C',str(m),'rev-parse','HEAD'],text=True).strip();ms=subprocess.check_output(['git','-C',str(m),'status','--porcelain'],text=True);assert mh=='d13f23b723b8a846827a245b89c10fc7d3f11612' and not ms
(out/'source-identity.json').write_text(json.dumps(dict(base_commit=base,products=261,changed_products=changed,unchanged_products=236,records=records,unchanged_protected_files=protected,mathlib_commit=mh,mathlib_status=ms),indent=2)+'\n')
print('evidence files',len([p for p in out.rglob('*') if p.is_file()]))
