#!/usr/bin/env python3
"""Bounded verification; run after source env.sh from the enclosing Lake package."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess
root=Path(__file__).resolve().parent.parent
os.chdir(root)
run=root/'Frontend/evidence'/datetime.datetime.now(datetime.timezone.utc).strftime('accepted-%Y%m%dT%H%M%SZ')
run.mkdir()
records=[]
def cmd(label,args):
 p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (run/(label+'.log')).write_text(p.stdout)
 (run/(label+'.exit')).write_text(str(p.returncode)+'\n')
 records.append({'label':label,'command':args,'exit_code':p.returncode})
 (run/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
 assert p.returncode==0,(label,p.stdout)
 return p.stdout
lean=cmd('lean',['lean','--version']);assert 'version 4.35.0,' in lean
pins={'mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679','Physlib':'c5a908ba7a1ee474063626bdf0470af006f9812e'}
for name,pin in pins.items():
 assert cmd('pin-'+name,['git','-C',str(root/'.lake/packages'/name),'rev-parse','HEAD']).strip()==pin
 assert not cmd('clean-'+name,['git','-C',str(root/'.lake/packages'/name),'status','--porcelain','--untracked-files=no']).strip()
cmd('source-identity',['python3','check-source-identity.py'])
# Portable preserved-code baseline; works in shallow clones without old Git objects.
for row in json.loads((root/'Frontend/preserved-source-sha256.json').read_text())['files']:
 rel=Path(row['path'])
 assert not rel.is_absolute() and '..' not in rel.parts
 assert hashlib.sha256((root/rel).read_bytes()).hexdigest()==row['sha256'],rel
files=sorted((root/'Frontend/FiniteProbability').glob('*.lean'))
names=[];hashes={}
for p in files:
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S))
 assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b',s),p
 ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 names += [ns+'.'+n for n in re.findall(r'^(?:@\[.*?\]\s*)?(?:lemma|theorem|def|instance)\s+(\w+)',s,re.M)]
 hashes[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
cmd('full-build',['lake','build','PMFBridgeDraft','PMFComparison','FiniteProbability','FiniteProbability.Clients','FiniteProbability.Contracts'])
for p in files:
 cmd('file-'+p.stem,['lake','env','lean',str(p.relative_to(root))])
audit=root/'Frontend/Audit.lean'
audit.write_text('import FiniteProbability.Contracts\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
a=cmd('new-axioms-types',['lake','env','lean','Frontend/Audit.lean'])
old=cmd('old-bridge-axioms',['lake','env','lean','Verified/Audit.lean'])+cmd('old-comparison-axioms',['lake','env','lean','Comparison/Audit.lean'])
def closures(s):return {n:[x.strip() for x in ax.split(',') if x.strip()] for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S)}
newax=closures(a);oldax=closures(old)
assert set(newax)==set(names),(len(newax),len(names))
assert len(oldax)==63,len(oldax)
assert all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in list(newax.values())+list(oldax.values()))
deps=cmd('dependencies',['lake','env','lean','Frontend/Dependencies.lean'])
for required in ['MeasureTheory.integral_fintype_prod_eq_prod','MeasureTheory.integral_comp_eval','ProbabilityTheory.variance_sum_pi','ProbabilityTheory.variance_const_mul','ProbabilityTheory.iIndepFun_pi']:
 assert required in deps,required
for forbidden in ['Finite.productMean','Finite.variance_on_fin','Finite.covariance_on_fin','Finite.productMean_centered_sum_sq']:
 assert forbidden not in deps,forbidden
report={'pass':True,'starting_commit':'0a6ef9bfa780891cc072c47227ee107ab5dcd627','published_base':'313de258d8356905209908bea60215c233e56824','lean':lean.strip(),'pins':pins,'new_declarations':len(names),'old_declarations':len(oldax),'new_axioms':newax,'source_sha256':hashes,'commands':records,'limits':'Finite homogeneous output type, real scores, fixed channel input. Proposed clients compiled; no upstream adoption, timing, upgrade or long-term maintenance study.'}
(run/'report.json').write_text(json.dumps(report,indent=2)+'\n')
(root/'Frontend/evidence/latest.txt').write_text(str(run.relative_to(root))+'\n')
print('PASS',len(names),'new declarations;',len(oldax),'historical declarations;',run)
