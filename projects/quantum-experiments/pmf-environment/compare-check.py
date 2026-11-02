#!/usr/bin/env python3
"""Bounded comparison verification and two alternating warm elaboration samples."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
root=Path(__file__).resolve().parent
os.chdir(root)
env=dict(os.environ);env.pop('LEAN_PATH',None)
run=root/'logs/comparison'/datetime.datetime.now(datetime.timezone.utc).strftime('accepted-%Y%m%dT%H%M%S%fZ')
run.mkdir(parents=True)
records=[]
def cmd(label,args):
 start=time.perf_counter()
 p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env=env)
 elapsed=time.perf_counter()-start
 (run/(label+'.log')).write_text(p.stdout)
 (run/(label+'.exit')).write_text(str(p.returncode)+'\n')
 records.append({'label':label,'command':args,'cwd':str(root),'exit_code':p.returncode,'wall_seconds':elapsed})
 (run/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
 assert p.returncode==0,(label,p.stdout)
 return p.stdout

def code(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
def declarations(p):
 s=code(p.read_text());ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 return [ns+'.'+n for n in re.findall(r'^(?:@\[.*?\]\s*)?(?:lemma|theorem|def|instance)\s+(\w+)',s,re.M)]
lean=cmd('lean',['lean','--version'])
assert 'version 4.35.0,' in lean
for name,pin in {'mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679','Physlib':'c5a908ba7a1ee474063626bdf0470af006f9812e'}.items():
 assert cmd('pin-'+name,['git','-C',str(root/'.lake/packages'/name),'rev-parse','HEAD']).strip()==pin
 assert not cmd('clean-'+name,['git','-C',str(root/'.lake/packages'/name),'status','--porcelain','--untracked-files=no']).strip()
cmd('source-identity',['python3','check-source-identity.py'])
allfiles=list((root/'Verified/PMFBridgeDraft').glob('*.lean'))+list((root/'Comparison/PMFComparison').glob('*.lean'))
names=[];metrics={}
for p in sorted(allfiles):
 s=code(p.read_text())
 assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b',s),p
 ds=declarations(p);names+=ds
 metrics[str(p.relative_to(root))]={'physical_lines':len(p.read_text().splitlines()),'nonblank_noncomment_lines':sum(bool(x.strip()) for x in s.splitlines()),'explicit_declarations':len(ds),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert len(names)==63,len(names)
cmd('full-build',['lake','build','PMFBridgeDraft','PMFComparison'])
for p in sorted((root/'Comparison/PMFComparison').glob('*.lean')):
 cmd('file-'+p.stem,['lake','env','lean',str(p.relative_to(root))])
audit=cmd('old-axioms',['lake','env','lean','Verified/Audit.lean'])+cmd('new-axioms',['lake','env','lean','Comparison/Audit.lean'])
closures={n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)}
assert set(closures)==set(names)
assert all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in closures.values())
deps=cmd('dependencies',['lake','env','lean','Comparison/Dependencies.lean'])
slices={n:re.findall(r'QuantumExperiments\.[\w.]+',body) for n,body in re.findall(r'SLICE (\S+): \[(.*?)\]',deps,re.S)}
# Warm source elaboration only, no rebuild or cache deletion; alternating route order.
for rnd,order in enumerate([['Finite','Transport','FiniteCovariance','TransportCovariance'],['Transport','Finite','TransportCovariance','FiniteCovariance']],1):
 for n in order:
  cmd(f'warm-{rnd}-{n}',['lake','env','lean',f'Comparison/PMFComparison/{n}.lean'])
report={'pass':True,'lean':lean.strip(),'base_commit':'05b07b3db0fa70dcae4b0cefb7c6be90538c6612','declaration_count':len(names),'axioms':closures,'metrics':metrics,'local_dependency_slices':slices,'commands':records,'published_historical_sources_unchanged':True,'verified_six_files_unchanged':True,'timing_scope':'Two alternating warm source-elaboration samples with compiled dependencies; not clean build, human effort or long-term maintenance.'}
(run/'report.json').write_text(json.dumps(report,indent=2)+'\n')
(root/'logs/comparison/latest-accepted.txt').write_text(str(run)+'\n')
print('PASS:',len(names),'declarations;',run)
for r in records:
 if r['label'].startswith('warm-'):print(r['label'],round(r['wall_seconds'],3))
for p,m in metrics.items():print(p,m['nonblank_noncomment_lines'],m['explicit_declarations'])
