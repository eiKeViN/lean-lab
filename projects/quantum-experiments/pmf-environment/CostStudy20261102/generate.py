#!/usr/bin/env python3
"""Extract unchanged declaration bodies into symmetric, isolated measurement modules."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SOURCE={
 'Bridge':'Verified/PMFBridgeDraft/Bridge.lean',
 'ChannelProduct':'Verified/PMFBridgeDraft/ChannelProduct.lean',
 'ChannelStatistics':'Verified/PMFBridgeDraft/ChannelStatistics.lean',
 'Native':'Comparison/PMFComparison/Finite.lean',
 'Transport':'Comparison/PMFComparison/Transport.lean',
 'Moments':'Comparison/PMFComparison/Moments.lean'}
PREFIX={'Bridge':'QuantumExperiments.PMFBridgeDraft.Bridge','ChannelProduct':'QuantumExperiments.PMFBridgeDraft.ChannelProduct','ChannelStatistics':'QuantumExperiments.PMFBridgeDraft.ChannelStatistics','Native':'QuantumExperiments.PMFComparison.Finite','Moments':'QuantumExperiments.PMFComparison.Finite','Transport':'QuantumExperiments.PMFComparison.Transport'}
def uncomment(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
BLOCKS={};ROWS=[]
for key,path in SOURCE.items():
 text=uncomment((ROOT/path).read_text())
 marks=list(re.finditer(r'^(?:@\[[^\n]*\]\s*)?(?:def|lemma|theorem|instance)\s+(\w+)|^(?:variable|namespace|end|open)\b',text,re.M))
 for i,m in enumerate(marks):
  if not m.group(1):continue
  end=marks[i+1].start() if i+1<len(marks) else len(text)
  BLOCKS[key,m.group(1)]=text[m.start():end].strip()+'\n'

def take(key,names,category):
 out=[]
 for name in names.split():
  b=BLOCKS[key,name];out.append(b)
  ROWS.append({'name':PREFIX[key]+'.'+name,'origin':SOURCE[key],'category':category,'declaration_lines':sum(bool(l.strip()) for l in b.splitlines()),'body_sha256':hashlib.sha256(b.encode()).hexdigest()})
 return '\n'.join(out)
def section(key,variables,body,opens=''):
 return f'namespace {PREFIX[key]}\n{opens}\n{variables}\n\n{body}\nend {PREFIX[key]}\n'
HEADER='noncomputable section\nopen scoped BigOperators\nopen MeasureTheory\n\n'
imports=set()
for path in SOURCE.values():
 for imp in re.findall(r'^import (\S+)',(ROOT/path).read_text(),re.M):
  if not imp.startswith(('PMFComparison.','PMFBridgeDraft.')):imports.add(imp)
common='\n'.join('import '+i for i in sorted(imports))+'\n\n'+HEADER+section('Moments','variable {α : Type*} [Fintype α]',take('Moments','mean variance','common'))
nbase='import CostStudy.Common\n\n'+HEADER+section('Native','variable {α ι O I : Type*}',take('Native','productMean mean_center productMean_prod productMean_coordinate productMean_pair productMean_sum productMean_sum_coordinate','native_basis'))
nconsumer='import CostStudy.NativeBase\n\n'+HEADER+section('Native','variable {α ι O I : Type*}',take('Native','productMean_centered_sum_sq variance_on_fin','native_consumer'))
bbase='import CostStudy.Common\n\n'+HEADER
bbase+=section('Bridge','variable {α β : Type*}',take('Bridge','toPMF toPMF_apply toPMF_toReal','bridge_representation'))
bbase+=section('ChannelProduct','variable {α : Type*}',take('ChannelProduct','law law_probability law_singleton','bridge_representation'))
bbase+=section('ChannelProduct','variable {I O : Type*} [Fintype O] {n : ℕ}',take('ChannelProduct','on_fin_real_apply','bridge_domain'))
bbase+=section('ChannelProduct','variable {I O : Type*} [Fintype O] {n : ℕ}\nvariable [MeasurableSpace O] [MeasurableSingletonClass O]',take('ChannelProduct','law_on_fin_eq_pi','bridge_domain'))
bbase+=section('ChannelStatistics','variable {O : Type*} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]',take('ChannelStatistics','integral_real','bridge_observation')+'\n'+take('ChannelStatistics','score_memLp_two','bridge_moment'),'open ChannelProduct')
bbase+=section('Transport','variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]',take('Transport','integral_eq_mean variance_eq_finite','bridge_observation'),'open PMFBridgeDraft PMFBridgeDraft.ChannelProduct PMFBridgeDraft.ChannelStatistics')
bconsumer='import CostStudy.BridgeBase\n\n'+HEADER
bconsumer+=section('ChannelStatistics','variable {O : Type*} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]\nvariable {I : Type*} {n : ℕ}',take('ChannelStatistics','totalScore variance_totalScore_of_memLp variance_totalScore','bridge_consumer'),'open ChannelProduct')
bconsumer+=section('Transport','variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]',take('Transport','variance_on_fin','bridge_consumer'),'open PMFBridgeDraft PMFBridgeDraft.ChannelProduct PMFBridgeDraft.ChannelStatistics')
files={'Common':common,'NativeBase':nbase,'NativeConsumer':nconsumer,'BridgeBase':bbase,'BridgeConsumer':bconsumer}
out=HERE/'sources/CostStudy';out.mkdir(parents=True,exist_ok=True)
for name,s in files.items():(out/(name+'.lean')).write_text('/- Measurement copy: generated from the published declarations; do not edit manually. -/\n'+s)
# Concrete source change: same-type proof-body refactor of each final consumer.
variants=HERE/'variants/CostStudy';variants.mkdir(parents=True,exist_ok=True)
for route,key in [('Native','Native'),('Bridge','Transport')]:
 b=BLOCKS[key,'variance_on_fin'];before,body=b.split(':= by\n',1)
 revised=before+':= by\n  exact (by\n'+''.join('  '+l+'\n' for l in body.rstrip().splitlines())+'  )\n'
 text=(out/(route+'Consumer.lean')).read_text();assert text.count(b)==1
 (variants/(route+'Consumer.lean')).write_text(text.replace(b,revised))
summary={}
for row in ROWS:summary[row['category']]=summary.get(row['category'],0)+row['declaration_lines']
manifest={'base_commit':'313de258d8356905209908bea60215c233e56824','metric':'nonblank noncomment declaration lines, including signature/body/attributes; excluding module scaffolding','declarations':ROWS,'category_lines':summary,'upstream_import_union':sorted(imports),'source_files':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in SOURCE.values()},'mutation':'Same statement, same proof steps, final consumer proof wrapped in exact (by ...); a proof-body refactor, not new mathematics or a new downstream theorem.'}
(HERE/'accounting.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(summary)
