#!/usr/bin/env python3
"""Isolated real split producer/client trial; never overwrites Lake artifacts.
Run only with no active project build. Temporary source edits restore in finally.
The artifact overlay contains two modules, not another maintained project.
"""
from pathlib import Path
import hashlib,json,os,resource,subprocess,time
import semantic_api as a
import validate
HERE=a.HERE;OUT=a.ROOT/'results/semantic-api/split-trial'
PRODUCER='ForMathlib/Algebra/Module/Cover/Local.lean'
CLIENT='ForMathlib/Algebra/Module/Graded/ModuleData/MinimalCover.lean'

def setup_for(source, out, label, shadows):
    # Keep Lake's exact normal import artifacts; override only selected modules.
    # No .olean.private is supplied for any selected producer.
    d=json.loads((HERE/'.lake/build/ir/OAI/Architecture.setup.json').read_text())
    src=Path(source)
    d['name']=str(src.with_suffix('')).replace('/','.') if not src.is_absolute() else src.stem
    d['isModule']=True
    for path,dest in shadows.items():
        module=path[:-5].replace('/','.')
        if len(d['importArts'][module][0])!=2:raise RuntimeError('Unexpected private artifact')
        d['importArts'][module]=[[str(dest),str(dest)+'.server'],
            [str(dest.with_suffix('.ir.sig')),str(dest.with_suffix('.ir'))]]
    p=out/(label+'.setup.json');p.write_text(json.dumps(d)+'\n');return str(p)

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    overlay=OUT/'artifacts';metrics=[];shadows={}
    env=validate.serial_environment()
    env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=HERE,env=env,text=True).strip()
    lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean')
    def run(label,args,success=True):
        start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
        args=args+['--setup',setup_for(args[0],OUT,label,shadows)]
        with (OUT/(label+'.log')).open('w') as log:
            p=subprocess.run([lean]+args,cwd=HERE,env=env,stdout=log,stderr=subprocess.STDOUT)
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        metrics.append(dict(label=label,command=[lean]+args,exit_code=p.returncode,
          wall_seconds=time.monotonic()-start,user_seconds=after.ru_utime-before.ru_utime,
          system_seconds=after.ru_stime-before.ru_stime,max_rss_kib_so_far=after.ru_maxrss))
        (OUT/'metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
        if (p.returncode==0)!=success:raise RuntimeError('Unexpected split trial result: '+label)
    snapshots={p:(HERE/p).read_bytes() for p in (PRODUCER,CLIENT)}
    artifacts={str(p):a.sha(p.read_bytes()) for module in (PRODUCER,CLIENT)
      for p in (HERE/'.lake/build/lib/lean'/module).with_suffix('.olean').parent.glob(Path(module).stem+'.olean*') if p.is_file()}
    try:
        source=snapshots[PRODUCER].decode()
        needle='@[expose] noncomputable def splitEquiv'
        if source.count(needle)!=1:raise RuntimeError('Unexpected split declaration')
        (HERE/PRODUCER).write_text(source.replace(needle,'noncomputable def splitEquiv'))
        dest=(overlay/PRODUCER).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        run('hidden-producer',[PRODUCER,'-o',str(dest)])
        shadows[PRODUCER]=dest
        (HERE/PRODUCER).write_bytes(snapshots[PRODUCER])
        # Actual old graded client: negative control, not a made-up proof.
        (HERE/CLIENT).write_bytes(a.original(CLIENT))
        dest=(overlay/CLIENT).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        run('old-real-client',[CLIENT,'-o',str(dest)],success=False)
        (HERE/CLIENT).write_bytes(snapshots[CLIENT])
        run('new-real-client',[CLIENT,'-o',str(dest)])
        shadows[CLIENT]=dest
        consumer=(HERE/'SemanticApiChecks.lean').read_text()
        consumer=consumer.replace('for n in #[`OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback] do','for n in #[`OAI.KLInvariance.LocalCover.splitEquiv,\n      `OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback] do')
        consumer=consumer.replace('for n in #[`OAI.KLInvariance.LocalCover.splitEquiv,\n      `OAI.KLInvariance.CoefficientChange.equivVal,','for n in #[`OAI.KLInvariance.CoefficientChange.equivVal,')
        consumer=consumer.replace('quotientPullback body hidden; splitEquiv/equivVal/map/baseChangeQuotient computation controls visible.','splitEquiv/quotientPullback bodies hidden; equivVal/map/baseChangeQuotient controls visible.')
        consumer=consumer.replace('-- A reconstruction identity,', '''example (b : B) : (LocalCover.splitEquiv g s hs b).1 = g b := by
  fail_if_success exact rfl
  exact LocalCover.splitEquiv_apply_fst g s hs b

-- A reconstruction identity,''')
        path=OUT/'HiddenSplitConsumer.lean';path.write_text(consumer)
        run('ordinary-hidden-consumer',[str(path)])
    finally:
        for p,b in snapshots.items():(HERE/p).write_bytes(b)
        restored=all((HERE/p).read_bytes()==b for p,b in snapshots.items())
        preserved=all(a.sha(Path(p).read_bytes())==h for p,h in artifacts.items())
        (OUT/'restoration.json').write_text(json.dumps(dict(source_restored=restored,
            lake_artifacts_unchanged=preserved,artifacts=artifacts),indent=2)+'\n')
        if not restored or not preserved:raise RuntimeError('Split trial restoration failed')
def map_trial():
    """Validate the retained map transparency decision on actual current sources."""
    out=a.ROOT/'results/semantic-api/map-trial';out.mkdir(parents=True,exist_ok=True)
    overlay=out/'artifacts';shadows={};env=validate.serial_environment()
    env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=HERE,env=env,text=True).strip()
    lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean');records=[]
    producer='ForMathlib/Algebra/Module/CoefficientChange/Basic.lean'
    source=(HERE/producer).read_bytes()
    art=(HERE/'.lake/build/lib/lean'/producer).with_suffix('.olean')
    art_hash=a.sha(art.read_bytes())
    def run(label,args,expected):
        start=time.monotonic()
        args=args+['--setup',setup_for(args[0],out,label,shadows)]
        with (out/(label+'.log')).open('w') as log:
            p=subprocess.run([lean]+args,cwd=HERE,env=env,stdout=log,stderr=subprocess.STDOUT)
        records.append(dict(label=label,command=[lean]+args,exit_code=p.returncode,wall_seconds=time.monotonic()-start))
        (out/'metrics.json').write_text(json.dumps(records,indent=2)+'\n')
        if (p.returncode==0)!=expected:raise RuntimeError('Unexpected map trial result: '+label)
    try:
        text=source.decode();needle='@[expose] def map ('
        if text.count(needle)!=1:raise RuntimeError('Unexpected map definition')
        (HERE/producer).write_text(text.replace(needle,'def map ('))
        bound=json.loads((a.ROOT/'reports/evidence/semantic-api/hidden-map-source.json').read_text())
        for path,record in bound['files'].items():
            if a.sha((HERE/path).read_bytes())!=record['after_sha256']:
                raise RuntimeError('Changed bound hidden-map trial source: '+path)
        dest=(overlay/producer).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        run('hidden-map-producer',[producer,'-o',str(dest)],True)
        shadows[producer]=dest
        (HERE/producer).write_bytes(source)
        for label,path in [('dual','CoefficientChange/Dual.lean'),('graded-hom','Graded/ModuleData/CoefficientChange/Basic.lean'),('top-split','Graded/ModuleData/CoefficientChange.lean')]:
            run(label,['ForMathlib/Algebra/Module/'+path],True)
        run('remaining-real-sheaf-gap',['ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Duality.lean'],False)
        if 'CoefficientChange.map' not in (out/'remaining-real-sheaf-gap.log').read_text():
            raise RuntimeError('Failure did not identify the selected hidden operation')
    finally:
        (HERE/producer).write_bytes(source)
        restored=(HERE/producer).read_bytes()==source
        preserved=a.sha(art.read_bytes())==art_hash
        (out/'restoration.json').write_text(json.dumps(dict(source_restored=restored,lake_artifacts_unchanged=preserved,artifact_sha256=art_hash),indent=2)+'\n')
        if not restored or not preserved:raise RuntimeError('Map trial restoration failed')

def quotient_trial():
    """The existing tensor API works hidden, but the historical eq_1 disappears."""
    out=a.ROOT/'results/semantic-api/quotient-trial';out.mkdir(parents=True,exist_ok=True)
    overlay=out/'artifacts';shadows={};env=validate.serial_environment()
    env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=HERE,env=env,text=True).strip()
    lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean');records=[]
    producer='ForMathlib/Combinatorics/MomentGraph/Sheaf/Structure.lean'
    source=(HERE/producer).read_bytes();art=(HERE/'.lake/build/lib/lean'/producer).with_suffix('.olean')
    art_hash=a.sha(art.read_bytes())
    def run(label,args):
        start=time.monotonic()
        args=args+['--setup',setup_for(args[0],out,label,shadows)]
        with (out/(label+'.log')).open('w') as log:
            p=subprocess.run([lean]+args,cwd=HERE,env=env,stdout=log,stderr=subprocess.STDOUT)
        records.append(dict(label=label,command=[lean]+args,exit_code=p.returncode,wall_seconds=time.monotonic()-start))
        (out/'metrics.json').write_text(json.dumps(records,indent=2)+'\n')
        if p.returncode:raise RuntimeError('Quotient trial failed: '+label)
    try:
        text=source.decode();needle='@[expose] def baseChangeQuotient ('
        if text.count(needle)!=1:raise RuntimeError('Unexpected quotient definition')
        (HERE/producer).write_text(text.replace(needle,'def baseChangeQuotient ('))
        dest=(overlay/producer).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        run('hidden-quotient-producer',[producer,'-o',str(dest)])
        shadows[producer]=dest
        (HERE/producer).write_bytes(source)
        consumer=(HERE/'SemanticApiChecks.lean').read_text()
        consumer=consumer.replace('for n in #[`OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback] do','for n in #[`OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient, `OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback] do')
        consumer=consumer.replace(',\n      `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient] do','] do')
        consumer=consumer.replace('quotientPullback body hidden; splitEquiv/equivVal/map/baseChangeQuotient computation controls visible.','Both quotient bodies hidden; tensor API works; historical eq_1 availability checked below.')
        consumer+='\nrun_elab do\n  if (← getEnv).contains `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient.eq_1 then\n    throwError "Expected the historical equation to be unavailable in this trial"\n  logInfo "Historical baseChangeQuotient.eq_1 unavailable: explicit reason to retain expose."\n'
        p=out/'HiddenQuotientConsumer.lean';p.write_text(consumer)
        run('ordinary-hidden-consumer',[str(p)])
    finally:
        (HERE/producer).write_bytes(source)
        restored=(HERE/producer).read_bytes()==source;preserved=a.sha(art.read_bytes())==art_hash
        (out/'restoration.json').write_text(json.dumps(dict(source_restored=restored,lake_artifacts_unchanged=preserved,artifact_sha256=art_hash),indent=2)+'\n')
        if not restored or not preserved:raise RuntimeError('Quotient trial restoration failed')

if __name__=='__main__':
    import sys
    if sys.argv[1:]==['--map']:map_trial()
    elif sys.argv[1:]==['--quotient']:quotient_trial()
    else:main()
