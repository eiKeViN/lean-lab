#!/usr/bin/env python3
"""Follow-up to module_pilot.py: real Lake consumers and isolated edit probes."""
import json, shutil, subprocess
import module_pilot as h
P,OUT=h.P,h.ROOT/'results/module-pilot-incremental'
h.OUT=OUT

def main():
    if (OUT/'measurements.json').exists():raise RuntimeError('Archive existing results before a fresh run: '+str(OUT))
    OUT.mkdir(parents=True,exist_ok=True)
    original=h.path(h.S).read_text(); kernel=h.path(h.K).read_text(); compat=h.path(h.C).read_text()
    config=P/'lakefile.toml'; cfg=config.read_text()
    src=P/'ModulePilotProbe'
    if src.exists():raise RuntimeError('Refusing existing probe directory')
    for m,t in [(h.S,original),(h.K,kernel),(h.C,compat)]:
        ref=subprocess.check_output(['git','show',h.BASE+':'+str(h.path(m).relative_to(h.ROOT))],cwd=h.ROOT,text=True)
        if t!=ref:raise RuntimeError('Source is not baseline: '+m)
    snapshots={}
    def snap(label):
        snapshots[label]={m:h.artifact(m) for m in [h.S,h.K,h.C,'ModulePilotProbe.Modern','ModulePilotProbe.Legacy','ModulePilotProbe.All']}
        (OUT/'artifacts.json').write_text(json.dumps(snapshots,indent=2)+'\n')
    # Fail before any source/config edit if the fixed upstream cache is not ready.
    h.run('pins',['python3',str(h.ROOT/'scripts/verify.py')])
    h.run('upstream-ready',['lake','--no-build','build','Mathlib'])
    try:
        src.mkdir()
        config.write_text(cfg+'\n[[lean_lib]]\nname = "ModulePilotProbe"\nglobs = ["ModulePilotProbe.+"]\n')
        narrow=['Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Basic.Real.Basic','Mathlib.Algebra.Polynomial.Basic','Mathlib.Tactic.Ring']
        hidden=h.variant(original,True,narrow).replace('\npublic section\n','\n')
        h.path(h.S).write_text(hidden)
        h.run('single-default-private-build',['lake','build',h.S])
        private_consumer=OUT/'private-consumer.lean'
        private_consumer.write_text('module\nimport '+h.S+'\n#check OAI.KLInvariance.weighted_sum_single\n')
        h.run('single-default-private-consumer',['lake','env','lean',str(private_consumer)],expect=1,error_contains='Unknown identifier `OAI.KLInvariance.weighted_sum_single`')
        for target,base,label in [(h.S,h.variant(original,True,narrow),'single'),(h.C,h.variant(compat,True,expose=True),'kernel')]:
            if target==h.C:h.path(h.K).write_text(h.variant(kernel,True,expose=True))
            h.path(target).write_text(base)
            for name,prefix in [('Modern','module\nimport '),('Legacy','import '),('All','module\nimport all ')]:
                body=('\n#check OAI.KLInvariance.weighted_sum_single\n' if target==h.S else
                     (P/'CompatChecks.lean').read_text().split('\n',1)[1])
                (src/(name+'.lean')).write_text(prefix+target+'\n'+body)
            h.run(label+'-prepare',['lake','build','ModulePilotProbe'])
            snap(label+'-baseline')
            if target==h.S:
                h.run('module-source-policy',['python3','validate.py','--static'],expect=1,error_contains='Unrecorded active proof change: ForMathlib/Algebra/BigOperators/SingleCoordinate.lean')
                h.run('existing-weighted-check',['lake','env','lean','WeightedSumImportChecks.lean'])
            h.run(label+'-warm',['lake','build','ModulePilotProbe'])
            changes=[('doc',base.replace('/-!', '/-! Pilot documentation change. ',1))]
            if target==h.S:changes.append(('proof',base.replace(':= by\n',':= by\n  apply id\n',1)))
            else:changes.append(('body',base.replace(':=\n  _root_',':=\n  id <| _root_',1)))
            for change,text in changes:
                for i in range(3):
                    h.path(target).write_text(text)
                    h.run(f'{label}-{change}-{i}',['lake','build','ModulePilotProbe']);snap(f'{label}-{change}-{i}')
                    h.path(target).write_text(base)
                    h.run(f'{label}-{change}-restore-{i}',['lake','build','ModulePilotProbe']);snap(f'{label}-{change}-restore-{i}')
            if target==h.S:
                # Read-only diagnostic, only after the full selected closure is ready.
                try:
                    h.run('shake-single',['lake','shake','--keep-public',h.S])
                except RuntimeError:
                    # Diagnostics may fail; retain status, never force or fix.
                    pass
    finally:
        h.path(h.S).write_text(original);h.path(h.K).write_text(kernel);h.path(h.C).write_text(compat)
        config.write_text(cfg)
        if src.exists():shutil.rmtree(src)
        h.run('restored-targets',['lake','build',h.S,h.K,h.C])
if __name__=='__main__':main()
