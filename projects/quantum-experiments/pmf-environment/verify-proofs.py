#!/usr/bin/env python3
"""Run from this directory after source env.sh; preserve each validation run."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys
root = Path(__file__).resolve().parent
os.chdir(root)
# Lake must select its freshly built library, not old manually emitted draft objects.
env = dict(os.environ)
env.pop('LEAN_PATH', None)
run = root / 'logs' / 'proof' / datetime.datetime.now(datetime.timezone.utc).strftime('validation-%Y%m%dT%H%M%S%fZ')
run.mkdir(parents=True)
records = []
def command(label, args):
    p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
    (run / (label + '.log')).write_text(p.stdout)
    (run / (label + '.exit')).write_text(str(p.returncode) + '\n')
    records.append({'label':label, 'command':args, 'cwd':str(root), 'exit_code':p.returncode})
    (run / 'commands.json').write_text(json.dumps(records, indent=2)+'\n')
    if p.returncode:
        print(p.stdout)
        raise SystemExit(f'Failed {label}; evidence: {run}')
    return p.stdout

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def uncomment(s):
    # Our six source files use ordinary non-nested block and line comments.
    return re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', s, flags=re.S))

def contracts(s):
    s=uncomment(s)
    ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
    return {ns+'.'+m.group(2): ' '.join(m.group(0).split())
            for m in re.finditer(r'^(?:@\[.*?\]\s*)?(theorem|def|instance)\s+(\w+).*?(?=:=|\bwhere\b)',s,re.M|re.S)}

lean = command('lean-version',['lean','--version']).strip()
assert 'version 4.35.0,' in lean
pins = {'mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679',
        'Physlib':'c5a908ba7a1ee474063626bdf0470af006f9812e'}
for name,sha in pins.items():
    assert command('pin-'+name,['git','-C',str(root/'.lake/packages'/name),'rev-parse','HEAD']).strip()==sha
    assert not command('status-'+name,['git','-C',str(root/'.lake/packages'/name),'status','--porcelain','--untracked-files=no']).strip()
original=root.parent/'physlib-pmf-bridge/UNVERIFIED_DRAFT/PMFBridgeDraft'
revision=root/'Verified/PMFBridgeDraft'
all_contracts={}
hashes={}
for src in sorted(revision.glob('*.lean')):
    old=original/src.name
    assert contracts(old.read_text())==contracts(src.read_text()), f'Changed declaration: {src}'
    # Ambient variables and namespace/open context are also unchanged.
    context=lambda s: re.findall(r'^(?:variable|namespace|open|noncomputable)[^\n]*',uncomment(s),re.M)
    assert context(old.read_text())==context(src.read_text()), f'Changed context: {src}'
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b', uncomment(src.read_text())),src
    all_contracts.update(contracts(src.read_text()))
    hashes[src.name]={'original':digest(old),'verified':digest(src)}
assert len(all_contracts)==36
assert set((root/'Verified/declarations.txt').read_text().splitlines())==set(all_contracts)
command('full-build',['lake','build','PMFBridgeDraft'])
for name in ['Bridge','Native','ViaPMF','Compare','ChannelProduct','ChannelStatistics']:
    command('file-'+name,['lake','env','lean',str(Path('Verified/PMFBridgeDraft')/(name+'.lean'))])
audit=command('axioms',['lake','env','lean','Verified/Audit.lean'])
closures={name:[a.strip() for a in axioms.split(',') if a.strip()]
          for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)}
assert set(closures)==set(all_contracts), 'Incomplete axiom audit'
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(axioms)<=allowed for axioms in closures.values()), closures
assert 'sorryAx' not in audit
# Check published source identity without requiring private transfer material.
command('source-identity',['python3','check-source-identity.py'])
report={'lean':lean,'pins':pins,'commands':records,'source_sha256':hashes,
        'declaration_count':36,'contracts_and_context_unchanged':True,
        'axiom_closures':closures,'published_historical_sources_unchanged':True,
        'source_admissions':False,'pass':True,
        'limits':['No separate whole-dependency kernel replay','No proof of engineering or maintenance benefit']}
(run/'report.json').write_text(json.dumps(report,indent=2)+'\n')
(root/'logs/proof/latest-validation.txt').write_text(str(run)+'\n')
print(f'PASS: 6 files, full build, 36 unchanged declarations and axiom closures; {run}')
