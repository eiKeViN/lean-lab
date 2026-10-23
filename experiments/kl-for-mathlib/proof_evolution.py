#!/usr/bin/env python3
"""Explicit source evolution over an unchanged, reproducible pristine migration."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PLAN = ROOT / 'reports/evidence/lemma-granularity/plan.json'
POLICY = HERE / 'lemma-pilot.json'
MANIFEST = HERE / 'proof-evolution.json'
EXPANSION = ROOT / 'reports/evidence/lemma-granularity-expansion/plan.json'
PRIOR_TYPES = ROOT / 'reports/evidence/lemma-granularity-expansion/first-round-added-types.json'
EXPANSION_SHA = 'baeb7f870cba363f9d1b86af0c8f56d033b322df15d7241999fb85c198a49531'
PRIOR_TYPES_SHA = '445bd6143410e33deb4004ca4a89cc47ce8fc9ec9c5a94444074a8b2f12239d3'
PRIOR_EVOLUTION_SHA = '84de13d6dc207dd305691d2037718c93a027548ae8e2ac575add41d64b9d546b'

COMPARISON = ROOT / 'reports/evidence/lemma-granularity-comparison/plan.json'
COMPARISON_TYPES = COMPARISON.parent / 'prior-added-types.json'
COMPARISON_EVOLUTION = COMPARISON.parent / 'prior-evolution.json'
COMPARISON_SHA = '73dfdc70e047af0bb338454a73ad050414b75ece440acba0186f34e3c27daa74'
COMPARISON_TYPES_SHA = '75306176d36cfe22dbfdba991ec7fa784023c3d464b0b55d0098a944271aacdc'
COMPARISON_EVOLUTION_SHA = '7e007b0691d585bf18eba89df40bca21ececbba304b49a12195ddf46ef4461d6'

LIBRARY = ROOT / 'reports/evidence/lemma-granularity-library/plan.json'
LIBRARY_TYPES = LIBRARY.parent / 'prior-added-types.json'
LIBRARY_EVOLUTION = LIBRARY.parent / 'prior-evolution.json'
LIBRARY_SHA = '59ca5b99c065af1cd4857e4c36e1a7f87505117510d489fe71479759ffec4100'
LIBRARY_TYPES_SHA = '5ac38e6c44a65cf80f601f7751f5346690a7976f00a10598819ed7f02dc9a55d'
LIBRARY_EVOLUTION_SHA = '77d80de4ea6df53847d1c59106b02a49170ed6f4b421d58886c5e6b502a66923'

def samples():
    return (json.loads(PLAN.read_text())['samples'] + json.loads(EXPANSION.read_text())['samples']
        + json.loads(COMPARISON.read_text())['samples'] + json.loads(LIBRARY.read_text())['samples'])

def sha(data):
    return hashlib.sha256(data).hexdigest()

def policy():
    p = json.loads(POLICY.read_text())
    original = json.loads(PLAN.read_text())
    if p['base_commit'] != original['base_commit'] or p['baseline_public_count'] != 3902:
        raise RuntimeError('Unexpected proof-evolution baseline')
    if sha(EXPANSION.read_bytes()) != EXPANSION_SHA or p.get('expansion_plan_sha256') != EXPANSION_SHA:
        raise RuntimeError('Changed committed expansion plan')
    if sha(PRIOR_TYPES.read_bytes()) != PRIOR_TYPES_SHA:
        raise RuntimeError('Changed retained first-round types')
    expansion = json.loads(EXPANSION.read_text())
    if sha(COMPARISON.read_bytes()) != COMPARISON_SHA or p.get('comparison_plan_sha256') != COMPARISON_SHA:
        raise RuntimeError('Changed committed comparison plan')
    if sha(COMPARISON_TYPES.read_bytes()) != COMPARISON_TYPES_SHA or sha(COMPARISON_EVOLUTION.read_bytes()) != COMPARISON_EVOLUTION_SHA:
        raise RuntimeError('Changed retained second-round bindings')
    continuation = json.loads(COMPARISON.read_text())
    paths = {x['path']: x['file_sha256'] for x in samples()}
    if p['pristine_files'] != paths or len(paths) != 21 or len(p['changed_declarations']) != 36:
        raise RuntimeError('Pilot source/declaration allowlist changed')
    if p['changed_declarations'] != [x['declaration'] for x in samples()]:
        raise RuntimeError('Unexpected rewritten declaration list')
    prior = json.loads(PRIOR_TYPES.read_text())
    second = json.loads(COMPARISON_TYPES.read_text())
    if list(second) != list(prior) + expansion['additions'] or any(second.get(k) != v for k,v in prior.items()):
        raise RuntimeError('Changed first-round subset of retained second-round types')
    third = json.loads(LIBRARY_TYPES.read_text())
    if list(third) != list(second) + continuation['additions'] or any(third.get(k) != v for k,v in second.items()):
        raise RuntimeError('Changed second-round subset of retained third-round types')
    if sha((LIBRARY.parent/'pre-reuse-plan.json').read_bytes()) != 'b34d8ed4c095a8b9bbce028192154826d691116d292fa200d5faeac673a94562':
        raise RuntimeError('Changed initial committed library plan')
    if (sha(LIBRARY.read_bytes()) != LIBRARY_SHA or p.get('library_plan_sha256') != LIBRARY_SHA
            or sha(LIBRARY_TYPES.read_bytes()) != LIBRARY_TYPES_SHA
            or sha(LIBRARY_EVOLUTION.read_bytes()) != LIBRARY_EVOLUTION_SHA):
        raise RuntimeError('Changed committed library plan or retained third-round bindings')
    if p['additions'] != list(third) + json.loads(LIBRARY.read_text())['additions'] or len(set(p['additions'])) != 45:
        raise RuntimeError('Expected twenty-one retained and twenty-four explicitly listed new lemmas')
    frozen_path = EXPANSION.parent/'first-round-evolution.json'
    if sha(frozen_path.read_bytes()) != PRIOR_EVOLUTION_SHA:
        raise RuntimeError('Changed retained first-round evolution record')
    frozen = json.loads(frozen_path.read_text())
    second_source = json.loads(COMPARISON_EVOLUTION.read_text())
    active = {k:v['active_sha256'] for k,v in second_source['files'].items()}
    if any(active.get(k) != v['active_sha256'] for k,v in frozen['files'].items()) :
        raise RuntimeError('Changed prior-round source bindings')
    third_source = json.loads(LIBRARY_EVOLUTION.read_text())
    third_active = {k:v['active_sha256'] for k,v in third_source['files'].items()}
    if any(third_active.get(k) != v for k,v in active.items()) or p.get('prior_active_files') != third_active:
        raise RuntimeError('Changed third-round source bindings')
    if p.get('additional_prefixes') != {'OAI.KLInvariance.BruhatGraph.adapted_path_sources_le':"omit [Fintype I'] in",
            'OAI.KLInvariance.BruhatGraph.rTilde_weighted_sum_upper':'omit [Fintype I] in'}:
        raise RuntimeError('Unlisted assumption-omission prefix')
    return p

def active_modules(modules):
    """Return the migration graph plus exact hash-bound integration imports."""
    policy()
    active = {n:{**v,'imports':list(v['imports'])} for n,v in modules.items()}
    for name, additions in json.loads(LIBRARY.read_text()).get('integration_imports',{}).items():
        if name not in active or any(d not in active or d in active[name]['imports'] for d in additions):
            raise RuntimeError('Invalid integration import')
        active[name]['imports'] += additions
    return active

def difference(path, before, after):
    return ''.join(difflib.unified_diff(before.decode().splitlines(True),
        after.decode().splitlines(True), fromfile='pristine/'+path, tofile='active/'+path, n=0))

def edit_scope(before, after, path):
    """Line-level diff must stay in thirty-six proof bodies or forty-five documented additions.

This is a bounded source check, not a general Lean parser. The unchanged old
headers and full kernel type export are independent checks of the same edit.
"""
    from source_check import uncomment
    p = policy()
    def regions(text, additions):
        code = uncomment(text); spans = []
        names = [x['declaration'] for x in samples() if x['path'] == path]
        entries = [(n, False) for n in names]
        if additions: entries += [(n, True) for n in p['additions']]
        boundary = r'(?m)^(?:end\b|[ ]{0,1}(?:(?:private|noncomputable|protected)\s+)*(?:theorem|lemma|def|namespace|include)\b)'
        for name, new in entries:
            short = name.rsplit('.', 1)[-1]
            matches = list(re.finditer(r'(?m)^[ ]{0,1}(?:theorem|lemma)\s+'+re.escape(short)+r'\b', code))
            if not matches and new: continue
            if len(matches) != 1: raise RuntimeError('Ambiguous edit-scope declaration: '+name)
            pos = matches[0].start(); proof = code.index(':= by', pos)+len(':= by')
            following = re.search(boundary, code[proof:]); end = proof+following.start() if following else len(code)
            # Extraction can align an unchanged old header as a moved block.
            # Its literal bytes are compared independently in overlay below.
            start_line = code[:pos].count('\n')
            if new:
                doc = text.rfind('/--', 0, pos)
                if doc < 0: raise RuntimeError('Expected documented addition: '+name)
                start_line = text[:doc].count('\n')
                prefix = text[:doc].rstrip()
                permitted = {'OAI.KLInvariance.BruhatGraph.upper_polynomial_eq_symm':'include hub in',
                    **json.loads(EXPANSION.read_text())['permitted_prefixes'],
                    **json.loads(COMPARISON.read_text())['permitted_prefixes'],
                    **json.loads(LIBRARY.read_text())['permitted_prefixes'],
                    **p['additional_prefixes']}
                extra = permitted.get(name)
                if extra and prefix.endswith(extra):
                    start_line = text[:prefix.rfind(extra)].count('\n')
            if not new:
                doc = text.rfind('/--', 0, pos)
                if doc >= 0 and not text[doc+3:text.index('-/', doc)].count(':= by'):
                    prefix = text[:doc].rstrip()
                    # Only exact prefixes already present in the pristine source
                    # are admitted as insertion destinations in the active source.
                    if name == 'OAI.KLInvariance.IntegralSupport.supported_iff_annihilates' and prefix.endswith('include hp hbalanced in'):
                        spans.append((text[:prefix.rfind('include hp hbalanced in')].count('\n'), text[:doc].count('\n')))
            spans.append((start_line, code[:end].count('\n')))
        if additions:
            imports = json.loads(LIBRARY.read_text()).get('integration_imports',{}).get(path[:-5].replace('/','.'),[])
            for module in imports:
                line = 'import '+module+'\n'
                if text.count(line)!=1: raise RuntimeError('Missing explicit integration import: '+module)
                pos = text.index(line); spans.append((text[:pos].count('\n'),text[:pos].count('\n')+1))
        return spans
    old_regions = regions(before, False); new_regions = regions(after, True)
    covered = lambda lo, hi, spans, lines: all(not lines[i].strip() or any(a <= i < b for a,b in spans) for i in range(lo,hi))
    matcher = difflib.SequenceMatcher(a=before.splitlines(True), b=after.splitlines(True), autojunk=False)
    for tag,a,b,c,d in matcher.get_opcodes():
        if tag != 'equal' and (not covered(a,b,old_regions,before.splitlines()) or not covered(c,d,new_regions,after.splitlines())):
            raise RuntimeError('Edit outside approved proof/declaration spans: '+path+' '+repr((tag,a,b,c,d))+' old='+repr(before.splitlines()[a:b])+' new='+repr(after.splitlines()[c:d]))

def check_prior_source(path, after, p):
    if path in p['prior_active_files'] and sha(after) != p['prior_active_files'][path]:
        raise RuntimeError('Changed frozen prior-round source: '+path)


def overlay(files):
    """All other products stay pristine; every active exception is hash/diff-bound."""
    p = policy(); record = json.loads(MANIFEST.read_text())
    if record['schema'] != 1 or record['policy_sha256'] != sha(POLICY.read_bytes()):
        raise RuntimeError('Evolution policy binding changed')
    if set(record['files']) != set(p['pristine_files']):
        raise RuntimeError('Unexpected evolved file allowlist')
    patches = []
    for path, expected in p['pristine_files'].items():
        from module_integration import legacy_source
        before = files[path]; after = legacy_source(path, (HERE/path).read_bytes()); item = record['files'][path]
        if sha(before) != expected or item['pristine_sha256'] != expected:
            raise RuntimeError('Pristine reconstruction changed: '+path)
        if sha(after) != item['active_sha256'] or before == after:
            raise RuntimeError('Unrecorded active proof change: '+path)
        check_prior_source(path, after, p)
        edit_scope(before.decode(), after.decode(), path)
        patches.append(difference(path, before, after))
        # No new axiom command, unsafe bypass or global attribute is accepted.
        from source_check import uncomment
        old = uncomment(before.decode()); new = uncomment(after.decode())
        for token in ('axiom', 'unsafe', 'sorry', 'admit'):
            if len(re.findall(r'\b'+token+r'\b', new)) > len(re.findall(r'\b'+token+r'\b', old)):
                raise RuntimeError('New proof-bypass token: '+token)
        if new.count('@[') != old.count('@[') or new.count('attribute ') != old.count('attribute '):
            raise RuntimeError('New attributes are outside the pilot')
        files[path] = after
    patch = ''.join(patches).encode()
    if patch != (HERE/'proof-evolution.patch').read_bytes() or sha(patch) != record['diff_sha256']:
        raise RuntimeError('Evolution diff does not describe the exact active source')
    # Preserve literal old declaration headers as well as kernel-exported types.
    pristine = __import__('migrate').pristine_products()
    for sample in samples():
        name = sample['declaration'].rsplit('.', 1)[-1]
        headers = []
        for body in (pristine[sample['path']].decode(), legacy_source(sample['path'], (HERE/sample['path']).read_bytes()).decode()):
            matches = list(re.finditer(r'\b(?:theorem|lemma)\s+'+re.escape(name)+r'\b', body))
            if len(matches) != 1: raise RuntimeError('Ambiguous old theorem header: '+name)
            start = matches[0].start(); end = body.index(':= by', start)
            headers.append(body[start:end])
        if headers[0] != headers[1]: raise RuntimeError('Changed old theorem statement: '+name)
    return files

def compare_export(path):
    from compare_types import load, load_snapshot, compare
    p = policy()
    expected_bytes = (HERE/'additional-types.json').read_bytes()
    if json.loads(MANIFEST.read_text()).get('additional_types_sha256') != sha(expected_bytes):
        raise RuntimeError('Unbound additional-type snapshot')
    expected = json.loads(expected_bytes)
    if set(expected) != set(p['additions']) or any(v['kind'] != 'theorem' for v in expected.values()):
        raise RuntimeError('Additional type snapshot is not the exact forty-five-lemma allowlist')
    prior = json.loads(LIBRARY_TYPES.read_text())
    if any(expected.get(k) != v for k,v in prior.items()):
        raise RuntimeError('Changed retained prior-round added types')
    all_types = load(path, 3902+len(p['additions']))
    old = load_snapshot(HERE/'reference-public-types.json')
    if set(all_types) != set(old)|set(expected) or set(old)&set(expected):
        raise RuntimeError('Missing old API or unlisted new public declaration')
    result = compare(old, {k:all_types[k] for k in old})
    additions = compare(expected, {k:all_types[k] for k in expected})
    if not additions['passed']:raise RuntimeError('Old API or explicit added types changed: '+json.dumps([result,additions]))
    from attach_module import accept_change
    try:accepted=[] if result['passed'] else [accept_change(result)]
    except RuntimeError as e:raise RuntimeError('Old API or explicit added types changed: '+str(e)) from e
    return dict(old_api=result, additions=additions, accepted_representation_changes=accepted, passed=True)

def check_pilot_axioms(text):
    p = policy(); expected = set(p['additions'] + p['changed_declarations'])
    records = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.S)
    if len(records) != len(expected) or {n for n,_ in records} != expected:
        raise RuntimeError('Incomplete pilot axiom audit')
    allowed = {'propext','Classical.choice','Quot.sound'}
    for name, body in records:
        if not set(re.findall(r'[A-Za-z_][A-Za-z_.]*',body)) <= allowed:
            raise RuntimeError('New axiom outside allowlist: '+name)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--record',action='store_true');parser.add_argument('--check',action='store_true');parser.add_argument('--compare');args=parser.parse_args()
    if args.record:
        from migrate import pristine_products
        from module_integration import legacy_source
        p=policy();files=pristine_products();items={};patches=[]
        for path, expected in p['pristine_files'].items():
            before=files[path];after=legacy_source(path, (HERE/path).read_bytes())
            if sha(before)!=expected:raise RuntimeError('Wrong pristine baseline: '+path)
            items[path]=dict(pristine_sha256=expected,active_sha256=sha(after))
            patches.append(difference(path,before,after))
        patch=''.join(patches).encode();(HERE/'proof-evolution.patch').write_bytes(patch)
        MANIFEST.write_text(json.dumps(dict(schema=1,policy_sha256=sha(POLICY.read_bytes()),files=items,diff_sha256=sha(patch),additional_types_sha256=sha((HERE/'additional-types.json').read_bytes()) if (HERE/'additional-types.json').exists() else None),indent=2)+'\n')
        overlay(files)
    elif args.check:
        from migrate import products
        products()
        print(json.dumps(dict(pristine_public_count=3902,explicit_additions=45,evolved_files=21,old_headers_preserved=True,passed=True)))
    elif args.compare:print(json.dumps(compare_export(args.compare),indent=2))
    else:parser.error('choose --record or --compare')
if __name__=='__main__':main()
