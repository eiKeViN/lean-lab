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

def sha(data):
    return hashlib.sha256(data).hexdigest()

def policy():
    p = json.loads(POLICY.read_text())
    original = json.loads(PLAN.read_text())
    if p['base_commit'] != original['base_commit'] or p['baseline_public_count'] != 3902:
        raise RuntimeError('Unexpected proof-evolution baseline')
    paths = {x['path']: x['file_sha256'] for x in original['samples']}
    if p['pristine_files'] != paths or len(paths) != 3 or len(p['changed_declarations']) != 4:
        raise RuntimeError('Pilot source/declaration allowlist changed')
    if p['changed_declarations'] != [x['declaration'] for x in original['samples']]:
        raise RuntimeError('Unexpected rewritten declaration list')
    if len(p['additions']) != 5 or len(set(p['additions'])) != 5:
        raise RuntimeError('Expected five explicitly listed new lemmas')
    return p

def difference(path, before, after):
    return ''.join(difflib.unified_diff(before.decode().splitlines(True),
        after.decode().splitlines(True), fromfile='pristine/'+path, tofile='active/'+path))

def edit_scope(before, after, path):
    """Line-level diff must stay in four proof bodies or five documented additions.

This is a bounded source check, not a general Lean parser. The unchanged old
headers and full kernel type export are independent checks of the same edit.
"""
    from source_check import uncomment
    plan = json.loads(PLAN.read_text()); p = policy()
    def regions(text, additions):
        code = uncomment(text); spans = []
        names = [x['declaration'] for x in plan['samples'] if x['path'] == path]
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
            start_line = code[:proof].count('\n')+1
            if new:
                doc = text.rfind('/--', 0, pos)
                if doc < 0: raise RuntimeError('Expected documented addition: '+name)
                start_line = text[:doc].count('\n')
                prefix = text[:doc].rstrip()
                if prefix.endswith('include hub in'):
                    start_line = text[:prefix.rfind('include hub in')].count('\n')
            spans.append((start_line, code[:end].count('\n')))
        return spans
    old_regions = regions(before, False); new_regions = regions(after, True)
    covered = lambda lo, hi, spans: all(any(a <= i < b for a,b in spans) for i in range(lo,hi))
    matcher = difflib.SequenceMatcher(a=before.splitlines(True), b=after.splitlines(True), autojunk=False)
    for tag,a,b,c,d in matcher.get_opcodes():
        if tag != 'equal' and (not covered(a,b,old_regions) or not covered(c,d,new_regions)):
            raise RuntimeError('Edit outside approved proof/declaration spans: '+path)

def overlay(files):
    """All other products stay pristine; every active exception is hash/diff-bound."""
    p = policy(); record = json.loads(MANIFEST.read_text())
    if record['schema'] != 1 or record['policy_sha256'] != sha(POLICY.read_bytes()):
        raise RuntimeError('Evolution policy binding changed')
    if set(record['files']) != set(p['pristine_files']):
        raise RuntimeError('Unexpected evolved file allowlist')
    patches = []
    for path, expected in p['pristine_files'].items():
        before = files[path]; after = (HERE/path).read_bytes(); item = record['files'][path]
        if sha(before) != expected or item['pristine_sha256'] != expected:
            raise RuntimeError('Pristine reconstruction changed: '+path)
        if sha(after) != item['active_sha256'] or before == after:
            raise RuntimeError('Unrecorded active proof change: '+path)
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
    original_plan = json.loads(PLAN.read_text())
    pristine = __import__('migrate').pristine_products()
    for sample in original_plan['samples']:
        name = sample['declaration'].rsplit('.', 1)[-1]
        headers = []
        for body in (pristine[sample['path']].decode(), (HERE/sample['path']).read_text()):
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
        raise RuntimeError('Additional type snapshot is not the exact five-lemma allowlist')
    all_types = load(path, 3902+len(p['additions']))
    old = load_snapshot(HERE/'reference-public-types.json')
    if set(all_types) != set(old)|set(expected) or set(old)&set(expected):
        raise RuntimeError('Missing old API or unlisted new public declaration')
    result = compare(old, {k:all_types[k] for k in old})
    additions = compare(expected, {k:all_types[k] for k in expected})
    if not result['passed'] or not additions['passed']:
        raise RuntimeError('Old API or explicit added types changed: '+json.dumps([result, additions]))
    return dict(old_api=result, additions=additions, passed=True)

def check_pilot_axioms(text):
    p = policy(); expected = set(p['additions'] + p['changed_declarations'])
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
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
        p=policy();files=pristine_products();items={};patches=[]
        for path, expected in p['pristine_files'].items():
            before=files[path];after=(HERE/path).read_bytes()
            if sha(before)!=expected:raise RuntimeError('Wrong pristine baseline: '+path)
            items[path]=dict(pristine_sha256=expected,active_sha256=sha(after))
            patches.append(difference(path,before,after))
        patch=''.join(patches).encode();(HERE/'proof-evolution.patch').write_bytes(patch)
        MANIFEST.write_text(json.dumps(dict(schema=1,policy_sha256=sha(POLICY.read_bytes()),files=items,diff_sha256=sha(patch),additional_types_sha256=sha((HERE/'additional-types.json').read_bytes()) if (HERE/'additional-types.json').exists() else None),indent=2)+'\n')
        overlay(files)
    elif args.check:
        from migrate import products
        products()
        print(json.dumps(dict(pristine_public_count=3902,explicit_additions=5,evolved_files=3,old_headers_preserved=True,passed=True)))
    elif args.compare:print(json.dumps(compare_export(args.compare),indent=2))
    else:parser.error('choose --record or --compare')
if __name__=='__main__':main()
