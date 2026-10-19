#!/usr/bin/env python3
"""Check preserved source blobs and resolved dependency pins without executing Lean."""
from pathlib import Path
import hashlib, json, subprocess
import sys
def require(condition, message):
    if not condition:
        sys.exit(message)
root = Path(__file__).resolve().parents[1]
p = root/'experiments/kl'
rows = [line.split('\t') for line in (root/'provenance/kl-blobs.tsv').read_text().splitlines()]
require(len(rows) == 34, 'Expected 34 source blobs')
require({str(f.relative_to(p)) for f in (p/'OAI').rglob('*.lean')} == {path for _,path in rows}, 'Source file set mismatch')
upstream = {path: sha for _,sha,path in [x.split('\t') for x in (root/'provenance/upstream.manifest.tsv').read_text().splitlines()[1:]]}
for sha,path in rows:
    data = (p/path).read_bytes()
    got = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    require(got == sha == upstream['lean/'+path], 'Source hash mismatch: '+path)
require((p/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1', 'Toolchain pin mismatch')
manifest=json.loads((p/'lake-manifest.json').read_text())
require(next(d['rev'] for d in manifest['packages'] if d['name']=='mathlib') == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'Mathlib pin mismatch')
for dep in manifest['packages']:
    directory=p/'.lake/packages'/dep['name']
    if directory.exists():
        actual=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'],text=True).strip()
        require(actual == dep['rev'], 'Dependency revision mismatch: '+dep['name'])
        subprocess.run(['git','-C',str(directory),'diff','--quiet','HEAD','--'],check=True)
for _,path in rows:
    for line in (p/path).read_text().splitlines():
        if line.startswith('import '):
            for module in line[7:].split():
                require(module == 'Mathlib' or (p/(module.replace('.', '/')+'.lean')).is_file(), 'Missing import: '+module)
print('34 source blobs match the upstream manifest; toolchain and available dependency revisions match.')
