#!/usr/bin/env python3
"""Capture actual input identities before one integration command; reuse measure.py."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
output=Path(sys.argv[1]).resolve();output.parent.mkdir(parents=True,exist_ok=True)
identity=output.with_suffix('.inputs.json')
if identity.exists():raise SystemExit('Refusing to overwrite recorded execution: '+str(identity))
paths=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=ROOT).decode().split('\0')
hashes={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(set(paths)) if p and (ROOT/p).is_file()}
for arg in sys.argv[2:]:
    candidate=Path(arg)
    if candidate.is_file():hashes[str(candidate.resolve())]=hashlib.sha256(candidate.read_bytes()).hexdigest()
identity.write_text(json.dumps(dict(schema=1,captured_at_unix=time.time(),command=sys.argv[2:],
    cwd=str(ROOT),git_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    tracked_diff_sha256=hashlib.sha256(subprocess.check_output(['git','diff','HEAD','--binary'],cwd=ROOT)).hexdigest(),
    files=hashes),indent=2)+'\n')
raise SystemExit(subprocess.call([sys.executable,str(ROOT/'scripts/measure.py'),str(output),*sys.argv[2:]],cwd=ROOT))
