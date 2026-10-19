#!/usr/bin/env python3
"""Record wall time, child CPU time, peak RSS and exit status, without GNU time."""
import json, pathlib, resource, subprocess, sys, time
out = pathlib.Path(sys.argv[1]); out.parent.mkdir(parents=True, exist_ok=True)
start = time.monotonic()
with out.open('w') as log:
    status = subprocess.call(sys.argv[2:], stdout=log, stderr=subprocess.STDOUT)
r = resource.getrusage(resource.RUSAGE_CHILDREN)
metrics = dict(command=sys.argv[2:], exit_code=status, wall_seconds=time.monotonic()-start,
               user_seconds=r.ru_utime, system_seconds=r.ru_stime, max_rss_kib=r.ru_maxrss)
out.with_suffix('.json').write_text(json.dumps(metrics, indent=2)+'\n')
print(json.dumps(metrics))
if status:
    print(out.read_text()[-5000:])
sys.exit(status)
