#!/usr/bin/env python3
"""Record real command wall/CPU time; no model token telemetry is inferred."""
from pathlib import Path
from datetime import datetime, timezone
import json,os,resource,subprocess,sys,time
HERE=Path(__file__).resolve().parent;OUT=HERE.parents[1]/'results/lemma-granularity';OUT.mkdir(exist_ok=True)
label=sys.argv[1];command=sys.argv[2:]
if not label.replace('-','').isalnum() or not command:raise SystemExit('Expected simple label and command')
start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN);stamp=datetime.now(timezone.utc).isoformat()
env=os.environ.copy()
if command[0]=='lake':
 from validate import serial_environment
 env=serial_environment()
with (OUT/(label+'.log')).open('w') as log:result=subprocess.run(command,cwd=HERE,env=env,stdout=log,stderr=subprocess.STDOUT)
after=resource.getrusage(resource.RUSAGE_CHILDREN)
row=dict(label=label,command=command,started_utc=stamp,ended_utc=datetime.now(timezone.utc).isoformat(),wall_seconds=time.monotonic()-start,user_seconds=after.ru_utime-before.ru_utime,system_seconds=after.ru_stime-before.ru_stime,exit_code=result.returncode)
with (OUT/'measurements.jsonl').open('a') as log:log.write(json.dumps(row)+'\n')
print(json.dumps(row),flush=True)
if result.returncode:print((OUT/(label+'.log')).read_text()[-5000:])
raise SystemExit(result.returncode)
