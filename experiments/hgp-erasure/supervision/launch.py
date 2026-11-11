"""Start and supervise the registered four sessions in separate working trees."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base",type=Path)
    parser.add_argument("study",type=Path)
    args=parser.parse_args()
    root=args.base.resolve()
    study=args.study.resolve()
    runs=json.loads((study/"runs.json").read_text())
    if (study/"start.json").exists():
        raise SystemExit("study already started")
    # Verify the shared installation through exactly the shell that participants use.
    os.environ["HGP_RUNTIME_ROOT"]=str(root)
    from room import execute
    result=execute(study/"rooms"/runs[0]["id"],"cd project/lean && lake build HGPExperiment && lake env lean HGPExperiment.lean",180)
    (study/"preflight-build.txt").write_text(result)
    if not result.startswith("[exit 0]"):
        raise SystemExit(result[-1500:])
    for row in runs:
        project=study/"rooms"/row["id"]/"project"/"lean"
        shutil.rmtree(project/".lake",ignore_errors=True)
    children=[]
    outputs=[]
    starts={}
    try:
        for row in runs:
            key=row["id"]
            output=(study/(key+".runner.log")).open("x")
            outputs.append(output)
            now=time.time()
            cmd=["taskset","-c",",".join(map(str,row["cpus"])),sys.executable,str(HERE/"runner.py"),
                 "--room",str(study/"rooms"/key),"--evidence",str(study/"evidence"/key),
                 "--prompt",str(study/"prompts"/(key+".txt")),"--seconds","3600","--units","12000000"]
            children.append(subprocess.Popen(cmd,stdout=output,stderr=subprocess.STDOUT))
            starts[key]=now
            (study/"start.json").write_text(json.dumps(starts,indent=2)+"\n")
        statuses={r["id"]:p.wait() for r,p in zip(runs,children)}
        (study/"process-exit.json").write_text(json.dumps(statuses,indent=2)+"\n")
        return int(any(statuses.values()))
    finally:
        for child in children:
            if child.poll() is None:
                child.terminate()
        for output in outputs:
            output.close()

if __name__=="__main__":
    raise SystemExit(main())
