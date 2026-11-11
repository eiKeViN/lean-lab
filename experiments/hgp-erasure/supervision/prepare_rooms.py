"""Create four clean trial rooms. Run once, before any participant is started."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent / "packet"
SHEAF = "ee75eba0f29643aafb51bca895a85d09d45e6691"
SHEAF_SETTINGS = """Read the SHEAF root AGENTS.md and start the project using its launcher procedure.
The project is named project. The source paper and approved targets are in
source.md (A through E) and acceptance.md; they have been approved for this
run. The prepared project is project/lean, its pinned dependencies are already
installed, and the shell starts in /work. Adopt this project and copy missing
coordination and role files from template/. Model/effort are gpt-6.1-sol/high
for all sessions. The total session cap is four people including the launcher,
there is no early human sign-off, and final output is local. On this host the
session transport for independently launching a maintainer or lead and
their workers is the provided spawn/status/wait/message API in place of tmux.
A spawned role has a fresh context. Use its prompt to identify its project
and contract. The source and scope above resolve the interactive setup fields.
"""


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument("base", type=Path, help="host runtime root containing sheaf-upstream")
    a.add_argument("destination", type=Path)
    args = a.parse_args()
    root = args.base.resolve()
    dest = args.destination.resolve()
    dest.mkdir(exist_ok=False)
    sheaf = root / "sheaf-upstream"
    if subprocess.check_output(["git", "-C", str(sheaf), "rev-parse", "HEAD"], text=True).strip() != SHEAF:
        raise SystemExit("SHEAF revision mismatch")
    if subprocess.check_output(["git", "-C", str(sheaf), "status", "--porcelain"]):
        raise SystemExit("dirty SHEAF tree")
    rng = random.Random(20261111)
    slots = [(a, r) for r in (1,2) for a in ("SHEAF","free")]
    rng.shuffle(slots)
    ids = ["cedar","flint","maple","slate"]
    rows=[]
    for i, (variant,replicate) in enumerate(slots):
        code=ids[i]
        room=dest/"rooms"/code
        room.mkdir(parents=True)
        if variant == "SHEAF":
            subprocess.run(["git", "-C", str(sheaf), "checkout-index", "-a", "--prefix", str(room)+"/"], check=True)
        for file in PACKET.iterdir():
            shutil.copy2(file,room/file.name)
        project=room/"project"
        project.mkdir()
        shutil.copytree(HERE/"lean-project", project/"lean", ignore=shutil.ignore_patterns(".lake","__pycache__"))
        if variant == "SHEAF":
            for name in ("source.md","acceptance.md","ENVIRONMENT.md"):
                shutil.copy2(PACKET/name,project/name)
        (dest/"prompts").mkdir(exist_ok=True)
        prompt=(PACKET/"task.txt").read_text()+("\n"+SHEAF_SETTINGS if variant=="SHEAF" else "")
        (dest/"prompts"/(code+".txt")).write_text(prompt)
        rows.append({"id":code,"arm":variant,"replicate":replicate,"cpus":[2*i,2*i+1],
                     "prompt_sha256":hashlib.sha256(prompt.encode()).hexdigest()})
    (dest/"runs.json").write_text(json.dumps(rows,indent=2)+"\n")
    print(json.dumps(rows))


if __name__ == "__main__":
    main()
