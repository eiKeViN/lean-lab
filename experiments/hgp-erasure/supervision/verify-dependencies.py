#!/usr/bin/env python3
"""Verify the frozen Lean project in a fresh offline room, then publish readiness."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone

ROOT = Path(os.environ.get("HGP_RUNTIME_ROOT", Path(__file__).resolve().parents[4])).resolve()
os.environ["HGP_RUNTIME_ROOT"] = str(ROOT)
from room import execute

SUPERVISION = Path(__file__).resolve().parent
PREFLIGHT = ROOT / "preflight"
PREFLIGHT.mkdir(exist_ok=True)
(PREFLIGHT / "room-ready.ok").unlink(missing_ok=True)
expected_qec = "c0ff74952c65b48e2ba5430fc4dfa4459d120440"
actual_qec = subprocess.check_output(["git", "-C", str(ROOT / "qecert"), "rev-parse", "HEAD"], text=True).strip()
if actual_qec != expected_qec:
    raise SystemExit(f"QEC source pin mismatch: {actual_qec}")
subprocess.run(["git", "-C", str(ROOT / "qecert"), "diff", "--quiet", "HEAD"], check=True)
manifest = json.loads((ROOT / "qecert/lake-manifest.json").read_text())
for package in manifest["packages"]:
    source = ROOT / "qecert/.lake/packages" / package["name"]
    actual = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    if actual != package["rev"]:
        raise SystemExit(f"Dependency pin mismatch: {package['name']}: {actual}")
room = Path(tempfile.mkdtemp(prefix="hgp-room-smoke-", dir=PREFLIGHT))
shutil.copytree(SUPERVISION / "lean-project", room / "lean-project",
                ignore=shutil.ignore_patterns(".lake"))
command = "cd lean-project && lake env lean HGPExperiment.lean && lake build HGPExperiment"
output = execute(room, command, 600)
(PREFLIGHT / "hgp-room-check.log").write_text(output)
if not output.startswith("[exit 0]\n"):
    print(output)
    raise SystemExit("Offline room verification failed; readiness marker not written.")
record = {
    "checked_at": datetime.now(timezone.utc).isoformat(),
    "command": command,
    "room": str(room),
    "toolchain": "leanprover/lean4:v4.33.1",
    "qecert_rev": "c0ff74952c65b48e2ba5430fc4dfa4459d120440",
    "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474",
    "dependency_mounts": {"/opt/lean": "read-only", "/opt/qecert": "read-only"},
    "network": "room.py denies network sockets",
    "result": "exit 0",
    "log": str(PREFLIGHT / "hgp-room-check.log"),
}
(PREFLIGHT / "hgp-dependency-readiness.json").write_text(json.dumps(record, indent=2) + "\n")
marker = PREFLIGHT / "room-ready.ok"
marker.with_suffix(".tmp").write_text("Offline import and build passed.\n" + command + "\n")
marker.with_suffix(".tmp").replace(marker)
print("Offline import and build passed; readiness marker written.")
print(command)
