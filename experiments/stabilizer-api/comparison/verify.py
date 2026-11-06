#!/usr/bin/env python3
"""Verify the examples against the two isolated Lean-QEC interfaces.

Run from a normal Lean installation, after building Stabilizer.API at the new
revision: python3 verify.py /absolute/path/to/lean-qec-downstream
The original Basic/CSS files are compiled into a separate import root.
Unchanged dependency object files are reused; new Stabilizer API modules are
never imported by the old-side examples.
"""

from pathlib import Path
import argparse
import os
import subprocess


ROOT = Path(__file__).resolve().parent
BASE = "8d115519b471b71a21fbdddf5341d8203b841cc9"
NEW = BASE


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    overlay = __import__("json").loads((ROOT.parent / "provenance/overlay-sources.json").read_text())
    import hashlib
    for relative, digest in overlay.items():
        if hashlib.sha256((repo / relative).read_bytes()).hexdigest() != digest:
            parser.error(f"reviewed overlay mismatch: {relative}")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if revision != NEW:
        parser.error(f"prepare the pinned experiment environment {NEW} first")
    library = repo / ".lake/build/lib/lean/LeanQEC"
    if not (library / "Stabilizer/API.olean").exists():
        parser.error("build LeanQEC.Stabilizer.API in the implementation checkout first")
    for module in ("Basic", "CSS"):
        relative = f"LeanQEC/Stabilizer/{module}.lean"
        original = subprocess.check_output(["git", "show", f"{BASE}:{relative}"], cwd=repo)
        if original != (ROOT / "before" / relative).read_bytes():
            parser.error(f"original source mismatch: {relative}")

    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, text=True
    ).strip()
    lean_prefix = subprocess.check_output(
        ["lake", "env", "lean", "--print-prefix"], cwd=repo, text=True
    ).strip()
    lean = Path(lean_prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    output = ROOT / ".verification"
    old_library = output / "old-lib"
    old_stabilizer = old_library / "LeanQEC/Stabilizer"
    old_stabilizer.mkdir(parents=True, exist_ok=True)
    logs = output / "logs"
    logs.mkdir(exist_ok=True)
    for source in library.iterdir():
        if source.name == "Stabilizer":
            continue
        destination = old_library / "LeanQEC" / source.name
        if not destination.exists():
            destination.symlink_to(source, target_is_directory=source.is_dir())

    tasks = [
        ("before", f"LeanQEC/Stabilizer/{module}", old_library)
        for module in ("Basic", "CSS")
    ] + [
        ("before", module, old_library)
        for module in ("Before", "BeforeLinear", "UserReindex", "BeforeTransport")
    ] + [("after", "After", output / "new-lib")]
    for side, module, target in tasks:
        destination = target / (module + ".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        env = os.environ.copy()
        env["LEAN_PATH"] = (str(old_library) + ":" if side == "before" else "") + lean_path
        log = logs / (module.replace("/", ".") + ".log")
        with log.open("w") as stream:
            result = subprocess.run(
                [str(lean), str(ROOT / side / (module + ".lean")),
                 "-o", str(destination)],
                cwd=ROOT / side, env=env, stdout=stream, stderr=subprocess.STDOUT,
            )
        if result.returncode:
            print(log.read_text())
            return result.returncode
        print(f"PASS {side}/{module}.lean", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
