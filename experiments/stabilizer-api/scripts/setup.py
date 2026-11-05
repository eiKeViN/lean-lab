#!/usr/bin/env python3
"""Materialize the pinned upstream and overlay without changing other experiments."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENT = ROOT / "environment"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*args, cwd=ENVIRONMENT, **kwargs):
    subprocess.run(args, cwd=cwd, check=True, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--with-regressions", action="store_true",
                        help="obtain only the six LFS certificates used by the regression targets")
    parser.add_argument("--skip-cache", action="store_true",
                        help="reuse an already populated official Mathlib cache")
    parser.add_argument("--workspace", type=Path,
                        help="place the generated checkout here and link environment/ to it")
    args = parser.parse_args()
    upstream = json.loads((ROOT / "provenance/upstream.json").read_text())
    baseline = json.loads((ROOT / "provenance/baseline-sources.json").read_text())
    overlay = json.loads((ROOT / "provenance/overlay-sources.json").read_text())
    process_env = os.environ.copy()
    process_env["GIT_LFS_SKIP_SMUDGE"] = "1"
    if args.workspace is not None:
        destination = args.workspace.expanduser().resolve()
        if ENVIRONMENT.is_symlink():
            if ENVIRONMENT.resolve() != destination:
                raise RuntimeError("environment already links to a different workspace; preserve it")
        elif ENVIRONMENT.exists():
            raise RuntimeError("environment already exists; preserve it before selecting another workspace")
        else:
            if destination == ENVIRONMENT.absolute():
                raise RuntimeError("--workspace must differ from the environment link path")
            if destination.exists() and not (destination / ".git").exists():
                if not destination.is_dir() or any(destination.iterdir()):
                    raise RuntimeError("the selected workspace is nonempty and is not a Git checkout")
            destination.mkdir(parents=True, exist_ok=True)
            ENVIRONMENT.symlink_to(destination, target_is_directory=True)
    if not (ENVIRONMENT / ".git").exists():
        if ENVIRONMENT.exists() and any(ENVIRONMENT.iterdir()):
            raise RuntimeError("the selected workspace is nonempty and is not the pinned Git checkout")
        ENVIRONMENT.mkdir(exist_ok=True)
        run("git", "init", "--quiet")
        run("git", "remote", "add", "origin", upstream["url"])
        run("git", "fetch", "--depth", "1", "origin", upstream["commit"], env=process_env)
        run("git", "checkout", "--detach", "FETCH_HEAD", env=process_env)
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ENVIRONMENT, text=True).strip()
    if head != upstream["commit"]:
        raise RuntimeError("environment HEAD differs from the pinned upstream; preserve it and use a fresh directory")
    previous_file = ENVIRONMENT / ".experiment-overlay.json"
    previous = json.loads(previous_file.read_text()) if previous_file.exists() else {}
    for relative, digest in baseline.items():
        path = ENVIRONMENT / relative
        allowed = {digest, overlay.get(relative), previous.get(relative)}
        if not path.exists() or sha(path) not in allowed:
            raise RuntimeError(f"unrecognized local source modification: {relative}")
    for relative, digest in overlay.items():
        source = ROOT / "overlay" / relative
        if sha(source) != digest:
            raise RuntimeError(f"update the reviewed overlay manifest before setup: {relative}")
        target = ENVIRONMENT / relative
        if target.exists() and relative not in baseline:
            if sha(target) not in {digest, previous.get(relative)}:
                raise RuntimeError(f"unrecognized local overlay modification: {relative}")
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or sha(target) != digest:
            # A changed source needs a fresh mtime so Lake invalidates cached file hashes.
            shutil.copyfile(source, target)
    for filename in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        source, target = ROOT / "config" / filename, ENVIRONMENT / filename
        if not target.exists() or target.read_bytes() != source.read_bytes():
            shutil.copyfile(source, target)
    previous_file.write_text(json.dumps(overlay, indent=2) + "\n")
    if args.with_regressions:
        paths = list(upstream["certificates"])
        valid = all((ENVIRONMENT / path).exists() and
                    sha(ENVIRONMENT / path) == info["sha256"]
                    for path, info in upstream["certificates"].items())
        if not valid:
            run("git", "lfs", "pull", "--include=" + ",".join(paths), "--exclude=")
        for path, info in upstream["certificates"].items():
            if sha(ENVIRONMENT / path) != info["sha256"]:
                raise RuntimeError(f"LFS certificate identity mismatch: {path}")
    if not args.skip_cache:
        run("lake", "exe", "cache", "get")
    print("Pinned environment and reviewed overlay prepared.")


if __name__ == "__main__":
    main()
