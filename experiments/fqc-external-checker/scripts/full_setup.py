"""Install exact integration dependencies and request only the needed official caches."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

import full
import run as base


def command(args, cwd=None):
    subprocess.run(args, cwd=cwd, check=True)


def setup(verify_only=False):
    version = base.toolchain()
    manifest, _ = full.locked()
    expected = json.loads(full.upstream("lake-manifest.json"))
    expected["name"] = "«fqc-photochemistry»"
    for package in expected["packages"]:
        if not package["inherited"]:
            package["inputRev"] = package["rev"]
    actual = json.loads((full.INTEGRATION / "lake-manifest.json").read_text())
    if actual != expected:
        raise ValueError("Integration dependency lock differs from pinned upstream revisions")
    pins = {}
    for package in actual["packages"]:
        directory = full.INTEGRATION / ".lake/packages" / package["name"]
        if not (directory / ".git").exists():
            if verify_only:
                raise ValueError(f"Missing dependency {package['name']}; run full setup")
            directory.mkdir(parents=True, exist_ok=True)
            command(["git", "init", "-q", str(directory)])
            command(["git", "remote", "add", "origin", package["url"]], directory)
            command(["git", "fetch", "--depth", "1", "origin", package["rev"]], directory)
            command(["git", "checkout", "--detach", "FETCH_HEAD"], directory)
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Dependency pin mismatch: {package['name']}")
        command(["git", "diff", "--quiet", "HEAD", "--"], directory)
        pins[package["name"]] = revision
    physlib = full.INTEGRATION / ".lake/packages/physlib"
    todo = list(manifest["external_imports"])
    mathlib, phys_modules = set(), set()
    while todo:
        module = todo.pop()
        if module.startswith("Mathlib."):
            mathlib.add(module)
        elif module.startswith(("QuantumInfo.", "Physlib.")) and module not in phys_modules:
            phys_modules.add(module)
            path = physlib / (module.replace(".", "/")+".lean")
            todo.extend(full.imports(path.read_text()))
    if not verify_only:
        # Never execute the preserved FQC lakefile, update pins or request all Mathlib.
        command(["lake", "exe", "cache", "get", *sorted(mathlib)], full.INTEGRATION)
        roots = [n for n in manifest["external_imports"] if n.startswith("QuantumInfo.")]
        for module in roots:
            command(["lake", "build", "+"+module+":olean"], full.INTEGRATION)
    report = {"status": "pins-verified" if verify_only else "ready", "toolchain": version,
        "dependencies": pins, "mathlib_cache_roots": sorted(mathlib),
        "physlib_source_closure": sorted(phys_modules), "upstream_lakefile_executed": False}
    full.RESULTS.mkdir(parents=True, exist_ok=True)
    (full.RESULTS / "dependencies.json").write_text(json.dumps(report, indent=2)+"\n")
    print(f"Exact pins verified; {len(mathlib)} Mathlib cache roots, {len(phys_modules)} Physlib modules")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true")
    setup(parser.parse_args().verify_only)
