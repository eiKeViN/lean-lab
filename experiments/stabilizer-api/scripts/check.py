#!/usr/bin/env python3
"""Check source identity, typed API contracts, consumers, axioms and comparisons."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import runpy
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENT = ROOT / "environment"
RESULTS = ROOT / "results"
CORE = ["LeanQEC.Stabilizer.Examples.DownstreamAPI",
        "LeanQEC.Stabilizer.Examples.PublicTypes",
        "LeanQEC.Stabilizer.Examples.PresentationWorkflow"]


def check_identity(baseline, overlay, upstream, with_certificates):
    """Verify the same complete source set before and after the build."""
    expected = {**baseline, **overlay}
    for relative, digest in expected.items():
        actual = hashlib.sha256((ENVIRONMENT / relative).read_bytes()).hexdigest()
        if actual != digest:
            raise RuntimeError(f"source identity mismatch: {relative}")
    lean_sources = {str(p.relative_to(ENVIRONMENT))
                    for p in (ENVIRONMENT / "LeanQEC").rglob("*.lean")}
    if lean_sources != {p for p in expected if p.endswith(".lean")}:
        raise RuntimeError("unrecorded or missing LeanQEC source files")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ENVIRONMENT, text=True).strip()
    if head != upstream["commit"]:
        raise RuntimeError("upstream commit mismatch")
    for filename in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        if (ENVIRONMENT / filename).read_bytes() != (ROOT / "config" / filename).read_bytes():
            raise RuntimeError(f"curated configuration mismatch: {filename}")
    pins = json.loads((ENVIRONMENT / "lake-manifest.json").read_text())["packages"]
    mathlib = next(p for p in pins if p["name"] == "mathlib")
    if mathlib["rev"] != upstream["mathlib"]:
        raise RuntimeError("Mathlib manifest mismatch")
    if not (ENVIRONMENT / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").is_file():
        raise RuntimeError("official Mathlib cache missing; run setup.py before checking")
    for package in pins:
        checkout = ENVIRONMENT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
        if revision != package["rev"]:
            raise RuntimeError(f"dependency checkout mismatch: {package['name']}")
    if with_certificates:
        for relative, certificate in upstream["certificates"].items():
            digest = hashlib.sha256((ENVIRONMENT / relative).read_bytes()).hexdigest()
            if digest != certificate["sha256"]:
                raise RuntimeError(f"obtain the pinned LFS certificate: {relative}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core-only", action="store_true")
    parser.add_argument("--skip-comparison", action="store_true")
    args = parser.parse_args()
    RESULTS.mkdir(exist_ok=True)
    baseline = json.loads((ROOT / "provenance/baseline-sources.json").read_text())
    overlay = json.loads((ROOT / "provenance/overlay-sources.json").read_text())
    upstream = json.loads((ROOT / "provenance/upstream.json").read_text())
    check_identity(baseline, overlay, upstream, not args.core_only)
    runner = runpy.run_path(str(ENVIRONMENT / "scripts/check_stabilizer_api.py"))
    targets = CORE if args.core_only else runner["DEFAULT_TARGETS"]
    modules = runner["build_order"](targets)
    requested_axioms = sorted({name for module in modules for name in re.findall(
        r"^#print axioms (\S+)",
        (ENVIRONMENT / (module.replace(".", "/") + ".lean")).read_text(), re.MULTILINE)})
    report = {"source_identity_before": "passed", "source_identity_after": "not_run",
              "upstream": upstream["commit"],
              "mathlib": upstream["mathlib"], "baseline_sources": len(baseline),
              "overlay_sources": len(overlay), "core_only": args.core_only,
              "targets": targets, "local_module_count": len(modules), "local_modules": modules,
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "compilation": "not_run", "printed_axioms": "not_run",
              "comparison": "not_run"}
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "2")
    command = [sys.executable, "scripts/check_stabilizer_api.py"] + (CORE if args.core_only else [])
    with (RESULTS / "build.log").open("w") as log:
        result = subprocess.run(command, cwd=ENVIRONMENT, env=env, stdout=log, stderr=subprocess.STDOUT)
    report["compilation"] = "passed" if result.returncode == 0 else "failed"
    text = (RESULTS / "build.log").read_text()
    printed = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
               for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.DOTALL)}
    report["axioms"] = {name: printed[name] for name in requested_axioms if name in printed}
    report["missing_axiom_prints"] = [name for name in requested_axioms if name not in printed]
    report["printed_axioms"] = ("passed_no_sorryAx" if not report["missing_axiom_prints"] and
                                 "sorryAx" not in text else "failed")
    if result.returncode:
        print(text[-14000:])
    elif not args.skip_comparison:
        with (RESULTS / "comparison.log").open("w") as log:
            result = subprocess.run([sys.executable, str(ROOT / "comparison/verify.py"), str(ENVIRONMENT)],
                                    env=env, stdout=log, stderr=subprocess.STDOUT)
        report["comparison"] = "passed" if result.returncode == 0 else "failed"
        if result.returncode:
            print((RESULTS / "comparison.log").read_text()[-14000:])
    try:
        check_identity(baseline, overlay, upstream, not args.core_only)
        report["source_identity_after"] = "passed"
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        report["source_identity_after"] = "failed"
        report["source_identity_error"] = str(error)
    report["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (RESULTS / "acceptance.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0 if (report["compilation"] == "passed" and
                 report["source_identity_after"] == "passed" and
                 report["printed_axioms"] == "passed_no_sorryAx" and
                 report["comparison"] in {"passed", "not_run"}) else 1


if __name__ == "__main__":
    raise SystemExit(main())
