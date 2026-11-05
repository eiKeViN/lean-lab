#!/usr/bin/env python3
"""Record bounded synthesis outcomes; a resource limit is not absence of an instance."""
from pathlib import Path
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENT = ROOT / "environment"


def main():
    results = ROOT / "results/instance-profile"
    results.mkdir(parents=True, exist_ok=True)
    old_library = ROOT / "comparison/.verification/old-lib"
    if not (old_library / "LeanQEC/Stabilizer/Basic.olean").exists():
        raise RuntimeError("run the isolated comparison first")
    lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                        cwd=ENVIRONMENT, text=True).strip()
    prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                     cwd=ENVIRONMENT, text=True).strip()
    lean = Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    records = []
    for variant, imported in [("before", "LeanQEC.Stabilizer.Basic"),
                              ("after", "LeanQEC.Stabilizer.API")]:
        source = results / (variant + ".lean")
        source.write_text(f"import {imported}\nset_option synthInstance.maxHeartbeats 2000\n"
                          "example (n : ℕ) : CommGroup (PauliGroup_group n) := inferInstance\n")
        env = os.environ.copy()
        env["LEAN_PATH"] = (str(old_library) + ":" if variant == "before" else "") + lean_path
        try:
            run = subprocess.run([str(lean), str(source)], cwd=results, env=env,
                                 capture_output=True, text=True, timeout=60)
            output = run.stdout + run.stderr
            if run.returncode == 0:
                status = "synthesized"
            elif any(term in output.lower() for term in
                     ["heartbeats", "maximum recursion depth", "timed out"]):
                status = "resource_limit"
            elif "failed to synthesize" in output.lower():
                status = "no_instance_reported"
            else:
                status = "unexpected_error"
        except subprocess.TimeoutExpired:
            status, output = "wall_timeout", "Process exceeded the 60-second wall budget."
        (results / (variant + ".log")).write_text(output)
        records.append({"variant": variant, "synthesis_heartbeats": 2000, "outcome": status})
    report = {"purpose": "bounded observation, not a theorem or complete performance benchmark",
              "records": records}
    (results / "outcomes.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 1 if any(r["outcome"] == "unexpected_error" for r in records) else 0


if __name__ == "__main__":
    raise SystemExit(main())
