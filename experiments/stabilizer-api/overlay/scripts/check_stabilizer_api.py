#!/usr/bin/env python3
"""Build the stabilizer API and representative consumers in dependency order.

Requires the repository's normal Lean toolchain, Mathlib cache, and LFS files.
Building local modules in order bounds memory use on smaller development hosts.
Additional module names on the command line replace the default target list.
"""

from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TARGETS = [
    "LeanQEC.Stabilizer.Examples.DownstreamAPI",
    "LeanQEC.Stabilizer.Examples.PublicTypes",
    "LeanQEC.Stabilizer.Examples.PresentationWorkflow",
    "LeanQEC.Stabilizer.Examples.Steane",
    "LeanQEC.Stabilizer.Examples.Golay",
    "LeanQEC.Stabilizer.Examples.BB.BB54",
    "LeanQEC.Stabilizer.Examples.Surface.Planar",
    "LeanQEC.Stabilizer.Examples.Surface.Toric",
]


def build_order(targets):
    seen = set()
    order = []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        for dependency in re.findall(
            r"^import\s+(LeanQEC\.[\w.]+)", source.read_text(), re.MULTILINE
        ):
            visit(dependency)
        order.append(module)

    for target in targets:
        visit(target)
    return order


def main():
    order = build_order(sys.argv[1:] or DEFAULT_TARGETS)
    for index, module in enumerate(order, 1):
        print(f"[{index}/{len(order)}] {module}", flush=True)
        result = subprocess.run(["lake", "build", module], cwd=ROOT)
        if result.returncode:
            return result.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
