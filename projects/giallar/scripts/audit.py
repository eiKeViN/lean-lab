#!/usr/bin/env python3
"""Audit freshly built Giallar declarations and retain public types and exact source identities."""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = sorted([ROOT / "Giallar.lean", *ROOT.joinpath("Giallar").glob("*.lean")])


def code_without_comments(text: str) -> str:
    """Remove Lean's nested comments and strings before scanning prohibited source constructs."""
    out: list[str] = []
    i, depth = 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    out.extend("  ")
                    i += 2
                elif text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    assert depth == 0, "Unclosed Lean comment"
    return "".join(out)


for source in SOURCES:
    code = code_without_comments(source.read_text())
    for pattern in [r"\b(sorry|sorryAx|admit|axiom|unsafe|partial|native_decide)\b",
                    r"\b(ofReduceBool|trustCompiler|addAndCompile|implemented_by|extern)\b",
                    r"\b(meta|elab|macro|run_cmd|run_elab|run_tac|_unsafe_rec)\b"]:
        match = re.search(pattern, code)
        if match:
            line = code[:match.start()].count("\n") + 1
            raise RuntimeError(f"Rejected source construct {match[0]} at {source}:{line}")

subprocess.run(["lake", "env", "lean", "scripts/audit.lean"], cwd=ROOT, check=True)
output = ROOT / "evidence/axioms.json"
result = json.loads(output.read_text())
expected = {"Giallar"} | {f"Giallar.{p.stem}" for p in ROOT.joinpath("Giallar").glob("*.lean")}
actual = set(result["audited_modules"])
assert expected == actual, f"Module coverage mismatch: missing {expected-actual}, extra {actual-expected}"
assert result["status"] == "PASS" and not result["rejected"]
result["source_sha256"] = {
    str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in SOURCES
}
result["source_construct_scan"] = "PASS"
result["module_coverage"] = "PASS"
output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(f"PASS: {len(SOURCES)} source files; {result['declaration_count']} exported declarations; "
      f"{len(actual)} modules; transitive axioms restricted to declared allowlist")
