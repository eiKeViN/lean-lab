"""Execute three original closed Cauchy predicates outside the kernel."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

import source
import run as base

MODULE = source.MODULE+"HalfPlaneCauchyWalkCore"
PART = MODULE+"Parts.Part12"
DEFS = MODULE+"Parts.Part12Defs"
NS = "QuantumComputation.Specs.PhotochemistrySolution.CompactCauchy"
CLAIMS = [
    {"name": "finite", "axiom": NS+".External.finite",
     "original_theorem": NS+".sum_fin_subCoin_3326847_le",
     "term": "checkSegListAuto 33258891316 3326847 10000 (segsD847C0 ++ segsD847C1 ++ segsD847C2 ++ segsD847C3)"},
    {"name": "tail", "axiom": NS+".External.tail",
     "original_theorem": NS+".sum_tail_subCoin_3326847_le",
     "term": "checkTailAuto 33258891316 3327649 36672351 10000 283000 733450"},
    {"name": "halfplane", "axiom": NS+".External.halfplane",
     "original_theorem": NS+".sum_u_subCoin_3326847_le",
     "term": "checkHalfWalkUAuto 33258891316 3326847 802 10000 407380 304768876"},
]


def facts():
    original = json.loads((source.ROOT / "provenance/photochemistry.json").read_text())
    expected = {"upstream": source.COMMIT, "source_module": MODULE,
        "source_sha256": original["sources"][MODULE]["sha256"], "claims": CLAIMS}
    lock = source.ROOT / "provenance/photochemistry-cauchy.json"
    if not lock.exists() or json.loads(lock.read_text()) != expected:
        raise ValueError("Cauchy predicates differ from the reviewed source/goal lock")
    return CLAIMS


def transform(rendered):
    text = rendered[PART].decode()
    start = text.index("theorem sum_fin_subCoin_3326847_le")
    prefix = text[:start]
    scopes = []
    for line in prefix.splitlines():
        section = re.fullmatch(r"(?:@\[[^\n]+\] )?(?:noncomputable |public )?section(?: (\w+))?", line)
        namespace = re.fullmatch(r"namespace (\S+)", line)
        if section or namespace: scopes.append((namespace or section).group(1))
        elif re.fullmatch(r"end(?: \S+)?", line): scopes.pop()
    if not scopes:
        raise ValueError("Invalid Cauchy definitions scope")
    closing = "".join("end"+(" "+name if name else "")+"\n" for name in reversed(scopes))
    rendered[DEFS] = (prefix + "\n" + closing).encode()
    # Replay the same namespace/open prelude, then import the original definitions.
    body_prefix = text[:text.index("/-- Arithmetic radius grid")]
    import_point = body_prefix.index("open QuantumComputation.")
    body_prefix = body_prefix[:import_point]+f"public import {DEFS}\n\n"+body_prefix[import_point:]
    axiom_text = ("/- External closed integer predicates; source and exact arguments are\n"
                  "locked in provenance/photochemistry-cauchy.json. -/\nnamespace External\n")
    for fact in facts():
        axiom_text += f"axiom {fact['name']} : {fact['term']} = true\n"
    axiom_text += "end External\n\n"
    remaining = text[start:]
    matches = list(re.finditer(r"\bby\s+decide\s+\+kernel", remaining))
    if len(matches) != len(CLAIMS):
        raise ValueError("Unexpected closed Cauchy proof sites")
    for match, fact in reversed(list(zip(matches, CLAIMS))):
        remaining = remaining[:match.start()]+"External."+fact["name"]+remaining[match.end():]
    rendered[PART] = (body_prefix+axiom_text+remaining).encode()


def evaluator_source():
    text = f"import {DEFS}\nopen Lean {NS}\n#eval do\n"
    for fact in facts(): text += f"  let {fact['name']} := {fact['term']}\n"
    text += "  let bad := checkSegListAuto 33258891316 3326847 10000 [(0, 406380, 2351733490)]\n"
    text += '  IO.println (Json.mkObj [("schema", toJson "fqc-cauchy-results-v1"),\n'
    text += '    ("checks", Json.mkObj [' + ", ".join(f'("{f["name"]}", toJson {f["name"]})' for f in facts()) + ']),\n'
    text += '    ("invalid_zero_length_rejected", toJson (!bad))]).compress\n'
    return text


def bind(output):
    expected = {"schema": "fqc-cauchy-results-v1", "checks": {f["name"]: True for f in facts()},
                "invalid_zero_length_rejected": True}
    if json.dumps(output, sort_keys=True) != json.dumps(expected, sort_keys=True):
        raise ValueError("External Cauchy result does not match the approved predicates")


def verify(report, rendered):
    import full
    bind(report["result"])
    lean = Path(shutil.which("lean") or "missing-lean")
    if (report["status"] != "passed" or report["admission_sources_sha256"] != full.admission_digest()
        or report["evaluator_source_sha256"] != source.sha(evaluator_source().encode())
        or report["definitions_sha256"] != source.sha(rendered[DEFS])
        or report["lean_binary_sha256"] != source.sha(lean.read_bytes())):
        raise ValueError("Cauchy execution evidence is missing/stale")


def check():
    import full
    base.toolchain()
    manifest, local = full.locked()
    full.validate_evidence(manifest, json.loads((full.RESULTS / "coverage.json").read_text()))
    rendered = full.rendered_sources(manifest, local)
    # No source containing the three new axioms is written before successful
    # evaluation. Definitions and earlier source-checked premises can bootstrap.
    for module, raw in rendered.items():
        if module in full.pending_modules(0): continue
        path = full.INTEGRATION / (module.replace(".", "/")+".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != raw: path.write_bytes(raw)
    env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    with (full.RESULTS / "cauchy-definitions-build.log").open("w") as log:
        subprocess.run(["lake", "build", "+"+DEFS+":olean"], cwd=full.INTEGRATION,
                       stdout=log, stderr=subprocess.STDOUT, env=env, check=True)
    script = full.CACHE / "CauchyExternal.lean"
    script.write_text(evaluator_source())
    start = time.monotonic()
    with (full.RESULTS / "cauchy-evaluation.out").open("w") as out, (full.RESULTS / "cauchy-evaluation.err").open("w") as err:
        subprocess.run(["lake", "env", "lean", "-M4800", "-j1", str(script)], cwd=full.INTEGRATION,
                       stdout=out, stderr=err, env=env, check=True)
    result = json.loads((full.RESULTS / "cauchy-evaluation.out").read_text())
    bind(result)
    negatives = []
    for bad in [{**result, "checks": {}}, {**result, "checks": {"finite": False, "tail": True, "halfplane": True}}]:
        try: bind(bad)
        except ValueError: negatives.append("rejected")
        else: raise ValueError("Cauchy binding negative test failed")
    return {"status": "passed", "result": result, "wall_seconds": time.monotonic()-start,
        "admission_sources_sha256": full.admission_digest(),
        "definitions_sha256": source.sha(rendered[DEFS]),
        "evaluator_source_sha256": source.sha(evaluator_source().encode()),
        "lean_binary_sha256": source.sha(Path(shutil.which("lean")).read_bytes()),
        "binding_negatives": negatives,
        "trust": "Original computable predicates executed with Lean #eval; not kernel reduction"}


if __name__ == "__main__":
    import full
    full.RESULTS.mkdir(parents=True, exist_ok=True)
    target = full.RESULTS / "cauchy.json"
    target.write_text(json.dumps({"status": "running"})+"\n")
    try: report = check()
    except Exception as error:
        target.write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        raise
    target.write_text(json.dumps(report, indent=2)+"\n")
    print("PASS: three external Cauchy predicates and zero-length rejection")
