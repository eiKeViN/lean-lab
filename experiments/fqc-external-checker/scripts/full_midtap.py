"""External execution of the original 8,192-input borrow-wire preservation check."""
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
import full_cauchy

MODULE = source.MODULE+"MidTap29Coul18Stage4K2"
PART = MODULE+"Parts.Part01"
DEFS = MODULE+"Parts.Part01Defs"
NS = "QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2"
TERM = """allBelow 64 (fun hi ↦ allBelow 128 (fun lo ↦
  let s := mid18Steps midSubBorrows18Ops (mid18OfHiLo hi lo)
  decide (s.b6 = lo.testBit 0 ∧ s.b7 = lo.testBit 1 ∧ s.b8 = lo.testBit 2 ∧
    s.b23 = lo.testBit 3 ∧ s.b24 = lo.testBit 4 ∧ s.b25 = lo.testBit 5 ∧
    s.b57 = hi.testBit 0)))"""
CLAIM = {"name": "borrow_preservation", "axiom": NS+".External.borrow_preservation",
    "original_theorem": NS+".midSubBorrows18_pres_cert", "term": TERM, "cases": 8192}


def fact():
    original = json.loads((source.ROOT / "provenance/photochemistry.json").read_text())
    expected = {"upstream": source.COMMIT, "source_module": MODULE,
        "source_sha256": original["sources"][MODULE]["sha256"], "claim": CLAIM}
    lock = source.ROOT / "provenance/photochemistry-midtap.json"
    if not lock.exists() or json.loads(lock.read_text()) != expected:
        raise ValueError("MidTap check differs from the reviewed source/goal lock")
    return CLAIM


def close_scopes(prefix):
    scopes = []
    for line in prefix.splitlines():
        section = re.fullmatch(r"(?:@\[[^\n]+\] )?(?:noncomputable |public )?section(?: (\w+))?", line)
        namespace = re.fullmatch(r"namespace (\S+)", line)
        if section or namespace: scopes.append((namespace or section).group(1))
        elif re.fullmatch(r"end(?: \S+)?", line): scopes.pop()
    return "".join("end"+(" "+name if name else "")+"\n" for name in reversed(scopes))


def transform(rendered):
    fact()
    text = rendered[PART].decode()
    theorem = text.index("theorem midSubBorrows18_pres_cert")
    start = text.rfind("set_option maxHeartbeats 3200000 in", 0, theorem)
    if start < 0 or "theorem " in text[start:theorem]:
        raise ValueError("Unexpected scoped preservation proof prefix")
    prefix = text[:start]
    rendered[DEFS] = (prefix+"\n"+close_scopes(prefix)).encode()
    first = re.search(r"^(?:def|abbrev|theorem|lemma|structure|inductive)\s", prefix, re.M)
    if first is None or re.search(r"^(?:attribute|variable|local)\s", prefix[first.start():], re.M):
        raise ValueError("Unmodelled local preservation proof context")
    prelude = text[:first.start()]
    point = prelude.index("open QuantumComputation.")
    prelude = prelude[:point]+f"public import {DEFS}\n\n"+prelude[point:]
    rest = text[start:]
    at = rest.index("by decide +kernel")
    rest = rest[:at]+"External.borrow_preservation"+rest[at+len("by decide +kernel"):]
    axioms = ("/- Original 8192-input Boolean check executed externally; exact source\n"
              "and predicate: provenance/photochemistry-midtap.json. -/\nnamespace External\n"
              f"axiom borrow_preservation : {TERM} = true\nend External\n\n")
    rendered[PART] = (prelude+axioms+rest).encode()


def evaluator_source():
    fact()
    bad = TERM.replace("s.b6 = lo.testBit 0", "s.b6 = !(lo.testBit 0)")
    return (f"import {DEFS}\nopen Lean {NS}\n#eval do\n"
        f"  let good := {TERM}\n  let bad := {bad}\n"
        '  IO.println (Json.mkObj [("schema", toJson "fqc-midtap-result-v1"),\n'
        '    ("accepted", toJson good), ("flipped_bit_rejected", toJson (!bad))]).compress\n')


def bind(result):
    expected = {"schema": "fqc-midtap-result-v1", "accepted": True, "flipped_bit_rejected": True}
    if json.dumps(result, sort_keys=True) != json.dumps(expected, sort_keys=True):
        raise ValueError("MidTap result does not match the approved preservation claim")


def verify(report, rendered):
    import full
    bind(report["result"])
    if (report["status"] != "passed" or report["admission_sources_sha256"] != full.admission_digest()
        or report["evaluator_source_sha256"] != source.sha(evaluator_source().encode())
        or report["definitions_sha256"] != source.sha(rendered[DEFS])
        or report["lean_binary_sha256"] != source.sha(Path(shutil.which("lean")).read_bytes())):
        raise ValueError("MidTap external evidence is missing/stale")


def check():
    import full
    base.toolchain()
    manifest, local = full.locked()
    full.validate_evidence(manifest, json.loads((full.RESULTS / "coverage.json").read_text()))
    rendered = full.rendered_sources(manifest, local)
    full_cauchy.verify(json.loads((full.RESULTS / "cauchy.json").read_text()), rendered)
    # Cauchy facts are now checked; the new preservation fact is still withheld.
    for module, raw in rendered.items():
        if module in full.pending_modules(1): continue
        path = full.INTEGRATION / (module.replace(".", "/")+".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != raw: path.write_bytes(raw)
    with (full.RESULTS / "midtap-definitions-build.log").open("w") as log:
        subprocess.run(["lake", "build", "+"+DEFS+":olean"], cwd=full.INTEGRATION,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    script = full.CACHE / "MidtapExternal.lean"
    script.write_text(evaluator_source())
    start = time.monotonic()
    with (full.RESULTS / "midtap-evaluation.out").open("w") as out, (full.RESULTS / "midtap-evaluation.err").open("w") as err:
        subprocess.run(["lake", "env", "lean", "-M4800", "-j1", str(script)], cwd=full.INTEGRATION,
                       stdout=out, stderr=err, check=True)
    result = json.loads((full.RESULTS / "midtap-evaluation.out").read_text())
    bind(result)
    try: bind({**result, "accepted": False})
    except ValueError: negative = "rejected"
    else: raise ValueError("MidTap binding negative test failed")
    return {"status": "passed", "result": result, "cases": 8192,
        "wall_seconds": time.monotonic()-start, "binding_negative": negative,
        "admission_sources_sha256": full.admission_digest(),
        "definitions_sha256": source.sha(rendered[DEFS]),
        "evaluator_source_sha256": source.sha(evaluator_source().encode()),
        "lean_binary_sha256": source.sha(Path(shutil.which("lean")).read_bytes()),
        "trust": "Original Boolean simulation evaluated with Lean #eval; not kernel reduction"}


if __name__ == "__main__":
    import full
    full.RESULTS.mkdir(parents=True, exist_ok=True)
    target = full.RESULTS / "midtap.json"
    target.write_text(json.dumps({"status": "running"})+"\n")
    try: report = check()
    except Exception as error:
        target.write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        raise
    target.write_text(json.dumps(report, indent=2)+"\n")
    print("PASS: original 8192-input preservation check and flipped-bit rejection")
