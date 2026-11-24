"""Source-bound batches of the original parameterized numerical checkers."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

import source
import run as base
import full_cauchy
import full_midtap

GENERIC = full_midtap.NS
PAIR_PART = full_midtap.MODULE+"Parts.Part04"
PAIR_DEFS = full_midtap.MODULE+"Parts.Part04Defs"
ULP_PARENT = source.MODULE+"Stage25PolyCoinCoul18"
ULP_FACTS = source.MODULE+"SubCoin62External"
ULP_SHARDS = [source.MODULE+f"SubCoin62UlpCertShard{i}" for i in range(4)]
SPECS = {
    "pairs": {"namespace": "QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs",
        "function": "checkPairFast3K2", "count": 16, "axiom_name": "pair_batch",
        "definitions_module": PAIR_DEFS, "sources": [full_midtap.MODULE]},
    "ulp": {"namespace": "QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs",
        "function": "checkOneABothSub62", "count": 32, "axiom_name": "ulp_batch",
        "definitions_module": ULP_PARENT, "sources": [ULP_PARENT, *ULP_SHARDS]},
}


def specifications():
    original = json.loads((source.ROOT / "provenance/photochemistry.json").read_text())
    expected = {"upstream": source.COMMIT, "families": {}}
    for key, spec in SPECS.items():
        expected["families"][key] = {**spec, "source_sha256": {n: original["sources"][n]["sha256"] for n in spec["sources"]}}
    lock = source.ROOT / "provenance/photochemistry-families.json"
    if not lock.exists() or json.loads(lock.read_text()) != expected:
        raise ValueError("Numerical family differs from the reviewed predicate/source lock")
    return SPECS


def axiom_names():
    return {s["namespace"]+".External."+s["axiom_name"] for s in specifications().values()}


def batch_type(spec, qualified=False):
    fn = spec["namespace"]+"."+spec["function"] if qualified else spec["function"]
    return f"{GENERIC}.allBelow {spec['count']} {fn} = true"


def axiom_text(spec):
    return ("/- External parameter batch: original predicate definitions, all indices\n"
            "and sources are locked in provenance/photochemistry-families.json. -/\n"
            f"namespace External\naxiom {spec['axiom_name']} : {batch_type(spec)}\nend External\n\n")


def replace_theorems(text, spec, name_prefix, expected_indices):
    pattern = re.compile(r"^theorem ("+name_prefix+r"(\d+))\s*:\s*"+spec["function"]+
        r"\s+(\d+)\s*=\s*true\s*:=\s*by\s+decide\s+\+kernel", re.M)
    seen = []
    def replace(match):
        index = int(match.group(2))
        if index != int(match.group(3)):
            raise ValueError("Theorem identifier/argument mismatch")
        seen.append(index)
        proof = (f"({GENERIC}.allBelow_true_iff {spec['count']} {spec['function']}).mp "
                 f"External.{spec['axiom_name']} {index} (by decide)")
        return f"theorem {match.group(1)} : {spec['function']} {index} = true := {proof}"
    result = pattern.sub(replace, text)
    if seen != expected_indices:
        raise ValueError("Numerical theorem family is incomplete or reordered")
    return result


def transform_pairs(rendered):
    spec = specifications()["pairs"]
    text = rendered[PAIR_PART].decode()
    start = text.index("set_option Elab.async true")
    prefix = text[:start]
    rendered[PAIR_DEFS] = (prefix+"\n"+full_midtap.close_scopes(prefix)).encode()
    first = re.search(r"^(?:def|abbrev|theorem|lemma|structure|inductive)\s", prefix, re.M)
    if first is None or re.search(r"^(?:attribute|variable|local)\s", prefix[first.start():], re.M):
        raise ValueError("Unmodelled numerical family proof scope")
    prelude = prefix[:first.start()]
    point = prelude.index("open QuantumComputation.")
    prelude = prelude[:point]+f"public import {PAIR_DEFS}\n\n"+prelude[point:]
    body = replace_theorems(text[start:], spec, "tB2K2_", list(range(16)))
    rendered[PAIR_PART] = (prelude+axiom_text(spec)+body).encode()


def transform_ulp(rendered):
    spec = specifications()["ulp"]
    original = rendered[ULP_SHARDS[0]].decode()
    license_header = original.split("\nmodule\n", 1)[0]
    rendered[ULP_FACTS] = (license_header+f"\nmodule\npublic import {ULP_PARENT}\n"
        f"@[expose] public section\nnamespace {spec['namespace']}\n"+axiom_text(spec)+
        f"end {spec['namespace']}\nend\n").encode()
    for index, module in enumerate(ULP_SHARDS):
        text = rendered[module].decode()
        point = text.index("open QuantumComputation.")
        text = text[:point]+f"public import {ULP_FACTS}\n\n"+text[point:]
        rendered[module] = replace_theorems(text, spec, "tSub62OneA_", list(range(index*8,index*8+8))).encode()


def evaluator_source(kind):
    spec = specifications()[kind]
    fn = spec["namespace"]+"."+spec["function"]
    return (f"import {spec['definitions_module']}\nopen Lean\n#eval do\n"
        f"  let accepted := {GENERIC}.allBelow {spec['count']} {fn}\n"
        f"  let checks := (List.range {spec['count']}).map fun index ↦\n"
        f'    Json.mkObj [("index", toJson index), ("accepted", toJson ({fn} index))]\n'
        f'  IO.println (Json.mkObj [("schema", toJson "fqc-{kind}-results-v1"),\n'
        '    ("accepted", toJson accepted), ("checks", Json.arr checks.toArray)]).compress\n')


def bind(kind, result):
    count = specifications()[kind]["count"]
    expected = {"schema": f"fqc-{kind}-results-v1", "accepted": True,
                "checks": [{"index": i, "accepted": True} for i in range(count)]}
    if json.dumps(result, sort_keys=True) != json.dumps(expected, sort_keys=True):
        raise ValueError(f"{kind}: external result is not the exact approved parameter batch")


def verify(kind, report, rendered):
    import full
    bind(kind, report["result"])
    spec = specifications()[kind]
    if (report["status"] != "passed" or report["admission_sources_sha256"] != full.admission_digest()
        or report["evaluator_source_sha256"] != source.sha(evaluator_source(kind).encode())
        or report["definitions_sha256"] != source.sha(rendered[spec["definitions_module"]])
        or report["lean_binary_sha256"] != source.sha(Path(shutil.which("lean")).read_bytes())):
        raise ValueError(f"{kind}: execution evidence is missing/stale")


def check(kind):
    import full
    base.toolchain()
    manifest, local = full.locked()
    full.validate_evidence(manifest, json.loads((full.RESULTS / "coverage.json").read_text()))
    rendered = full.rendered_sources(manifest, local)
    full_cauchy.verify(json.loads((full.RESULTS / "cauchy.json").read_text()), rendered)
    full_midtap.verify(json.loads((full.RESULTS / "midtap.json").read_text()), rendered)
    if kind == "ulp": verify("pairs", json.loads((full.RESULTS / "pairs.json").read_text()), rendered)
    pending = full.pending_modules(2 if kind == "pairs" else 3)
    for module, raw in rendered.items():
        if module in pending: continue
        path = full.INTEGRATION / (module.replace(".", "/")+".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != raw: path.write_bytes(raw)
    spec = specifications()[kind]
    with (full.RESULTS / (kind+"-definitions-build.log")).open("w") as log:
        subprocess.run(["lake", "build", "+"+spec["definitions_module"]+":olean"], cwd=full.INTEGRATION,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    script = full.CACHE / (kind.title()+"External.lean")
    script.write_text(evaluator_source(kind))
    start = time.monotonic()
    with (full.RESULTS / (kind+"-evaluation.out")).open("w") as out, (full.RESULTS / (kind+"-evaluation.err")).open("w") as err:
        subprocess.run(["lake", "env", "lean", "-M4800", "-j1", str(script)], cwd=full.INTEGRATION,
                       stdout=out, stderr=err, check=True)
    result = json.loads((full.RESULTS / (kind+"-evaluation.out")).read_text())
    bind(kind, result)
    negative_results = []
    for label in ["omitted", "wrong-index", "false-result"]:
        bad = json.loads(json.dumps(result))
        if label == "omitted": bad["checks"].pop()
        elif label == "wrong-index": bad["checks"][0]["index"] = 999
        else: bad["checks"][0]["accepted"] = False
        try: bind(kind, bad)
        except ValueError: negative_results.append({label: "rejected"})
        else: raise ValueError(f"{kind}: invalid result admitted")
    return {"status": "passed", "result": result, "count": spec["count"],
        "wall_seconds": time.monotonic()-start, "binding_negatives": negative_results,
        "admission_sources_sha256": full.admission_digest(),
        "definitions_sha256": source.sha(rendered[spec["definitions_module"]]),
        "evaluator_source_sha256": source.sha(evaluator_source(kind).encode()),
        "lean_binary_sha256": source.sha(Path(shutil.which("lean")).read_bytes()),
        "trust": "Original pure predicates evaluated externally with Lean #eval; not kernel reduction"}


if __name__ == "__main__":
    import full
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", choices=sorted(SPECS))
    kind = parser.parse_args().family
    full.RESULTS.mkdir(parents=True, exist_ok=True)
    target = full.RESULTS / (kind+".json")
    target.write_text(json.dumps({"status": "running"})+"\n")
    try: report = check(kind)
    except Exception as error:
        target.write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        raise
    target.write_text(json.dumps(report, indent=2)+"\n")
    print(f"PASS: {kind}, all {report['count']} source-bound numerical cases")
