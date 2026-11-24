"""Pinned full Photochemistry source inventory, coverage execution and integration."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.request

import source
import run as base
import full_shard
import full_cauchy
import full_midtap
import full_family
import full_oracle

ROOT = source.ROOT
CACHE = ROOT / ".cache/full"
RESULTS = ROOT / "results/full"
INTEGRATION = ROOT / "integration"
TARGET = "QuantumComputationDiscoveries.Algorithms.Photochemistry"
NS = source.NS
FAMILIES = {
    "TopHadStage1Tab1Shard0": 1, "TopHadStage1Tab1Shard1": 1,
    "TopHadStage1Tab2Shard0": 2, "TopHadStage1Tab2Shard1": 2,
    "TopHadStage1Tab2Shard2": 2, "TopHadStage1Tab2Shard3": 2,
}


def upstream(path: str) -> bytes:
    if os.environ.get("FQC_UPSTREAM_ROOT"):
        return (Path(os.environ["FQC_UPSTREAM_ROOT"]) / path).read_bytes()
    p = CACHE / "upstream" / path
    if not p.exists():
        url = f"https://raw.githubusercontent.com/google-deepmind/formal-quantum-computation/{source.COMMIT}/{path}"
        with urllib.request.urlopen(url, timeout=45) as response:
            raw = response.read()
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(raw)
    return p.read_bytes()


def imports(text: str):
    return re.findall(r"^(?:public )?import (?:all )?([\w.]+)", text, re.M)


def snapshot():
    local, external, todo = {}, set(), [TARGET]
    while todo:
        module = todo.pop()
        if module in local or module in external:
            continue
        if not module.startswith(("QuantumComputation.", "QuantumComputationSpecs.",
                                  "QuantumComputationDiscoveries.")):
            external.add(module)
            continue
        path = module.replace(".", "/") + ".lean"
        raw = upstream(path)
        local[module] = raw
        todo.extend(imports(raw.decode()))
    return local, sorted(external)


def declarations(text: str, stage: int):
    matches = list(re.finditer(rf"^theorem (c{stage}_\d+)\s*:", text, re.M))
    boundaries = [m.start() for m in re.finditer(
        r"^(?:theorem|lemma|def|abbrev|noncomputable (?:def|abbrev))\s+", text, re.M)]
    end = text.rindex("end " + NS)
    for match in matches:
        stop = next((p for p in boundaries if p > match.start()), end)
        # A later, differently named theorem is not part of the final c_i proof.
        # Retain its immediately preceding documentation as well as its body.
        comment = text.rfind("/--", match.end(), stop)
        if comment >= 0 and text[comment:stop].rstrip().endswith("-/"):
            stop = comment
        declaration = text[match.start():stop]
        yield match.start(), stop, match.group(1), declaration


def extract_group(declaration: str, stage: int, offset: int):
    checker = "evalS1Batch_sound" if stage == 1 else "evalS2Batch460_sound"
    batches = []
    for match in re.finditer(checker, declaration):
        parser = source.Parser(declaration[match.end():])
        values, terms = [], []
        for _ in range(3):
            start = parser.pos
            values.append(parser.term())
            terms.append(parser.text[start:parser.pos].strip())
        if not re.match(r"\s*\(by\s+decide\s+\+kernel\s*\)", parser.text[parser.pos:]):
            raise ValueError("Unexpected closed certificate proof")
        batches.append({"schema": f"fqc-stage{stage}-batch-v1", "batch": offset+len(batches),
                        "cells": source.cells(values[0]), "words": source.tree(values[1]),
                        "stream": source.stream(values[2]), "_terms": terms})
    ty = declaration[declaration.index(":")+1:declaration.index(":=")].strip()
    expected = [[int(x) for x in triple] for triple in
                re.findall(rf"D{stage}\s+(\d+)\s+(\d+)\s+(\d+)", ty)]
    actual = [cell for b in batches for cell in b["cells"]]
    if not batches or expected != actual:
        raise ValueError("Coverage batch-to-proposition mapping differs")
    return ty, batches


def catalog():
    local, external = snapshot()
    result = {"upstream": source.COMMIT, "target": TARGET, "sources": {},
              "external_imports": external, "groups": [], "batches": [],
              "final_theorems": ["QuantumComputation.Specs.photochemistry_correctness",
                                 "QuantumComputation.Specs.photochemistry_const_cost"]}
    ids = {1: 0, 2: 0}
    for module, raw in sorted(local.items()):
        stem = module.split(".")[-1]
        text = raw.decode()
        result["sources"][module] = {"sha256": source.sha(raw), "bytes": len(raw),
            "git_blob_sha1": hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest(),
            "kernel_sites_lexical": len(re.findall(r"decide\s+\+kernel", text))}
        if stem not in FAMILIES:
            continue
        stage = FAMILIES[stem]
        for _, _, name, declaration in declarations(text, stage):
            ty, batches = extract_group(declaration, stage, ids[stage])
            group = {"module": module, "name": name, "stage": stage, "type": ty,
                     "axiom": f"{NS}.External.{stem}_{name}", "batches": []}
            for batch in batches:
                batch.pop("_terms")
                rel = f"certificates/stage{stage}/{batch['batch']:04d}.json"
                data = (json.dumps(batch, indent=2)+"\n").encode()
                dest = CACHE / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)
                record = {"path": rel, "sha256": source.sha(data), "stage": stage,
                          "batch": batch["batch"], "cells": batch["cells"], "bytes": len(data)}
                result["batches"].append(record)
                group["batches"].append(rel)
            ids[stage] += len(batches)
            result["groups"].append(group)
    result["coverage_families"] = {str(k): {"groups": sum(g["stage"] == k for g in result["groups"]),
        "batches": ids[k]} for k in [1, 2]}
    return result, local


def locked():
    manifest, local = catalog()
    p = ROOT / "provenance/photochemistry.json"
    if not p.exists():
        raise ValueError("Missing committed source/claim catalog; restore the reviewed Git snapshot")
    if json.loads(p.read_text()) != manifest:
        raise ValueError("Full source/claim catalog differs from reviewed snapshot")
    return manifest, local


def execute(manifest):
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "coverage.json").write_text(json.dumps({"status": "running"})+"\n")
    base.toolchain()
    base.run(["lake", "build", "fqc_checker"], "full-build-checker")
    checker = ROOT / ".lake/build/bin/fqc_checker"
    accepted = []
    measurements = []
    native_seconds = 0.0
    for start in range(0, len(manifest["batches"]), 64):
        chunk = manifest["batches"][start:start+64]
        paths = [CACHE / b["path"] for b in chunk]
        for p, b in zip(paths, chunk):
            if source.sha(p.read_bytes()) != b["sha256"]:
                raise ValueError("Certificate byte identity mismatch")
        metrics, out = base.run([str(checker), *map(str, paths)], f"full-native-{start:04d}")
        measurements.append({"first_batch_index": start, "batches": len(chunk), **metrics})
        records = [json.loads(line) for line in out.splitlines()]
        if len(records) != len(chunk):
            raise ValueError("External checker omitted/added a result")
        for b, actual in zip(chunk, records):
            expected = {"schema": f"fqc-stage{b['stage']}-result-v1", "batch": b["batch"],
                        "cells": b["cells"], "accepted": True}
            if json.dumps(actual, sort_keys=True) != json.dumps(expected, sort_keys=True):
                raise ValueError("Result-to-claim identity mismatch")
            accepted.append(b["path"])
        native_seconds += metrics["wall_seconds"]
    report = {"status": "passed", "catalog_sha256": source.sha(json.dumps(manifest,sort_keys=True).encode()),
        "checker_sources_sha256": base.checker_sources_digest(),
        "admission_sources_sha256": admission_digest(),
        "checker_binary_sha256": source.sha(checker.read_bytes()),
        "accepted": accepted, "groups": len(manifest["groups"]), "native_seconds": native_seconds,
        "native_chunks": measurements,
        "whole_decoder_equivalence": "not proved; external implementation explicitly trusted"}
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "coverage.json").write_text(json.dumps(report, indent=2)+"\n")
    print(f"All {len(accepted)} certificate batches accepted ({native_seconds:.2f}s native runtime)")


def admission_digest():
    paths = [ROOT / "scripts" / name for name in ["source.py", "run.py", "full.py",
        "full_reference.py", "full_audit.py", "full_setup.py", "full_shard.py", "full_cauchy.py", "full_midtap.py", "full_family.py", "full_oracle.py", "check.sh", "setup.sh"]]
    paths += [INTEGRATION / "Audit/Export.lean", INTEGRATION / "lakefile.toml",
              INTEGRATION / "lake-manifest.json", INTEGRATION / "lean-toolchain"]
    paths += [ROOT / "provenance/photochemistry-shards.json"]
    paths += [ROOT / "provenance/photochemistry-cauchy.json"]
    paths += [ROOT / "provenance/photochemistry-midtap-shards.json"]
    paths += [ROOT / "provenance/photochemistry-coulomb-shards.json"]
    paths += [ROOT / "provenance/photochemistry-poly-shards.json"]
    paths += [ROOT / "provenance/photochemistry-midtap.json"]
    paths += [ROOT / "provenance/photochemistry-families.json"]
    paths += [ROOT / "provenance/photochemistry-oracle-sites.json", INTEGRATION / "FQCOracle/Tactic.lean"]
    return source.sha(b"".join(str(p.relative_to(ROOT)).encode()+b"\0"+p.read_bytes()+b"\0"
                               for p in sorted(paths)))


def validate_evidence(manifest, report):
    digest = source.sha(json.dumps(manifest,sort_keys=True).encode())
    if (report["status"] != "passed" or report["catalog_sha256"] != digest or
            report["checker_sources_sha256"] != base.checker_sources_digest() or
            report["admission_sources_sha256"] != admission_digest() or
            len(report["accepted"]) != len(manifest["batches"]) or
            set(report["accepted"]) != {b["path"] for b in manifest["batches"]}):
        raise ValueError("Full native evidence is missing/stale/incomplete")
    checker = ROOT / ".lake/build/bin/fqc_checker"
    if report["checker_binary_sha256"] != source.sha(checker.read_bytes()):
        raise ValueError("Native executable changed after coverage checking")


def negative_admission_tests(manifest):
    original = json.loads((RESULTS / "coverage.json").read_text())
    tests = {}
    for label in ["catalog", "checker-source", "admission-source", "binary", "missing", "duplicate"]:
        report = json.loads(json.dumps(original))
        if label in {"catalog", "checker-source", "admission-source", "binary"}:
            field = {"catalog": "catalog_sha256", "checker-source": "checker_sources_sha256",
                "admission-source": "admission_sources_sha256", "binary": "checker_binary_sha256"}[label]
            report[field] = "altered"
        elif label == "missing": report["accepted"].pop()
        else: report["accepted"].append(report["accepted"][0])
        try:
            validate_evidence(manifest, report)
        except ValueError:
            tests[label] = "rejected"
        else:
            raise ValueError(f"Full admission negative test failed: {label}")
    (RESULTS / "admission-negatives.json").write_text(json.dumps(tests, indent=2)+"\n")


def rendered_sources(manifest, local):
    digest = source.sha(json.dumps(manifest,sort_keys=True).encode())
    rendered = {}
    for module, raw in local.items():
        text = raw.decode()
        stem = module.split(".")[-1]
        if stem in FAMILIES:
            stage = FAMILIES[stem]
            for a, b, name, declaration in reversed(list(declarations(text, stage))):
                group = next(g for g in manifest["groups"] if g["module"] == module and g["name"] == name)
                ty = group["type"]
                ax = stem+"_"+name
                replacement = (f"/- External coverage evidence: {digest}; {len(group['batches'])} checked batches. -/\n"
                    f"namespace External\naxiom {ax} : {ty}\nend External\n"
                    f"theorem {name} : {ty} := External.{ax}\n\n")
                text = text[:a]+replacement+text[b:]
            original = raw.decode()
            for other in re.finditer(r"^theorem ([A-Za-z_][A-Za-z_0-9]*)\s*:", original, re.M):
                if re.fullmatch(rf"c{stage}_\d+", other.group(1)): continue
                # The source snapshot has an additional top1D73_cov theorem.
                # Its complete proof, including four kernel computations, stays.
                next_decl = re.search(r"^(?:theorem|lemma|def|abbrev|end)\s+",
                                      original[other.end():], re.M)
                end_other = other.end()+next_decl.start() if next_decl else len(original)
                if original[other.start():end_other] not in text:
                    raise ValueError(f"Unselected theorem was altered: {stem}.{other.group(1)}")
        rendered[module] = text.encode()
    rendered.update(full_shard.render(local[full_shard.MODULE]))
    rendered.update(full_shard.render_midtap(local[full_shard.MIDTAP]))
    full_family.transform_ulp(rendered)
    rendered.update(full_oracle.render(manifest, local))
    rendered.update(full_shard.render_coulomb(local[full_shard.COULOMB], rendered[full_shard.COULOMB]))
    rendered.update(full_shard.render_poly(local[full_shard.POLY], rendered[full_shard.POLY]))
    return rendered


def pending_modules(stage):
    pending = set()
    if stage <= 0: pending.add(full_cauchy.PART)
    if stage <= 1: pending.add(full_midtap.PART)
    if stage <= 2: pending.add(full_family.PAIR_PART)
    if stage <= 3: pending |= {full_family.ULP_FACTS, *full_family.ULP_SHARDS}
    return pending


def materialize(manifest, local):
    report = json.loads((RESULTS / "coverage.json").read_text())
    validate_evidence(manifest, report)
    rendered = rendered_sources(manifest, local)
    full_cauchy.verify(json.loads((RESULTS / "cauchy.json").read_text()), rendered)
    full_midtap.verify(json.loads((RESULTS / "midtap.json").read_text()), rendered)
    for kind in full_family.SPECS:
        full_family.verify(kind, json.loads((RESULTS / (kind+".json")).read_text()), rendered)
    derived = {}
    for module, raw in rendered.items():
        rel = module.replace(".", "/")+".lean"
        out = INTEGRATION / rel
        out.parent.mkdir(parents=True, exist_ok=True)
        if not out.exists() or out.read_bytes() != raw:
            out.write_bytes(raw)
        derived[module] = source.sha(raw)
    # These are generated sources, not independent mathematical reimplementations.
    (RESULTS / "derived-sources.json").write_text(json.dumps(derived,indent=2)+"\n")
    return derived


def verify_materialized(manifest, local):
    validate_evidence(manifest, json.loads((RESULTS / "coverage.json").read_text()))
    derived = json.loads((RESULTS / "derived-sources.json").read_text())
    expected = rendered_sources(manifest, local)
    full_cauchy.verify(json.loads((RESULTS / "cauchy.json").read_text()), expected)
    full_midtap.verify(json.loads((RESULTS / "midtap.json").read_text()), expected)
    for kind in full_family.SPECS:
        full_family.verify(kind, json.loads((RESULTS / (kind+".json")).read_text()), expected)
    if set(derived) != set(expected):
        raise ValueError("Generated source closure differs from pinned target closure")
    for module, raw in expected.items():
        path = INTEGRATION / (module.replace(".", "/")+".lean")
        if path.read_bytes() != raw or source.sha(raw) != derived[module]:
            raise ValueError(f"Generated source is not the approved transformation: {module}")


def build(manifest, local):
    if not (INTEGRATION / "QuantumComputationDiscoveries/Algorithms/Photochemistry.lean").exists():
        raise ValueError("Run source materialization before integration")
    RESULTS.mkdir(parents=True, exist_ok=True)
    base.toolchain()
    subprocess.run([sys.executable, str(ROOT / "scripts/full_setup.py"), "--verify-only"], check=True)
    verify_materialized(manifest, local)
    ordered, visited = [], set()
    def visit(module):
        if module not in local or module in visited: return
        visited.add(module)
        for dep in imports(local[module].decode()): visit(dep)
        ordered.append(module)
    visit(TARGET)
    status = {"status": "building", "target": TARGET, "modules": []}
    status_path = RESULTS / "integration-status.json"
    status_path.write_text(json.dumps(status, indent=2)+"\n")
    # One local module at a time: Lake's default scheduling can otherwise compile
    # several large proof files concurrently. Existing valid traces remain usable.
    env = {**os.environ, "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "1")}
    for index, module in enumerate(ordered):
        print(f"[{index+1}/{len(ordered)}] {module}", flush=True)
        start = time.monotonic()
        log_path = RESULTS / ("build-"+module+".log")
        with log_path.open("w") as log:
            process = subprocess.Popen(["lake", "build", "+"+module+":olean"], cwd=INTEGRATION,
                                       stdout=log, stderr=subprocess.STDOUT, env=env)
            _, code, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(code)
            result = process
        status["modules"].append({"module": module, "exit_code": result.returncode,
            "wall_seconds": time.monotonic()-start, "maxrss_kib": usage.ru_maxrss, "log": str(log_path.relative_to(ROOT))})
        status["status"] = "building" if result.returncode == 0 else "build-failed"
        status_path.write_text(json.dumps(status, indent=2)+"\n")
        if result.returncode:
            raise RuntimeError(f"Integration failed: {module}; see {log_path}")
    status["status"] = "built"
    status_path.write_text(json.dumps(status, indent=2)+"\n")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("mode", choices=["inventory", "coverage", "numeric", "materialize", "build", "audit", "all"])
    args = p.parse_args()
    manifest, local = locked()
    print("Source modules:",len(local),"coverage:",manifest["coverage_families"],flush=True)
    if args.mode == "coverage": execute(manifest)
    elif args.mode == "numeric":
        subprocess.run([sys.executable, str(ROOT / "scripts/full_cauchy.py")], check=True)
        subprocess.run([sys.executable, str(ROOT / "scripts/full_midtap.py")], check=True)
        for kind in full_family.SPECS:
            subprocess.run([sys.executable, str(ROOT / "scripts/full_family.py"), kind], check=True)
    elif args.mode == "materialize": materialize(manifest,local)
    elif args.mode == "build": build(manifest,local)
    elif args.mode == "audit":
        subprocess.run([sys.executable, str(ROOT / "scripts/full_audit.py")], check=True)
    elif args.mode == "all":
        (RESULTS / "all-status.json").write_text(json.dumps({"status": "running"})+"\n")
        subprocess.run([sys.executable, str(ROOT / "scripts/full_setup.py"), "--verify-only"], check=True)
        subprocess.run([sys.executable, str(ROOT / "scripts/run.py"), "check"], check=True)
        execute(manifest)
        negative_admission_tests(manifest)
        subprocess.run([sys.executable, str(ROOT / "scripts/full_reference.py")], check=True)
        subprocess.run([sys.executable, str(ROOT / "scripts/full_cauchy.py")], check=True)
        subprocess.run([sys.executable, str(ROOT / "scripts/full_midtap.py")], check=True)
        for kind in full_family.SPECS:
            subprocess.run([sys.executable, str(ROOT / "scripts/full_family.py"), kind], check=True)
        materialize(manifest,local)
        build(manifest,local)
        full_oracle.negative_tests(local)
        subprocess.run([sys.executable, str(ROOT / "scripts/full_audit.py")], check=True)
        (RESULTS / "all-status.json").write_text(json.dumps({"status": "passed",
            "catalog_sha256": source.sha(json.dumps(manifest,sort_keys=True).encode()),
            "admission_sources_sha256": admission_digest(), "final_theorems": manifest["final_theorems"]},
            indent=2)+"\n")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        RESULTS.mkdir(parents=True, exist_ok=True)
        (RESULTS / "last-failure.json").write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        if len(sys.argv) > 1 and sys.argv[1] == "coverage":
            (RESULTS / "coverage.json").write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        if len(sys.argv) > 1 and sys.argv[1] == "all":
            (RESULTS / "all-status.json").write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        raise
