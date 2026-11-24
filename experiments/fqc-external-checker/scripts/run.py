"""Build, execute, bind and audit the explicitly trusted c1_0 experiment."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

import source

ROOT = source.ROOT
RESULTS = ROOT / "results"
STANDARD = {"propext", "Quot.sound", "Classical.choice"}
BRIDGES = ["entryExec_eq", "acceptedEntry_sound", "spread16Exec_eq", "expandWord_eq",
           "entryOption_eq", "braunCons_eq", "cellCheck_eq", "even25_eq", "splitWord_eq"]


def run(cmd, label, expected=0):
    RESULTS.mkdir(exist_ok=True)
    outpath, errpath = RESULTS / (label + ".out"), RESULTS / (label + ".err")
    start = time.monotonic()
    with outpath.open("wb") as out, errpath.open("wb") as err:
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=out, stderr=err)
        _, status, usage = os.wait4(p.pid, 0)
        p.returncode = os.waitstatus_to_exitcode(status)
    result = {"command": list(map(str, cmd)), "exit_code": p.returncode,
              "wall_seconds": time.monotonic() - start,
              "maxrss_kib": usage.ru_maxrss}
    if expected is not None and p.returncode != expected:
        raise RuntimeError(f"{label}: exit {p.returncode}\n" + outpath.read_text()[-6000:]
                           + errpath.read_text()[-3000:])
    print(f"{label}: exit={p.returncode}, {result['wall_seconds']:.3f}s, "
          f"maxrss={result['maxrss_kib']} KiB", flush=True)
    return result, outpath.read_text()


def toolchain():
    if sys.platform != "linux":
        raise RuntimeError("This measurement runner requires Linux (including WSL2)")
    for tool in ["lean", "lake"]:
        if not shutil.which(tool):
            raise RuntimeError("Install pinned Lean 4.35.0 or set FQC_TOOLCHAIN_DIR")
    version = subprocess.check_output(["lean", "--version"], text=True)
    if not re.search(r"version 4\.35\.0[,)]", version):
        raise RuntimeError(f"Wrong Lean version: {version.strip()}")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0":
        raise RuntimeError("Unexpected toolchain pin")
    return version.strip()


def cells_term(cells):
    def go(i):
        k, x, y = cells[i]
        return f"(cl1 {k} {x} {y})" if i == len(cells)-1 else f"(clm {k} {x} {y} {go(i+1)})"
    return go(0)


def checker_sources_digest():
    paths = [ROOT / "Main.lean", ROOT / "lean-toolchain", ROOT / "lakefile.toml",
             ROOT / "FQCExternal/Entry.lean", ROOT / "FQCExternal/Exec.lean"]
    paths += sorted((ROOT / "FQCExternal/Vendor").glob("*.lean"))
    payload = b"".join(str(p.relative_to(ROOT)).encode() + b"\0" + p.read_bytes() + b"\0"
                       for p in sorted(paths))
    return source.sha(payload)


def admission_sources_digest():
    return source.sha((ROOT / "scripts/source.py").read_bytes() + b"\0" +
                      (ROOT / "scripts/run.py").read_bytes())


def proof_closure():
    """Check that the admitted public proof cannot import the selected payload or executable."""
    seen, todo = set(), ["FQCExternal.Claim"]
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        if module in {"Main", "FQCExternal.Exec", "FQCExternal.Entry"}:
            raise ValueError("Executable code leaked into the admitted proof import closure")
        path = ROOT / (module.replace(".", "/") + ".lean")
        text = path.read_text()
        if "data/c1_0" in text and module != "FQCExternal.ExternalFacts":
            raise ValueError("Payload path leaked into proof modules")
        seen.add(module)
        for imported in re.findall(r"^(?:public )?import ([\w.]+)", text, re.M):
            if imported.startswith("FQCExternal."):
                todo.append(imported)
            else:
                raise ValueError(f"Unexpected proof dependency: {imported}")
    return sorted(seen)


def facts_text(manifest, batches):
    text = ("import FQCExternal.Vendor.Stage1\n\n"
            "open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth\n\n"
            "/- Generated only after successful external execution and exact source/input binding.\n"
            "These axioms are external assumptions, not kernel-checked computations.\n"
            f"Upstream commit: {source.COMMIT}\n"
            f"Checker sources SHA256: {checker_sources_digest()}\n"
            f"Admission scripts SHA256: {admission_sources_digest()}\n"
            "Runtime observations and executable hashes: results/acceptance.json (not in Git).\n-/\n\n"
            "namespace FQCExternal.External\n\n")
    for b in batches:
        name = f"data/c1_0/batch{b['batch']}.json"
        text += (f"/-- External checker acceptance of `{name}`.\n"
                 f"Input SHA256: {manifest['fixtures'][name]}\n"
                 "Source: TopHadStage1Tab1Shard0.lean, theorem c1_0. -/\n"
                 f"axiom batch{b['batch']} : Stage1BatchCov {cells_term(b['cells'])}\n\n")
    return text + "end FQCExternal.External\n"


def bind_result(batch, raw, result, manifest):
    name = f"data/c1_0/batch{batch['batch']}.json"
    if source.sha(raw) != manifest["fixtures"][name]:
        raise ValueError("Unapproved certificate hash")
    expected = {"schema": "fqc-stage1-result-v1", "batch": batch["batch"],
                "cells": batch["cells"], "accepted": True}
    # No ignored/extra result fields, and no coercion of a truthy value to Bool.
    if (type(result) is not dict or
            json.dumps(result, sort_keys=True) != json.dumps(expected, sort_keys=True) or
            type(result.get("accepted")) is not bool):
        raise ValueError("External result does not match the approved claim")


def axiom_list(output, theorem):
    if f"'{theorem}' does not depend on any axioms" in output:
        return set()
    found = re.search(r"'" + re.escape(theorem) + r"' depends on axioms:\s*\[([^]]*)\]", output)
    if not found:
        raise ValueError(f"No axiom audit for {theorem}")
    return {x.strip() for x in found.group(1).split(",") if x.strip()}


def expected_claim(body):
    return ("import FQCExternal.ExternalFacts\n\n"
            "open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth\n\n"
            "namespace FQCExternal\n" + body +
            "\n#print axioms c1_0_external\nend FQCExternal\n")


def check(generate=False):
    version = toolchain()
    manifest, batches, body = source.verify_sources()
    if (ROOT / "FQCExternal/Claim.lean").read_text() != expected_claim(body):
        raise ValueError("Claim proof/type differs from the source-derived skeleton")
    report = {"toolchain": version, "source_identity": "passed",
              "public_type_source_identity": "passed", "steps": {}}
    report["measurement_notes"] = (
        "Linux wait4 process maxrss, which may include inherited pre-exec memory; "
        "not aggregate concurrent RAM. Native timing excludes build/provenance/audit. "
        "Kernel reference timing is fresh proof elaboration with built imports, not comparator.")
    build, _ = run(["lake", "build", "fqc_checker"], "build")
    report["steps"]["build"] = build
    checker = ROOT / ".lake/build/bin/fqc_checker"
    report["checker_binary_sha256"] = source.sha(checker.read_bytes())
    report["checker_sources_sha256"] = checker_sources_digest()
    report["admission_sources_sha256"] = admission_sources_digest()
    report["python"] = sys.version
    report["external_results"] = []
    for b in batches:
        name = f"data/c1_0/batch{b['batch']}.json"
        metrics, output = run([str(checker), name], f"native-batch{b['batch']}")
        result = json.loads(output)
        bind_result(b, (ROOT / name).read_bytes(), result, manifest)
        report["external_results"].append({"input": name, "result": result, "metrics": metrics})

    # Exercise invalid arithmetic/dictionary/stream inputs, not just malformed JSON.
    bad_inputs = {}
    original = batches[0]
    bad = json.loads(json.dumps(original)); bad["words"][0] = "0x0"
    bad_inputs["dictionary-tag"] = bad
    bad = json.loads(json.dumps(original)); bad["stream"][0] = "0x0"
    bad_inputs["stream-tag"] = bad
    bad = json.loads(json.dumps(original)); bad["stream"] = []
    bad_inputs["missing-stream"] = bad
    bad = json.loads(json.dumps(original)); bad["words"] = None
    bad_inputs["missing-dictionary"] = bad
    report["negative_tests"] = {}
    for label, bad in bad_inputs.items():
        path = RESULTS / ("invalid-" + label + ".json")
        path.write_text(json.dumps(bad))
        metrics, output = run([str(checker), str(path)], "reject-" + label, expected=1)
        if json.loads(output)["accepted"] is not False:
            raise ValueError("Invalid certificate accepted")
        report["negative_tests"][label] = metrics
    good_result = report["external_results"][0]["result"]
    for label, raw, res in [
        ("input-hash", b"altered input", good_result),
        ("claim-binding", (ROOT / "data/c1_0/batch0.json").read_bytes(),
         {**good_result, "cells": [[1, 0, 2]]}),
        ("claim-identifier-type", (ROOT / "data/c1_0/batch0.json").read_bytes(),
         {**good_result, "batch": False}),
    ]:
        try:
            bind_result(batches[0], raw, res, manifest)
        except ValueError:
            report["negative_tests"][label] = "rejected"
        else:
            raise ValueError(f"Binding negative test failed: {label}")

    # Elaborate the original full computational proof freshly, not a frozen log.
    raw = source.read_upstream("TopHadStage1Tab1Shard0").decode()
    declaration = raw[raw.index("theorem c1_0"):raw.index("theorem c1_1")]
    declaration = declaration.replace("theorem c1_0", "theorem kernel_c1_0", 1)
    reference = ROOT / ".cache/Reference.lean"
    reference.write_text("import FQCExternal.Vendor.Stage1\n"
                         "open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth\n"
                         "set_option maxHeartbeats 4000000\n"
                         "namespace KernelReference\n" + declaration +
                         "\nend KernelReference\nset_option pp.fullNames true\n"
                         "#print axioms KernelReference.kernel_c1_0\n")
    metrics, out = run(["lake", "env", "lean", str(reference)], "kernel-reference")
    if not axiom_list(out, "KernelReference.kernel_c1_0") <= STANDARD:
        raise ValueError("Kernel reference used extra axioms")
    report["steps"]["kernel_reference"] = metrics

    def tree_term(t):
        return "e0" if t is None else f"(bn (nat_lit {t[0]}) {tree_term(t[1])} {tree_term(t[2])})"

    def stream_term(ws):
        term = "BitChain.empty"
        for w in reversed(ws):
            term = f"(BitChain.more (nat_lit {w}) {term})"
        return term

    negative = ROOT / ".cache/NegativeReference.lean"
    text = ("import FQCExternal.Vendor.Stage1\n"
            "open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth\n"
            "set_option maxHeartbeats 4000000\n")
    for i, b in enumerate(bad_inputs.values()):
        text += (f"theorem negative{i} : evalS1Batch {cells_term(b['cells'])} "
                 f"{tree_term(b['words'])} {stream_term(b['stream'])} = false := by decide +kernel\n"
                 f"#print axioms negative{i}\n")
    negative.write_text(text)
    metrics, out = run(["lake", "env", "lean", str(negative)], "kernel-negative-reference")
    for i in range(len(bad_inputs)):
        if not axiom_list(out, f"negative{i}") <= STANDARD:
            raise ValueError("Negative kernel reference used extra axioms")
    report["steps"]["kernel_negative_reference"] = metrics

    facts = ROOT / "FQCExternal/ExternalFacts.lean"
    generated = facts_text(manifest, batches)
    if generate:
        facts.write_text(generated)
    elif not facts.exists() or facts.read_text() != generated:
        raise ValueError("ExternalFacts differs; review source changes before --generate-facts")

    claim_build, _ = run(["lake", "build", "FQCExternal.Claim"], "claim-build")
    report["steps"]["claim_build"] = claim_build
    audit = ROOT / ".cache/Audit.lean"
    audit.parent.mkdir(exist_ok=True)
    audit.write_text("import FQCExternal.Claim\nimport FQCExternal.Exec\n"
                     "open QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth\n"
                     "set_option pp.fullNames true\n"
                     f"example : {manifest['public_type']} := FQCExternal.c1_0_external\n"
                     "#print axioms FQCExternal.c1_0_external\n"
                     + "".join(f"#print axioms FQCExternal.{name}\n" for name in BRIDGES))
    audit_metrics, out = run(["lake", "env", "lean", str(audit)], "type-and-axioms")
    report["steps"]["type_and_axioms"] = audit_metrics
    expected = {f"FQCExternal.External.batch{i}" for i in range(4)}
    actual = axiom_list(out, "FQCExternal.c1_0_external")
    if not actual <= STANDARD | expected or actual & expected != expected:
        raise ValueError(f"Unexpected external assumptions: {actual}")
    for name in ["FQCExternal." + name for name in BRIDGES]:
        if not axiom_list(out, name) <= STANDARD:
            raise ValueError(f"Unproved bridge: {name}")
    report["public_type_elaboration"] = "passed"
    report["kernel_checked_bridges"] = BRIDGES
    report["external_axioms"] = sorted(actual)
    report["admitted_proof_import_closure"] = proof_closure()

    report["reference_vs_external"] = "both accept the same pinned c1_0 proposition"
    report["whole_decoder_equivalence"] = "not proved; explicitly trusted external implementation"
    report["comparator"] = "not run; upstream whitelist excludes these four custom axioms"
    report["scope"] = "four batches, six cells; not full Stage 1 or Photochemistry"
    report["status"] = "passed"
    (RESULTS / "acceptance.json").write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: pinned source, native checks, negative tests, public type, axiom audit, kernel reference")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["setup", "check"], nargs="?", default="check")
    parser.add_argument("--generate-facts", action="store_true")
    args = parser.parse_args()
    os.chdir(ROOT)
    if args.mode == "setup":
        print(toolchain())
        source.verify_sources()
        run(["lake", "build", "fqc_checker"], "setup-build")
    else:
        RESULTS.mkdir(exist_ok=True)
        (RESULTS / "acceptance.json").write_text(json.dumps({"status": "running"}) + "\n")
        try:
            check(args.generate_facts)
        except Exception as error:
            (RESULTS / "acceptance.json").write_text(json.dumps({
                "status": "failed", "error": str(error)}) + "\n")
            raise


if __name__ == "__main__":
    main()
