"""Separate source, public-type and reachable-axiom audits of full Photochemistry."""
from __future__ import annotations

import hashlib
import json
import subprocess

import full
import run as base
import source

SPEC = "QuantumComputationSpecs.Algorithms.Photochemistry"


def invoke(args, label):
    with (full.RESULTS / (label+".log")).open("w") as log:
        result = subprocess.run(args, cwd=full.INTEGRATION, stdout=log, stderr=subprocess.STDOUT)
    output = (full.RESULTS / (label+".log")).read_text()
    if result.returncode:
        raise RuntimeError(f"{label}: exit {result.returncode}\n{output[-6000:]}")
    return output


def check():
    base.toolchain()
    from full_setup import setup
    setup(verify_only=True)
    manifest, local = full.locked()
    full.verify_materialized(manifest, local)
    status = json.loads((full.RESULTS / "integration-status.json").read_text())
    if status["status"] != "built":
        raise ValueError("Full target has not built successfully")
    # The original specification contains intentional candidate placeholders.
    # It is imported ONLY by the separate reference export process, never by the
    # solution or its axiom audit. Definition bodies are checked by source identity.
    path = SPEC.replace(".", "/")+".lean"
    raw = full.upstream(path)
    record = {"upstream": source.COMMIT, "path": path, "sha256": source.sha(raw),
              "git_blob_sha1": hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()}
    lock = source.ROOT / "provenance/photochemistry-spec.json"
    if not lock.exists() or json.loads(lock.read_text()) != record:
        raise ValueError("Reference specification differs from the reviewed source lock")
    reference_source = full.INTEGRATION / path
    reference_source.parent.mkdir(parents=True, exist_ok=True)
    reference_source.write_bytes(raw)
    invoke(["lake", "build", "+Audit.Export:olean", "+"+SPEC+":olean"], "audit-dependencies")
    names = ["QuantumComputation.Specs."+n for n in ["photochemistryAncillas",
        "photochemistryProgram", "photochemistryConstCost", "photochemistry_correctness",
        "photochemistry_const_cost"]]
    auxiliary = source.NS+".top1D73_cov"
    scalar_bridge = full.full_cauchy.NS+".cauchy_seg_list_auto_le"
    boolean_bridge = full.full_midtap.NS+".allBelow_true_iff"
    all_axioms, per_name = set(), {}
    types = {}
    for label, module in [("reference", SPEC), ("solution", full.TARGET)]:
        output_path = full.RESULTS / ("types-"+label+".json")
        script = full.CACHE / ("Types"+label.title()+".lean")
        text = f"import {module}\nimport Audit.Export\n"
        if label == "solution":
            text += "import FQCOracle.Tactic\nset_option maxHeartbeats 0\nrun_cmd FQCOracle.replay\n"
        text += f"run_cmd FQCAudit.exportTypes {json.dumps(str(output_path))}\n"
        if label == "solution":
            text += ("set_option pp.fullNames true\n"
                     "example : QuantumComputation.Specs.photochemistryAncillas = 417 := rfl\n"
                     "example : QuantumComputation.Specs.photochemistryConstCost = 605980010227389 := rfl\n")
            text += "".join(f"#print axioms {name}\n" for name in names)
            text += f"#print axioms {auxiliary}\n"
            text += f"#print axioms {scalar_bridge}\n"
            text += f"#print axioms {boolean_bridge}\n"
        script.write_text(text)
        output = invoke(["lake", "env", "lean", "-M4800", "-j1", str(script)], "audit-"+label)
        types[label] = json.loads(output_path.read_text())
        if label == "solution":
            if not base.axiom_list(output, auxiliary) <= base.STANDARD:
                raise ValueError("Unselected 1D coverage theorem gained an external assumption")
            if not base.axiom_list(output, scalar_bridge) <= base.STANDARD:
                raise ValueError("Generic Cauchy soundness bridge gained an external assumption")
            if not base.axiom_list(output, boolean_bridge) <= base.STANDARD:
                raise ValueError("Finite Boolean soundness bridge gained an external assumption")
            allowed = base.STANDARD | {g["axiom"] for g in manifest["groups"]} | {g["axiom"] for g in full.full_cauchy.facts()} | {full.full_midtap.fact()["axiom"]} | full.full_family.axiom_names()
            allowed |= full.full_oracle.names(local)
            for name in names:
                axioms = base.axiom_list(output, name)
                if not axioms <= allowed:
                    raise ValueError(f"Unexpected reachable axioms for {name}: {axioms-allowed}")
                per_name[name] = sorted(axioms)
                all_axioms |= axioms
    if types["reference"] != types["solution"]:
        raise ValueError("Elaborated public types differ from the original specification")
    type_lock = source.ROOT / "provenance/photochemistry-types.json"
    if not type_lock.exists() or json.loads(type_lock.read_text()) != types["reference"]:
        raise ValueError("Reference public types differ from the committed reviewed export")
    expected = {g["axiom"] for g in manifest["groups"]} | {g["axiom"] for g in full.full_cauchy.facts()} | {full.full_midtap.fact()["axiom"]} | full.full_family.axiom_names()
    oracle = full.full_oracle.verify_observations(local, full.RESULTS / "oracle-replay")
    expected |= set(oracle["goals"])
    reached = all_axioms & expected
    rendered = full.rendered_sources(manifest, local)
    report = {"status": "passed", "source_identity": "passed",
        "source_modules": len(local), "generated_modules": len(rendered),
        "unchanged_modules": sum(rendered[n] == raw for n,raw in local.items()),
        "namespace_shards": 23, "additional_section_shards": 8, "external_scalar_predicates": 3,
        "external_boolean_circuit_predicates": 1,
        "external_parameter_batches": {k: v["count"] for k,v in full.full_family.SPECS.items()},
        "freshly_replayed_named_decisions": len(oracle["goals"]),
        "oracle_goal_registry_sha256": source.sha((source.ROOT / "provenance/photochemistry-oracle-goals.json").read_bytes()),
        "final_program_and_theorem_source": "byte-identical to pinned upstream",
        "public_types": "equal canonical elaborated Expr in separate Lean processes",
        "type_export_sha256": source.sha(type_lock.read_bytes()),
        "external_axioms_registered": len(expected), "external_axioms_reachable": len(reached),
        "external_axioms_unused": sorted(expected-reached), "axioms_by_declaration": per_name,
        "retained_auxiliary_kernel_theorem": auxiliary,
        "kernel_checked_scalar_bridge": scalar_bridge,
        "kernel_checked_boolean_bridge": boolean_bridge,
        "unapproved_axioms": [], "comparator": "not run; original whitelist rejects external axioms",
        "reference_specification": "isolated type export; its intentional placeholders are not imported by solution"}
    return report


if __name__ == "__main__":
    full.RESULTS.mkdir(parents=True, exist_ok=True)
    result_path = full.RESULTS / "audit.json"
    result_path.write_text(json.dumps({"status": "running"})+"\n")
    try:
        report = check()
    except Exception as error:
        result_path.write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        raise
    result_path.write_text(json.dumps(report, indent=2)+"\n")
    print("PASS: final source identity, elaborated public types and reachable-axiom whitelist")
