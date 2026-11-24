"""Fresh kernel/native cross-checks for a representative Stage-2 certificate group."""
from __future__ import annotations

import json
from pathlib import Path

import full
import run as base
import source


def tree_term(t):
    return "e0" if t is None else f"(bn (nat_lit {t[0]}) {tree_term(t[1])} {tree_term(t[2])})"


def stream_term(words):
    term = "BitChain.empty"
    for word in reversed(words):
        term = f"(BitChain.more (nat_lit {word}) {term})"
    return term


def check():
    base.toolchain()
    manifest, _ = full.locked()
    raw = source.read_upstream("TopHadStage1Tab2Shard0").decode()
    declaration = raw[raw.index("theorem c2_0"):raw.index("theorem c2_1")]
    declaration = declaration.replace("theorem c2_0", "theorem kernel_c2_0", 1)
    preamble = ("import FQCExternal.Vendor.Shared\n"
                f"open {source.NS}\nset_option maxHeartbeats 4000000\n")
    reference = full.CACHE / "Stage2Reference.lean"
    reference.parent.mkdir(parents=True, exist_ok=True)
    reference.write_text(preamble + "namespace KernelReference\n" + declaration +
        "\nend KernelReference\nset_option pp.fullNames true\n"
        "#print axioms KernelReference.kernel_c2_0\n")
    metrics, out = base.run(["lake", "env", "lean", str(reference)], "stage2-kernel-reference")
    if not base.axiom_list(out, "KernelReference.kernel_c2_0") <= base.STANDARD:
        raise ValueError("Stage-2 reference uses an unexpected axiom")
    report = {"status": "passed", "kernel_reference": metrics, "group": "c2_0",
              "whole_decoder_equivalence": "not proved", "negative_tests": {}}
    record = next(b for b in manifest["batches"] if b["stage"] == 2)
    original = json.loads((full.CACHE / record["path"]).read_bytes())
    bad_inputs = {}
    bad = json.loads(json.dumps(original)); bad["words"][0] = "0x0"
    bad_inputs["dictionary-tag"] = bad
    bad = json.loads(json.dumps(original)); bad["stream"][0] = "0x0"
    bad_inputs["stream-tag"] = bad
    bad = json.loads(json.dumps(original)); bad["stream"] = []
    bad_inputs["missing-stream"] = bad
    bad = json.loads(json.dumps(original)); bad["words"] = None
    bad_inputs["missing-dictionary"] = bad
    negative_text = preamble
    checker = source.ROOT / ".lake/build/bin/fqc_checker"
    for i, (label, bad) in enumerate(bad_inputs.items()):
        path = full.RESULTS / ("invalid-stage2-"+label+".json")
        path.write_text(json.dumps(bad))
        metrics, out = base.run([str(checker), str(path)], "stage2-reject-"+label, expected=1)
        if json.loads(out)["accepted"] is not False:
            raise ValueError("Invalid Stage-2 certificate accepted")
        report["negative_tests"][label] = metrics
        negative_text += (f"theorem stage2_negative{i} : evalS2Batch460 "
            f"{base.cells_term(bad['cells'])} {tree_term(bad['words'])} "
            f"{stream_term(bad['stream'])} = false := by decide +kernel\n"
            f"#print axioms stage2_negative{i}\n")
    negative = full.CACHE / "Stage2NegativeReference.lean"
    negative.write_text(negative_text)
    metrics, out = base.run(["lake", "env", "lean", str(negative)], "stage2-kernel-negatives")
    for i in range(len(bad_inputs)):
        if not base.axiom_list(out, f"stage2_negative{i}") <= base.STANDARD:
            raise ValueError("Negative Stage-2 reference uses an unexpected axiom")
    report["kernel_negatives"] = metrics
    return report


if __name__ == "__main__":
    full.RESULTS.mkdir(parents=True, exist_ok=True)
    target = full.RESULTS / "stage2-reference.json"
    target.write_text(json.dumps({"status": "running"})+"\n")
    try:
        report = check()
    except Exception as error:
        target.write_text(json.dumps({"status": "failed", "error": str(error)})+"\n")
        raise
    target.write_text(json.dumps(report, indent=2)+"\n")
