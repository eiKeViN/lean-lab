"""Pinned locations for named, outside-kernel evaluation of remaining closed goals."""
from __future__ import annotations

import json
import re
import subprocess

import source
import full_cauchy
import full_midtap
import full_family

STEMS = ["Stage4PrefixHoldDeferMux", "CrossStageCarryTap29", "CoulombMid36Stage5W298",
         "Stage25PolyCoinCoul18", "Stage25W314Splice"]


def code_only(text):
    """Mask nested Lean comments and quoted strings, preserving source offsets."""
    chars, i = list(text), 0
    while i < len(text):
        start = i
        if text.startswith("/-", i):
            depth, i = 1, i+2
            while depth and i < len(text):
                if text.startswith("/-", i): depth, i = depth+1, i+2
                elif text.startswith("-/", i): depth, i = depth-1, i+2
                else: i += 1
            if depth: raise ValueError("Unclosed Lean comment")
        elif text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0: i = len(text)
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
        else:
            i += 1
            continue
        for j in range(start, i):
            if chars[j] != "\n": chars[j] = " "
    return "".join(chars)


def plan(local):
    result = {"upstream": source.COMMIT, "sites": [], "retained_finite_case_sites": []}
    for stem in STEMS:
        module = source.MODULE+stem
        raw = local[module]
        text = raw.decode()
        for index, match in enumerate(re.finditer(r"\bdecide\s+\+kernel", code_only(text))):
            site = {"name": f"FQCOracle.Checked.{stem}_{index}",
                "module": module, "source_sha256": source.sha(raw), "index": index,
                "line": text.count("\n",0,match.start())+1, "offset": match.start(), "end": match.end()}
            # These two tiny sites run once per fin_cases branch, rather than
            # identifying one closed obligation. Keep their original kernel proofs.
            before = text[text.rfind("\n", 0, match.start())+1:match.start()]
            if before.strip() == "fin_cases b <;> dsimp [rt139MDOf] <;>":
                result["retained_finite_case_sites"].append(site)
            else:
                result["sites"].append(site)
    return result


def locked(local):
    actual = plan(local)
    path = source.ROOT / "provenance/photochemistry-oracle-sites.json"
    if not path.exists() or json.loads(path.read_text()) != actual:
        raise ValueError("Closed-goal oracle sites differ from reviewed source positions")
    return actual


def names(local):
    return {s["name"] for s in locked(local)["sites"]}


def observations(local, directory):
    result = {}
    for site in locked(local)["sites"]:
        record = json.loads((directory / (site["name"]+".json")).read_text())
        identity = {"name": site["name"], "module": site["module"],
                    "source_sha256": site["source_sha256"], "source_line": site["line"]}
        if any(record.get(k) != v for k,v in identity.items()) or record.get("accepted") is not True:
            raise ValueError("External observation differs from its locked source site")
        fields = ["goal_expr", "decision_expr", "axiom_type_expr", "decision_axioms", "goal"]
        result[site["name"]] = {**identity, **{k: record[k] for k in fields}}
    return {"upstream": source.COMMIT, "goals": result}


def verify_observations(local, directory):
    actual = observations(local, directory)
    path = source.ROOT / "provenance/photochemistry-oracle-goals.json"
    def semantic(record):
        # Pretty printing can change with open notation scopes. The retained
        # elaborated expressions, dependency sets and source positions cannot.
        return {"upstream": record["upstream"], "goals": {
            n: {k:v for k,v in goal.items() if k != "goal"} for n,goal in record["goals"].items()}}
    if not path.exists() or semantic(json.loads(path.read_text())) != semantic(actual):
        raise ValueError("Elaborated external goals differ from the reviewed exact proposition registry")
    return actual


def negative_tests(local):
    """Exercise actual Lean rejection paths, not fabricated success reports."""
    import full
    name = locked(local)["sites"][0]["name"]
    cases = {
        "false": (f"example : False := by fqc_checked {name}\n", "returned false"),
        "free-variable": (f"example (n : Nat) : n = n := by fqc_checked {name}\n", "requires a closed goal"),
        "unregistered": ("example : True := by fqc_checked FQCOracle.Unregistered\n", "Unregistered external source site"),
        "foreign-axiom": ("axiom foreign : Prop\naxiom foreignDecision : Decidable foreign\n"
            "attribute [local instance] foreignDecision\n"+
            f"example : foreign := by fqc_checked {name}\n", "Unapproved axiom"),
    }
    results = {}
    for label, (body, message) in cases.items():
        path = full.CACHE / ("OracleReject_"+label.replace("-", "_")+".lean")
        path.write_text("import FQCOracle.Tactic\n"+body)
        run = subprocess.run(["lake", "env", "lean", "-M4800", "-j1", str(path)],
            cwd=full.INTEGRATION, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (full.RESULTS / ("oracle-reject-"+label+".log")).write_text(run.stdout)
        if run.returncode == 0 or message not in run.stdout:
            raise ValueError(f"Oracle rejection case {label} did not fail for its intended reason")
        results[label] = "rejected"
    (full.RESULTS / "oracle-negatives.json").write_text(json.dumps(results, indent=2)+"\n")
    print("PASS: named evaluator rejects false, open, unregistered and foreign-axiom goals", flush=True)


def render(manifest, local):
    sites = locked(local)["sites"]
    fixed = {"propext", "Classical.choice", "Quot.sound"}
    fixed |= {g["axiom"] for g in manifest["groups"]}
    fixed |= {g["axiom"] for g in full_cauchy.facts()}
    fixed |= {full_midtap.fact()["axiom"]} | full_family.axiom_names()
    policy = ("module\npublic import Lean\n@[expose] public section\nnamespace FQCOracle.Policy\n"
              "structure Site where\n  name : Lean.Name\n  owner : String\n  source : String\n  line : Nat\n"
              "def sites : List Site := [\n")
    policy += ",\n".join("  ⟨`"+s["name"]+", "+json.dumps(s["module"])+", "+
        json.dumps(s["source_sha256"])+", "+str(s["line"])+"⟩" for s in sites)
    policy += "]\ndef fixed : List Lean.Name := [\n"
    policy += ",\n".join("  `"+name for name in sorted(fixed))
    policy += "]\ndef allowed (name : Lean.Name) : Bool :=\n  fixed.contains name || sites.any (·.name == name)\nend FQCOracle.Policy\n"
    rendered = {"FQCOracle.Policy": policy.encode()}
    for stem in STEMS:
        module = source.MODULE+stem
        text = local[module].decode()
        mine = [s for s in sites if s["module"] == module]
        for site in reversed(mine):
            text = text[:site["offset"]]+"fqc_checked "+site["name"]+text[site["end"]:]
        # Global named audit declarations must be added by synchronous elaboration.
        text = text.replace("set_option Elab.async true", "set_option Elab.async false")
        point = text.index("open QuantumComputation.")
        parents = re.findall(r"^(?:public )?import (?:all )?([\w.]+)", text, re.M)
        # Native evaluation inside a `module` needs transitive interpreter IR;
        # ordinary imports intentionally load only the runtime signatures.
        imports = "".join("meta import "+parent+"\n" for parent in parents)
        text = text[:point]+imports+"public import FQCOracle.Tactic\nset_option Elab.async false\n"+text[point:]
        rendered[module] = text.encode()
    return rendered
