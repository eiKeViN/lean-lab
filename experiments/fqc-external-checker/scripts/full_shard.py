"""Verbatim namespace shards of the pinned, memory-heavy HalfPlane module."""
from __future__ import annotations

import copy
import json
import re

import source
import full_cauchy
import full_midtap
import full_family

MODULE = source.MODULE + "HalfPlaneCauchyWalkCore"
ENDS = [721, 4035, 4725, 5097, 9069, 14273, 15047, 15577, 15611, 17027,
        17170, 17548, 17793, 18218, 18278, 20219]
PRELUDE = 89
MIDTAP = source.MODULE+"MidTap29Coul18Stage4K2"
MID_ENDS = [820, 2716, 3271, 4146, 4689, 5627, 6224]
COULOMB = source.MODULE+"CoulombMid36Stage5W298"
COULOMB_ENDS = [3461, 5407, 7423]
POLY = source.MODULE+"Stage25PolyCoinCoul18"
POLY_ENDS = [929, 985, 2310, 4070, 5796]


def plan(raw, module=MODULE, ends=ENDS, prelude=PRELUDE):
    lines = raw.decode().splitlines(keepends=True)
    if len(lines) != ends[-1]:
        raise ValueError("Pinned HalfPlane source layout changed")
    starts = [prelude+1] + [end+1 for end in ends[:-1]]
    before, after, stack = {}, {}, []
    for number, line in enumerate(lines, 1):
        if number in starts:
            if any(frame["kind"] == "namespace" for frame in stack):
                raise ValueError("Shard boundary lies inside a namespace")
            before[number] = copy.deepcopy(stack)
        text = line.rstrip()
        section = re.fullmatch(r"(?:@\[[^\n]+\] )?(?:noncomputable |public )?section(?: (\w+))?", text)
        namespace = re.fullmatch(r"namespace (\S+)", text)
        closing = re.fullmatch(r"end(?: (\S+))?", text)
        if section or namespace:
            match = namespace or section
            stack.append({"kind": "namespace" if namespace else "section",
                          "name": match.group(1), "opening": line, "commands": []})
        elif closing:
            if not stack:
                raise ValueError("Unbalanced source scope")
            frame = stack.pop()
            if closing.group(1) and frame["name"] != closing.group(1):
                raise ValueError("Mismatched source scope")
        elif number > prelude and not any(f["kind"] == "namespace" for f in stack):
            if text.startswith(("set_option ", "open ")):
                stack[-1]["commands"].append(line)
            elif text.startswith(("variable ", "attribute ", "local ")):
                raise ValueError("Unmodelled outer-scope command")
        if number in ends:
            after[number] = len(stack)
    if stack:
        raise ValueError("Unclosed source scopes")
    chunks = []
    for index, (start, end) in enumerate(zip(starts, ends)):
        frames = before[start]
        if frames[0]["opening"].strip() != "@[expose] public section":
            raise ValueError("Unexpected public declaration scope")
        chunks.append({"module": module+f"Parts.Part{index:02d}", "first_line": start,
            "last_line": end, "sha256": source.sha("".join(lines[start-1:end]).encode()),
            "active_scopes": frames, "closing_scopes": after[end]})
    return {"upstream": source.COMMIT, "original_module": module,
        "original_sha256": source.sha(raw), "prelude_lines": prelude,
        "prelude_sha256": source.sha("".join(lines[:prelude]).encode()), "chunks": chunks}


def render(raw):
    layout = plan(raw)
    lock = source.ROOT / "provenance/photochemistry-shards.json"
    if not lock.exists() or json.loads(lock.read_text()) != layout:
        raise ValueError("Namespace shard layout differs from the reviewed source ranges")
    lines = raw.decode().splitlines(keepends=True)
    rendered = {}
    previous = None
    for chunk in layout["chunks"]:
        prefix = "".join(lines[:20])
        if previous:
            prefix += f"public import {previous}\n"
        prefix += "".join(lines[20:PRELUDE])
        for index, frame in enumerate(chunk["active_scopes"]):
            if index:
                prefix += frame["opening"]
            prefix += "".join(frame["commands"])
        body = "".join(lines[chunk["first_line"]-1:chunk["last_line"]])
        text = prefix + body + "\n" + "end\n" * chunk["closing_scopes"]
        rendered[chunk["module"]] = text.encode()
        previous = chunk["module"]
    # Preserve the original import path. All declaration/proof bodies occur
    # verbatim, in order, in the publicly re-exported namespace shards.
    rendered[MODULE] = ("".join(lines[:17]) + f"\npublic import {previous}\n").encode()
    full_cauchy.transform(rendered)
    return rendered


def midtap_plan(raw):
    layout = plan(raw, MIDTAP, MID_ENDS, 135)
    lines = raw.decode().splitlines(keepends=True)
    layout["repeated_prelude_omission"] = {"first_line": 26, "last_line": 29,
        "sha256": source.sha("".join(lines[25:29]).encode()),
        "reason": "Scoped instance declarations occur once in Part00 and are imported thereafter"}
    return layout


def render_midtap(raw):
    layout = midtap_plan(raw)
    lock = source.ROOT / "provenance/photochemistry-midtap-shards.json"
    if not lock.exists() or json.loads(lock.read_text()) != layout:
        raise ValueError("MidTap namespace layout differs from the reviewed ranges")
    lines = raw.decode().splitlines(keepends=True)
    rendered, previous = {}, None
    for chunk in layout["chunks"]:
        prefix = "".join(lines[:135]) if previous is None else "".join(lines[:25]+lines[29:135])
        if previous:
            point = prefix.index("open QuantumComputation.")
            prefix = prefix[:point]+f"public import {previous}\n\n"+prefix[point:]
        # The original prelude already opens the public and noncomputable sections.
        for index, frame in enumerate(chunk["active_scopes"]):
            if index >= 2: prefix += frame["opening"]
            prefix += "".join(frame["commands"])
        body = "".join(lines[chunk["first_line"]-1:chunk["last_line"]])
        rendered[chunk["module"]] = (prefix+body+"\n"+"end\n"*chunk["closing_scopes"]).encode()
        previous = chunk["module"]
    rendered[MIDTAP] = ("".join(lines[:17])+f"\npublic import {previous}\n").encode()
    full_midtap.transform(rendered)
    full_family.transform_pairs(rendered)
    return rendered


def coulomb_plan(raw):
    layout = plan(raw, COULOMB, COULOMB_ENDS, 205)
    lines = raw.decode().splitlines(keepends=True)
    layout["repeated_prelude_omissions"] = [{"first_line": a, "last_line": b,
        "sha256": source.sha("".join(lines[a-1:b]).encode()),
        "reason": "Scoped instances are declared once in Part00"}
        for a,b in [(25,27),(48,50)]]
    if any(len(c["active_scopes"]) != 1 for c in layout["chunks"]):
        raise ValueError("Coulomb section boundaries must share only the public section")
    return layout


def render_coulomb(raw, transformed):
    """Partition the approved oracle transform at the original section ends."""
    layout = coulomb_plan(raw)
    lock = source.ROOT / "provenance/photochemistry-coulomb-shards.json"
    if not lock.exists() or json.loads(lock.read_text()) != layout:
        raise ValueError("Coulomb section layout differs from the reviewed ranges")
    return render_transformed(raw, transformed, layout)


def poly_plan(raw):
    layout = plan(raw, POLY, POLY_ENDS, 238)
    lines = raw.decode().splitlines(keepends=True)
    layout["repeated_prelude_omissions"] = [{"first_line": 26, "last_line": 29,
        "sha256": source.sha("".join(lines[25:29]).encode()),
        "reason": "Scoped instances are declared once in Part00"}]
    return layout


def render_poly(raw, transformed):
    layout = poly_plan(raw)
    lock = source.ROOT / "provenance/photochemistry-poly-shards.json"
    if not lock.exists() or json.loads(lock.read_text()) != layout:
        raise ValueError("Polynomial section layout differs from the reviewed ranges")
    return render_transformed(raw, transformed, layout)


def render_transformed(raw, transformed, layout):
    original = raw.decode().splitlines(keepends=True)
    lines = transformed.decode().splitlines(keepends=True)
    # Meta imports, the evaluator import and one synchronous option. Decision
    # replacements preserve line counts, so the original ranges remain usable.
    extra = len(re.findall(r"^(?:public )?import (?:all )?[\w.]+", raw.decode(), re.M))+2
    if len(lines) != len(original)+extra:
        raise ValueError("Oracle transform changed unexpected source lines")
    rendered, previous = {}, None
    for chunk in layout["chunks"]:
        prefix = "".join(lines[:layout["prelude_lines"]+extra])
        if previous:
            for item in layout["repeated_prelude_omissions"]:
                block = "".join(original[item["first_line"]-1:item["last_line"]])
                if prefix.count(block) != 1: raise ValueError("Scoped-instance source mismatch")
                prefix = prefix.replace(block, "", 1)
            point = prefix.index("public import FQCOracle.Tactic")
            prefix = prefix[:point]+f"public import {previous}\nmeta import {previous}\n"+prefix[point:]
        for index, frame in enumerate(chunk["active_scopes"]):
            if index: prefix += frame["opening"]
            prefix += "".join(frame["commands"])
        body = "".join(lines[chunk["first_line"]-1+extra:chunk["last_line"]+extra])
        rendered[chunk["module"]] = (prefix+body+"\n"+"end\n"*chunk["closing_scopes"]).encode()
        previous = chunk["module"]
    rendered[layout["original_module"]] = ("".join(original[:17])+f"\npublic import {previous}\n").encode()
    return rendered
