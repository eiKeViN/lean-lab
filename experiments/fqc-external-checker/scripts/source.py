"""Reproduce the pinned source slices and parse only whitelisted certificate constructors."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
COMMIT = "a88de8ff65d78af564b2373088ca369dc95f6547"
PREFIX = "QuantumComputationDiscoveries/Algorithms/Photochemistry/Solution/"
MODULE = PREFIX.replace("/", ".")
SOURCES = {
    "Core": ("TopHadStage1Tab0Core", None),
    "Stream": ("TopHadCbvStreamCore", None),
    "Shared": ("TopHadStage1Tab2Shard0", "theorem c2_0"),
    "Stage1": ("TopHadStage1Tab1Shard0", "theorem c1_0"),
}
NS = "QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_upstream(stem: str) -> bytes:
    path = PREFIX + stem + ".lean"
    local = os.environ.get("FQC_UPSTREAM_ROOT")
    if local:
        return (Path(local) / path).read_bytes()
    cache = ROOT / ".cache/upstream" / (stem + ".lean")
    if not cache.exists():
        url = f"https://raw.githubusercontent.com/google-deepmind/formal-quantum-computation/{COMMIT}/{path}"
        with urllib.request.urlopen(url, timeout=45) as r:
            content = r.read()
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_bytes(content)
    return cache.read_bytes()


def sliced(stem: str, stop: str | None, raw: bytes) -> bytes:
    text = raw.decode()
    if stop:
        text = text[:text.index(stop)] + f"end {NS}\n\nend\n"
    for new, (old, _) in SOURCES.items():
        text = text.replace(MODULE + old, "FQCExternal.Vendor." + new)
    return text.encode()


# This is a constructor parser, not eval/exec of upstream Lean code.
TOKEN = re.compile(r"\s*(0x[0-9a-fA-F]+|[0-9]+|[A-Za-z_][A-Za-z_0-9]*|[()~])")
ARITY = {"bn": 3, "lf": 1, "e0": 0, "clm": 4, "cl1": 3, "bcm": 2, "bc1": 1}


class Parser:
    def __init__(self, text: str):
        self.text, self.pos = text, 0

    def token(self) -> str:
        m = TOKEN.match(self.text, self.pos)
        if not m:
            raise ValueError(f"Unsupported certificate syntax at {self.pos}")
        self.pos = m.end()
        return m.group(1)

    def term(self):
        token = self.token()
        if token == "(":
            value = self.term()
            if self.token() != ")":
                raise ValueError("Unbalanced certificate constructor")
            return value
        if token == "~":
            token = self.token()  # upstream ~n is nat_lit n, not bitwise negation
        if token.startswith("0x") or token.isdecimal():
            return int(token, 16 if token.startswith("0x") else 10)
        if token not in ARITY:
            raise ValueError(f"Unsupported constructor {token}")
        return [token, *[self.term() for _ in range(ARITY[token])]]


def cells(term) -> list[list[int]]:
    if term[0] == "cl1":
        return [term[1:4]]
    if term[0] == "clm":
        return [term[1:4], *cells(term[4])]
    raise ValueError("Invalid CellList")


def tree(term):
    if term[0] == "e0":
        return None
    if term[0] == "lf":
        return [hex(term[1]), None, None]
    if term[0] == "bn":
        return [hex(term[1]), tree(term[2]), tree(term[3])]
    raise ValueError("Invalid BTree")


def stream(term) -> list[str]:
    if term[0] == "bc1":
        return [hex(term[1])]
    if term[0] == "bcm":
        return [hex(term[1]), *stream(term[2])]
    raise ValueError("Invalid BitChain")


def extract(raw: bytes):
    text = raw.decode()
    declaration = text[text.index("theorem c1_0"):text.index("theorem c1_1")]
    needle = "evalS1Batch_sound"
    batches, replacements = [], []
    for i, match in enumerate(re.finditer(needle, declaration)):
        p = Parser(declaration[match.end():])
        values, terms = [], []
        for _ in range(3):
            start = p.pos
            values.append(p.term())
            terms.append(p.text[start:p.pos].strip())
        proof = re.match(r"\s*\(by decide \+kernel\)", p.text[p.pos:])
        if not proof:
            raise ValueError("Unexpected computational proof format")
        end = match.end() + p.pos + proof.end()
        batches.append({"schema": "fqc-stage1-batch-v1", "batch": i,
                        "cells": cells(values[0]), "words": tree(values[1]),
                        "stream": stream(values[2])})
        replacements.append((match.start(), end, f"External.batch{i}"))
        batches[-1]["_lean_terms"] = terms
    if len(batches) != 4:
        raise ValueError("Expected exactly four checker calls")
    public_type = declaration[declaration.index(":") + 1:declaration.index(":=")].strip()
    body = declaration
    for a, b, replacement in reversed(replacements):
        body = body[:a] + replacement + body[b:]
    body = body.replace("theorem c1_0", "theorem c1_0_external", 1)
    return batches, public_type, body


def verify_sources():
    manifest = json.loads((ROOT / "provenance/upstream.json").read_text())
    for new, (old, stop) in SOURCES.items():
        raw = read_upstream(old)
        record = manifest["sources"][new]
        if sha(raw) != record["sha256"]:
            raise ValueError(f"Upstream source hash mismatch: {old}")
        expected = sliced(old, stop, raw)
        actual = (ROOT / f"FQCExternal/Vendor/{new}.lean").read_bytes()
        if expected != actual or sha(actual) != record["derived_sha256"]:
            raise ValueError(f"Vendored slice mismatch: {new}")
    batches, public_type, body = extract(read_upstream("TopHadStage1Tab1Shard0"))
    if public_type != manifest["public_type"]:
        raise ValueError("Public proposition differs from upstream")
    for batch in batches:
        batch.pop("_lean_terms")
        name = f"data/c1_0/batch{batch['batch']}.json"
        raw = (ROOT / name).read_bytes()
        if json.loads(raw) != batch or sha(raw) != manifest["fixtures"][name]:
            raise ValueError(f"Fixture mismatch: {name}")
    return manifest, batches, body
