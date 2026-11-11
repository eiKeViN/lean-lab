#!/usr/bin/env python3
"""Fresh, offline mechanical checks of supervisor-selected Lean declarations.

Example:
  HGP_RUNTIME_ROOT=/path/to/runtime-root python3 supervision/check_submission.py \
    --snapshot /path/to/frozen-snapshot --project lean-project \
    --module HGPExperiment --declaration HGPExperiment:Namespace.theoremName \
    --output /path/to/new-supervisor-evaluation

The original snapshot is never executed or modified. Only ordinary .lean source
files are copied, into a newly created supervisor-owned room. Participant Lake
configuration, manifests, caches, executables, oleans, and native artifacts are
not used. Trusted configuration comes from supervision/lean-project. Builds
target each selected module separately, so an unrelated broken module cannot
hide an otherwise checkable milestone. Each declaration gets an independent
downstream import, #check, and #print axioms. Semantic acceptance remains a
separate supervisor review.

Target-map JSON schema: {"targets": [{"label": "A", "module": "Foo.Bar",
"declarations": ["Namespace.result"], "incomplete": false}]}.
Only a supervisor-selected JSON map is interpreted; TARGETS.md is not executed.
Repeat --source-dir for libraries with different source roots. Explicit roots
are supervisor-vetted; unrelated SHEAF links and .lake trees are not traversed.
Every consumed source path and its SHA-256 identity are recorded.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import stat
import sys
import tomllib


HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
TRUSTED_ROOTS = frozenset({"Init", "Lean", "Std", "Lake", "Mathlib", "QEC", "Aesop",
                           "Batteries", "Qq", "Plausible", "ProofWidgets", "Cli",
                           "LeanSearchClient", "ImportGraph"})
SKIP_DIRS = frozenset({".lake", ".git", ".cache", "node_modules", "build", "__pycache__"})
IDENT = re.compile(r"[^\W\d]\w*'*\Z", re.UNICODE)


class UnsafeInput(ValueError):
    pass


def checked_name(name):
    if not isinstance(name, str) or not name or any(not IDENT.fullmatch(x) for x in name.split(".")):
        raise UnsafeInput(f"unsupported or unsafe qualified Lean name: {name!r}")
    return name


def relative_path(value):
    p = Path(value)
    if p.is_absolute() or ".." in p.parts:
        raise UnsafeInput(f"expected a relative path without parent traversal: {value}")
    return p


def scan_snapshot(root):
    """Reject links and special files even inside directories later omitted."""
    if root.is_symlink() or root.resolve() != root or not root.is_dir():
        raise UnsafeInput("snapshot must be an ordinary directory")
    count = 0
    for current, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            path = Path(current) / name
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode):
                raise UnsafeInput(f"snapshot symlink rejected: {path.relative_to(root)}")
            if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                raise UnsafeInput(f"snapshot special file rejected: {path.relative_to(root)}")
            count += 1
    return count


def strip_comments(text):
    """Remove nested Lean comments and strings before checking import spelling."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                break
            out.append("\n")
            i = end + 1
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def source_manifest(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob("*.lean")) if ".lake" not in p.relative_to(root).parts
            and not p.name.startswith("SupervisorFreshAudit")}


def prepare_sources(source_roots, project, modules):
    """Materialize only selected modules and their local source import closure.

    Explicit source roots are supervisor-selected and may point through vetted
    directory symlinks. A consumed file must stay within its selected root.
    Unrelated snapshot links and ignored directories are never traversed.
    """
    copied, origins, missing, visited = [], {}, [], set()
    pending = list(modules)
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        checked_name(module)
        if module.split(".")[0] in TRUSTED_ROOTS or module.startswith("SupervisorFreshAudit"):
            raise UnsafeInput(f"selected source shadows a trusted/audit module: {module}")
        rel = Path(*module.split(".")).with_suffix(".lean")
        if any(part in SKIP_DIRS for part in rel.parts):
            raise UnsafeInput(f"source imports a build/cache path: {module}")
        candidates = [root / rel for root in source_roots if (root / rel).exists()]
        if not candidates:
            missing.append(module)
            continue
        contents = []
        for candidate in candidates:
            root = next(root for root in source_roots if candidate == root / rel)
            if not candidate.resolve().is_relative_to(root.resolve()):
                raise UnsafeInput(f"consumed source escapes selected root: {candidate}")
            if not stat.S_ISREG(candidate.stat().st_mode):
                raise UnsafeInput(f"consumed source is not a regular file: {candidate}")
            contents.append(candidate.read_bytes())
        if any(data != contents[0] for data in contents[1:]):
            raise UnsafeInput(f"ambiguous source module in multiple selected roots: {module}")
        clean = strip_comments(contents[0].decode("utf-8"))
        for match in re.finditer(r"(?m)^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)", clean):
            for imported in match.group(1).split():
                checked_name(imported)
                if any(x in {"lake", "build"} for x in imported.split(".")):
                    raise UnsafeInput(f"contrived build-path import in {rel}: {imported}")
                if imported.split(".")[0] not in TRUSTED_ROOTS:
                    pending.append(imported)
        dest = project / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(contents[0])
        copied.append(module)
        origins[module] = [str(candidate.resolve()) for candidate in candidates]
    template = tomllib.loads((HERE / "lean-project/lakefile.toml").read_text())
    lines = ['name = "SupervisorFreshEvaluation"', 'version = "0.1.0"',
             '[leanOptions]', 'autoImplicit = false']
    for dependency in template["require"]:
        lines += ['[[require]]', 'name = ' + json.dumps(dependency["name"]),
                  'path = ' + json.dumps(dependency["path"])]
    for root in sorted({m.split(".")[0] for m in copied}):
        lines += ['[[lean_lib]]', 'name = ' + json.dumps(root)]
    (project / "lakefile.toml").write_text("\n".join(lines) + "\n")
    for name in ("lean-toolchain", "lake-manifest.json"):
        shutil.copyfile(HERE / "lean-project" / name, project / name)
    return {"copied_source_modules": sorted(copied), "source_origins": origins,
            "missing_local_modules": sorted(missing),
            "policy": "selected source import closure only; unrelated links, participant Lake configuration, caches and binary artifacts unused"}


def parse_axioms(stdout, declaration):
    """Fail closed when Lean's actual axiom report is absent or ambiguous."""
    prefix = re.escape("'" + declaration + "'")
    empty = re.findall(prefix + r" does not depend on any axioms", stdout)
    nonempty = re.findall(prefix + r" depends on axioms:\s*\[([^\]]*)\]", stdout, re.S)
    if len(empty) + len(nonempty) != 1:
        raise ValueError("missing or ambiguous #print axioms output")
    axioms = [] if empty else [x.strip() for x in nonempty[0].split(",") if x.strip()]
    for axiom in axioms:
        checked_name(axiom)
    return {"axioms": axioms, "disallowed_axioms": sorted(set(axioms) - ALLOWED_AXIOMS)}


def load_targets(args):
    targets = []
    if args.target_map:
        raw = json.loads(args.target_map.read_text())
        records = raw["targets"] if isinstance(raw, dict) else raw
        if not isinstance(records, list):
            raise UnsafeInput("target map must contain a list of target records")
        for record in records:
            module = checked_name(record["module"])
            declarations = record.get("declarations", [])
            if not isinstance(declarations, list):
                raise UnsafeInput("target declarations must be a list")
            targets.append({"label": str(record.get("label", module)), "module": module,
                            "declarations": [checked_name(x) for x in declarations],
                            "declared_incomplete": bool(record.get("incomplete", False))})
    for module in args.module:
        targets.append({"label": module, "module": checked_name(module), "declarations": [],
                        "declared_incomplete": False})
    for spec in args.declaration:
        if ":" not in spec:
            raise UnsafeInput("--declaration must be MODULE:FULL_DECLARATION_NAME")
        module, declaration = (checked_name(x) for x in spec.split(":", 1))
        target = next((x for x in targets if x["module"] == module), None)
        if target is None:
            target = {"label": module, "module": module, "declarations": [], "declared_incomplete": False}
            targets.append(target)
        if declaration not in target["declarations"]:
            target["declarations"].append(declaration)
    if not targets:
        raise UnsafeInput("select at least one --module, --declaration, or --target-map record")
    return targets


def run_command(execute, room, output, index, argv, timeout):
    stem = f"command-{index:03d}"
    capture = room / "_supervisor_logs"
    capture.mkdir(exist_ok=True)
    log = capture / (stem + ".stdout")
    code = capture / (stem + ".exit")
    command = "cd /work/project && " + shlex.join(argv)
    wrapped = ("( " + command + " ) > " + shlex.quote("/work/_supervisor_logs/" + log.name)
               + " 2>&1; result=$?; printf '%s\\n' \"$result\" > "
               + shlex.quote("/work/_supervisor_logs/" + code.name) + '; exit "$result"')
    wrapper_output = execute(room, wrapped, timeout)
    (output / (stem + ".room-response.txt")).write_text(wrapper_output)
    # Do not follow links created by Lean metaprograms when reading host logs.
    scan_snapshot(room)
    raw = log.read_bytes() if log.exists() and not log.is_symlink() else b""
    (output / (stem + ".stdout")).write_bytes(raw)
    exit_code = None
    if code.is_file() and not code.is_symlink():
        try:
            exit_code = int(code.read_text().strip())
        except ValueError:
            pass
    response_code = re.match(r"\[exit (-?\d+)\]", wrapper_output)
    if response_code and exit_code != int(response_code.group(1)):
        raise UnsafeInput("command exit evidence inconsistent with room response")
    return {"argv": argv, "exit_code": exit_code,
            "timed_out": wrapper_output.startswith("[command timed out]"),
            "stdout_file": stem + ".stdout", "room_response_file": stem + ".room-response.txt"}, raw.decode(errors="replace")


def evaluate(args):
    targets = load_targets(args)
    snapshot = args.snapshot.absolute()
    if not snapshot.is_dir():
        raise UnsafeInput("snapshot must be a directory")
    project_root = snapshot / relative_path(args.project)
    source_dirs = args.source_dir or ["."]
    source_roots = [project_root / relative_path(value) for value in source_dirs]
    for source_root in source_roots:
        if not source_root.is_dir():
            raise UnsafeInput(f"project source directory does not exist: {source_root}")
    if not args.source_dir and not project_root.resolve().is_relative_to(snapshot.resolve()):
        raise UnsafeInput("project root escapes snapshot; explicitly select a vetted --source-dir")
    output = args.output.absolute()
    if output.resolve() == snapshot.resolve() or snapshot.resolve() in output.resolve().parents:
        raise UnsafeInput("evaluation output must be outside the participant snapshot")
    output.mkdir(parents=True, exist_ok=False)
    args._created_output = True
    room, project = output / "fresh-room", output / "fresh-room/project"
    project.mkdir(parents=True)
    preparation = prepare_sources(source_roots, project, [x["module"] for x in targets])
    original_sources = source_manifest(project)
    (output / "source-sha256.json").write_text(json.dumps(original_sources, indent=2, sort_keys=True) + "\n")
    # Import only after runtime-root is set. No participant Python is imported.
    if args.runtime_root:
        os.environ["HGP_RUNTIME_ROOT"] = str(args.runtime_root.resolve())
    from room import execute
    import room as room_runtime
    if not room_runtime.LEAN.is_dir() or not room_runtime.QEC.is_dir():
        raise OSError("trusted Lean/QEC runtime unavailable; set --runtime-root or HGP_RUNTIME_ROOT")
    report = {"snapshot": str(snapshot), "project": args.project, "source_dirs": source_dirs,
              "resolved_source_roots": [str(root.resolve()) for root in source_roots], "preparation": preparation,
              "allowed_axioms": sorted(ALLOWED_AXIOMS), "semantic_review": "required separately",
              "modules": {}, "targets": []}
    counter = 0
    for module in sorted({x["module"] for x in targets}):
        counter += 1
        command, _ = run_command(execute, room, output, counter, ["lake", "--no-cache", "--no-ansi", "build", "+" + module], args.timeout)
        command["status"] = "built" if command["exit_code"] == 0 else "incomplete"
        report["modules"][module] = command
    for target in targets:
        result = {**target, "checks": []}
        for declaration in target["declarations"]:
            counter += 1
            audit = project / f"SupervisorFreshAudit{counter}.lean"
            audit.write_text(f"import {target['module']}\n\nset_option pp.universes true\n"
                             f"#check {declaration}\n#print axioms {declaration}\n")
            shutil.copyfile(audit, output / audit.name)
            command, stdout = run_command(execute, room, output, counter,
                                           ["lake", "--no-cache", "--no-ansi", "env", "lean", audit.name], args.timeout)
            check = {"declaration": declaration, **command}
            if command["exit_code"] != 0:
                check["status"] = "incomplete"
                check["reason"] = "independent import/check failed or declaration missing"
            else:
                try:
                    check.update(parse_axioms(stdout, declaration))
                    check["status"] = "rejected" if check["disallowed_axioms"] else "mechanical_checks_passed"
                except (ValueError, UnsafeInput) as exc:
                    check["status"], check["reason"] = "rejected", str(exc)
            result["checks"].append(check)
        statuses = {x["status"] for x in result["checks"]}
        if "rejected" in statuses:
            result["status"] = "rejected"
        elif (target["declared_incomplete"] or "incomplete" in statuses
              or report["modules"][target["module"]]["status"] != "built"):
            result["status"] = "incomplete"
        else:
            result["status"] = "mechanical_checks_passed" if result["checks"] else "built_only"
        report["targets"].append(result)
    scan_snapshot(room)
    if source_manifest(project) != original_sources:
        raise UnsafeInput("participant sources changed during evaluation")
    statuses = {x["status"] for x in report["targets"]}
    report["status"] = ("rejected" if "rejected" in statuses else "incomplete" if "incomplete" in statuses
                        else "built_only" if "built_only" in statuses else "mechanical_checks_passed")
    (output / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return report


def self_test():
    assert parse_axioms("'Foo.good' does not depend on any axioms\n", "Foo.good")["axioms"] == []
    assert not parse_axioms("'Foo.good' depends on axioms: [propext,\n Classical.choice, Quot.sound]", "Foo.good")["disallowed_axioms"]
    assert parse_axioms("'Foo.bad' depends on axioms: [sorryAx]", "Foo.bad")["disallowed_axioms"] == ["sorryAx"]
    assert parse_axioms("'Foo.bad' depends on axioms: [Hidden.assumption]", "Foo.bad")["disallowed_axioms"] == ["Hidden.assumption"]
    for text in ("", "'Other.name' does not depend on any axioms", "'Foo.x' does not depend on any axioms\n'Foo.x' does not depend on any axioms"):
        try:
            parse_axioms(text, "Foo.x")
        except ValueError:
            pass
        else:
            raise AssertionError("missing/ambiguous axiom report accepted")
    for name in ("Foo;touch", "../Foo", "Foo.\n#error", "«.lake.build»"):
        try:
            checked_name(name)
        except UnsafeInput:
            pass
        else:
            raise AssertionError("unsafe Lean name accepted")
    assert "import Bad" not in strip_comments('/- /- nested -/ import Bad -/\nimport Good')
    return {"status": "passed", "tests": "happy/empty/standard/disallowed axioms; missing/ambiguous reports; unsafe names; nested comments"}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--snapshot", type=Path)
    parser.add_argument("--project", default=".")
    parser.add_argument("--source-dir", action="append", default=[],
                        help="repeat for supervisor-vetted source roots relative to project (including vetted directory links); default .")
    parser.add_argument("--output", type=Path, help="new supervisor-owned output directory, outside snapshot")
    parser.add_argument("--runtime-root", type=Path)
    parser.add_argument("--module", action="append", default=[])
    parser.add_argument("--declaration", action="append", default=[], metavar="MODULE:FULL_NAME")
    parser.add_argument("--target-map", type=Path)
    parser.add_argument("--timeout", type=int, default=120, help="per-command timeout, 1..600 seconds")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
        return 0
    if not args.snapshot or not args.output:
        parser.error("--snapshot and --output are required unless --self-test")
    if not 1 <= args.timeout <= 600:
        parser.error("--timeout must be from 1 through 600")
    try:
        report = evaluate(args)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        failure = {"status": "rejected" if isinstance(exc, UnsafeInput) else "evaluation_error", "reason": str(exc)}
        if getattr(args, "_created_output", False):
            (args.output / "failure.json").write_text(json.dumps(failure, indent=2) + "\n")
        print(json.dumps(failure, indent=2))
        return 2
    print(json.dumps({"status": report["status"], "report": str(args.output / "report.json"),
                      "targets": [{"label": x["label"], "status": x["status"]} for x in report["targets"]]}, indent=2))
    return 0 if report["status"] in {"mechanical_checks_passed", "built_only"} else 1


if __name__ == "__main__":
    sys.exit(main())
