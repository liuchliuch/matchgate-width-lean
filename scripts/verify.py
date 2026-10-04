#!/usr/bin/env python3
"""Build, audit and replay the complete mathematical project (Python 3.11+)."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]


def lean_code(text):
    """Remove nested comments and strings before checking forbidden tokens."""
    result, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            result.append(" ")
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unterminated Lean comment")
    return "".join(result)


def mathematical_files():
    return sorted([ROOT / "MatchgateWidth.lean", *ROOT.glob("MatchgateWidth/*.lean"),
                   ROOT / "PaperStatements.lean", ROOT / "PaperProofs.lean",
                   ROOT / "Verification.lean", ROOT / "Verification/Regression.lean",
                   ROOT / "Verification/OrderRegression.lean"])


def module_name(path):
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def source_checks(files):
    modules = {module_name(p) for p in files}
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|partial|initialize)\b")
    imports = {}
    for path in files:
        code = lean_code(path.read_text())
        if match := forbidden.search(code):
            raise ValueError(f"Forbidden token {match[0]} in {path.relative_to(ROOT)}")
        deps = re.findall(r"^import\s+([\w.]+)", code, re.M)
        if "PaperChallenge" in deps:
            raise ValueError("The trusted challenge is imported by mathematical code")
        imports[module_name(path)] = deps
    reachable = set()

    def visit(name):
        if name in reachable:
            return
        reachable.add(name)
        for dep in imports.get(name, []):
            visit(dep)

    for name in ["MatchgateWidth", "PaperProofs", "Verification"]:
        visit(name)
    if missing := modules - reachable:
        raise ValueError(f"Unimported mathematical modules: {sorted(missing)}")
    config = json.loads((ROOT / "Verification/comparator.json").read_text())
    targets = re.findall(r"^theorem\s+(\w+)", (ROOT / "PaperProofs.lean").read_text(), re.M)
    expected = ["MatchgateWidth.Paper." + target for target in targets]
    if config["theorem_names"] != expected:
        raise ValueError("Comparator targets do not match the complete paper proof interface")
    challenge = (ROOT / "PaperChallenge.lean").read_text()
    if re.findall(r"^theorem\s+(\w+)", challenge, re.M) != targets:
        raise ValueError("Challenge and solution target lists differ")
    return len(targets)


def digest(files):
    data = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in files}
    return hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()


def check_dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / package["name"]
        head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                       text=True).strip()
        if head != package["rev"]:
            raise ValueError(f"Dependency revision differs from lockfile: {package['name']}")
        dirty = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain",
                                         "--untracked-files=normal"], text=True).strip()
        if dirty:
            raise ValueError(f"Dependency has uncommitted changes: {package['name']}")
    return len(manifest["packages"])


def run(command, log_path, env=None):
    print("Running " + " ".join(map(str, command[:5])), flush=True)
    with log_path.open("w") as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        print(log_path.read_text()[-8000:], file=sys.stderr)
        raise RuntimeError(f"Command failed with exit {result.returncode}; see {log_path}")
    return log_path.read_text()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true", help="Remove project build artifacts only")
    parser.add_argument("--report", type=Path, help="Write a compact verification receipt")
    parser.add_argument("--comparator", type=Path, help="Official Comparator executable")
    parser.add_argument("--lean4export", type=Path, help="Compatible lean4export executable")
    parser.add_argument("--landrun", type=Path, help="Linux Landrun executable")
    parser.add_argument("--local-comparator", action="store_true",
                        help="Run Comparator without a sandbox, for trusted local code only")
    args = parser.parse_args()
    if args.local_comparator and not args.comparator:
        parser.error("--local-comparator requires --comparator")
    files = mathematical_files()
    contracts = source_checks(files)
    dependency_count = check_dependencies()
    frozen = files + [ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                      ROOT / "PaperChallenge.lean", ROOT / "Verification/comparator.json",
                      ROOT / "Verification/comparator-toolchain.json",
                      ROOT / "Verification/Audit.lean", ROOT / "Verification/Replay.lean",
                      ROOT / "scripts/verify.py"]
    before = digest(frozen)
    if args.clean:
        shutil.rmtree(ROOT / ".lake/build", ignore_errors=True)
    logs = ROOT / ".lake/verification"
    logs.mkdir(parents=True, exist_ok=True)
    build = run(["lake", "build", "MatchgateWidth", "PaperProofs", "Verification",
                 "Verification.Audit", "replay"], logs / "build.log")
    audit = run(["lake", "env", "lean", "Verification/Audit.lean"], logs / "axioms.log")
    match = re.search(r"AUDIT_OK declarations=(\d+) modules_with_declarations=(\d+)", audit)
    if not match:
        raise RuntimeError("Missing axiom audit completion marker")
    modules = sorted(map(module_name, files))
    replay = run(["lake", "exe", "replay", *modules], logs / "replay.log")
    if set(re.findall(r"^REPLAY_OK (\S+)$", replay, re.M)) != set(modules):
        raise RuntimeError("Kernel replay omitted a mathematical module")
    comparator = {"status": "not_run"}
    if args.comparator:
        env = os.environ.copy()
        if args.lean4export:
            env["COMPARATOR_LEAN4EXPORT"] = str(args.lean4export.resolve())
        if args.local_comparator:
            print("Comparator local mode: NO build sandbox; only use reviewed, trusted code.", flush=True)
            adapter = logs / "local-landrun.sh"
            adapter.write_text('#!/bin/sh\nwhile [ "$#" -gt 0 ]; do\n'
                               '  if [ "$1" = "--" ]; then shift; exec "$@"; fi\n'
                               '  shift\ndone\nexit 2\n')
            adapter.chmod(0o755)
            env["COMPARATOR_LANDRUN"] = str(adapter)
        elif args.landrun:
            env["COMPARATOR_LANDRUN"] = str(args.landrun.resolve())
        run(["lake", "env", str(args.comparator.resolve()), "Verification/comparator.json"],
            logs / "comparator.log", env)
        comparator = {"status": "pass", "statement_contracts": contracts,
                      "build_sandbox": not args.local_comparator, "external_kernel": False}
    if before != digest(frozen):
        raise RuntimeError("Mathematical sources or configuration changed during verification")
    check_dependencies()
    receipt = {"status": "pass", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
               "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
               "source_digest_sha256": before, "mathematical_modules": len(modules),
               "audited_declarations": int(match[1]), "paper_statement_contracts": contracts,
               "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
               "clean_project_build": args.clean, "kernel_replay": "same Lean kernel",
               "nonfatal_build_warnings": len(re.findall(r"^warning:", build, re.M)),
               "clean_pinned_dependencies": dependency_count,
               "dependencies": "pinned dependency build artifacts reused",
               "comparator": comparator}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
