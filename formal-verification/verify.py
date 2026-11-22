#!/usr/bin/env python3
"""Reproduce positive proofs and semantic rejection of false claims."""
from pathlib import Path
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / "logs"
LOGS.mkdir(exist_ok=True)
env = os.environ.copy()
env["CARGO_HOME"] = str(ROOT / "tooling/cargo")
env["RUSTUP_HOME"] = str(ROOT / "tooling/rustup")
env["PATH"] = str(ROOT / "tooling/cargo/bin") + os.pathsep + env.get("PATH", "")
VERUS = ROOT / "tooling/verus-arm64-macos/verus"

def run(arguments):
    command = [str(VERUS), *arguments]
    process = subprocess.Popen(command, cwd=ROOT, env=env, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=120)
        return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        return subprocess.CompletedProcess(command, 124, stdout, stderr + "\nVERIFICATION TIMEOUT\n")

(LOGS / "verification-summary.json").write_text(json.dumps(
    {"status": "running", "all_checks_passed": False}))
version = run(["--version"])
if version.returncode:
    sys.exit(version.stderr or version.stdout)
(LOGS / "versions.txt").write_text(version.stdout + version.stderr)
z3 = subprocess.run([str(VERUS.parent / "z3"), "--version"],
                    text=True, capture_output=True, check=True)
with (LOGS / "versions.txt").open("a") as handle:
    handle.write(z3.stdout)

files = [ROOT / "material_proofs.rs", *sorted((ROOT / "negative-controls").glob("*.rs"))]
report = {"utc": datetime.now(timezone.utc).isoformat(),
          "version": version.stdout.strip(), "z3": z3.stdout.strip(),
          "sha256_verifier": hashlib.sha256(VERUS.read_bytes()).hexdigest(),
          "sha256_rust_verify": hashlib.sha256((VERUS.parent / "rust_verify").read_bytes()).hexdigest(),
          "sha256_z3": hashlib.sha256((VERUS.parent / "z3").read_bytes()).hexdigest(),
          "runs": []}
for source in files:
    # Audit task-owned source only, not the trusted dependency library.
    code = re.sub(r"//[^\n]*", "", source.read_text())
    forbidden = re.search(r"\b(?:assume|admit)\s*\(|external_body|external_fn_specification|" 
                          r"verifier\s*::\s*(?:external|verify\s*\(\s*false)", code)
    if forbidden:
        sys.exit(f"Forbidden proof escape in {source.name}: {forbidden.group()}")
    rel = str(source.relative_to(ROOT))
    result = run([rel])
    output = result.stdout + result.stderr
    log = LOGS / (source.stem + ".log")
    log.write_text(f"COMMAND: {VERUS} {rel}\nEXIT: {result.returncode}\n\n{output}")
    is_positive = source.name == "material_proofs.rs"
    match = re.search(r"verification results:: (\d+) verified, (\d+) errors", output)
    if is_positive:
        ok = result.returncode == 0 and match is not None and int(match[1]) > 0 and int(match[2]) == 0
    else:
        ok = (result.returncode != 0 and match is not None
              and int(match[2]) > 0 and "postcondition not satisfied" in output)
    row = {"file": rel, "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
           "expected": "verified" if is_positive else "semantic rejection",
           "exit": result.returncode, "verified": int(match[1]) if match else None,
           "errors": int(match[2]) if match else None, "check_passed": ok}
    report["runs"].append(row)
    print(json.dumps(row, ensure_ascii=False), flush=True)
report["all_checks_passed"] = all(x["check_passed"] for x in report["runs"])
report["task_source_escape_audit"] = "No explicit forbidden constructs found; dependencies are trusted."
report["sha256_runner"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(LOGS / "verification-summary.json").write_text(json.dumps(report, indent=2, ensure_ascii=False))
sys.exit(0 if report["all_checks_passed"] else 1)
