"""Validate a cold Lean transcript and export its public replay records."""
import argparse
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1] / "formal"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("log", type=Path)
args = parser.parse_args()
raw = args.log.read_bytes()
log = raw.decode()

modules = {}
for module, source, obj in re.findall(
    r"^PASS ([\w.]+) source=([0-9a-f]{64}) object=([0-9a-f]{64})$", log, re.M
):
    if module in modules:
        raise SystemExit(f"Repeated replay record for {module}")
    modules[module] = {"source_sha256": source, "object_sha256": obj}

files = {str(file.relative_to(root).with_suffix("")).replace("/", "."): file
         for file in root.rglob("*.lean")}
if files.keys() != modules.keys():
    raise SystemExit("Replay records do not match the local Lean source closure")
for module, file in files.items():
    if hashlib.sha256(file.read_bytes()).hexdigest() != modules[module]["source_sha256"]:
        raise SystemExit(f"Source mismatch for {module}")
complete = f"PASS {len(files)} local modules; no preexisting local objects were copied."
if not log.rstrip().endswith(complete):
    raise SystemExit("Missing successful completion of source-only replays")
if not re.search(r"^Build completed successfully \(\d+ jobs\)\.$", log, re.M):
    raise SystemExit("No successful strict build in the transcript")

decls = set(re.findall(r"^#print axioms ([\w.]+)$", (root / "HalfWordsAudit.lean").read_text(), re.M))
audits = {}
for decl, listed in re.findall(
    r"^info: HalfWordsAudit\.lean:\d+:\d+: '([\w.]+)' depends on axioms: \[([^\]]*)\]$",
    log, re.M,
):
    axioms = set(listed.split(", ")) if listed else set()
    if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit(f"{decl}: unexpected transitive axioms {sorted(axioms)}")
    audits[decl] = sorted(axioms)
if audits.keys() != decls:
    raise SystemExit("Axiom records do not match the requested audit declarations")

record = {
    "raw_transcript_sha256": hashlib.sha256(raw).hexdigest(),
    "toolchain": (root / "lean-toolchain").read_text().strip(),
    "build": "pass (fresh project directory, only third-party cache reused)",
    "transitive_axioms": audits,
    "independent_kernel_replays": modules,
}
print(json.dumps(record, indent=2, sort_keys=True))
