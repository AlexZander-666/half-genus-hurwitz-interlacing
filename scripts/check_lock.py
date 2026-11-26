"""Check the Lean dependency checkout revisions before sharing the package cache."""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "formal" / "lake-manifest.json").read_text())
packages = Path(sys.argv[1]).resolve(strict=True)

for package in manifest["packages"]:
    name = package["name"]
    result = subprocess.check_output(
        ["git", "-C", str(packages / name), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    if result != package["rev"]:
        raise SystemExit(f"{name}: expected {package['rev']}, found {result}")
    diff = subprocess.check_output(
        ["git", "-C", str(packages / name), "status", "--porcelain", "--untracked-files=no"],
        text=True,
    )
    if diff:
        raise SystemExit(f"{name}: tracked dependency sources were changed")
    print(f"PASS {name} {result}")
