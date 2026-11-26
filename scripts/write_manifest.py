"""Register the curated source files already staged in Git."""
from hashlib import sha256
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
index = subprocess.check_output(["git", "ls-files", "--cached", "-z"], cwd=root)
entries = index.decode().split("\0")
lines = []
for name in sorted(path for path in entries if path and path != "MANIFEST.sha256"):
    value = subprocess.check_output(["git", "show", f":{name}"], cwd=root)
    if (root / name).read_bytes() != value:
        raise SystemExit(f"Restage modified source {name}")
    lines.append(f"{sha256(value).hexdigest()}  {name}\n")
(root / "MANIFEST.sha256").write_text("".join(lines))
