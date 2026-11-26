"""Build version 1.0.0 assets from a sealed source-only checkout."""
import argparse
import json
from hashlib import sha256
from pathlib import Path, PurePosixPath
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("source_zip", type=Path, help="unmodified verified upstream Lean source ZIP")
parser.add_argument("output", type=Path)
args = parser.parse_args()
output = args.output.resolve()
if output.is_relative_to(root):
    raise SystemExit("Write release assets outside the source checkout")
output.mkdir(parents=True, exist_ok=True)
if any(output.iterdir()):
    raise SystemExit("Choose a new or empty asset directory")

source_manifest = root / "MANIFEST.sha256"
files = {}
for line in source_manifest.read_text().splitlines():
    digest, name = line.split("  ", 1)
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or name in files:
        raise SystemExit(f"Unsafe or repeated path {name}")
    local = root / name
    if local.is_symlink() or not local.is_file():
        raise SystemExit(f"Invalid source entry {name}")
    data = local.read_bytes()
    if sha256(data).hexdigest() != digest:
        raise SystemExit(f"Source integrity failure {name}")
    files[name] = data

formal = {key.removeprefix("formal/"): value for key, value in files.items()
          if key.startswith("formal/")}
with ZipFile(args.source_zip) as source:
    evidence = {"fresh-kernel.log", "SHA256SUMS"}
    names = source.namelist()
    if sorted(set(formal) | evidence) != sorted(names):
        raise SystemExit("Lean verification ZIP inventory mismatch")
    if any(source.read(name) != data for name, data in formal.items()):
        raise SystemExit("Lean source ZIP byte mismatch")
    sums = {name: checksum
            for checksum, name in (line.split("  ", 1)
                                   for line in source.read("SHA256SUMS").decode().splitlines())}
    if sums.keys() != set(names) - {"SHA256SUMS"}:
        raise SystemExit("Lean verification ZIP checksum inventory mismatch")
    if any(sha256(source.read(name)).hexdigest() != checksum for name, checksum in sums.items()):
        raise SystemExit("Lean verification ZIP checksum mismatch")
    receipt = json.loads(files["verification/lean-cold-receipt.json"])
    if sums["fresh-kernel.log"] != receipt["raw_transcript_sha256"]:
        raise SystemExit("Lean cold-build receipt belongs to a different run")

assets = {
    "half-genus-hurwitz-paper.pdf": files["paper/main.pdf"],
    "half-genus-hurwitz-arxiv-source.zip": files["paper/arxiv-source.zip"],
    "half-genus-hurwitz-lean-source-v1.0.0.zip": args.source_zip.read_bytes(),
}
for name, data in assets.items():
    (output / name).write_bytes(data)
research = output / "half-genus-hurwitz-research-v1.0.0.zip"
prefix = "half-genus-hurwitz-v1.0.0/"
with ZipFile(research, "w") as package:
    for name, data in sorted({**files, source_manifest.name: source_manifest.read_bytes()}.items()):
        entry = ZipInfo(prefix + name, (2026, 11, 26, 0, 0, 0))
        entry.create_system = 3
        entry.external_attr = 0o100644 << 16
        package.writestr(entry, data, ZIP_DEFLATED, compresslevel=9)

with ZipFile(research) as package:
    if package.testzip() is not None:
        raise SystemExit("Research ZIP failed integrity check")
    if any(package.read(prefix + name) != data for name, data in files.items()):
        raise SystemExit("Research ZIP file mismatch")

checksums = "".join(f"{sha256(path.read_bytes()).hexdigest()}  {path.name}\n"
                    for path in sorted(output.iterdir()))
(output / "SHA256SUMS").write_text(checksums)
print(checksums, end="")
