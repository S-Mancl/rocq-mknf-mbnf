#!/usr/bin/env python3
"""Generate local release assets and an index entry from an existing Git tag."""
import argparse
import gzip
import hashlib
import io
from pathlib import Path
import re
import subprocess
import tarfile

PACKAGE = "rocq-mknf-mbnf"
REPOSITORY = "https://github.com/S-Mancl/rocq-mknf-mbnf"
ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("version", help="release version, e.g. 0.1.0 (tag v0.1.0 must exist)")
    args = parser.parse_args()
    version = args.version
    if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", version):
        parser.error("use a numeric major.minor.patch version")
    tag = "v" + version
    try:
        commit = git("rev-parse", "--verify", f"refs/tags/{tag}^{{commit}}").decode().strip()
    except subprocess.CalledProcessError:
        parser.error(f"create tag {tag} on the tested release commit first")
    prefix = f"{PACKAGE}-{version}"
    archive_bytes = git("archive", "--format=tar", f"--prefix={prefix}/", commit)
    with tarfile.open(fileobj=io.BytesIO(archive_bytes)) as archive:
        metadata_file = archive.extractfile(f"{prefix}/{PACKAGE}.opam")
        if metadata_file is None:
            parser.error("tag does not contain the package metadata")
        metadata = metadata_file.read().decode()
        archive.getmember(f"{prefix}/LICENSE")
    if re.search(r"^\s*(version\s*:|url\s*\{)", metadata, re.M):
        parser.error("source opam file must omit version and url; this script adds them")
    payload = gzip.compress(archive_bytes, mtime=0)
    checksum = hashlib.sha512(payload).hexdigest()
    filename = prefix + ".tar.gz"
    metadata += (f'\nversion: "{version}"\nurl {{\n'
                 f'  src: "{REPOSITORY}/releases/download/{tag}/{filename}"\n'
                 f'  checksum: "sha512={checksum}"\n}}\n')
    output = ROOT / "dist" / version
    if output.exists():
        parser.error(f"{output} exists; move it aside before regenerating assets")
    entry = output / "released" / "packages" / PACKAGE / f"{PACKAGE}.{version}"
    entry.mkdir(parents=True)
    (output / filename).write_bytes(payload)
    (output / "SHA512SUMS").write_text(f"{checksum}  {filename}\n")
    (entry / "opam").write_text(metadata)
    print(f"Source commit: {commit}")
    print(f"Archive: {output / filename}")
    print(f"Index entry: {entry / 'opam'}")
    print("No files were uploaded. Follow docs/RELEASING.md to test and publish.")


if __name__ == "__main__":
    main()
