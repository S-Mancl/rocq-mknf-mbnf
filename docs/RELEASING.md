# Releasing to the Rocq package index

The upstream submission process is documented in the
[Rocq packaging guide](https://rocq-prover.org/docs/opam-packaging).
The index is maintained in [rocq-prover/opam](https://github.com/rocq-prover/opam).
This repository hosts source, metadata, documentation, and the release helper;
publication requires a GitHub release followed by a separate index pull request.

## 1. Prepare a release commit

The suggested first version is `0.1.0`. Replace it consistently below if needed.

- Review `rocq-mknf-mbnf.opam`, including maintainer contact and dependency bounds.
  The source file deliberately omits `version` and `url` so local opam installs
  work before a release exists. The release helper adds both to the index entry.
- Update `CHANGELOG.md`: replace `Unreleased` with the version and release date.
- If changes have been made in the original repository since the recorded
  provenance commit, import and review them here before releasing.
- Run the checks below and wait for GitHub CI to pass on the release commit.
  The MIT license is included with the source contributors' permission.

```sh
opam lint rocq-mknf-mbnf.opam
opam install . --working-dir --with-test --with-doc
```

The `--working-dir` flag includes uncommitted local changes during this check.
Commit all intended source and packaging files, then tag that commit:

```sh
git add README.md LICENSE CHANGELOG.md Makefile _CoqProject theories docs scripts .github .gitignore .gitattributes rocq-mknf-mbnf.opam
git commit -m 'Prepare rocq-mknf-mbnf 0.1.0'
git tag -a v0.1.0 -m 'rocq-mknf-mbnf 0.1.0'
python3 scripts/prepare-release.py 0.1.0
```

The helper reads the tagged commit, not uncommitted files, and writes:

```text
dist/0.1.0/rocq-mknf-mbnf-0.1.0.tar.gz
dist/0.1.0/SHA512SUMS
dist/0.1.0/released/packages/rocq-mknf-mbnf/rocq-mknf-mbnf.0.1.0/opam
```

Keep these generated files together. The checksum in the generated opam file
matches those exact archive bytes. Do not replace published release assets or
move published tags; fix a published release by making a new version.

## 2. Test the actual archive

From this repository, extract into a fresh directory and install the archive
contents in a disposable opam switch with the supported dependencies:

```sh
mkdir -p /tmp/mknf-release-test
tar -xzf dist/0.1.0/rocq-mknf-mbnf-0.1.0.tar.gz -C /tmp/mknf-release-test
opam install /tmp/mknf-release-test/rocq-mknf-mbnf-0.1.0 --with-test --with-doc
```

Verify imports from outside either source tree, then remove the test package:

```sh
cd /tmp
printf '%s\n' 'From MKNF Require Import Finite Syntax Semantics Algorithms MurderMystery.' > MknfSmoke.v
opam exec -- rocq compile MknfSmoke.v
opam remove rocq-mknf-mbnf
```

Return to this repository for the next step.

## 3. Push and upload stable release assets

```sh
git push origin HEAD
git push origin v0.1.0
gh release create v0.1.0 --verify-tag --title 'rocq-mknf-mbnf 0.1.0' --notes-file CHANGELOG.md dist/0.1.0/rocq-mknf-mbnf-0.1.0.tar.gz dist/0.1.0/SHA512SUMS
opam lint --check-upstream dist/0.1.0/released/packages/rocq-mknf-mbnf/rocq-mknf-mbnf.0.1.0/opam
```

Upload the generated archive as a release **asset**. Do not use GitHub's
`archive/refs/tags/...` URL: GitHub does not guarantee stable checksums for those
automatically generated archives. The helper already uses the asset URL.
If a release already exists, use `gh release upload` to add the assets once.

## 4. Submit the package-index pull request

Fork `rocq-prover/opam` on GitHub. In a separate clone of your fork, add the
upstream remote if necessary, then create a branch from current upstream:

```sh
git remote add upstream https://github.com/rocq-prover/opam.git
git fetch upstream
git switch -c rocq-mknf-mbnf.0.1.0 upstream/master
```

Copy the generated `dist/0.1.0/released/packages/rocq-mknf-mbnf/` directory from
this repository into that clone's `released/packages/`. The resulting file must
be `released/packages/rocq-mknf-mbnf/rocq-mknf-mbnf.0.1.0/opam`.
From the index clone, lint and test it without a source pin masking the release:

```sh
opam lint --check-upstream released/packages/rocq-mknf-mbnf/rocq-mknf-mbnf.0.1.0/opam
# In a disposable switch, ensure no pin for this package remains:
opam pin remove rocq-mknf-mbnf --no-action
opam repository add mknf-release-test ./released
opam update
opam install rocq-mknf-mbnf.0.1.0 --with-test --with-doc --verbose
```

After successful installation:

```sh
git add released/packages/rocq-mknf-mbnf/rocq-mknf-mbnf.0.1.0/opam
git commit -m 'Package rocq-mknf-mbnf.0.1.0'
git push -u origin rocq-mknf-mbnf.0.1.0
gh pr create --repo rocq-prover/opam --title 'Package rocq-mknf-mbnf.0.1.0' --body 'Initial release of the propositional MKNF/MBNF formalization. Tested with Rocq 9.1.0 and rocq-stdlib 9.0.0.'
```

Respond to index CI and reviewer feedback. Once merged and published, users
can install with `opam update` and `opam install rocq-mknf-mbnf`.
