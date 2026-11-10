# Propositional MKNF and MBNF in Rocq

`rocq-mknf-mbnf` formalizes propositional minimal knowledge and negation as
failure (MKNF) and minimal belief and negation as failure (MBNF). It includes
syntax, finite-world semantics, verified reasoning procedures, and a worked
murder mystery.

This is the package distribution repository for
[MKNF-MBNF-Rocq](https://github.com/S-Mancl/MKNF-MBNF-Rocq).
The sources are unchanged from commit
[`ffef74a`](https://github.com/S-Mancl/MKNF-MBNF-Rocq/tree/ffef74a666c135d963038f0a41396ed28f6f6c4e).

## Requirements

Requires Rocq **9.1.x**, **rocq-stdlib 9.0.x**, GNU Make, and opam 2.x.
Python 3 is used by the release script.

## Install from this checkout

In an initialized opam switch:

```sh
opam repository add rocq-released https://rocq-prover.org/opam/released
opam install . --working-dir --with-test
```

Once a release has been accepted into the Rocq package index, users can instead
run `opam update` followed by `opam install rocq-mknf-mbnf`.

## Use the installed library

```coq
From MKNF Require Import Syntax Semantics Algorithms.
From MKNF Require Import MurderMystery.
Check entails91b_correct.
Check rosati_general_entailsb_correct.
Check bob_is_the_factual_culprit.
```

The opam package is called `rocq-mknf-mbnf`; its logical import namespace is
`MKNF`, preserving the original development's imports.

## Build and read the development

```sh
opam install . --deps-only
opam exec -- make -j2
opam exec -- make check
opam exec -- make html
```

Open `html/toc.html` to read the generated source documentation. `make install`
and `make uninstall` support manual installation; prefer opam for package
management. For a staged manual installation use `make install DESTDIR=/tmp/stage`.
`make clean` removes compilation products.

| Module | Contents |
| --- | --- |
| `MKNF.Finite` | Finite enumeration support |
| `MKNF.Syntax` | Formula syntax and notation |
| `MKNF.Semantics` | MKNF and MBNF model semantics |
| `MKNF.Algorithms` | Entailment, countermodels, partition algorithms, correctness |
| `MKNF.MurderMystery` | Worked reasoning example |

The development contains no declared axioms or admitted proofs.

## Maintenance

Run `opam lint rocq-mknf-mbnf.opam`, `make check`, and `make html` before
submitting changes. Record changes in [CHANGELOG.md](CHANGELOG.md).

To prepare release files from a tag such as `v0.1.0`, run
`python3 scripts/prepare-release.py 0.1.0`. The archive, checksum, and
package-index entry are written to `dist/0.1.0/`.

Licensed under the [MIT license](LICENSE).
