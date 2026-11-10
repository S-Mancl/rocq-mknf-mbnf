# Propositional MKNF and MBNF in Rocq

`rocq-mknf-mbnf` formalizes propositional minimal knowledge and negation as
failure (MKNF) and minimal belief and negation as failure (MBNF). It includes
syntax, finite-world semantics, verified reasoning procedures, and a worked
murder mystery.

This is the package distribution repository for
[MKNF-MBNF-Rocq](https://github.com/S-Mancl/MKNF-MBNF-Rocq).
The source provenance and proof assumptions are recorded in
[docs/ASSUMPTIONS.md](docs/ASSUMPTIONS.md).

## Requirements

The supported combination is Rocq **9.1.x** with **rocq-stdlib 9.0.x**, GNU Make,
and opam 2.x. These two Rocq packages have independent version numbers.
The initial local validation uses Rocq 9.1.0 and stdlib 9.0.0; other release
families are intentionally excluded until tested. There are no third-party
Rocq library or OCaml plugin dependencies. Python 3 is needed only to prepare
release assets.

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

## Releases and contributions

See [docs/RELEASING.md](docs/RELEASING.md) for the complete release and
package-index submission procedure. CI lints the opam definition, builds and
kernel-checks proofs, generates documentation, and checks installed imports.
For changes, run `opam lint rocq-mknf-mbnf.opam`, `make check`, and `make html`.
Record user-visible changes in [CHANGELOG.md](CHANGELOG.md).

Licensed under the [MIT license](LICENSE).
