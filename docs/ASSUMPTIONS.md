# Proof assumptions and source provenance

The five files in `theories/` are copied unchanged from
[S-Mancl/MKNF-MBNF-Rocq](https://github.com/S-Mancl/MKNF-MBNF-Rocq), commit
`ffef74a666c135d963038f0a41396ed28f6f6c4e` (verified against GitHub HEAD during package preparation).
The original report, generated HTML, and ZIP are not packaged here; documentation
is generated directly from the included source comments with `make html`.

There are no project-declared axioms, parameters, admitted proofs, or aborted
proofs in these sources. The library depends only on Rocq's kernel/core library
and the Rocq standard library. No OCaml plugin or extracted code is shipped.
`make check` runs the kernel checker on all five modules and their dependencies.

To inspect the transitive assumptions of a particular theorem, run `rocq repl`
after `make`, passing `-Q theories MKNF`, for example:

```coq
From MKNF Require Import Algorithms MurderMystery.
Print Assumptions entails91b_correct.
Print Assumptions rosati_general_entailsb_correct.
Print Assumptions bob_is_the_factual_culprit.
```

Kernel checking and `Print Assumptions` serve different purposes: the former
checks proof terms, while the latter reports any axioms a selected result uses.

Initial validation with Rocq 9.1.0 / rocq-stdlib 9.0.0 reports
`Closed under the global context` for all three results shown above.
