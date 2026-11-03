# Feedback graphs in Lean

Formalization accompanying [The Price of Partial Information with Switching Costs:
A Complete Characterization for Feedback Graphs](paper.pdf).

The scope is the mathematical statements and algorithm correctness indexed in
[correspondence.tsv](correspondence.tsv): 42 labeled environments. Computational
complexity claims are excluded. In `ScoreRule`, "computable" means determined by
observed comparisons and known parameters, as expressed by
`ScoreRule.decoder_realization`. This does not assert a finite-precision implementation.

## Verify

Extract into a fresh directory. Install Lean through
[elan](https://github.com/leanprover/elan), and make `lake` and Git available.
`lean-toolchain` pins Lean 4.35.0; `lake-manifest.json` pins the dependencies.
The first build needs network access to obtain dependencies. From this directory:

```sh
lake --no-cache --wfail build
lake env lean -DwarningAsError=true Check.lean
```

`Check.lean` contains standard `#check` and `#print axioms` commands for the
58 indexed declarations. Inspect their types and transitive axiom dependencies;
the expected axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The project is distributed without compiled artifacts. Dependency artifacts may
be reused; a fresh project build checks the project proof sources.

An additional inspectable check rejects project axioms, unsafe declarations,
missing bodies, and other transitive axiom dependencies throughout the imported project:

```sh
lake env lean -DwarningAsError=true VerifyAxioms.lean
```

## Inspect

`Tournament.lean` imports all project modules; the proof sources are in
`Tournament/`. The correspondence table gives each result's number, title,
one-based PDF file page, printed page, and Lean declarations and source files.
It is a navigation index, not a certificate of semantic correspondence.

Lean checks the formal propositions. Comparison with the paper also requires
review of definitions, hypotheses, quantifiers, conclusions, and proof dependencies.
Readers can inspect any source and use their own verification procedures.
`SHA256SUMS` identifies the distributed files; hashes identify bytes, not correctness.

