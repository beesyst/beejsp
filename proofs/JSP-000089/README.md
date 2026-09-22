# JSP-000089 — Iteration 4 Lean feasibility spike

Status: **GO for Iteration 5 planning only; not a complete formalization.**

This isolated Lean project tests the selected representation boundary from
Iteration 3. It defines simple-cycle lengths of a finite `SimpleGraph`, proves
that they form a bounded finite set, and proves the equivalence between the
source-style existential and a nonempty finite filtered set.

The full, unproved source statement, evidence, risks, and independent
statement-fidelity review are in [STATEMENT.md](STATEMENT.md) and
[EVIDENCE.md](EVIDENCE.md).

## Reproduce

From this directory, with network access only if Lake has not already fetched
the pinned dependencies:

```bash
lake build
lake env lean Statement.lean
lake env lean Audit.lean
```

`lean-toolchain` pins Lean `v4.19.0`. `lake-manifest.json` pins Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; the remaining manifest entries
are Mathlib's pinned transitive build dependencies. No local patch or parent
Python state is needed.

## Boundary and non-claim

`Main.lean` proves only `hasCycleLengthIn_iff_filter_nonempty`. It neither
constructs the source set nor proves the average-degree theorem. There are no
exploratory placeholders, `sorry`, `admit`, or custom axioms in this project.
