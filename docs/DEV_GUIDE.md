# DEV_GUIDE — BeeJSP development and formalization

## Purpose

This document explains:

- how to develop `beejsp`;
- how to use the Python environment through `uv`;
- how to work with the managed JSP reference snapshot;
- how to create and verify Lean proof projects;
- how to preserve proof reproducibility and attribution;
- how to use the BeeJSP repository workflow;
- how version and release lifecycle work.

## Related project docs

Use this document together with:

- `docs/ROADMAP.md` — delivery stages and iteration scope;
- `docs/ARCHITECTURE.md` — project boundaries and repository structure;
- `docs/FORMALIZATION.md` — mathematical and Lean formalization contract;
- `docs/SECURITY.md` — trust, external-input and supply-chain rules;
- `docs/SUBMISSION.md` — official JSP submission preparation and lifecycle;
- `AGENTS.md` — stable agent and repository rules.

Rule:

> `DEV_GUIDE` explains how to work on BeeJSP. It does not replace architecture,
> formalization, security, roadmap or submission contracts.

## Requirements

Base development requirements:

- Python 3.14+;
- `uv`;
- Git;
- Bash;
- standard Unix command-line tools used by repository scripts.

For Lean work:

- Lean 4 tooling compatible with the proof project's `lean-toolchain`;
- `lake`;
- normally `elan` for local toolchain management;
- VS Code Lean extension or equivalent editor support is recommended.

Do not use one globally assumed Lean version as proof evidence.

Each proof project pins its required environment.

## Repository

Primary repository:

```text
/home/bee/Pro/beejsp
```

Python distribution:

```text
beejsp
```

Python import:

```python
import beejsp
```

Managed JSP reference:

```text
docs/vendor/jsp/
```

Proof root:

```text
proofs/
```

## Development setup

From repository root:

```bash
uv sync
```

Manual `.venv` activation is not required.

Run Python and tool commands through:

```bash
uv run ...
```

## Basic commands

| Task                                   | Command                                                    |
| -------------------------------------- | ---------------------------------------------------------- |
| install Python development environment | `uv sync`                                                  |
| run tests                              | `uv run pytest -q`                                         |
| run Ruff                               | `uv run ruff check .`                                      |
| verify Ruff formatting                 | `uv run ruff format --check .`                             |
| build Python package                   | `uv build`                                                 |
| import smoke                           | `uv run python -c "import beejsp; print(beejsp.__file__)"` |
| show Python dependency tree            | `uv tree`                                                  |
| synchronize JSP reference              | `./scripts/sync_jsp_docs.sh`                               |
| inspect repository state               | `git status`                                               |
| validate diff whitespace               | `git diff --check`                                         |

For Lean, run commands from the relevant proof project.

Example:

```bash
cd proofs/_template
lake build
```

For a real proof:

```bash
cd proofs/JSP-XXXXXX
lake build
```

## Python dependency source of truth

Python dependency sources of truth:

```text
pyproject.toml
uv.lock
```

Rules:

- keep dependencies minimal;
- add dependencies only for demonstrated implementation need;
- update `pyproject.toml` and `uv.lock` together when an approved dependency
  change occurs;
- do not run or require `uv lock --check`;
- do not modify dependency surface during unrelated work.

The initial package may have:

```text
runtime dependencies = []
```

Do not add a GitHub library, HTTP client, parser framework or database merely because future scanner work might need one.

Use the standard library where it is sufficient.

## Lean dependency source of truth

Each real proof project owns its Lean dependency state.

Typical sources include:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
```

Rules:

- pin the environment required to reproduce the proof;
- commit reproducibility metadata;
- do not update Lean or Mathlib casually during unrelated proof work;
- inspect proof impact when a dependency revision changes;
- do not force all proofs to one global repository Lean version.

## Package structure

Initial Python package:

```text
src/beejsp/
└── __init__.py
```

Add modules only when required by current roadmap work.

Possible future modules include:

```text
catalog.py
scanner.py
competition.py
scoring.py
report.py
```

Do not create directories only for organizational symmetry.

Avoid premature:

```text
runtime/
server/
services/
database/
providers/
plugins/
state/
config/
```

## Package initializer

Keep:

```text
src/beejsp/__init__.py
```

byte-empty unless an explicitly approved public-package contract changes this rule.

Do not use it as a re-export layer.

## Development model

BeeJSP has two implementation modes:

```text
Python tooling
→ find, normalize, compare and report

Lean formalization
→ state and prove mathematics
```

Neither should silently absorb the other's responsibility.

Python candidate analysis does not prove a theorem.

Lean proof success does not prove that the selected theorem exactly matches the original problem unless statement fidelity was separately verified.

## Managed JSP reference

Synchronize the official reference with:

```bash
./scripts/sync_jsp_docs.sh
```

Managed destination:

```text
docs/vendor/jsp/
```

Do not edit files inside this directory manually.

If upstream reference material must change locally:

```text
change sync selection/logic if justified
→ run sync
→ review generated vendor diff
```

Do not hand-edit the generated result.

## Vendor provenance

Every valid managed snapshot records:

```text
docs/vendor/jsp/UPSTREAM_REF
docs/vendor/jsp/UPSTREAM_COMMIT
```

`UPSTREAM_COMMIT` should identify the exact resolved upstream revision.

Before relying on vendor material for a submission-sensitive task, verify that the snapshot is fresh enough for the approved task.

## Vendor idempotence

For synchronization changes, verify:

```bash
./scripts/sync_jsp_docs.sh
```

and then run it again.

The second synchronization against the same upstream revision should produce no additional managed diff.

Do not claim idempotence if it was not checked.

## Vendor failure behavior

Synchronization should validate the complete staged snapshot before accepting it.

A network error, missing required upstream file or invalid provenance state should not leave:

```text
docs/vendor/jsp/
```

half-updated while appearing valid.

When modifying synchronization behavior, test the applicable failure path.

## Live GitHub state

Do not use the managed snapshot as evidence of live:

- open PRs;
- closed PRs;
- merged PRs;
- current Issues;
- external competing proof repositories.

Future competition tooling should query live state explicitly.

For manual work, inspect current external state separately when the task requires it.

## Adding Python tooling

Before introducing a new scanner/parser/report contract, answer:

```text
Which roadmap iteration requires it?
What exact input does it consume?
What exact output does it produce?
Which fields are authoritative?
Which fields are derived?
Must the output be deterministic?
How is malformed input handled?
Why is a new dependency required, if any?
```

Avoid writing a broad framework before the first concrete ingestion/scanner use case exists.

## Problem-bank ingestion

Problem-bank ingestion should treat the upstream catalog as external data.

Prefer:

```text
vendored official record
→ parse
→ normalized internal representation
→ validation
```

Do not silently rewrite upstream facts.

When a value is:

- absent;
- ambiguous;
- malformed;
- contradictory;

represent that explicitly rather than inventing a value.

### Iteration 2 scanner

The first scanner consumes only the managed, pinned JSP snapshot. Run it from
the repository root with:

```bash
uv run python -m beejsp.scanner --output problem-bank.json --summary problem-bank.txt
```

It dynamically discovers `problems/catalog-*.md` under
`docs/vendor/jsp/`; it does not query the network or use the vendor snapshot as
live competition evidence. The canonical JSON contains the catalog paths,
vendor provenance, one normalized record per detailed catalog entry, diagnostics
and the derived `candidate_ids` set. Each record keeps raw official fields next
to normalized status values. `candidate_ids` is the unranked deterministic
filter for `Current status == Solved` and `Lean proof == No`.

If parsing or identity validation reports an error, `is_complete` is false and
the scanner withholds `candidate_ids`. Iteration 3 can consume the JSON records
and candidate IDs directly rather than reparsing JSP Markdown.

## Candidate analysis

Candidate analysis should separate facts from derived prioritization.

Example:

```text
Facts:
- problem status
- Lean status
- publication/source
- current competition evidence

Derived:
- estimated formalization complexity
- candidate score
- recommendation
```

Do not store a derived recommendation as though it were official JSP metadata.

## Deterministic tooling

When parser/scoring behavior is defined as deterministic:

```text
same normalized input
→ same deterministic output
```

Tests should cover stable normalization and scoring where applicable.

LLM analysis may supplement research.

It should not silently become the implementation of a deterministic repository contract.

## Creating a proof project

Do not create a real:

```text
proofs/JSP-XXXXXX/
```

until planning has approved work on that exact target.

Start from the smallest useful structure.

Typical command sequence may be:

```bash
mkdir -p proofs/JSP-XXXXXX
```

Then add only the Lake/Lean files required by the actual problem.

Do not mechanically copy unused layers from another proof.

## Proof template

The repository contains:

```text
proofs/_template/
```

Its purpose is:

- Lean CI smoke;
- project-layout example;
- toolchain/build demonstration.

It is not:

- a formalization candidate;
- a proof of any JSP problem;
- submission evidence.

## Formalization workflow

Use:

```text
docs/FORMALIZATION.md
```

as the formalization contract.

Typical development progression:

```text
problem evidence
↓
exact statement
↓
definitions
↓
bounded spike if needed
↓
lemmas
↓
complete proof
↓
lake build
↓
axiom audit
↓
statement review
↓
provenance review
```

Do not skip statement review merely because the code compiles.

## Bounded proof spike

When proof feasibility is unclear, prefer a bounded spike before committing to a large formalization.

A useful spike should test the actual hard boundary, such as:

- representation of the source statement;
- required Mathlib definitions;
- hardest known lemma;
- explicit counterexample;
- finite computation;
- specialized dependency availability.

The spike should result in:

```text
GO
```

or:

```text
NO-GO
```

for complete formalization.

Do not allow a spike to silently become an unreviewed full project.

## Statement development

Before proving a theorem, make the top-level mathematical contract inspectable.

Check:

- domains;
- quantifiers;
- hypotheses;
- conclusion;
- edge cases;
- equality/inequality direction;
- finiteness assumptions;
- existence/uniqueness conditions;
- source notation translation.

If the original problem is ambiguous, resolve the ambiguity before claiming completion.

## Proof development

Lean code should remain readable enough to review mathematical structure.

Prefer:

- standard Mathlib definitions;
- small meaningful lemmas;
- direct use of existing theorems;
- local proof-specific abstractions.

Avoid:

- custom frameworks unrelated to the problem;
- duplicated Mathlib functionality;
- hidden assumptions;
- opaque generated code that cannot be reviewed;
- unproved shortcuts.

## `sorry` and `admit`

A completed formalization must not depend on:

```text
sorry
admit
```

Temporary use during local exploration must not survive into completed proof evidence.

Before final review, verify their absence in the relevant proof scope.

## Axioms

Do not introduce a custom unproved axiom merely to bridge a missing proof step.

Where Lean/Mathlib foundations use standard trusted axioms, inspect the final theorem's axiom dependencies according to the approved verification contract.

Record required axiom-audit evidence.

## Clean proof reproduction

Before submission-sensitive review, reproduce the proof from committed sources and committed dependency metadata.

The proof should not depend on:

- an uncommitted local file;
- manually modified Mathlib source;
- hidden editor state;
- environment-only source code;
- unrecorded dependency checkout.

## AI-assisted Lean development

Copilot, Codex and other AI tools may assist with Lean development.

The required engineering loop remains:

```text
propose
→ compile
→ inspect
→ correct
→ verify
```

Do not treat generated proof text as accepted merely because it looks mathematically plausible.

## Tests

Primary Python test command:

```bash
uv run pytest -q
```

### Python areas to test

As applicable:

- package imports;
- catalog parsing;
- normalization;
- malformed-input handling;
- scoring/filtering;
- deterministic output;
- report generation;
- vendor metadata validation;
- synchronization helpers.

### Lean areas to verify

As applicable:

- project builds;
- target theorem exists;
- no incomplete placeholders;
- required theorem uses acceptable axioms;
- source scope matches formal scope;
- proof reproduces from committed environment.

## Python package build

When Python package or public metadata is affected:

```bash
uv build
```

Check at minimum:

- wheel produced;
- source distribution produced;
- `beejsp` importable;
- unrelated proof/vendor content is not unintentionally packaged;
- dependency metadata matches `pyproject.toml`.

Generated directories such as:

```text
dist/
build/
*.egg-info/
```

are verification outputs and normally remain ignored.

## Documentation

Relevant documentation:

```text
README.md
docs/ARCHITECTURE.md
docs/DEV_GUIDE.md
docs/FORMALIZATION.md
docs/ROADMAP.md
docs/SECURITY.md
docs/SUBMISSION.md
```

Do not mechanically modify every document.

Update only the contracts actually affected by the change.

## Versioning

Current Python/tooling version source of truth:

```text
pyproject.toml
```

BeeJSP uses SemVer.

Ordinary implementation work must not manually change the version.

Use Conventional Commits.

Typical mapping:

```text
feat:       additive project/tooling capability
fix:        compatible defect correction
docs:       documentation only
test:       tests only
refactor:   no intended behavior change
chore:      maintenance
ci:         CI
build:      build tooling
```

Breaking changes use the repository's normal breaking-change syntax.

Release-please owns release PR, version, changelog and tag lifecycle.

A new proof does not use the package version as its proof identity.

## Contribution flow

For significant work:

```text
ROADMAP
→ Issue
→ feature branch
→ implementation
→ tests / proof checks
→ independent verification
→ final review
→ PR
→ merge
→ release process when applicable
```

For external JSP submission after a BeeJSP proof is complete:

```text
BeeJSP final review
→ selected public proof commit
→ current submission runbook
→ external contribution flow
```

See:

```text
docs/SUBMISSION.md
```

## Branch naming

Follow the branch name selected by planning and the approved Issue.

Keep one coherent implementation task per branch.

Do not combine unrelated formalizations into one feature branch merely because they are both Lean work.

## What not to do

Do not:

- create a server without a concrete requirement;
- create `start.sh` without a runtime;
- add `config/settings.yml` without configurable runtime behavior;
- add a database before a data-persistence requirement exists;
- add dependencies "for later";
- manually edit managed JSP vendor files;
- treat catalog metadata as mathematical truth without review;
- treat `lake build` as statement-fidelity proof;
- use `sorry` in completed proof evidence;
- replace missing mathematics with a custom axiom;
- claim someone else's mathematical discovery;
- claim official JSP status without official evidence;
- manually bump package version during ordinary work.

## Before a significant PR

Run checks required by the actual task.

Typical Python baseline:

```bash
uv sync
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
```

When package behavior is affected:

```bash
uv build
```

When vendor synchronization is affected:

```bash
./scripts/sync_jsp_docs.sh
```

and verify applicable provenance/idempotence requirements.

When a Lean project is affected:

```bash
cd proofs/JSP-XXXXXX
lake build
```

plus the formalization-specific checks required by:

```text
docs/FORMALIZATION.md
```

Before PR, reviewer should be able to answer:

- what changed;
- which roadmap iteration owns it;
- whether Python/package behavior changed;
- whether vendor behavior changed;
- whether formalization scope changed;
- whether dependencies changed;
- which checks were executed;
- whether proof provenance changed;
- which limitations remain.

## Summary

BeeJSP development should remain centered on:

```text
small tooling
+ exact source data
+ exact mathematical statement
+ complete Lean proof
+ reproducible verification
+ correct provenance
```

Do not build infrastructure faster than real mathematical work requires it.
