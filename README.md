# BeeJSP — Reproducible Lean Formalization for Mathematical Problems

**BeeJSP** is an open-source Python and Lean project for helping the mathematical community identify suitable problems, formalize valid mathematical results in Lean, and publish reproducible machine-checked evidence.

The initial problem source and submission path is [The Justin Sun Prize](https://github.com/TheJustinSunPrize/awards).

> **Finding a candidate is not proving it. Compiling Lean is not enough either.**

BeeJSP asks a stricter question:

> Can we identify a worthwhile mathematical result, represent its exact meaning faithfully in Lean, prove it completely, independently reproduce the proof, and publish evidence another person can verify?

## Why BeeJSP

Modern AI systems can help with:

- mathematical research;
- theorem search;
- source analysis;
- Lean authoring;
- Mathlib discovery;
- proof decomposition;
- proof debugging;
- verification.

But there is a large gap between:

```text
AI produced Lean code
```

and:

```text
the original mathematical result
was represented faithfully
and completely machine-verified
```

BeeJSP is designed around closing that gap.

The target flow is:

```text
Problem
→ Research
→ Screen
→ Select
→ Formalize
→ Verify
→ Reproduce
→ Publish
→ Submit when appropriate
```

The objective is useful public formal mathematics.

A prize is a possible outcome.

It is not the definition of success.

## Project thesis

BeeJSP is built around one core chain:

```text
original mathematical problem
        ↓
exact mathematical meaning
        ↓
exact Lean statement
        ↓
complete Lean proof
        ↓
Lean verification
        ↓
independent statement review
        ↓
reproducible public evidence
```

Every transition matters.

A proof can compile and still be wrong for the original task if the formal statement:

- omits a case;
- weakens the conclusion;
- restricts the domain;
- adds a stronger assumption;
- formalizes a convenient special case instead of the full problem.

Therefore:

```text
lake build PASS
!=
original problem fully formalized
```

## Current status

BeeJSP is currently establishing the repository and verification foundation.

Current project flow:

```text
Repository foundation       IN PROGRESS
Managed JSP reference       IN PROGRESS
Python tooling foundation   IN PROGRESS
Lean template               IN PROGRESS

Problem scanner             NEXT
TOP-5 candidate selection   NEXT
First Lean spike            NEXT
Complete formalization      NEXT
Independent verification   NEXT
Official submission         NEXT
```

The first end-to-end project cycle is:

```text
official JSP problem bank
→ deterministic candidate scanner
→ evidence-backed TOP-5
→ selected candidate
→ bounded Lean feasibility spike
→ complete proof
→ independent verification
→ immutable public evidence
→ optional official JSP submission
```

See [`docs/ROADMAP.md`](docs/ROADMAP.md) for the complete iteration contracts.

## What BeeJSP is building

BeeJSP has three primary areas.

### 1. Problem discovery

Python tooling will help inspect and normalize mathematical problem records.

Initial goals include:

- parse the JSP problem bank;
- normalize problem metadata;
- identify solved problems without recorded Lean formalizations;
- preserve upstream provenance;
- distinguish official facts from BeeJSP-derived analysis;
- avoid manually scanning hundreds of catalog entries.

Conceptually:

```text
official problem records
→ normalized data
→ deterministic filters
→ candidate set
```

### 2. Candidate assessment

Not every mathematically solved problem is a good first formalization target.

BeeJSP evaluates candidates using evidence such as:

```text
mathematical solution available?
complete proof available?
statement unambiguous?
Lean proof already exists?
another formalization in progress?
finite / constructive structure?
Mathlib support?
formalization complexity?
submission/process risk?
```

Candidate assessment helps prioritize work.

It does not establish mathematical truth.

### 3. Lean formalization

Selected problems are formalized as independent Lean projects.

Conceptually:

```text
proofs/
├── _template/
├── JSP-XXXXXX/
├── JSP-YYYYYY/
└── ...
```

Each real proof should contain enough information to reproduce:

```text
problem
statement
proof
Lean toolchain
dependencies
verification
provenance
```

## One repository, multiple proofs

BeeJSP uses one public repository for the project.

We do **not** create a separate GitHub repository for every JSP problem.

Instead:

```text
beesyst/beejsp

proofs/
├── JSP-XXXXXX/
├── JSP-YYYYYY/
└── JSP-ZZZZZZ/
```

Each proof is isolated as its own Lean/Lake project when required.

This gives BeeJSP one:

- development workflow;
- Issue system;
- review process;
- CI foundation;
- public provenance history;
- security model;
- contribution model.

while preserving proof-level isolation.

## Formalization standard

A completed BeeJSP formalization must satisfy more than compilation.

### Exact statement

The formal theorem must preserve the required:

- domains;
- quantifiers;
- hypotheses;
- conclusion;
- cases;
- boundary assumptions;
- mathematical meaning.

### Complete proof

Completed proof evidence must not depend on:

```text
sorry
admit
```

or a custom unproved axiom introduced merely to bypass missing mathematics.

### Reproducible environment

Each real proof pins its required Lean environment.

Typical proof metadata includes:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
```

where applicable.

### Axiom audit

The principal theorem receives the applicable axiom review.

The goal is not necessarily "no axioms whatsoever".

The goal is to ensure the theorem does not depend on an unexpected custom axiom that substitutes for missing proof.

### Provenance

A completed proof should make it possible to recover:

```text
problem source
mathematical solution source
solver
formalizer
repository
exact commit
proof project
principal theorem
toolchain
dependencies
build evidence
axiom evidence
```

See [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md).

## Attribution

BeeJSP keeps the following roles distinct:

```text
problem author / source
mathematical solver
Lean formalizer
independent verifier
```

These may be the same person.

They may also be completely different people.

Formalizing someone else's mathematical result does not transfer authorship of the mathematical discovery.

AI assistance does not erase original solver attribution.

## AI boundary

AI may assist with:

- problem research;
- source organization;
- candidate screening;
- theorem translation;
- Lean coding;
- Mathlib search;
- proof decomposition;
- debugging;
- review;
- documentation.

AI output is not itself proof evidence.

The engineering loop remains:

```text
propose
→ compile
→ inspect
→ correct
→ verify
```

The final mathematical claim must be grounded in:

```text
source evidence
+
exact Lean statement
+
kernel-checked proof
+
independent review
```

## Managed JSP reference

BeeJSP keeps a selected read-only snapshot of official Justin Sun Prize material under:

```text
docs/vendor/jsp/
```

Canonical source:

```text
https://github.com/TheJustinSunPrize/awards
```

Canonical synchronization command:

```bash
./scripts/sync_jsp_docs.sh
```

Every valid snapshot records:

```text
docs/vendor/jsp/UPSTREAM_REF
docs/vendor/jsp/UPSTREAM_COMMIT
```

The vendor snapshot is:

- generated;
- pinned to an exact upstream revision;
- reviewable;
- reproducible;
- read-only.

It is **not**:

- a permanent fork;
- a Git submodule;
- live GitHub state;
- an independent official authority.

Correct model:

```text
official JSP upstream
→ exact revision
→ BeeJSP managed snapshot
→ local research / planning / verification
```

## Why not a permanent JSP fork?

BeeJSP is its own project.

The official JSP repository is an external source and contribution target.

Development happens here:

```text
beesyst/beejsp
```

When a completed formalization is ready for official submission:

```text
verified BeeJSP proof
→ exact public BeeJSP commit
→ fresh official rules
→ current official fork
→ contribution branch
→ official PR
```

The external fork is contribution transport.

It is not BeeJSP's architecture.

## Vendor snapshot vs live competition state

The managed JSP snapshot tells us what official source material looked like at a specific revision.

It does not prove current live state such as:

```text
open PR
new Issue
another Lean attempt
external proof repository
recent merge
```

Therefore BeeJSP keeps these concepts separate:

```text
docs/vendor/jsp/
→ pinned official reference

live GitHub research
→ current competition evidence
```

Before investing heavily in a candidate or submitting a proof, current competition state should be checked separately.

## Candidate selection

The first scanner is intended to reduce the current problem bank into a smaller set worth manual mathematical review.

A useful initial direction is:

```text
Solved
+
no recorded Lean proof
+
complete mathematical solution available
+
reasonable Lean complexity
+
no known competing complete formalization
```

But no single catalog field is authoritative enough to select a proof by itself.

For example:

```text
Solved
```

in a problem catalog does not automatically mean universal mathematical consensus.

And:

```text
Lean proof: No
```

does not prove another formalizer is not already working on it.

BeeJSP therefore combines:

```text
official record
+
mathematical source
+
live competition evidence
+
formalization feasibility
```

before committing to substantial proof work.

## Bounded Lean spike

BeeJSP does not immediately spend weeks formalizing a difficult theorem.

For an uncertain candidate, the first proof iteration should test the hardest known boundary.

Examples:

- exact theorem representation;
- explicit counterexample;
- finite witness;
- hardest central lemma;
- specialized Mathlib support;
- computational verification boundary.

The spike ends with:

```text
GO
```

or:

```text
NO-GO
```

A well-supported `NO-GO` is a successful engineering result.

It prevents wasted formalization effort.

## Proof projects

A real formalization lives under:

```text
proofs/JSP-XXXXXX/
```

The exact internal layout depends on the mathematics.

A proof may evolve toward:

```text
proofs/JSP-XXXXXX/
├── README.md
├── lean-toolchain
├── lakefile.toml
├── lake-manifest.json
├── Challenge.lean
├── Solution.lean
└── BeeJSP/
    ├── Definitions.lean
    ├── Lemmas.lean
    └── Main.lean
```

This is not a mandatory framework.

Use the smallest structure that makes the proof understandable and reproducible.

Rule:

> Add proof structure because the mathematics requires it, not because a framework template has empty folders available.

## Independent verification

Proof implementation and proof verification are separate passes.

Independent verification checks:

```text
original problem
vs
mathematical interpretation
vs
Lean definitions
vs
top-level theorem
```

and also verifies:

```text
complete proof
Lean build
sorry/admit absence
axiom dependencies
toolchain
dependencies
provenance
attribution
reproduction
```

The verifier should not simply trust:

- the implementation report;
- generated documentation;
- AI reasoning;
- theorem name;
- successful compilation.

## Submission model

BeeJSP supports formalizations intended for The Justin Sun Prize.

External submission happens only after local proof completion.

Correct order:

```text
formalize
→ independently verify
→ freeze public evidence
→ refresh official rules
→ check live competition
→ submit
```

Not:

```text
open official PR
→ finish proof later
```

Before an actual JSP submission, BeeJSP rechecks current official:

- contribution rules;
- verification requirements;
- attribution rules;
- award/claim process;
- exact problem record.

See [`docs/SUBMISSION.md`](docs/SUBMISSION.md).

## External status

BeeJSP distinguishes states carefully.

```text
BeeJSP proof complete
!=
official JSP verified
```

```text
official PR opened
!=
official PR merged
```

```text
official PR merged
!=
award approved
```

```text
award approved
!=
payment completed
```

Public project status should reflect only evidence that actually exists.

## Architecture

BeeJSP has two implementation surfaces and one external-reference boundary.

```text
                    Mathematical sources
                           │
                           ▼
               TheJustinSunPrize/awards
                           │
               ┌───────────┴───────────┐
               │                       │
               ▼                       ▼
       docs/vendor/jsp/         live external state
        pinned reference        PRs / Issues / repos
               │                       │
               └───────────┬───────────┘
                           ▼
                    BeeJSP tooling
               discovery / selection
                           │
                           ▼
                    Lean proof project
                           │
                           ▼
                reproducible verification
                           │
                           ▼
                  public proof evidence
                           │
                           ▼
                 optional JSP submission
```

### Python owns

- catalog ingestion;
- normalization;
- deterministic filtering;
- candidate tooling;
- competition analysis;
- reports;
- repository automation.

### Lean owns

- exact mathematical statements;
- proof-local definitions;
- proof-local lemmas;
- complete proofs;
- machine-checking evidence.

### Official JSP upstream owns

- official problem records;
- official candidate records;
- official verification state;
- official eligibility/claim state;
- award decisions.

BeeJSP must not manufacture official status locally.

## Python / Lean boundary

Python helps answer:

> What should we work on?

Lean helps answer:

> Is this exact formal theorem proved?

Python does not establish mathematical truth.

Lean compilation does not establish that the theorem chosen by Python faithfully matches the original problem.

Both layers need review.

## Repository structure

Target project structure:

```text
beejsp/
├── .agents/
│   ├── prompts/
│   └── skills/
├── .github/
│   ├── ISSUE_TEMPLATE/
│   ├── PULL_REQUEST_TEMPLATE/
│   ├── release-please/
│   └── workflows/
├── docs/
│   ├── ARCHITECTURE.md
│   ├── DEV_GUIDE.md
│   ├── FORMALIZATION.md
│   ├── ROADMAP.md
│   ├── SECURITY.md
│   ├── SUBMISSION.md
│   └── vendor/
│       └── jsp/
├── proofs/
│   └── _template/
├── scripts/
│   └── sync_jsp_docs.sh
├── src/
│   └── beejsp/
│       └── __init__.py
├── tests/
├── AGENTS.md
├── CHANGELOG.md
├── LICENSE
├── README.md
├── pyproject.toml
└── uv.lock
```

BeeJSP currently does not need:

```text
start.sh
config/start.py
config/settings.yml
database/
server/
worker/
runtime storage/
```

There is no application runtime to configure or start.

## Python package

The Python package follows the standard `src` layout:

```text
src/beejsp/
```

`src/beejsp/__init__.py` remains byte-empty.

Do not use it for:

- re-exports;
- registration;
- initialization;
- version constants;
- hidden I/O.

Future modules should be introduced only when real work requires them.

Possible examples:

```text
catalog.py
scanner.py
competition.py
scoring.py
report.py
```

These are not bootstrap requirements.

## Import safety

This must remain safe:

```python
import beejsp
```

Importing the package must not unexpectedly:

- access the network;
- invoke Git;
- synchronize JSP upstream;
- run shell commands;
- build Lean;
- modify repository files;
- contact GitHub;
- load credentials.

## Security

BeeJSP processes external content.

That content is untrusted until reviewed.

Examples:

- public repositories;
- mathematical documents;
- Lean projects;
- GitHub data;
- catalog content;
- dependency metadata;
- downloaded files.

Core rules:

```text
external content
!=
execution authority
```

```text
vendor snapshot
!=
trusted executable code
```

```text
proof evidence
!=
GitHub write authority
```

Do not commit:

- GitHub tokens;
- SSH keys;
- wallet private keys;
- seed phrases;
- KYC documents;
- tax documents;
- private payment information;
- unrelated personal data.

See [`docs/SECURITY.md`](docs/SECURITY.md).

## Development

Requirements:

- Python 3.14+
- `uv`
- Git
- Bash
- Lean/Lake tooling when working on formalizations

Install Python environment:

```bash
uv sync
```

Run Python tests:

```bash
uv run pytest -q
```

Run Ruff:

```bash
uv run ruff check .
uv run ruff format --check .
```

Build Python package:

```bash
uv build
```

Import smoke:

```bash
uv run python -c "import beejsp; print(beejsp.__file__)"
```

Show Python dependencies:

```bash
uv tree
```

Synchronize JSP reference:

```bash
./scripts/sync_jsp_docs.sh
```

Build the Lean template:

```bash
cd proofs/_template
lake build
```

Build a real proof:

```bash
cd proofs/JSP-XXXXXX
lake build
```

Do not run or require:

```text
uv lock --check
```

## Development workflow

Significant work follows:

```text
ROADMAP
→ planning
→ Issue
→ feature branch
→ implementation
→ tests / proof checks
→ independent verification
→ final read-only review
→ PR
→ merge
```

BeeJSP uses the same canonical agent pipeline for:

- Python tooling;
- repository automation;
- Lean formalizations;
- verification corrections.

There is no separate submission agent pipeline.

Repository-wide agent rules are defined in [`AGENTS.md`](AGENTS.md).

## Versioning

BeeJSP tooling uses SemVer.

Version source of truth:

```text
pyproject.toml
```

Release lifecycle is managed through release automation.

Ordinary:

- feature;
- fix;
- docs;
- proof;
- maintenance;

work does not manually edit the package version unless the task is explicitly release-related.

Important distinction:

```text
BeeJSP version
→ software/tooling release

proof identity
→ exact repository source + commit + theorem
```

A package version is not mathematical proof provenance.

## CI

BeeJSP CI validates separate project boundaries.

Conceptually:

```text
Python
→ tests
→ Ruff
→ package checks

JSP reference
→ managed metadata sanity
→ required reference files

Lean
→ template / proof build
→ pinned proof environment
```

Proof projects may intentionally use different pinned Lean toolchains.

Do not force every formalization onto one global Lean version solely for CI convenience.

## Roadmap

The first BeeJSP cycle is deliberately small.

### Stage 1 — Foundation

```text
repository
→ Python/Lean foundation
→ managed JSP reference
```

### Stage 2 — Discovery

```text
problem-bank parser
→ candidate scanner
→ live competition evidence
→ TOP-5
→ one selected candidate
```

### Stage 3 — Formalization

```text
exact statement
→ bounded Lean spike
→ GO / NO-GO
→ complete proof
```

### Stage 4 — Verification and submission

```text
independent verification
→ immutable public evidence
→ current official JSP process
→ external contribution
```

After the first end-to-end proof, BeeJSP stops and evaluates what actually needs to become reusable.

It does not automatically continue building infrastructure merely because more iteration numbers are available.

See [`docs/ROADMAP.md`](docs/ROADMAP.md).

## Documentation

- [`docs/ROADMAP.md`](docs/ROADMAP.md) — project stages and iteration contracts
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — project boundaries and repository architecture
- [`docs/DEV_GUIDE.md`](docs/DEV_GUIDE.md) — local Python, vendor and Lean development
- [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md) — statement, proof, reproducibility, axioms and attribution contract
- [`docs/SECURITY.md`](docs/SECURITY.md) — external-input, supply-chain, credential and private-data rules
- [`docs/SUBMISSION.md`](docs/SUBMISSION.md) — official JSP contribution and claim preparation
- [`AGENTS.md`](AGENTS.md) — repository guidance for development agents

## KISS

BeeJSP should produce useful mathematics before building a platform.

Current priority:

```text
reproducible official reference
→ good candidate selection
→ exact theorem
→ complete Lean proof
→ independent verification
→ public evidence
```

Not:

```text
database
→ generic agent framework
→ dashboard
→ hosted proof service
→ generic theorem platform
→ automatic claims
→ eventually prove something
```

New abstractions should appear only after real proofs demonstrate a repeated need.

## Goal

BeeJSP succeeds when another person can take a mathematical result produced or formalized through this project and answer:

> What exactly was claimed, where did it come from, who solved it, who formalized it, what exact Lean theorem represents it, and can I reproduce the proof myself?

with public, machine-checkable evidence.

That remains useful whether or not a prize is awarded.
