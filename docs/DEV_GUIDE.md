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
- update `pyproject.toml` and `uv.lock` together when an approved dependency change occurs;
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

The first scanner consumes only the managed, pinned JSP snapshot. Run it from the repository root with:

```bash
uv run python -m beejsp.scanner --output problem-bank.json --summary problem-bank.txt
```

It dynamically discovers `problems/catalog-*.md` under `docs/vendor/jsp/`; it does not query the network or use the vendor snapshot as live competition evidence. The canonical JSON contains the catalog paths, vendor provenance, one normalized record per detailed catalog entry, diagnostics and the derived `candidate_ids` set. Each record keeps raw official fields next to normalized status values. `candidate_ids` is the unranked deterministic filter for `Current status == Solved` and `Lean proof == No`.

If parsing or identity validation reports an error, `is_complete` is false and the scanner withholds `candidate_ids`. Iteration 3 can consume the JSON records and candidate IDs directly rather than reparsing JSP Markdown.

### Iteration 3 evidence-backed TOP-5

Iteration 3 consumes the saved scanner JSON, a deliberately reviewed research JSON file, and a separately captured GitHub JSON file. It never reparses the managed catalog Markdown. Capture current public competition data explicitly:

```bash
uv run python -m beejsp.assessment capture-github --output competition.json
```

This is a bounded read-only traversal of all PR and Issue pages in `TheJustinSunPrize/awards`. A failed, rate-limited, malformed, or incomplete capture is written as incomplete evidence and cannot produce a TOP-5.

Create research JSON with `schema_version: 1`, `reviewed_prefix_count`, and one item per deeply reviewed candidate. Candidates must be in exact deterministic triage-prefix order: the bounded prefix may continue beyond the initial review limit when necessary, but must never cherry-pick outside that prefix. Record explicit solution evidence (`complete`, `answer`, `sketch`, `partial`, `unsupported`, or `unknown`), formalization search scope, and a separate qualitative estimate with rationale. Each formalization observation requires a source, URL, `status`, `blocking`, and rationale; supported statuses are `complete`, `partial`, `scoped`, `activity`, and `unknown`. A `blocking: true` observation additionally requires an explicit blocker rationale. Do not present estimates as official facts or turn a scoped empty search into a global absence claim.

Then render the deterministic assessment offline:

```bash
uv run python -m beejsp.assessment assess \
  --scanner problem-bank.json \
  --research research.json \
  --competition competition.json \
  --output assessment.json \
  --report top5.md
```

The assessment validates scanner provenance and identities, triages the whole candidate set with its recorded formula and stable JSP-ID tie-breaker, and emits exactly one GO primary plus four reserves only when a viable primary exists. Otherwise it fails closed without a TOP-5. Its saved inputs, not a later network request, are the reproducibility boundary. The primary's bounded spike objective is an Iteration 4 input, not Lean code produced by this command.

### Iteration 6 selection and inspection

The Iteration 2 scanner still emits `schema_version: 1` with all normalized `records` and its historical `candidate_ids`. Iteration 3 `assess`, its research format, scoring and saved artifacts retain their original semantics. Use the new `select` and `inspect` commands for future discovery: their version 2 reports keep unresolved competing proofs visible and never issue mathematical GO. Selecting a row means it matches a screening profile; exact-source research and a bounded feasibility decision remain separate gates.

Capture enriched public competition and the official registers explicitly:

```bash
uv run python -m beejsp.assessment capture-github --evidence-version 2 --output competition-v2.json
uv run python -m beejsp.assessment capture-records --output official-records.json
```

`capture-github` defaults to version 1 for existing consumers. Version 2 adds per-endpoint completeness, observation timestamps, published creation/update/closure/merge timestamps, submission kind, Erdős IDs, bounded proof references and links to predecessor submissions. PRs and Issues remain separate, deduplicated lists; PR entries returned by the Issues API are skipped. Capture uses all states, up to 200 pages of 100 items per endpoint, 2 MB per response, 1024 characters per title, and 100,000 characters per body. Pagination must retain the original endpoint and query scope and advance exactly one page; cycles, conflicting duplicates, unexpected redirects, malformed responses and rate limits yield incomplete evidence and exit code 2. Raw bodies and authentication metadata are never retained. Source references are extracted from GitHub links and the official submission template's JSON proof-source blocks, with branch, full commit SHA, file and theorem when explicitly supplied. These references are claims, not build or verification evidence. Submission-kind classification is a screening hint derived from the captured text, not an official adjudication.

For an independent Issue capture, add `--kind issues`; for PRs use `--kind pull_requests`. These options require version 2. A successfully completed Issue-only capture does not establish absence of competing PRs. Saved partial captures remain inspectable, with competition uncertainty, instead of being converted to negative findings.

`capture-records` resolves `main` to one full commit and reads `candidates/README.md` and `awards/README.md` at that revision through the same fixed official GitHub API boundary. Its declared scope is those two documented register tables. Candidate solver/formalizer review periods are separate rows; announced awards are separate from submissions. Missing files or unsupported table layouts mark acquisition incomplete. Records retain recipients, role, review dates, canonical immutable source URL and acquisition timestamp. Current register tables do not publish levels or amounts, so those fields remain null. An inspected register is evidence of its own captured revision, not future live state or payment. No private identity or payout records are collected.

Select all valid normalized catalog records offline, including records outside the historical scanner candidate subset:

```bash
uv run python -m beejsp.assessment select \
  --scanner problem-bank.json --competition competition-v2.json \
  --awards official-records.json --profile general \
  --output selection.json --csv selection.csv
uv run python -m beejsp.assessment select \
  --scanner problem-bank.json --competition competition-v2.json \
  --research discovery-research.json --awards official-records.json \
  --profile high-value --output high-value.json --csv high-value.csv
uv run python -m beejsp.assessment inspect \
  --scanner problem-bank.json --competition competition-v2.json \
  --jsp JSP-000161 --output inspection.json --csv inspection.csv
```

Inspection optionally accepts `--research` and `--awards` too. Use `--kind issue --state open` to inspect all matching recorded open Issues independently; `--state closed`, `--kind pull_request`, `--state closed-unmerged` and `--state merged` are also supported. Filters affect displayed observations, while the problem's aggregate competition classification still considers the entire supplied evidence. Exact JSP identities take precedence over aliases and titles. A title match with no explicit identity is supplementary and uncertain; it cannot override a conflicting exact JSP ID. Inspection never initiates a fresh repository capture.

#### Profiles and ranking

The built-in `general` profile has no filters and selects up to 20 rows. `high-value` keeps high or unknown scientific significance and qualitative prize potential, also with a limit of 20. Unknown cases are deliberately retained for research. Both profiles rank by scientific significance (`high=6`, `medium=3`, `low=1`), qualitative prize potential (`high=3`, `medium=2`, `low=1`), and difficulty preference (`low=4`, `medium=3`, `high=2`, `extreme=1`). Unknown contributes no prioritization signal; it remains unknown in the report. The descending sum and ascending JSP ID determine order. Scores do not represent proof feasibility, dollars, payment probabilities or official award grades.

Pass a TOML path to `--profile` for custom filters. Only `schema_version`, `name`, `limit` and the documented filter keys are accepted. `schema_version = 2`, a nonempty name and an integer limit from 1 to 1000 are required. Every supplied filter is a nonempty list; omitted filters are unrestricted. This example selects solved records without recorded Lean proofs while retaining unresolved competition:

```toml
schema_version = 2
name = "focused-research"
limit = 10
problem_status = ["Solved"]
lean_status = ["No"]
area = ["Combinatorics"]
difficulty = ["low", "medium", "high", "extreme", "unknown"]
competition_state = ["CONTESTED", "REVIEWED", "NONE_IN_SCOPE", "UNKNOWN"]
solution_kind = ["complete", "unknown"]
scientific_significance = ["high", "unknown"]
prize_potential = ["high", "unknown"]
award_state = ["candidate", "announced", "none_in_scope", "unknown"]
published_amount = ["known", "unknown"]
historical_bounty = ["known", "unknown"]
award_level = ["unknown"]
```

`problem_status` supports `Solved`, `Open`, `Unknown`, `Missing`; `lean_status` supports `Yes`, `No`, `Unknown`, `Missing`. `area` matches the exact recorded mathematical-area field, using `unknown` when absent. Difficulty supports `low`, `medium`, `high`, `extreme`, `unknown`. Scientific significance and prize potential support `low`, `medium`, `high`, `unknown`. Solution kinds are `complete`, `answer`, `sketch`, `partial`, `unsupported`, `unknown`. Competition states are `CONTESTED`, `REVIEWED`, `VERIFIED`, `NONE_IN_SCOPE`, `UNKNOWN`. Award-level filters match exact published labels; absent levels use `unknown`. Known/unknown monetary and bounty filters operate separately; a historical bounty never populates an official amount.

#### Research and proof-review contract

Selection research uses `schema_version: 2` and a `candidates` list keyed by exact catalog JSP IDs. It is a separate contract from Iteration 3 research; the two formats are not silently interchangeable. Missing research remains unknown. Each candidate may have `difficulty`, `scientific_significance` and `prize_potential` objects with `value`. Any known value also requires a public HTTPS `url`, timezone-aware ISO `observed_at`, and nonempty `rationale`. These are non-official research estimates. For example:

```json
{
  "schema_version": 2,
  "candidates": [{
    "jsp_id": "JSP-000161",
    "difficulty": {"value": "unknown"},
    "scientific_significance": {"value": "unknown"},
    "prize_potential": {"value": "unknown"},
    "solution": {"kind": "unknown", "sources": []},
    "aliases": [],
    "proof_reviews": []
  }]
}
```

`solution` contains `kind` and `sources`; every source has `url`, `observed_at` and `rationale`. A known solution kind requires at least one source. `aliases` contains evidence objects with an additional `erdos_id` decimal string. A reviewed alias must explicitly link the original problem to its JSP identity; a filename or guessed title alone is insufficient. Aliases assigned to two JSP IDs are rejected as ambiguous. Captured Erdős references only become authoritative matches through these supplied identity-review records.

`proof_reviews` contains externally supplied reviewed evidence, not automatic certification. Each review requires `subject_url`, `state`, `url`, `observed_at` and `rationale`. The subject is a captured submission URL or proof-source URL. Supported states are `claimed`, `source_linked`, `partial`, `invalid`, `reproduced`, `independently_verified`, `unresolved`. Reviews without a matching submission remain visible as external-source research. Optional `proof_source` contains `url`, `repository` as `owner/repo`, nullable `branch`, full `commit`, relative `file` and `theorem`. Blob URLs must agree with any declared commit, branch and file. No referenced repository is downloaded or executed.

Build findings (`passed`, `failed`, `environmental_failure`, `unknown`), statement fidelity (`exact`, `weaker`, `unknown`), axiom audit (`passed`, `unexpected`, `unknown`) and placeholders (`absent`, `present`, `unknown`) are independent fields named `build`, `statement_fidelity`, `axiom_audit`, `placeholders`. `reproduced` requires a pinned full commit, proof file, a passed build and a `build_evidence` object with URL, observation timestamp and rationale. `independently_verified` additionally requires an independent `reviewer`, exact statement fidelity, a passed axiom audit, absent placeholders, and separate `statement_evidence` and `axiom_evidence` objects. A build result alone cannot satisfy this gate. Partial or invalid reviews require linked review rationale; closure of a PR and environmental build failures do not establish invalidity. An `invalid` review with an environmental build failure must also report a weaker statement, unexpected axioms or present placeholders; otherwise the contradictory classification is rejected. Supplied review records remain attributed evidence claims and require human review of their linked sources.

For source-linked submissions, a partial, invalid, reproduced or independently verified review applies only when the captured and reviewed repository, full commit and file agree, and any captured theorem identity also agrees. Matching a mutable repository or submission URL alone is insufficient. Reviews of different or unpinned sources remain visible separately and do not clear the captured claim.

Unresolved material PR claims, including closed-unmerged submissions and reproduced proofs without independent statement review, yield `CONTESTED`. Explicit Lean claims in Issues also yield `CONTESTED`. Partial and invalid reviewed work remains visible as `REVIEWED`; an independently verified exact proof yields `VERIFIED`, which signals originality risk without deciding official priority. Supplementary title activity and unclassified Issues retain `UNKNOWN`. Only a complete capture with no unresolved relevant activity can produce `NONE_IN_SCOPE`, which is limited to that captured repository scope. Incomplete acquisition is always reported separately, including when a positive competing observation was retained. Every selected row has `decision: REVIEW_REQUIRED`.

Official record evidence uses `schema_version: 2`, an `acquisition` object (`repository`, `observed_at`, `complete`, `search_scope`, `upstream_commit`), and `records`. Records contain `jsp_id`, `state` (`candidate` or `announced`), `role` (`solver` or `formalizer`), `recipients`, `review_start`, `review_end`, `url`, `observed_at`, `upstream_commit`, `official_award_level`, `published_amount` and `currency`. Sources must identify the appropriate official register directory at the captured commit. A researcher may enrich saved records with an explicitly published level or decimal-string amount only when a `publication_evidence` object links official public evidence with timestamp and rationale. Known amounts require a three-letter currency; missing amounts and currencies remain null. This enrichment records observed publications and cannot calculate future awards. Neither registration nor announcement is payment evidence. The report's `official_acceptance: recorded` indicates a formalizer entry in one of these registers, separate from independently verified proof state.

#### Output and security boundary

JSON reports have `schema_version: 2`, the resolved profile, scanner provenance, competition acquisition/completeness, award acquisition, and fully explained `selected` and `excluded` rows. Inspection has a `query` and one `problem` instead. Rows expose raw official fields, source provenance, known/unknown filter values, research rationale, matching submissions, proof reviews, separate bounty/award/amount fields, score components, stable rank, inclusion/exclusion reasons and uncertainty. Result limits produce explicit exclusion reasons. JSON key ordering, row ordering and CSV columns are deterministic for identical saved inputs. CSV includes selected and excluded rows; nested evidence is canonical JSON and unknown values are `null`. Scalar spreadsheet formula prefixes are escaped with an apostrophe.

Offline commands accept existing version 1 competition captures without rewriting their historical assessment semantics. For new selection and inspection, version 1 does not certify per-problem coverage: even `acquisition.complete: true` can describe complete API acquisition followed by retention of only a bounded candidate subset. Positive observations remain visible, including `CONTESTED` claims, but absence of observations yields `UNKNOWN` with explicit coverage uncertainty and `competition_complete: false`. The original acquisition metadata is preserved; arbitrary `search_scope` prose is never parsed as a completeness certificate. Only version 2 evidence with complete acquisition and both structured endpoint scopes complete can support `NONE_IN_SCOPE` when no relevant unresolved activity is recorded. Files larger than 32 MB are rejected; invalid schemas, identities, timestamps, URLs, duplicate conflicting evidence and colliding input/output paths fail before report writes. Empty selections are valid explained results. Capture alone uses public GET requests to the fixed official API; credentials, GitHub writes, external proof execution and dependency additions are absent. Managed vendor files and Lean projects remain unchanged.

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
