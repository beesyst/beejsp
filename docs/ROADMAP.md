# ROADMAP — BeeJSP

## Purpose

This document defines the development path for `beejsp` through explicit project stages and substantial implementation iterations.

BeeJSP uses the ROADMAP as a lightweight delivery artifact to:

- define project direction;
- keep work focused on useful mathematical output;
- define the acceptance boundary of each substantial iteration;
- connect Issue → Code / Proof → Verification → PR → Merge;
- separate discovery tooling from mathematical proof;
- preserve exact mathematical statement fidelity;
- preserve reproducible Lean verification;
- preserve solver, formalizer and verifier attribution;
- keep official JSP reference material reproducible without turning it into a
  second source of truth;
- prevent speculative platform development before the first useful proof is
  delivered.

The ROADMAP does not replace Issues or Pull Requests:

- **Issue** defines the exact approved implementation task;
- **PR** records what was actually implemented and verified;
- **ROADMAP** defines the iteration-level project contract and delivery
  direction.

A significant roadmap iteration is normally delivered through a BeeJSP PR.

Small low-risk maintenance that does not change project behavior, formalization semantics, managed vendor behavior, dependencies, security boundaries or public contracts does not become a roadmap iteration merely to create another numbered item.

The ROADMAP does not duplicate full repository rules:

- project architecture and ownership belong in `docs/ARCHITECTURE.md`;
- development instructions belong in `docs/DEV_GUIDE.md`;
- mathematical and Lean formalization rules belong in
  `docs/FORMALIZATION.md`;
- security and trust boundaries belong in `docs/SECURITY.md`;
- official JSP submission workflow belongs in `docs/SUBMISSION.md`;
- repository-level AI/development instructions belong in `AGENTS.md`.

## Vision

| Block                         | Statement                                                                                                                                                                                           |
| ----------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Project identity**          | BeeJSP is an open-source project for helping the mathematical community discover suitable problems, formalize valid mathematical results in Lean and publish reproducible machine-checked evidence. |
| **Primary objective**         | Produce useful, independently reproducible formal mathematics rather than merely generate candidate proofs.                                                                                         |
| **Core question**             | Can this mathematical result be represented faithfully, proved completely in Lean and independently reproduced from public evidence?                                                                |
| **Community principle**       | Mathematical usefulness and correct attribution come before prize optimization.                                                                                                                     |
| **Formalization principle**   | A Lean proof is useful only when the formal statement faithfully represents the intended mathematical result.                                                                                       |
| **Proof principle**           | Successful compilation is necessary evidence, not sufficient evidence of statement fidelity.                                                                                                        |
| **Reproducibility principle** | A selected public source revision should contain everything required to reproduce the claimed proof using its pinned environment.                                                                   |
| **Attribution principle**     | Problem author, mathematical solver, Lean formalizer and independent verifier are distinct roles and must not be conflated.                                                                         |
| **AI principle**              | AI may assist research, implementation and review, but mathematical claims remain grounded in source evidence and machine-checked proof.                                                            |
| **Discovery principle**       | Candidate ranking helps choose work; it does not establish mathematical truth or official prize status.                                                                                             |
| **Vendor principle**          | `docs/vendor/jsp/` is a pinned generated reference snapshot, not a manually maintained authority.                                                                                                   |
| **Competition principle**     | Current PR/Issue/formalization competition is live external state and must be checked separately from the vendor snapshot.                                                                          |
| **Submission principle**      | BeeJSP remains the original proof repository; the official JSP repository is an external contribution target.                                                                                       |
| **KISS principle**            | Build only the tooling required to select, formalize, verify and submit real mathematical work.                                                                                                     |
| **Project principle**         | BeeJSP is not primarily a generic theorem generator, SaaS platform, research-agent framework or prize-farming bot.                                                                                  |

## Project thesis

BeeJSP does not primarily answer:

> Can an AI produce Lean code for this problem?

That is too weak.

BeeJSP answers:

> Can we identify a worthwhile mathematical result, represent the exact result
> faithfully in Lean, prove it completely, independently reproduce it and make
> the evidence useful to the mathematical community?

Target flow:

```text
mathematical problem bank
→ source/status research
→ evidence-based candidate screening
→ TOP candidate selection
→ exact mathematical statement
→ bounded Lean feasibility spike
→ complete Lean formalization
→ independent verification
→ public immutable proof evidence
→ optional official JSP submission
```

Core project principle:

> Formalization is not code generation.
> It is preservation of mathematical meaning under machine verification.

The Justin Sun Prize is an important initial problem source and supported submission path.

BeeJSP must remain useful even when:

- a selected problem has no prize;
- another formalizer submits first;
- an official claim is unsuccessful;
- a useful proof is produced outside the JSP program.

## Architecture boundary

The intended ownership model is:

```text
Official mathematical sources
→ problem and solution evidence

TheJustinSunPrize/awards
→ official JSP records and process

docs/vendor/jsp/
→ pinned read-only local JSP reference

BeeJSP Python tooling
→ ingestion
→ normalization
→ discovery
→ candidate analysis
→ competition analysis
→ deterministic reports

BeeJSP Lean projects
→ exact statements
→ complete proofs
→ reproducible verification

BeeJSP public Git history
→ immutable proof provenance

Official JSP contribution
→ external submission / verification / claim process
```

Architecture invariants:

```text
vendor snapshot
!=
official authority
```

```text
candidate score
!=
mathematical truth
```

```text
lake build success
!=
statement fidelity
```

```text
formalization
!=
mathematical discovery authorship
```

```text
official PR opened
!=
official verification or award
```

## Repository ownership

BeeJSP owns:

```text
Python discovery/scanning tooling
problem-bank normalization
candidate prioritization
read-only competition analysis
managed JSP reference synchronization
Lean proof projects
proof reproducibility metadata
formalization verification evidence
project documentation
submission preparation
```

BeeJSP does not own official JSP:

```text
problem status
award eligibility
candidate status
formal verification status
priority decision
award decision
claim approval
payment status
```

Those remain external official state.

## Managed JSP reference rule

Canonical managed reference:

```text
docs/vendor/jsp/
```

Canonical update command:

```text
scripts/sync_jsp_docs.sh
```

Remote source:

```text
https://github.com/TheJustinSunPrize/awards
```

Every accepted snapshot records:

```text
UPSTREAM_REF
UPSTREAM_COMMIT
```

Correct flow:

```text
official upstream
→ exact upstream revision
→ temporary staging
→ validation
→ managed snapshot replacement
→ recorded provenance
```

Do not manually maintain vendored JSP files.

The snapshot is used for:

- planning;
- scanner input;
- local problem-bank inspection;
- formalization guidance;
- submission guidance.

It is not sufficient evidence of current:

- open PRs;
- merged PRs;
- active Issues;
- competing external formalizations.

## Formalization invariants

The following rules apply to all real BeeJSP proof work.

### Exact problem identity

Every formalization must identify the exact mathematical problem being claimed.

### Statement fidelity

The Lean statement must preserve the required:

- domain;
- quantifiers;
- hypotheses;
- conclusion;
- cases;
- boundary assumptions;
- mathematical meaning.

A materially weaker theorem is not completion evidence for the original problem.

### No hidden stronger assumptions

Implementation convenience must not silently introduce assumptions absent from the original mathematics.

### Complete proof

Completed proof evidence must not depend on:

```text
sorry
admit
```

or a custom unproved axiom inserted to replace missing mathematics.

### Reproducible environment

The proof must pin the Lean environment and dependencies necessary to reproduce the result.

### Axiom review

The principal theorem must receive the applicable axiom audit.

### Attribution

Keep distinct:

```text
problem source / author
mathematical solver
Lean formalizer
independent verifier
```

### Conservative claims

Do not upgrade:

```text
build succeeded
```

to:

```text
original mathematical problem fully formalized
```

until statement fidelity and complete scope are independently reviewed.

## Security invariants

### External data is untrusted

Treat:

- upstream repositories;
- GitHub responses;
- mathematical documents;
- third-party Lean code;
- external dependencies;

as external input.

### No hidden execution

External source material must not silently become arbitrary local execution.

### Managed path safety

Vendor synchronization must remain bounded to its approved staging and destination paths.

### Minimal GitHub authority

Read-only research does not justify write permissions.

GitHub write automation requires explicit approved scope.

### Private data

Do not commit:

- credentials;
- access tokens;
- private keys;
- seed phrases;
- KYC documents;
- private payment information;
- unnecessary private identity data.

### Provenance integrity

Do not claim a repository revision contains proof evidence without verifying that exact source state.

## Development principles

BeeJSP uses small but substantial project iterations.

Every significant roadmap iteration must:

- have a concrete mathematical, tooling or verification goal;
- produce a meaningful code, proof or evidence increment;
- remain inside declared scope;
- avoid speculative infrastructure;
- preserve source-of-truth boundaries;
- preserve formalization fidelity;
- preserve reproducibility;
- preserve attribution;
- use verification proportional to actual risk;
- keep external writes separate from local evidence production.

For BeeJSP:

```text
candidate
!=
proof
```

```text
proof text
!=
verified proof
```

```text
compiled theorem
!=
verified source equivalence
```

```text
official catalog metadata
!=
current mathematical consensus
```

```text
vendor snapshot
!=
live competition state
```

## Iteration significance rule

A numbered iteration must produce at least one substantial increment such as:

- a stable problem-bank ingestion contract;
- a useful candidate-screening capability;
- a live competition-analysis capability;
- an evidence-backed TOP candidate decision;
- a bounded Lean feasibility result;
- a complete real formalization;
- independent proof-verification evidence;
- a public immutable proof package;
- an official external submission artifact;
- a material formalization/security hardening increment.

The following do **not** justify a standalone roadmap iteration by themselves:

- wording changes;
- formatting;
- README cleanup;
- one small helper;
- one extra test with no contract increment;
- speculative abstraction;
- generic infrastructure for future proofs;
- another wrapper around existing tooling.

If two planned iterations produce one inseparable project capability, merge them.

## KISS roadmap rule

Do not add roadmap iterations merely because the following may eventually be useful:

```text
web dashboard
database
hosted SaaS
generic theorem-prover abstraction
generic agent framework
multi-competition platform
generic plugin system
hosted proof runner fleet
automatic prize claiming
social/reputation system
large knowledge graph
```

A new scope item is justified only when at least one condition holds:

1. it is necessary to complete useful mathematical work;
2. a current iteration cannot be completed correctly without it;
3. real proof work exposes a concrete reusable gap;
4. verification or submission evidence exposes a concrete deficiency;
5. multiple real proofs demonstrate a stable reusable need.

Insufficient reasons include:

```text
"might be useful later"
"makes the architecture cleaner"
"a mature platform would have it"
"we should support every proof system now"
"we may enter other competitions later"
```

## Delivery workflow for roadmap items

A significant BeeJSP iteration follows this flow:

1. **Planning**
   - inspect current repository state;
   - confirm the actual gap;
   - confirm iteration necessity;
   - confirm source of truth;
   - reject speculative scope.

2. **Requirements**
   - define Goal;
   - define Scope;
   - define Excluded;
   - define Deliverable;
   - define Acceptance criteria;
   - define contract impact;
   - define dependency impact;
   - define formalization impact;
   - define security impact;
   - define Checks;
   - define DoD.

3. **Issue**
   - create one focused BeeJSP Issue.

4. **Implementation**
   - implement the smallest complete solution on a dedicated branch.

5. **Independent verification**
   - verify actual implementation or proof independently;
   - correct only demonstrated in-scope blockers.

6. **Final read-only review**
   - compare actual target worktree with approved Issue and current contracts.

7. **PR / merge**
   - record actual implementation and evidence;
   - merge only after Acceptance Criteria are satisfied.

8. **External submission**
   - only when the iteration explicitly requires it and local evidence is
     already complete.

Tiny low-risk repository maintenance may use a shorter path and does not require a roadmap iteration.

## Status values

Allowed roadmap iteration statuses:

- **PLANNED** — scope is approved, implementation has not started;
- **IN PROGRESS** — active implementation is underway;
- **DONE** — iteration contract is fully delivered;
- **DONE (partial)** — intentionally closed with explicit limitations.

For later directions:

- **FUTURE / orientation** — known direction, not approved implementation scope.

`FUTURE / orientation` does not pre-authorize architecture or implementation.

## Roadmap item format

Iterations use:

- `Goal`
- `Scope`
- `Excluded`
- `Deliverable`
- `Acceptance criteria`
- `Checks`
- `DoD`

The ROADMAP defines iteration-level contracts.

Detailed:

- schemas;
- algorithms;
- theorem statements;
- exact file lists;
- test matrices;
- command evidence;
- reviewer findings;

belong in Issues, implementation, tests and PRs.

## Global Definition of Done

A significant BeeJSP iteration is complete only when:

- declared scope is implemented;
- excluded scope was not silently introduced;
- source-of-truth boundaries remain correct;
- managed vendor content is not manually maintained;
- Python behavior is deterministic where the contract requires it;
- formalization-sensitive changes preserve mathematical scope;
- no completed proof relies on `sorry` or `admit`;
- no custom placeholder axiom substitutes for missing mathematics;
- applicable Lean environment is reproducible;
- applicable axiom audit is complete;
- provenance and attribution remain accurate;
- targeted checks pass;
- full Python checks pass when applicable;
- package build passes when package behavior changes;
- Lean build passes when proof code changes;
- security checks proportional to the change are complete;
- no secrets or private KYC/payment material enter repository state;
- documentation matches actual behavior;
- significant delivery is recorded in PR;
- no unrelated architecture or cleanup is mixed into the iteration.

## Change levels for verification

BeeJSP uses three ordinary change levels.

### low-risk

Changes without meaningful executable/security behavior impact.

Examples:

- documentation;
- agent prompt/skill maintenance;
- wording;
- metadata;
- narrow test-only changes.

Usually required:

- relevant targeted checks;
- consistency review.

### runtime-risk

Changes affecting executable project/tooling behavior without introducing a critical trust/write boundary.

Examples:

- catalog parser;
- normalization;
- scanner;
- filtering/scoring;
- report generation;
- vendor synchronization;
- CI behavior;
- package/public behavior;
- external read-only API integration.

Usually required:

- targeted tests;
- `uv run pytest -q`;
- Ruff checks;
- package build/import checks when applicable;
- deterministic-output checks;
- vendor provenance/idempotence checks where applicable.

### security-sensitive

Changes affecting trust, filesystem, execution, credentials or external write boundaries.

Examples:

- shell construction from external values;
- path handling;
- archive extraction;
- execution of external code;
- GitHub write automation;
- credentials;
- private identity/payment processing;
- material dependency expansion.

Usually required:

- applicable runtime-risk checks;
- explicit security review;
- SAST;
- SCA when dependency surface changes;
- relevant negative/adversarial tests.

DAST, IAST and fuzzing are used only when the actual change creates a meaningful corresponding surface.

## Formalization-sensitive verification

Formalization sensitivity is orthogonal to the normal change level.

A change is formalization-sensitive when it affects:

- Lean statement;
- proof;
- theorem scope;
- mathematical assumptions;
- proof dependencies;
- toolchain;
- proof provenance;
- formalizer attribution;
- axiom evidence;
- submission proof evidence.

Applicable checks include:

```text
exact statement review
full-scope review
lake build
sorry/admit audit
placeholder-axiom review
axiom audit
dependency/toolchain review
clean reproduction
source/provenance review
attribution review
```

Successful compilation alone does not close a formalization-sensitive iteration.

## Versioning and release rule

BeeJSP tooling uses SemVer.

Version source of truth:

```text
pyproject.toml
```

Roadmap iteration and release version are different concepts.

Ordinary feature/fix/proof work must not manually bump the package version unless the task is explicitly release-related.

Release automation owns:

```text
release PR
version
CHANGELOG
tag/release lifecycle
```

A specific formalization is identified by its proof provenance, not by the BeeJSP package version.

For submission-sensitive work, relevant immutable evidence may include:

```text
repository
branch when required
full selected commit SHA
proof project
principal theorem
```

Conventional Commits should be used.

Recommended release impact:

| Commit          | Release impact                         |
| --------------- | -------------------------------------- |
| `feat:`         | MINOR                                  |
| `fix:`          | PATCH                                  |
| `docs:`         | normally no release bump by itself     |
| `test:`         | normally no release bump by itself     |
| `refactor:`     | normally no release bump by itself     |
| `chore:`        | normally no release bump by itself     |
| `ci:`           | normally no release bump by itself     |
| `build:`        | normally no release bump by itself     |
| breaking change | MAJOR when SemVer maturity requires it |

Release mechanics must not become a blocker for mathematical work.

## Project phases

| Phase                                                 | Status      | What it means                                                                                                                                              |
| ----------------------------------------------------- | ----------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Phase A — Foundation and official reference**       | IN PROGRESS | BeeJSP becomes a governed Python + Lean repository with reproducible managed JSP reference material.                                                       |
| **Phase B — Discovery and candidate selection**       | PLANNED     | BeeJSP can inspect the current problem bank, identify realistic formalization candidates and produce an evidence-backed TOP shortlist.                     |
| **Phase C — First real formalization**                | PLANNED     | One selected mathematical problem progresses from exact source statement through bounded feasibility work to a complete Lean proof.                        |
| **Phase D — Independent verification and submission** | PLANNED     | The completed proof is independently checked, frozen as public immutable evidence and submitted through the current official JSP process when appropriate. |

### Stages

- **Stage 1 — Foundation and official reference:** repository architecture,
  governance, Python/Lean foundations, CI and managed official JSP snapshot.
- **Stage 2 — Discovery and candidate selection:** deterministic problem-bank
  ingestion, filtering, live competition analysis and evidence-backed TOP
  candidates.
- **Stage 3 — First real formalization:** exact source package, Lean feasibility
  spike and complete formal proof.
- **Stage 4 — Independent verification and submission:** independent proof
  verification, immutable public evidence and external contribution.

## Project gates

These are decision gates, not additional iterations.

### Gate 1 — Foundation integrity

After Iteration 1:

```text
official JSP upstream
→ managed reproducible snapshot
→ BeeJSP local reference
```

must work without:

- permanent upstream fork dependency;
- manual vendor editing;
- speculative runtime architecture;
- missing provenance.

If this does not work, do not build scanner logic over an unstable source.

### Gate 2 — Candidate quality

After Iteration 3, BeeJSP must be able to produce a defensible shortlist where each leading candidate has evidence for:

```text
exact problem
current official record
known mathematical solution/source
Lean status
live competition status
formalization complexity
main risks
```

If the shortlist is based only on catalog labels or intuition, do not start a large proof.

### Gate 3 — Formalization feasibility

After Iteration 4, the selected candidate must have a clear:

```text
GO
```

or:

```text
NO-GO
```

for full formalization.

If the hardest mathematical/Lean boundary has not been tested, do not expand into a long implementation blindly.

### Gate 4 — Proof truth

After Iteration 6:

```text
exact source problem
→ exact Lean statement
→ complete proof
→ reproducible build
→ acceptable axiom audit
→ independent statement review
```

must hold.

If not, do not submit externally.

---

## Stage 1 — Foundation and official reference

### Purpose of stage

Stage 1 establishes BeeJSP as a small governed Python + Lean repository before candidate tooling or real mathematical formalization begins.

The stage proves:

```text
BeeJSP
→ standalone repository
→ Python tooling foundation
→ Lean project foundation
→ managed official JSP reference
→ agent/review workflow
```

without creating:

```text
web runtime
database
permanent JSP fork dependency
generic theorem framework
submission bot
```

### Iteration 1 — Repository foundation and managed JSP reference

**Status:** DONE

#### Goal

Bootstrap BeeJSP as an independent open-source Python + Lean repository with a safe managed snapshot of the official Justin Sun Prize reference material and the minimum governance required for real formalization work.

#### Scope

Included:

- standalone `beejsp` repository;
- Python distribution/import package `beejsp`;
- Python `>=3.14`;
- `uv`;
- standard `src` layout;
- byte-empty first-party package initializer;
- Lean smoke/template project;
- `AGENTS.md`;
- BeeJSP planning, implementation, verification and final-review skills;
- GitHub Issue/PR templates;
- CI baseline;
- SemVer/release-please baseline;
- architecture/development/formalization/security/submission documentation;
- `scripts/sync_jsp_docs.sh`;
- managed `docs/vendor/jsp/`;
- exact upstream ref and full commit provenance;
- safe staged vendor replacement;
- vendor idempotence;
- scheduled/manual vendor synchronization PR workflow.

#### Excluded

- real JSP formalization;
- candidate scanner;
- candidate ranking;
- live competition crawler;
- database;
- web UI;
- application runtime;
- `start.sh`;
- runtime configuration framework;
- permanent local dependency on an official JSP fork;
- external submission PR;
- claim automation.

#### Deliverable

A governed standalone BeeJSP repository that can reproducibly consume selected official JSP reference material and build a minimal Lean project.

#### Acceptance criteria

- repository identity is `beejsp`;
- Python package uses the standard `src` layout;
- `src/beejsp/__init__.py` is byte-empty;
- Python import has no hidden I/O or network side effects;
- Lean template builds with its pinned toolchain;
- canonical agent pipeline is:
  `planning → implementation → verify/correct → final review`;
- no separate submission/formalization agent pipeline exists;
- vendor source is the configured official JSP upstream;
- vendor snapshot records `UPSTREAM_REF`;
- vendor snapshot records a full resolved `UPSTREAM_COMMIT`;
- required official reference files are materialized;
- vendored files are read-only/generated;
- incomplete synchronization fails before an invalid snapshot is accepted;
- synchronization removes stale managed content;
- repeated synchronization to the same upstream revision is idempotent;
- scheduled/manual GitHub workflow creates a reviewable sync branch/PR rather
  than directly modifying `main`;
- no private credentials or identity/payment data are committed;
- no speculative runtime/service architecture is introduced.

#### Checks

```text
uv sync
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
uv build when package verification is required
package import smoke
Lean template lake build
vendor synchronization
vendor metadata validation
vendor required-file validation
second-run vendor idempotence
git diff --check
security review
SAST for sync/shell code
SCA only when dependency surface changes
```

#### DoD

BeeJSP has a minimal governed Python + Lean foundation and a reproducible managed JSP reference snapshot suitable for discovery and formalization planning.

---

## Stage 2 — Discovery and candidate selection

### Purpose of stage

Stage 2 prevents BeeJSP from spending substantial formalization effort on the wrong problem.

It must establish:

```text
current problem bank
→ normalized facts
→ viable formalization candidates
→ live competition evidence
→ evidence-backed TOP shortlist
→ one selected candidate
```

Candidate analysis is prioritization.

It is not proof.

### Iteration 2 — Problem-bank ingestion and deterministic candidate scanner

**Status:** DONE

#### Goal

Turn the managed JSP problem bank into a deterministic local representation that can identify formalization candidates without manually scanning every catalog entry.

#### Scope

Included:

- parse the current vendored JSP problem-bank files;
- discover catalog files from the managed snapshot rather than hardcoding their
  count;
- normalize one record per JSP problem;
- preserve source catalog/provenance information;
- normalize relevant official fields such as:
  - JSP ID;
  - title;
  - current problem status;
  - Lean-proof status;
  - current eligibility/claim metadata when present;
  - source/reference information when present;

- explicitly represent missing/unknown values;
- deterministic filtering;
- initial useful candidate filter such as solved problems lacking a recorded
  Lean proof;
- machine-readable scanner output;
- concise human-readable summary;
- malformed/duplicate record handling;
- deterministic tests against pinned vendor fixtures/snapshot content.

#### Excluded

- mathematical proof validation;
- source-paper proof checking;
- LLM-only ranking;
- live GitHub PR/Issue scanning;
- external repository search;
- database;
- web UI;
- automatic formalization;
- award prediction.

#### Deliverable

A deterministic scanner that transforms the current managed JSP problem bank into validated normalized candidate data and can produce an initial formalization-candidate set.

#### Acceptance criteria

- all discovered current catalog records can be parsed or explicitly reported as
  invalid;
- JSP IDs are unique;
- normalized records retain source provenance;
- missing values are not silently invented;
- official values and derived values remain distinguishable;
- scanner does not hardcode the current total problem count;
- current solved/no-Lean-style candidates can be selected deterministically;
- identical pinned input produces identical normalized output;
- malformed records fail or degrade explicitly according to the approved
  contract;
- no live GitHub state is inferred from vendor data;
- no database is required;
- vendor content remains unmodified.

#### Checks

```text
catalog discovery
complete pinned-snapshot parse
duplicate-ID test
malformed-record tests
missing-field tests
normalization tests
deterministic serialization/output
candidate-filter tests
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
uv build when package/public behavior is affected
package import smoke when applicable
git diff --check
```

#### DoD

BeeJSP can inspect the current JSP problem bank programmatically and produce a deterministic candidate set without manual catalog-by-catalog scanning.

### Iteration 3 — Evidence-backed TOP-5 and live competition analysis

**Status:** DONE

#### Goal

Select five realistic formalization candidates using current mathematical, formalization and competition evidence rather than catalog labels alone.

#### Scope

Included:

- consume normalized candidate data from Iteration 2;
- define a compact explainable candidate-assessment model;
- evaluate source mathematical solution availability;
- record solution date/source where material;
- distinguish complete proof from answer/sketch/claim;
- evaluate expected Lean/Mathlib difficulty;
- identify finite/counterexample/constructive structure when relevant;
- perform read-only current GitHub competition checks;
- check official PRs/Issues for exact JSP IDs and relevant titles;
- record current external formalization evidence when found;
- timestamp live-state observations;
- separate deterministic facts from qualitative engineering estimates;
- produce evidence-backed TOP-5;
- identify primary, reserve and rejected candidates;
- document explicit GO/NO-GO reasons;
- recommend exactly one candidate for the first bounded Lean spike.

#### Excluded

- full Lean proof;
- mathematical claim that a catalog status equals community consensus;
- automatic award prediction;
- write access to official GitHub repositories;
- opening official PRs;
- generalized research crawler;
- broad academic search platform;
- database.

#### Deliverable

A reviewable TOP-5 candidate report with current evidence and one selected candidate for the first formalization spike.

#### Acceptance criteria

For every TOP-5 candidate, the report identifies as applicable:

- exact JSP ID;
- exact current problem record;
- problem status;
- recorded Lean status;
- mathematical solution source;
- evidence that a complete solution is available or explicit uncertainty;
- current live official competition evidence;
- known external formalization evidence;
- estimated formalization complexity;
- relevant Mathlib/domain risk;
- statement ambiguity risk;
- provenance/date risk;
- submission/process risk;
- reason for inclusion.

The selected primary candidate additionally has:

- no known blocker that already makes the work pointless;
- enough mathematical source material to attempt formalization;
- an explicit reason it is preferable to the four alternatives;
- a bounded spike objective for Iteration 4.

The report must not:

- claim absence of competitors beyond searched evidence;
- equate official catalog `Solved` with universal mathematical consensus;
- equate `Lean proof: No` with proof that no current formalization exists;
- invent prize value or award certainty;
- hide qualitative judgment inside deterministic fields.

#### Checks

```text
normalized-input validation
live GitHub query tests/mocks where implemented
read-only permission review
exact JSP-ID matching
duplicate/collision tests
timestamp/provenance checks
TOP-5 report reproducibility for pinned inputs
manual evidence review
security review for external reads
SCA only if dependencies change
git diff --check
```

#### DoD

BeeJSP has five defensible candidates and one selected first formalization target based on mathematical, Lean and current competition evidence rather than intuition alone.

---

## Stage 3 — First real formalization

### Purpose of stage

Stage 3 converts one selected mathematical result into a real machine-checked formalization.

It deliberately separates:

```text
feasibility
```

from:

```text
complete formalization
```

so difficult mathematics or missing library support can produce an early NO-GO instead of consuming an open-ended implementation effort.

### Iteration 4 — Selected candidate statement package and bounded Lean spike

**Status:** PLANNED

#### Goal

Establish the exact formalization contract for the selected candidate and test the hardest known Lean feasibility boundary before committing to the full proof.

#### Scope

Included:

- one exact selected JSP candidate from Iteration 3;
- fresh review of the target JSP record;
- fresh relevant competition check;
- authoritative/relevant problem-source collection;
- complete mathematical solution-source review;
- solver attribution;
- exact mathematical statement analysis;
- explicit Lean representation of the target statement;
- initial proof project under `proofs/JSP-XXXXXX/`;
- pinned Lean toolchain;
- minimum required pinned dependencies;
- Mathlib theorem/definition discovery;
- bounded implementation of the hardest representative proof boundary;
- compile/build evidence for the spike;
- statement-fidelity review;
- documented formalization risks;
- explicit final `GO` or `NO-GO`.

Possible spike forms include:

- exact explicit counterexample/witness verification;
- hardest central lemma;
- difficult source-definition encoding;
- finite-computation boundary;
- specialized Mathlib dependency proof;
- theorem statement elaboration with required definitions.

#### Excluded

- obligation to complete the entire formalization;
- changing the selected theorem to an easier materially weaker theorem;
- official external submission;
- claim of proof completion;
- broad reusable formalization framework;
- generic Lean utilities without demonstrated reuse;
- new candidate scanner architecture.

#### Deliverable

A bounded, reproducible Lean project that proves the selected problem is either practical enough to continue or has a concrete current blocking reason.

#### Acceptance criteria

- exact problem source is identified;
- current relevant JSP record is identified;
- complete mathematical solution source is identified or the missing source is
  itself the explicit blocker;
- mathematical solver attribution is recorded;
- intended top-level Lean statement is explicit;
- domains, quantifiers, hypotheses and conclusion are reviewed;
- no material weakening of the source problem is hidden in the statement;
- no unapproved stronger assumption is introduced;
- Lean toolchain is pinned;
- required dependencies are pinned;
- the selected hard boundary is attempted directly rather than replaced by
  unrelated easy scaffolding;
- spike code builds for the proved portion;
- temporary incomplete work is clearly distinguished from completed proof;
- any `sorry`/temporary placeholder used during exploration is not represented
  as completed proof evidence;
- final report states exactly `GO` or `NO-GO`;
- `GO` identifies remaining proof work;
- `NO-GO` identifies the concrete blocker and whether Iteration 3 should select
  a reserve candidate.

#### Checks

```text
source/problem identity review
statement-fidelity review
Lean project reproducibility
lake build
dependency/toolchain inspection
hard-boundary proof evidence
placeholder inventory
competition refresh
provenance/attribution review
git diff --check
```

#### DoD

BeeJSP has an evidence-based formalization decision for one real candidate.

A `NO-GO` is a valid successful iteration outcome when the blocker is real and well evidenced.

### Iteration 5 — Complete Lean formalization

**Status:** PLANNED

#### Goal

Complete the full Lean formalization of the candidate approved by Iteration 4 without weakening the mathematical claim or bypassing missing mathematics.

#### Scope

Included:

- complete target theorem;
- required local definitions;
- required supporting lemmas;
- Mathlib reuse;
- full proof implementation;
- pinned Lean environment;
- committed dependency state;
- proof-project README;
- mathematical source references;
- source-proof-to-Lean mapping where useful;
- solver/formalizer attribution;
- successful complete build;
- removal of exploratory placeholders;
- preliminary axiom inspection;
- targeted proof regression checks.

#### Excluded

- official JSP PR;
- official award claim;
- weakening theorem scope for convenience;
- unproved custom proof axioms;
- generic reusable theorem framework unless current proof demonstrates a real
  need;
- unrelated scanner improvements;
- unrelated repository refactors.

#### Deliverable

One complete BeeJSP-owned Lean formalization of the selected mathematical problem.

#### Acceptance criteria

- principal theorem is clearly identified;
- theorem represents the exact approved statement from Iteration 4;
- all required mathematical cases are covered;
- no material source assumption is omitted;
- no unapproved stronger assumption was added;
- proof contains no `sorry`;
- proof contains no `admit`;
- no custom unproved axiom replaces missing mathematics;
- proof builds from the committed project environment;
- Lean toolchain is pinned;
- required dependencies are pinned;
- mathematical solver attribution is accurate;
- Lean formalizer attribution is accurate;
- proof README identifies source and principal theorem;
- proof source does not depend on undocumented local files;
- no official-submission status is claimed.

#### Checks

```text
lake build
principal-theorem inspection
full statement-fidelity comparison
sorry search/audit
admit search/audit
custom-axiom review
dependency/toolchain inspection
source/provenance review
attribution review
clean project-state check
git diff --check
```

#### DoD

BeeJSP contains one complete real formalization suitable for independent verification.

---

## Stage 4 — Independent verification and submission

### Purpose of stage

Stage 4 separates:

```text
proof authored
```

from:

```text
proof independently verified and suitable for public external submission
```

External submission is attempted only after BeeJSP's own evidence is complete.

### Iteration 6 — Independent proof verification and evidence freeze

**Status:** PLANNED

#### Goal

Independently verify the completed formalization, prove that the claimed theorem matches the source problem, reproduce the proof from committed state and prepare an immutable public evidence package.

#### Scope

Included:

- independent verification by a separate verification pass;
- exact original problem review;
- exact source mathematical solution review;
- principal Lean statement review;
- statement-fidelity comparison;
- complete proof review;
- clean Lean build;
- `sorry`/`admit` audit;
- custom-axiom review;
- formal axiom audit of the principal theorem;
- toolchain/dependency reproducibility review;
- clean reproduction from committed source state;
- provenance review;
- solver/formalizer attribution review;
- security/supply-chain review;
- final BeeJSP PR review;
- evidence required to identify the eventually selected public proof revision.

#### Excluded

- official JSP contribution PR;
- award claim;
- payment/KYC;
- new mathematical scope;
- opportunistic proof rewrites without a blocker;
- new candidate tooling.

#### Deliverable

A fully independently verified BeeJSP proof with no known blocker to public submission preparation.

#### Acceptance criteria

- source problem and source solution are independently reviewed;
- Lean statement faithfully represents the approved mathematical statement;
- all required scope/cases remain represented;
- complete proof builds;
- no `sorry`;
- no `admit`;
- no custom proof-placeholder axiom;
- principal theorem axiom audit is complete;
- axiom result is acceptable under current proof contract;
- proof reproduces from committed sources and pinned environment;
- no hidden local dependency is required;
- mathematical solver attribution is correct;
- formalizer attribution is correct;
- proof README/evidence matches actual files;
- supplied verification commands/results are recorded;
- final read-only BeeJSP review returns no blocking finding;
- no official acceptance/priority/award claim is made.

#### Checks

```text
independent statement review
independent source review
clean lake build
sorry/admit audit
custom-axiom audit
principal theorem axiom audit
clean reproduction
dependency/toolchain verification
provenance review
attribution review
security/supply-chain review
final BeeJSP read-only review
git diff --check
```

#### DoD

BeeJSP has one independently verified proof whose mathematical meaning, machine-checking evidence, provenance and reproducibility are strong enough to freeze for public external submission.

### Iteration 7 — Official JSP submission package and external contribution

**Status:** PLANNED

#### Goal

Submit the independently verified proof through the current official Justin Sun Prize contribution process without weakening BeeJSP provenance or overstating external status.

#### Scope

Included:

- fresh managed JSP reference synchronization;
- review of current official contribution instructions;
- review of current official verification instructions;
- review of current attribution/award process;
- fresh exact target JSP record;
- fresh live competition check;
- selected public BeeJSP proof revision;
- full immutable commit SHA when required;
- exact theorem/proof location;
- exact formalizer attribution;
- official fork updated from current upstream;
- minimum official catalog/submission changes required by current process;
- official contribution PR;
- public recording of the official PR reference;
- verifier-feedback handling;
- correction loop through BeeJSP if proof changes are required;
- claim-ready evidence preparation only after official prerequisites are met.

#### Excluded

- claiming official verification before it occurs;
- claiming priority without official evidence;
- claiming an award before official approval;
- automatic merge;
- automatic claim submission;
- storing KYC material in BeeJSP;
- storing private payment credentials;
- modifying managed vendor files as an official contribution;
- rewriting BeeJSP provenance to manufacture authorship/priority.

#### Deliverable

One current-process-compliant official JSP contribution backed by an independently verified public BeeJSP proof.

#### Acceptance criteria

Before official submission:

- BeeJSP formalization remains complete;
- Iteration 6 verification remains valid;
- managed JSP reference is freshly synchronized;
- current contribution/verification rules are reread;
- exact current JSP record is confirmed;
- live official competition state is checked;
- relevant external competing formalizations are checked where practical;
- selected public BeeJSP commit contains the reviewed proof;
- exact full commit SHA is recorded where required;
- exact principal theorem/proof location is recorded;
- solver/formalizer attribution is accurate;
- official fork is current with upstream;
- only required official contribution scope is modified;
- no private KYC/payment information enters BeeJSP or the public PR.

After submission:

- official PR URL/reference is recorded;
- BeeJSP does not describe the PR as verified/awarded unless official evidence
  exists;
- proof corrections, when required, are made in BeeJSP first and independently
  reverified;
- updated immutable evidence is supplied when the official review requires it;
- claim workflow is attempted only after current official prerequisites are
  actually satisfied.

#### Checks

```text
fresh vendor sync
vendor provenance review
current official process review
exact target-record review
live competition review
selected public commit verification
proof build against selected source state
statement/provenance/attribution recheck
official fork freshness
official contribution diff review
private-data review
public-status wording review
```

#### DoD

A correct, independently verified BeeJSP proof has entered the official JSP contribution process with immutable evidence and accurate public status.

Award approval or payment is **not** required to mark this engineering iteration complete because those decisions are external to BeeJSP.

---

## First proof-cycle completion gate

Iteration 7 completes the first BeeJSP end-to-end cycle:

```text
official/public problem source
→ deterministic discovery tooling
→ evidence-backed candidate selection
→ bounded Lean feasibility
→ complete formalization
→ independent verification
→ immutable public proof evidence
→ official external submission
```

At this point, stop and evaluate actual evidence before expanding the architecture.

Questions:

- Did the scanner materially reduce candidate-selection work?
- Which candidate-assessment fields were genuinely useful?
- Which parts still required manual mathematical judgment?
- What formalization work was reusable?
- What verification work was repeatedly manual?
- Did the managed JSP snapshot provide enough local context?
- Was live competition analysis useful?
- What caused the most formalization cost?
- Did the official submission process expose a real tooling gap?
- Did the mathematical community gain a useful reusable proof regardless of
  award outcome?

Do not automatically create Iteration 8 solely because Iteration 7 exists.

## Post-first-submission orientation

**Status:** FUTURE / orientation

Post-first-submission work is not pre-approved implementation scope.

Potential directions include:

- select and formalize a second JSP candidate;
- validate whether proof-project conventions are genuinely reusable;
- improve candidate scoring using evidence from the first proof;
- automate additional read-only competition checks;
- create reusable Lean helpers only when multiple proofs require them;
- improve proof-reproduction automation;
- add machine-readable formalization evidence manifests;
- support non-JSP mathematical problem sources;
- document community contribution workflow;
- accept external formalization contributions;
- build a larger verified problem corpus.

A future item becomes real scope only after:

```text
first proof-cycle evidence
→ concrete recurring gap
→ necessity decision
→ architecture review
→ roadmap item
→ Issue
```

Do not create:

```text
generic proof platform
generic research-agent framework
hosted SaaS
database
web UI
automatic claim system
multi-competition abstraction
```

before real repeated work demonstrates the need.

### Related external boundary — The Justin Sun Prize

The official JSP repository is an external source and contribution target.

BeeJSP uses it for:

```text
problem discovery
official reference
verification requirements
submission
claim process
```

BeeJSP does not own its official state.

Current official facts must be refreshed before submission-sensitive decisions.

### Related project boundary — Bee Dev MCP

Bee Dev MCP remains a development/planning/review tool.

BeeJSP should be registered as an independent Bee Dev MCP project so planning and final review can inspect the actual repository.

Bee Dev MCP is not a BeeJSP runtime or proof dependency.

### Future roadmap rule

After the first end-to-end proof cycle, new roadmap work follows:

```text
real mathematical / tooling gap
→ evidence
→ necessity decision
→ ownership decision
→ roadmap item
→ Issue
→ implementation
→ verification
→ PR
```

Not:

```text
Iteration 7
→ Iteration 8
→ Iteration 9
→ Iteration 10
```

only because more iteration numbers are available.

The correct result may be:

```text
no architecture change
```

and simply:

```text
select next candidate
→ create next formalization Issue
→ prove it
```

using the architecture that already exists.

### Related process documents

BeeJSP development uses:

- `docs/ARCHITECTURE.md` — project ownership, repository structure and
  dependency boundaries;
- `docs/DEV_GUIDE.md` — local Python, vendor and Lean development workflow;
- `docs/FORMALIZATION.md` — mathematical statement, proof, reproducibility,
  axioms and attribution contract;
- `docs/SECURITY.md` — external-input, supply-chain, GitHub authority and
  private-data rules;
- `docs/SUBMISSION.md` — official JSP submission and claim preparation;
- `AGENTS.md` — repository-wide development and AI-agent instructions.

### Summary

BeeJSP develops according to this principle:

```text
build only enough infrastructure
→ select a good real problem
→ test formalization feasibility
→ prove the exact theorem
→ independently verify it
→ publish reproducible evidence
→ submit when appropriate
→ learn from the real cycle
```

Not:

```text
build a mathematical platform
→ build agents
→ build dashboards
→ build databases
→ build submission automation
→ eventually try to prove something
```

Target first-cycle state:

```text
small
useful
mathematically faithful
machine-checked
reproducible
well-attributed
public
submission-ready
```
