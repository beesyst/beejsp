# ROADMAP — BeeJSP

## Purpose

This document defines the development path for `beejsp` through explicit project stages and substantial implementation iterations.

BeeJSP uses the ROADMAP to:

- define project direction and meaningful delivery boundaries;
- connect Issue → Code / Proof → Verification → PR → Merge;
- keep discovery tooling separate from mathematical proof;
- preserve exact statement fidelity, reproducibility and correct attribution;
- distinguish catalog metadata, submitted claims, independently verified proofs and official award decisions;
- keep the official JSP reference reproducible without treating a vendored snapshot as live competition evidence;
- prioritize useful mathematical work without speculative platform development.

The ROADMAP does not replace Issues or Pull Requests:

- **Issue** defines the exact approved implementation task;
- **PR** records the actual implementation and verification evidence;
- **ROADMAP** defines the iteration-level contract and delivery direction.

A substantial roadmap iteration is normally delivered through a BeeJSP PR. Small low-risk maintenance does not become a numbered iteration solely to create another roadmap item.

Detailed ownership and rules belong in `docs/ARCHITECTURE.md`, `docs/DEV_GUIDE.md`, `docs/FORMALIZATION.md`, `docs/SECURITY.md`, `docs/SUBMISSION.md` and `AGENTS.md`.

## Vision

| Block                         | Statement                                                                                                                                                                                 |
| ----------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Project identity**          | BeeJSP is an open-source Python and Lean project for discovering suitable mathematical problems, proving faithful formal statements and publishing reproducible machine-checked evidence. |
| **Primary objective**         | Produce useful, independently reproducible formal mathematics rather than merely generate candidate proofs.                                                                               |
| **Core question**             | Can the exact intended mathematical result be represented faithfully, proved completely in Lean and independently reproduced?                                                             |
| **Community principle**       | Mathematical usefulness, correctness and attribution come before prize optimization.                                                                                                      |
| **Formalization principle**   | A compiling Lean theorem is not sufficient unless it faithfully represents the intended problem.                                                                                          |
| **Reproducibility principle** | The selected public source revision must support reconstruction using pinned dependencies and toolchain.                                                                                  |
| **Attribution principle**     | Problem author, mathematical solver, Lean formalizer and independent verifier are distinct roles.                                                                                         |
| **AI principle**              | AI may assist research, implementation and review, but its claims are not proof evidence.                                                                                                 |
| **Discovery principle**       | Candidate assessment supports research decisions; it does not establish mathematical truth.                                                                                               |
| **Competition principle**     | Submitted work, source-linked work, reproduced work, verified work and officially accepted work must be distinguished.                                                                    |
| **Award principle**           | Historical bounties, published JSP award information and qualitative future potential are separate evidence classes.                                                                      |
| **Vendor principle**          | `docs/vendor/jsp/` is a pinned generated reference, not live official authority.                                                                                                          |
| **Submission principle**      | BeeJSP owns its proof repository; official JSP contributions are external submissions.                                                                                                    |
| **KISS principle**            | Build only what real mathematical work and verification need.                                                                                                                             |

## Project thesis

BeeJSP does not primarily answer:

> Can AI produce Lean code for this problem?

BeeJSP answers:

> Can we identify a worthwhile mathematical result, formalize the exact statement, prove it completely in Lean, reproduce the result independently and publish trustworthy evidence?

Target flow:

```text
mathematical problem bank
→ authoritative problem and mathematical-solution sources
→ validated normalized records
→ live competition and external proof evidence
→ configurable evidence-aware candidate selection
→ bounded Lean feasibility spike
→ exact complete Lean formalization
→ independent statement and proof verification
→ immutable public proof evidence
→ optional official JSP submission
```

The Justin Sun Prize is a supported source and submission route, not BeeJSP's entire purpose. BeeJSP remains useful if a problem has no prize, a competitor submits first or an award claim fails.

## Architecture boundary

```text
Official mathematical sources
→ original problems and mathematical solutions

TheJustinSunPrize/awards
→ official problem, submission, candidate and award records

docs/vendor/jsp/
→ pinned read-only JSP reference

BeeJSP Python tooling
→ ingestion and normalization
→ evidence acquisition and candidate selection
→ deterministic reports

BeeJSP Lean projects
→ exact statements and complete proofs
→ reproducible verification

BeeJSP public Git history
→ immutable source provenance

Official JSP contribution
→ external review, priority, claim and award process
```

Architecture invariants:

```text
vendor snapshot != live official authority
candidate score != mathematical truth
PR opened != proof completed
PR merged != independently verified theorem
Lean build success != statement fidelity
external proof claim != verified external proof
historical bounty != official JSP payout
qualitative prize potential != monetary forecast
formalization != mathematical discovery authorship
official submission != official acceptance or award
```

## Repository ownership

BeeJSP owns:

- Python problem-bank scanning, normalization and candidate prioritization;
- read-only competition and award-evidence collection;
- managed JSP reference synchronization;
- explicit assessment, provenance and reproducible reports;
- Lean proof projects and verification evidence;
- project documentation and submission preparation.

BeeJSP does not own official JSP problem status, eligibility, candidate registration, formal verification decisions, priority decisions, award decisions, claims or payments.

Public official observations may be collected and analyzed, but BeeJSP's derived assessments must not overwrite or impersonate the official source of truth.

## Managed JSP reference rule

Canonical managed reference: `docs/vendor/jsp/`.

Canonical update command: `scripts/sync_jsp_docs.sh`.

Remote source: `https://github.com/TheJustinSunPrize/awards`.

Every accepted snapshot records `UPSTREAM_REF` and the full `UPSTREAM_COMMIT`.

```text
official upstream
→ exact upstream revision
→ bounded temporary staging
→ validation
→ managed snapshot replacement
→ recorded provenance
```

Do not manually maintain vendored JSP files.

The snapshot supports planning, local catalog scanning, formalization and submission guidance, but it does not establish the current state of open or merged PRs, Issues, external Lean repositories, candidate registrations, announced awards or payments.

Live evidence requires separate read-only capture with timestamps, source URLs, completeness status and provenance.

## Formalization invariants

### Exact problem identity

Each proof must identify the exact mathematical problem, authoritative source, selected formulation and expected conclusion.

### Statement fidelity

The Lean statement must preserve domains, quantifiers, hypotheses, conclusions, cases, boundary conditions and mathematical meaning. A weaker theorem or silently stronger assumptions cannot count as completion.

### Complete proof

A completed proof must not depend on `sorry`, `admit` or custom unproved axioms substituting for missing mathematics.

### Reproducible environment

The proof must pin the Lean toolchain and dependencies and reproduce from committed source files.

### Axiom review

The principal theorem and required dependencies must receive the applicable axiom audit.

### Attribution

Problem author, mathematical solver, Lean formalizer and independent verifier must be recorded separately.

### Conservative claims

A successful Lean build does not establish statement fidelity or independent verification. A source link, PR description or third-party claim does not establish that the original problem was fully formalized.

### External proof evidence

Do not discard a candidate solely because a competing PR exists, and do not ignore a source-linked earlier proof solely because its PR remains unmerged. Classification must reflect the available evidence and retain unresolved priority risk.

## Security invariants

### External data is untrusted

Treat upstream repositories, API responses, external Lean projects, mathematical documents, award records and downloaded dependencies as untrusted data.

### No hidden execution

External code and setup scripts must not execute merely because a repository was referenced in a PR. Any targeted external proof check requires a reviewed, isolated and authorized workflow.

### Managed path safety

Vendor synchronization and any bounded evidence capture must not allow upstream-controlled paths to escape approved destinations.

### Minimal GitHub authority

Read-only research does not justify write permissions. GitHub writes require explicit approved scope.

### Private data

Do not commit tokens, credentials, private keys, seed phrases, private identity documents, KYC data or private payment information.

### Provenance integrity

Do not claim a proof exists at a repository revision without checking its exact source state. Preserve source URL, branch and pinned full commit SHA when available.

## Development principles

Every significant BeeJSP iteration must:

- have a concrete mathematical, tooling or verification goal;
- produce a meaningful code, proof or evidence increment;
- remain within approved scope;
- avoid speculative abstractions;
- preserve source-of-truth and formalization boundaries;
- preserve reproducibility and attribution;
- use verification proportional to change risk;
- keep external writes separate from local evidence production.

```text
candidate != proof
proof text != verified proof
compiled theorem != verified source equivalence
catalog Lean proof: No != no external Lean work
vendor snapshot != live competition state
competing PR != verified competing proof
historical bounty != available JSP award
```

## Iteration significance rule

A numbered iteration must deliver a substantive capability such as validated catalog ingestion, evidence-backed selection, meaningful competition analysis, a bounded Lean feasibility result, a complete real formalization, independent proof verification, an official submission artifact or a material correction revealed by actual use.

Formatting, README cleanup, one narrow helper, an isolated test or speculative architecture do not justify separate numbered iterations.

If two planned efforts produce one inseparable capability, consolidate them rather than creating artificial milestones.

## KISS roadmap rule

Do not add a web dashboard, database, SaaS platform, general theorem-prover abstraction, research-agent framework, hosted proof-runner fleet, generic plugin system, knowledge graph, multi-competition abstraction or automatic award-claim system without demonstrated current need.

A new scope item is justified only when real proof work exposes a reusable gap, a current iteration cannot complete without it, or verification/submission evidence exposes a concrete deficiency.

Insufficient reasons include architectural aesthetics, hypothetical future scale or a desire to support every research workflow.

## Delivery workflow for roadmap items

1. **Planning:** inspect repository state, validate the gap, reject speculative scope and identify sources of truth.
2. **Requirements:** define Goal, Scope, Excluded, Deliverable, Acceptance criteria, contract/dependency/security impact, Checks and DoD.
3. **Issue:** create one focused BeeJSP Issue containing the approved task.
4. **Implementation:** deliver the smallest complete change on an approved dedicated branch.
5. **Independent verification:** reproduce and review results, correcting only demonstrated in-scope blockers.
6. **Final read-only review:** compare the actual worktree and evidence with the approved Issue and repository contracts.
7. **PR / merge:** record verified scope, tests and provenance; merge only after acceptance criteria pass.
8. **External submission:** only where expressly required and after proof evidence is complete.

Tiny low-risk maintenance may use a shorter path without a roadmap iteration.

## Status values

Allowed iteration statuses:

- **PLANNED** — approved scope, implementation not started;
- **IN PROGRESS** — implementation underway;
- **DONE** — complete acceptance contract delivered;
- **DONE (partial)** — intentionally closed with disclosed limitations.

**FUTURE / orientation** describes an unapproved direction, not authorized implementation scope.

External JSP acceptance, priority, award and payment are independent of local engineering status.

## Roadmap item format

Every numbered iteration uses:

- `Goal`;
- `Scope`;
- `Excluded`;
- `Deliverable`;
- `Acceptance criteria`;
- `Checks`;
- `DoD`.

Schemas, exact file lists, implementation algorithms, detailed test matrices, theorem statements and reviewer findings belong in Issues, code, tests and PRs rather than the iteration-level ROADMAP.

## Global Definition of Done

A substantial iteration is complete only when:

- approved scope is implemented and excluded scope remains excluded;
- source-of-truth and managed vendor boundaries are preserved;
- deterministic contracts reproduce identical output from identical validated inputs;
- formalization-sensitive work preserves exact mathematical scope;
- completed proofs contain no unresolved placeholders or substituted axioms;
- applicable builds, axiom audits and independent verification pass;
- provenance and attribution are accurate;
- targeted tests and applicable full Python checks pass;
- package build and import checks pass when package contracts change;
- applicable security, supply-chain and dependency checks pass;
- no secrets or private payment/identity information enter repository state;
- documentation accurately describes actual behavior;
- meaningful delivery and verification are recorded in the PR;
- unrelated refactoring and speculative infrastructure remain out of scope.

## Change levels for verification

### low-risk

Documentation, agent guidance, metadata and narrow test-only changes generally require targeted checks and consistency review.

### runtime-risk

Parser, normalization, scanner, ranking, report, vendor, CI, package and read-only API changes require targeted tests, `uv run pytest -q`, Ruff checks, applicable build/import checks, reproducibility tests and input-safety review.

### security-sensitive

Changes to execution, credentials, path security, extraction, GitHub write permissions or dependency trust require runtime-risk checks plus explicit security review, negative/adversarial tests, SAST and SCA if the dependency surface changes.

DAST, IAST and fuzzing are only required where the change actually creates a corresponding surface.

## Formalization-sensitive verification

Formalization sensitivity is independent of the ordinary change level and applies to theorem statements, proof terms, assumptions, dependencies, toolchain, provenance, attribution, axiom evidence or submission proof evidence.

Applicable checks:

```text
exact statement review
full mathematical scope review
lake build
sorry/admit audit
custom placeholder-axiom review
principal theorem axiom audit
dependency/toolchain review
clean reproduction
source/provenance review
solver/formalizer attribution review
```

Successful compilation alone does not close a formalization-sensitive task.

## Versioning and release rule

BeeJSP tooling follows SemVer. The version source of truth is `pyproject.toml`.

Roadmap iteration numbers are unrelated to package versions. Routine feature, fix, proof and documentation work must not manually increment the package version unless the approved task explicitly requires release work.

Release automation owns the release PR, version, CHANGELOG, tags and release lifecycle.

A formalization is identified by its repository, selected branch where required, immutable full commit SHA, Lean proof project and principal theorem.

Conventional Commits should be used.

| Commit          | Release impact                         |
| --------------- | -------------------------------------- |
| `feat:`         | MINOR                                  |
| `fix:`          | PATCH                                  |
| `docs:`         | Normally no release bump by itself     |
| `test:`         | Normally no release bump by itself     |
| `refactor:`     | Normally no release bump by itself     |
| `chore:`        | Normally no release bump by itself     |
| `ci:`           | Normally no release bump by itself     |
| `build:`        | Normally no release bump by itself     |
| Breaking change | MAJOR when SemVer maturity requires it |

Release mechanics must not block mathematical work.

## Project phases

| Phase                                              | Status      | Delivery                                                                                 |
| -------------------------------------------------- | ----------- | ---------------------------------------------------------------------------------------- |
| **Phase A — Foundation and official reference**    | DONE        | Stage 1, Iteration 1.                                                                    |
| **Phase B — Discovery and candidate selection**    | DONE        | Stage 2, Iterations 2–3.                                                                 |
| **Phase C — First proof cycle**                    | DONE        | Stage 3, Iterations 4–5, plus recorded independent verification and external submission. |
| **Phase D — Evidence-aware discovery improvement** | IN PROGRESS | Stage 4, Iterations 6–7.                                                                 |

### Stages

- **Stage 1 — Foundation and official reference:** Iteration 1 establishes repository governance, Python/Lean foundations, CI and managed JSP reference.
- **Stage 2 — Discovery and candidate selection:** Iterations 2–3 deliver scanner ingestion, live competition capture and an initial evidence-backed TOP-5.
- **Stage 3 — First real formalization:** Iterations 4–5 establish a bounded Lean spike and complete JSP-000089 proof; the verified submission is recorded as the completion of this first proof cycle rather than as unimplemented future iterations.
- **Stage 4 — Evidence-aware discovery improvement:** Iteration 6 improves the existing scanner and assessment based on actual competition and prize-data gaps.

Every active stage has at least one numbered iteration, and iteration numbers are unique and monotonically increasing.

## Project gates

These are decision gates, not additional numbered iterations.

### Gate 1 — Foundation integrity

After Iteration 1, pinned upstream material must synchronize reproducibly into `docs/vendor/jsp/` without manual edits, missing provenance or speculative platform dependencies.

### Gate 2 — Candidate quality

After Iteration 3, a defensible shortlist must identify the original problem, official catalog record, complete mathematical source where known, recorded Lean status, current scoped competition observations, estimated Lean complexity and major risks.

If the shortlist is derived only from catalog labels or intuition, do not start a large proof. Iteration 6 strengthens this gate without rewriting historical Iteration 3 evidence.

### Gate 3 — Formalization feasibility

Before a full proof begins, inspect the hardest material theorem or Mathlib boundary through a bounded Lean feasibility spike. Record GO or NO-GO with concrete evidence and remaining obligations.

### Gate 4 — Proof truth

Before external submission, the chain `exact problem → exact Lean statement → complete proof → reproducible build → acceptable axiom audit → independent statement review` must hold.

This is a reusable verification requirement, not a historical iteration number.

### Gate 5 — Evidence-aware candidate selection

After Iteration 6, a validated pinned catalog, complete scoped live competition capture, external proof observations, official candidate/award evidence and configurable selection profile must produce a reproducible shortlist with source links and explicit uncertainty.

An open PR must not automatically block a proof. A purported source-linked full proof must not be ignored. A missing prize amount must remain unknown. No score may silently turn uncertainty into a confirmed GO.

---

## Stage 1 — Foundation and official reference

### Purpose of stage

Establish BeeJSP as a governed Python and Lean repository with a reproducible managed official reference before candidate selection or real proof work.

### Iteration 1 — Repository foundation and managed JSP reference

**Status:** DONE

#### Goal

Bootstrap a standalone BeeJSP repository with minimal Python/Lean foundations, governance, CI and safe managed JSP reference synchronization.

#### Scope

Included:

- `beejsp` Python package with `src` layout, Python `>=3.14`, `uv` and byte-empty package initializer;
- pinned Lean template and minimal smoke build;
- `AGENTS.md`, required skills/prompts, Issue/PR templates, CI and SemVer/release baseline;
- architecture, development, formalization, security and submission contracts;
- `scripts/sync_jsp_docs.sh` and `docs/vendor/jsp/`;
- exact upstream reference and commit provenance;
- safe staged validation and atomic managed snapshot replacement;
- idempotent vendor synchronization;
- scheduled/manual GitHub update PR workflow.

#### Excluded

- full mathematical formalization;
- candidate scanner and ranking;
- live competition crawler;
- database, web UI or runtime framework;
- permanent dependency on an official JSP fork;
- official contribution PR or award automation.

#### Deliverable

A governed standalone BeeJSP repository that can reproducibly consume the official JSP reference and build a minimal Lean project.

#### Acceptance criteria

- package identity and `src` layout are correct, imports have no hidden I/O and initializer remains byte-empty;
- Lean template builds with a pinned toolchain;
- canonical agent workflow is planning → implementation → verify/correct → final review;
- vendor source and full upstream SHA are recorded;
- required reference files are materialized, validated and read-only/generated;
- invalid sync fails without replacing a valid snapshot;
- repeated sync against the same revision is idempotent;
- automated vendor updates use reviewable PRs rather than direct modifications to `main`;
- no speculative runtime or secret handling is introduced.

#### Checks

```text
uv sync
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
uv build where applicable
package import smoke
Lean template lake build
vendor sync validation and idempotence
git diff --check
security review
SAST for sync/shell code
SCA only if dependencies change
```

#### DoD

BeeJSP has a reproducible, governed Python/Lean foundation and a managed official JSP reference suitable for real mathematical work.

---

## Stage 2 — Discovery and candidate selection

### Purpose of stage

Prevent substantial proof effort from being spent on the wrong problem by creating deterministic ingestion and evidence-backed candidate research.

### Iteration 2 — Problem-bank ingestion and deterministic candidate scanner

**Status:** DONE

#### Goal

Transform the managed JSP catalog into normalized, validated, provenance-preserving records and an initial solved/no-recorded-Lean candidate set.

#### Scope

Included:

- dynamically discover vendored catalog volumes without hardcoded problem counts;
- parse and normalize JSP ID, title, mathematical status, Lean status, eligibility/claim fields and source data;
- preserve raw official values and upstream provenance alongside derived values;
- distinguish missing and unknown states;
- deterministic filtering, JSON report and human summary;
- malformed and duplicate identity detection;
- deterministic regression tests over pinned fixtures and snapshots.

#### Excluded

- mathematical proof validation;
- source-paper proof checking;
- LLM-only ranking;
- live GitHub state or external repository scanning;
- database, web UI, automatic formalization or prize prediction.

#### Deliverable

A deterministic local scanner that produces validated normalized records and an initial formalization candidate set.

#### Acceptance criteria

- every discovered record is parsed or explicitly reported invalid;
- JSP identities remain unique, with complete upstream provenance;
- official fields and derived fields are separated;
- missing values are never invented;
- no fixed total catalog count is assumed;
- identical pinned source produces identical output;
- incomplete or malformed input fails clearly;
- no live competition state is inferred from the vendor snapshot.

#### Checks

```text
catalog discovery
full pinned-snapshot parse
duplicate and malformed-record tests
missing-value normalization tests
deterministic JSON and filter tests
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
uv build where applicable
git diff --check
```

#### DoD

BeeJSP can inspect the current pinned catalog without manually reading every volume and can produce an initial deterministic candidate set.

### Iteration 3 — Evidence-backed TOP-5 and live competition analysis

**Status:** DONE

#### Goal

Produce a reviewable TOP-5 with one primary candidate using mathematical-source, external formalization and current competition evidence rather than catalog flags alone.

#### Scope

Included:

- consume Iteration 2 normalized candidate records;
- distinguish complete mathematical solutions from answers, sketches, partial work and unsupported claims;
- review source solutions and estimate Lean/Mathlib feasibility;
- collect read-only public GitHub PR/Issue evidence by JSP ID and supplementary title matching;
- record scoped external formalization observations and timestamps;
- keep official facts separate from qualitative estimates;
- produce deterministic primary/reserve/rejected selection with explanations;
- specify one bounded Lean spike objective.

#### Excluded

- full Lean proof;
- treating `Solved` as mathematical consensus;
- assuming `Lean proof: No` means competitors do not exist;
- automatic award predictions or official GitHub writes;
- general research crawler, database or hosted platform.

#### Deliverable

An evidence-backed TOP-5 report and one candidate selected for bounded Lean feasibility research.

#### Acceptance criteria

- every reported candidate includes exact JSP ID, official record, solution source and solution-completeness classification;
- competition and formalization evidence is timestamped and scoped;
- difficulty, Mathlib, statement, provenance and process risks are explicit;
- primary selection includes a real mathematical source and bounded spike objective;
- reported evidence does not claim global absence of competition;
- no unverified award value is presented as official;
- deterministic selection is reproducible from pinned inputs.

#### Checks

```text
normalized input validation
GitHub API pagination and mock tests
exact-ID and supplementary-title matching
duplicate and collision tests
timestamp/provenance checks
TOP-5 deterministic reproduction
manual evidence review
read-only security review
git diff --check
```

#### DoD

BeeJSP can produce a reviewable initial TOP-5 with one bounded-spike target. Iteration 6 may refine selection quality without rewriting this historical result.

---

## Stage 3 — First real formalization

### Purpose of stage

Take one selected mathematical problem from exact source review through bounded proof feasibility and complete Lean formalization, then independently verify and submit it as the first finished cycle.

### Iteration 4 — Selected candidate statement package and bounded Lean spike

**Status:** DONE

#### Goal

Establish the exact selected mathematical statement and test a representative difficult Lean boundary before committing to full proof work.

#### Scope

Included:

- selected JSP candidate and current target-record review;
- original problem and complete solution-source research;
- solver attribution and mathematical statement decomposition;
- exact Lean statement and minimal local proof project;
- pinned Lean/Mathlib dependencies;
- proof of or bounded investigation into the hardest representative lemma;
- statement-fidelity inspection, proof feasibility and explicit GO/NO-GO decision.

#### Excluded

- obligation to complete the entire proof;
- silent weakening of the target theorem;
- official external submission;
- generic theorem framework or new candidate scanner architecture.

#### Deliverable

A reproducible Lean feasibility spike and defensible decision about full formalization.

#### Acceptance criteria

- exact source identity, mathematical meaning and solver attribution are documented;
- quantifiers, hypotheses, domain and conclusion are faithfully represented;
- dependencies/toolchain are pinned;
- real hard-boundary mathematics is tested, not bypassed with unrelated scaffolding;
- proved portion builds;
- exploratory placeholders are identified and never reported as completed evidence;
- GO identifies remaining work and NO-GO identifies concrete blockers.

#### Checks

```text
source and problem identity review
statement-fidelity review
lake build for proved portion
dependency/toolchain audit
hard-boundary review
placeholder inventory
competition refresh
attribution and provenance review
git diff --check
```

#### DoD

BeeJSP has a source-grounded GO/NO-GO decision for one real formalization candidate.

### Iteration 5 — Complete Lean formalization

**Status:** DONE

#### Goal

Complete the full Lean proof approved after the bounded spike without weakening the mathematical statement or inserting unproved proof assumptions.

#### Scope

Included:

- complete principal theorem and required mathematical foundations;
- local definitions and supporting lemmas with appropriate Mathlib reuse;
- pinned Lean and dependency environment;
- explicit proof source/provenance and solver/formalizer attribution;
- proof README and source-to-Lean mapping where needed;
- successful full Lean build, placeholder removal and preliminary axiom audit.

#### Excluded

- official JSP PR as an implementation deliverable;
- official award claim or entitlement;
- silent theorem weakening or unproved custom axioms;
- generic theorem infrastructure without demonstrated reuse;
- unrelated scanner and repository refactors.

#### Deliverable

One complete BeeJSP-owned Lean formalization of the selected original mathematical problem.

#### Acceptance criteria

- principal theorem is clearly identified and matches the approved original statement;
- all required mathematical cases are proved;
- no unapproved assumptions, `sorry`, `admit` or placeholder custom axioms remain;
- complete proof reproduces in the pinned project environment;
- attribution, source references and theorem location are accurate;
- proof requires no undocumented local resources;
- local completion does not claim external acceptance or an award.

#### Checks

```text
lake build
principal theorem inspection
full statement-fidelity comparison
sorry/admit audit
custom-axiom and dependency review
source/provenance and attribution review
clean project-state check
git diff --check
```

#### DoD

BeeJSP contains one complete real formalization ready for independent verification and external submission preparation.

---

## Stage 4 — Evidence-aware discovery improvement

### Purpose of stage

Improve candidate discovery after the completed first proof cycle so BeeJSP can distinguish submitted claims from verified proofs, assess competition without premature rejection and query mathematical problems by difficulty and award evidence.

Stage 4 contains Iterations 6–7. Iteration 6 establishes evidence-aware candidate selection, and Iteration 7 delivers a local research dashboard with one-command refresh. No additional stage number is created for historical verification or submission activity already completed.

### Iteration 6 — Evidence-Aware Candidate Discovery & Prize Screening

**Status:** DONE

#### Goal

Enhance the existing BeeJSP scanner and assessment with configurable discovery, independently classified competition and proof evidence, current public award records and reproducible selection reports.

The result must help researchers select high-value feasible Lean targets without pretending that submitted PRs prove theorems or that unknown award amounts have predictable dollar values.

#### Scope

Included:

**Existing tooling and compatibility**

- extend `beejsp.scanner` and `beejsp.assessment` instead of building a second platform;
- preserve the existing solved/no-recorded-Lean scanner workflow;
- make the full normalized problem bank available to configurable queries;
- keep managed vendor facts, live observations and qualitative research inputs separate;
- preserve prior scanner/assessment evidence compatibility or provide an explicitly documented schema migration;
- keep live capture as bounded read-only I/O and subsequent selection as deterministic offline processing.

**Competition evidence acquisition**

- capture all accessible official PRs and Issues, including open, closed-unmerged and merged states;
- preserve canonical URLs, exact JSP matches, evidence timestamps and acquisition completeness;
- associate replacement submissions and older submissions where explicit source links establish their relationship;
- distinguish mathematical solver submissions, Lean formalization submissions, administrative catalog updates and other issue activity;
- preserve bounded structured references to external proof source repositories, branches, full commit SHAs and theorem/file paths where supplied;
- handle missing API pages, rate limits and malformed responses without making false clearance claims;
- use exact JSP-ID and evidence-backed original Erdős-ID/theorem aliases; mark weak title matches as uncertain rather than authoritative;
- avoid persisting arbitrary unbounded PR bodies.

**Independent evidence classification**

- model GitHub submission state separately from proof-verification state and official award state;
- distinguish unverified claims, source-linked claims, partial work, locally reproduced proofs, independently statement-reviewed complete proofs and official acceptance;
- do not mark a theorem verified solely because an external PR says it is complete or `lake build` passes;
- retain `CONTESTED` or equivalent state when a competing claim remains unresolved;
- classify a verified matching external proof as an originality and priority risk, not a self-made official award decision;
- retain documented evidence for demonstrated incompleteness, materially weaker statements, bad axioms or unproved placeholders;
- allow a demonstrated invalid or partial external proof to be reconsidered without automatically awarding priority to BeeJSP;
- never treat a closed-unmerged PR as mathematically refuted solely because it was closed.

**Public candidates and award evidence**

- capture official public candidate and confirmed-award records through a bounded read-only mechanism;
- do not assume `candidates/` or `awards/` are present in the current vendored subset;
- distinguish public candidate registration, review, announced award and payment evidence;
- retain JSP identity, solver/formalizer role, award category, source URL and observation timestamp where published;
- distinguish historical third-party bounties, officially announced JSP awards and known published monetary amounts;
- keep unknown amounts null or explicitly unknown, not zero;
- distinguish published official categories from qualitative, non-official estimates;
- never infer an available future payout directly from a historical Clay or other external prize.

**Configurable selection**

- implement compact documented selection profiles using existing Python facilities and minimal dependencies;
- filter by mathematical status, catalog Lean status, evidence-based competition state and mathematical area;
- filter by estimated Lean formalization difficulty, including low, medium, high, extreme and unknown;
- filter by availability and completeness of published mathematical solutions;
- filter by official candidate/award records, known historical bounties, known published amounts and missing monetary information;
- support researcher preferences for scientific significance and potential prize value with explicit qualitative rationale;
- provide bounded limits and deterministic tie-breaking;
- distinguish initial broad screening from deeper manual mathematical and external-proof research;
- provide at least one general discovery profile and one high-value research profile;
- allow unresolved competing claims to be displayed instead of silently excluded;
- reserve unconditional GO for candidates that passed all required applicable evidence gates and bounded mathematical feasibility checks;
- avoid hidden LLM-generated scores or automatically inferred numerical award probabilities.

**Inspection and reporting**

- provide a documented CLI to select candidates using a named profile;
- provide a documented CLI to inspect one JSP problem and its linked evidence;
- support deterministic JSON and CSV outputs and an optional readable report;
- show source provenance, captured-at times, official fields, derived classifications, complexity rationale, competition and award information;
- explain inclusion, exclusion, contested status and unresolved information;
- maintain the historical TOP-5 workflow or document and test a clear migration path.

#### Excluded

- rewriting the scanner or assessment from scratch;
- database, web UI, hosted SaaS or general research platform;
- arbitrary open-web scraping or a large external indexer;
- autonomous downloading, installation and execution of untrusted Lean repositories;
- automatic proof correctness or universal statement-fidelity certification;
- permanent rejection of every problem with an open PR;
- hidden numerical prize prediction, invented award amounts or unsupported probability estimates;
- official priority adjudication, automatic prize claim or payment processing;
- GitHub write automation;
- new general AI-agent framework;
- unrelated Lean proof modifications, including changes to JSP-000089;
- speculative dependency growth or broad refactors.

#### Deliverable

A backward-compatible, evidence-aware Python CLI workflow producing filtered and ranked candidate reports from validated current JSP and competition/award evidence, with explainable uncertainty and no false claims of proof verification or payout certainty.

#### Acceptance criteria

**Data and compatibility**

- the original scanner and existing assessment entry points continue to operate or have an approved and tested compatibility migration;
- full normalized problem records remain available beyond the original candidate subset;
- raw official data, live observations and derived assessments are explicitly separated;
- duplicate and malformed JSP records fail safely;
- source provenance and deterministic offline output are preserved;
- identical inputs and configuration produce identical candidate ordering and reports.

**Competition and proof states**

- open, closed-unmerged and merged PRs are captured within a declared complete scope;
- exact JSP matches and weaker alternate-name matches are distinguishable;
- missing pages, API errors or rate limits cannot silently establish absence of competition;
- a source-linked proof claim does not automatically become verified;
- a successful Lean build alone does not establish exact statement fidelity;
- a competing open PR does not automatically disqualify a candidate;
- a competing closed PR does not automatically mean the proof failed;
- source-linked claimed complete proofs can become contested while verification is pending;
- verified matching existing proofs can be identified without claiming an official priority or award decision;
- partial, unsupported or demonstrably invalid external work remains visible with links and reasons;
- incomplete and unknown evidence is explicit and cannot become unqualified GO.

**Award and prize states**

- public official candidate registrations and confirmed awards are distinguished;
- solver and formalizer roles remain separate;
- historical bounty, official award level and published monetary amount are separate fields;
- unknown amounts remain unknown rather than zero;
- no historical prize is silently counted as a currently payable JSP prize;
- qualitative scientific-value or prize-potential estimates are labeled non-official and have source/rationale;
- no unsupported guarantee or probability of payment is generated.

**Configuration and reporting**

- configurable general and high-value selection profiles are documented and usable;
- status, area, difficulty, competition and award filters work deterministically;
- result count limits and stable tie-breaking are tested;
- selection and single-problem inspection have usable documented CLI commands;
- JSON and CSV contain source URLs, provenance, classifications and explicit unknowns;
- empty or incomplete results are reported clearly;
- saved evidence can be reprocessed offline with identical output.

**Regression cases**

- JSP-000161 with PR #1248 is flagged as having a competing source-linked claim, not automatically accepted as independently verified;
- JSP-000475 with PR #1269 is flagged as having a competing source-linked claim, not automatically accepted as independently verified;
- the historical JSP-000089 assessment must not ignore competing claims merely because an aggregate score remains positive;
- a PR claim with no proof source cannot become verified;
- an externally claimed proof with `sorry`, unexpected axioms or a weaker theorem cannot become verified complete;
- a source-linked proof that fails to build solely for environmental reasons remains unresolved rather than proven false;
- a closed-unmerged PR remains valid historical competition evidence;
- incomplete GitHub capture blocks unqualified competition-clearance claims;
- missing monetary values remain unknown;
- historical bounty values never populate the official JSP payout field.

#### Checks

```text
scanner and assessment regression tests
complete-scope GitHub capture and pagination tests
GitHub rate-limit and malformed-data tests
JSP identity and alias collision tests
competition submission and proof-state tests
candidate and award record normalization tests
missing and ambiguous award-value tests
selection profile validation tests
CSV/JSON deterministic reproduction
backward compatibility tests
JSP-000161 / PR #1248 regression
JSP-000475 / PR #1269 regression
JSP-000089 historic competition regression
read-only GitHub authority review
external input and bounded resource review
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
uv build where package behavior changes
package import smoke where applicable
git diff --check
security review
SAST for external-input handling
SCA only where dependencies change
independent final read-only review
```

#### DoD

BeeJSP can list and inspect mathematical formalization opportunities using configurable difficulty, competition and prize-evidence criteria, without equating PR submissions to completed proofs or unknown monetary amounts to zero.

A general profile and a high-value profile must work over validated saved evidence, provide transparent explanations, retain contested/unknown cases and pass all applicable regression, security and reproducibility checks.

The iteration delivers a material enhancement to existing Python tooling without introducing a new platform or weakening the Lean formalization contract.

### Iteration 7 — Local Discovery Dashboard & One-Command Refresh

**Status:** DONE

Startup follows `start.sh → config/start.py → beejsp.dashboard`. Optional local read-only GitHub authentication is implemented; authenticated live acquisition and complete snapshot verification passed on 2026-10-12. Final read-only review remains pending. The approved HTML simplification uses seven overview columns and seven filters, with readable award/proof labels and full evidence in details and both JSON/CSV profiles. The final refinement adds a static dark theme, four catalog-derived overview metrics, announced official amounts and keyboard-accessible PR/Issue count navigation; unknown award coverage stays visible without an overview filter option. Offline template upgrades preserve validated immutable snapshots and acquisition timestamps. Implementation entry points are `start.sh`, `config/start.py` and `src/beejsp/dashboard.py`; the standalone presentation is `src/beejsp/_dashboard_view.py`. Generated snapshots live in Git-ignored `storage/discovery/`. Targeted contracts are exercised by `tests/test_dashboard.py` and the optional installed-browser check `tests/dashboard_browser_check.py`. See [local workflow and snapshot behavior](DEV_GUIDE.md#iteration-7-local-discovery-dashboard).

#### Goal

Turn the existing BeeJSP evidence-aware discovery tooling into a practical local research workspace with one-command data refresh, a searchable standalone HTML dashboard and detailed per-problem inspection.

A researcher must be able to open one local report, inspect the complete JSP problem bank, identify promising Lean formalization candidates, examine competing PRs and Issues, review mathematical sources and award evidence, and decide which candidate deserves a targeted mathematical and Lean feasibility investigation.

The primary entry point is `./start.sh update`. The dashboard must remain useful without a server, database, JavaScript framework or external hosting.

#### Scope

Included:

**Stable CLI entry point**

- Add a minimal root `start.sh` as a stable user-facing command dispatcher for the existing Python tooling.
- Support `./start.sh update` to acquire current public evidence, regenerate reports and open the resulting dashboard when a graphical desktop session is available.
- Support `./start.sh report` to open the most recent saved dashboard without network access or data refresh.
- Support `./start.sh inspect JSP-XXXXXX` to inspect a particular problem using the latest saved evidence and existing Assessment contracts.
- Keep the CLI independent of the current working directory after resolving the repository root.
- Reuse existing Scanner and Assessment commands instead of reimplementing their normalization, matching, evidence classification or selection behavior.
- Document non-interactive/headless behavior: data refresh and report generation must complete without requiring a browser.
- Avoid starting a persistent background process, HTTP server or service.

**One-command discovery update**

- Use the current approved local `docs/vendor/jsp/` snapshot as the source for the official problem bank.
- Run the existing deterministic Scanner over the complete managed problem bank.
- Refresh public PR and Issue evidence using the existing version 2 `capture-github` workflow with both required endpoint scopes.
- Refresh official public candidate and award records using the existing `capture-records` workflow.
- Reuse validated research evidence where available without replacing reviewed findings with speculative automatic estimates.
- Run evidence-aware selection using the documented general and high-value profiles.
- Generate reproducible JSON, CSV and standalone HTML outputs.
- Preserve acquisition timestamps, source URLs, exact source revisions, completeness and uncertainty.
- Keep the existing managed vendor synchronization workflow independent from discovery refresh.
- Never silently modify `docs/vendor/jsp/`, switch Git branches, pull upstream source, create commits or merge synchronization PRs.
- Display the pinned vendor SHA and the current live acquisition revision where available so differing revisions are visible.
- Fail visibly when GitHub acquisition is incomplete, rate-limited or malformed.
- Never replace the last known complete competition snapshot with an incomplete snapshot presented as complete.
- Permit inspection of retained historical evidence with explicit stale or incomplete warnings when a current refresh fails.
- Never infer absence of competition from a legacy version 1 capture or a partial version 2 capture.

**Generated report storage**

- Use one clearly documented local output directory, such as `storage/discovery/`, for generated discovery data and reports.
- Keep generated runtime reports out of Git by default.
- Preserve the latest validated scanner, competition, award and selection artifacts needed for offline inspection.
- Make report updates deterministic for identical saved inputs, apart from explicitly displayed acquisition timestamps and other genuine source changes.
- Avoid creating a new persistence framework or duplicating official records in a separate database.
- Do not modify committed historical Iteration 3 evidence.

**Standalone HTML dashboard**

- Generate one self-contained HTML report that opens locally in a standard browser.
- Use Python and minimal embedded HTML, CSS and JavaScript without a frontend framework.
- Do not depend on external CDN assets, remote JavaScript, a web server or network access to render saved evidence.
- Include all normalized JSP records, not only the shortlisted or originally unformalized candidates.
- Provide compact catalog/award counts and one snapshot freshness/completeness line; keep mathematical and recorded Lean status in the table and competition/selection evidence in details and JSON/CSV.
- Clearly distinguish official catalog facts from derived research estimates and current captured public observations.
- Support client-side searching, sorting and filtering without additional backend calls.
- Support mathematical status, Lean status, mathematical area, award evidence, separate PR/Issue count filters and PR lifecycle filtering in the compact HTML overview; retain additional research/proof/competition evidence in details and machine-readable outputs.
- Preserve general and high-value research profiles in JSON/CSV and per-problem details using existing version 2 selection contracts, without an HTML profile selector.
- Keep contested and unknown candidates visible rather than silently excluding them.
- Display explicit empty-result and incomplete-evidence states.
- Make the report usable on desktop and reasonably readable on narrower screens.
- Use safe HTML escaping and validated external URLs when rendering untrusted problem descriptions, contributor fields and GitHub evidence.

**Problem overview table**

- Render seven columns: Problem, Math status, Lean, Area, PRs, Issues and Award; retain four overview metrics: Total problems, Math Open, Lean No and Awards announced.
- Display exact JSP ID/title and a usable detail action and official catalog link.
- Keep official mathematical status and catalog Lean status distinct from external proof observations.
- Display separate clickable captured PR and Issue counts per JSP task in their own columns, with noninteractive zero values. Both count filters offer All, exact 0–10 and >10 for eleven or more, combine with all filters/search using AND, and preserve evidence uncertainty. Both columns sort numerically with JSP ID tie-breaking; changing filters resets pagination and Reset clears all filters/search.
- Add PR status options All, Open, Merged, Closed, unmerged and No open PR, using saved observations and AND with every other filter/search. Disable No open PR under incomplete capture; lifecycle is separate from mathematical/proof verification. Explain Claimed/Source linked as not independently verified and administrative fallback as Not a proof claim, preserving canonical evidence states.
- Display readable award states and support direct award filtering/sorting, with officially announced awards first when explicitly sorted.
- Preserve stable JSP identity while filtering, sorting and paging, including unknown and contested records.
- Keep attribution, sources, difficulty/significance, competition/proof evidence, historical bounty, published amounts and selection reasons in per-problem details and JSON/CSV.

**Detailed problem inspection**

- Allow opening an expanded detail view for an individual JSP problem from the overview table.
- Display the available original mathematical problem description without inventing or summarizing missing mathematical requirements.
- Display source publications, reference links, publication details and available solution evidence.
- Display recorded mathematical solver, formalization authors and other contributors only where grounded in sources.
- Display the official catalog mathematical status, Lean status, eligibility and claim metadata independently.
- Display matching official PRs and Issues with canonical links, current captured state, submission type and observation timestamp.
- Distinguish exact JSP-ID matches from reviewed aliases and supplementary uncertain title matches.
- Display source-linked external Lean repositories with pinned commit, branch, file and theorem identity where available.
- Display claimed, partial, reproduced and independently verified proof evidence separately.
- Show evidence of statement fidelity, build reproduction, axiom audit and placeholders when independently recorded.
- Allow the user to open external PRs and proof-source links for subsequent targeted Codex investigation.
- Do not automatically download, execute, install or certify external Lean code from the dashboard.
- Display captured candidate and announced-award information with source links and review dates.
- Preserve unknown payment information as unknown.
- Display the exact reason for candidate inclusion, exclusion, ranking or unresolved evidence.

**Freshness and uncertainty**

- Display the vendor source SHA and the time of the latest successful evidence acquisition.
- Display independent acquisition freshness for GitHub PR/Issue evidence and official award registers.
- Make stale, incomplete, unknown and contested evidence visibly distinguishable.
- Never convert missing data into a positive or negative mathematical conclusion.
- Do not present an old complete capture as current merely because the HTML page was regenerated today.
- Never present a blank PR/Issue list as proof of no competitors unless the relevant acquisition scope supports that conclusion.
- Preserve the version 1 historical Assessment compatibility contract.
- Treat the complete current version 2 evidence contract as the authoritative source for new negative competition findings.

**Documentation**

- Document the three stable CLI commands and the output directory.
- Document the boundary between vendor synchronization and live discovery refresh.
- Explain the generated HTML, JSON and CSV artifacts.
- Explain how to inspect PR evidence and launch a separate targeted Codex proof investigation.
- Update the existing architectural description so `start.sh` is recognized as a user-facing CLI launcher rather than a long-running application runtime.
- Keep the project independent of a web server, database and background service.

#### Excluded

- Rewriting or replacing Scanner and Assessment.
- A second competition crawler.
- New database, REST API, web server, hosted application or SaaS runtime.
- React, Next.js, Vue, Node.js or frontend build tooling.
- Generic UI component framework or dashboard platform.
- Automatic execution or downloading of arbitrary third-party Lean proofs.
- Automatic mathematical proof verification from PR descriptions.
- Automatic Codex execution when clicking problem links.
- Automatic official JSP submissions, claim applications or award processing.
- Automated Git commits, pushes, vendor merges or changes to GitHub permissions.
- Automatic mutation of managed JSP vendor files during discovery refresh.
- Historical bounty amounts presented as current payable JSP rewards.
- Numeric prize predictions without sufficient official evidence.
- Reimplementing deterministic selection, proof classification or official award normalization.
- New runtime dependencies without demonstrated necessity.
- Changes to existing Lean proofs, including JSP-000089.
- Unrelated repository refactors or speculative runtime architecture.

#### Deliverable

A local, offline-viewable BeeJSP Discovery Dashboard supported by one-command refresh and stable CLI entry points.

The user runs:

```bash
./start.sh update
```

BeeJSP then uses the approved local catalog snapshot, refreshes live public evidence, rebuilds the existing selection outputs, generates a standalone HTML dashboard and opens it when the local environment supports browser launching.

The dashboard provides a searchable overview of the complete JSP catalog and detailed per-problem evidence, including mathematical sources, recorded Lean status, competing Issues/PRs, external proof references, candidate and award records, and uncertainty.

The user may also run:

```bash
./start.sh report
./start.sh inspect JSP-000161
```

without refreshing public data.

The implementation is a small presentation and orchestration layer over Iteration 6, not a new application platform.

#### Acceptance criteria

**CLI and update workflow**

- `./start.sh update` is the documented primary command.
- The command resolves repository paths reliably and does not depend on invocation from the repository root.
- It invokes existing Scanner, capture and Assessment behavior rather than duplicating their logic.
- It generates validated JSON, CSV and HTML outputs from the approved data sources.
- It opens the HTML report in an available graphical desktop environment without making browser availability a requirement for successful data generation.
- `./start.sh report` opens the last valid HTML report without network access.
- `./start.sh inspect JSP-XXXXXX` provides offline inspection of an exact JSP ID.
- Invalid JSP IDs and missing required saved evidence produce clear nonzero failures.
- Refresh acquisition failures are reported clearly and cannot be misrepresented as successful current acquisition.
- Incomplete network results never overwrite the last complete competition evidence as if they were complete.
- The vendor snapshot is not modified by the update command.
- No Git branches, commits, upstream PRs or GitHub write operations are modified by these commands.

**Dashboard coverage**

- The generated dashboard contains all valid normalized records from the current selected vendor snapshot.
- The current 1,022-record snapshot is covered by an explicit integration test.
- Overview counts agree with the corresponding validated JSON inputs.
- Search and filters operate locally in the browser.
- Candidate table sorting is stable and preserves exact JSP identities.
- Every row includes a usable path to detailed inspection.
- General and high-value machine-readable selections and per-problem reasons use existing profile semantics; the HTML overview has no profile selector.
- Unknown research values remain visible rather than silently becoming low difficulty or zero scientific value.
- Contested candidates remain inspectable regardless of their ranking.

**Mathematical and competition evidence**

- Problem descriptions and mathematical source references come from the official catalog or explicitly reviewed evidence.
- Available solver and formalizer attribution is preserved without guessing authorship.
- Official mathematical status and recorded Lean status remain distinct from current external proof classifications.
- PRs and Issues remain separate and retain source links, state and observation timestamp.
- Exact-ID matches, reviewed aliases and uncertain matches remain distinguishable.
- Source-linked complete-proof claims remain contested unless independently verified.
- Closed-unmerged PRs remain historical evidence rather than automatic proof failures.
- A positive competing observation is retained even when capture completeness is insufficient.
- Missing competition observations under insufficient coverage produce `UNKNOWN`, not `NONE_IN_SCOPE`.
- JSP-000161, JSP-000475 and JSP-000089 retain the established Iteration 6 regression semantics.

**Awards and value**

- Historical bounties, official announced awards, published monetary amounts and qualitative prize potential remain separate.
- Public candidate registration is not displayed as confirmed award payment.
- Solver and Lean formalizer roles remain separate.
- Unknown official amounts remain unknown.
- All known award values and levels retain their supporting official evidence URLs.
- The dashboard does not invent future payout amounts, probabilities or guarantees.

**Security and reproducibility**

- Untrusted titles, descriptions, citations and contributor fields cannot inject active HTML or JavaScript into the report.
- External links use validated destinations and safe link attributes.
- Generated HTML contains no external JavaScript or CDN dependency.
- Saved-input report generation works without network access.
- Equivalent saved inputs produce deterministic report content except for explicitly justified generated-at metadata.
- Generated artifacts do not create accidental tracked repository changes.
- Existing version 1 and version 2 Scanner/Assessment tests remain green.
- No new external-proof execution boundary or GitHub write permissions are introduced; the approved clarification permits optional local read-only GitHub authentication, with no credentials in artifacts.
- The existing JSP vendor synchronization and daily PR workflow remain unchanged.

#### Checks

```text
start.sh command dispatch tests
update orchestration tests
offline report and inspect tests
repository-root and external-working-directory tests
headless browser behavior tests
missing evidence and invalid JSP-ID tests
complete 1,022-record dashboard fixture
HTML escaping and script-injection tests
safe external-link tests
local search/filter data integrity tests
JSON/CSV/HTML source consistency tests
general and high-value profile regression
competition freshness and failure-path tests
legacy v1 incomplete-coverage regression
version 2 complete-scope regression
JSP-000161 / PR #1248 regression
JSP-000475 / PR #1269 regression
JSP-000089 historical competition regression
generated-output path and overwrite safety
vendor provenance and unchanged-content check
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
uv build where package behavior is affected
package import smoke where applicable
git diff --check
security review
SAST for untrusted data and HTML generation
SCA only if dependencies actually change
independent final read-only review
```

#### DoD

BeeJSP provides one convenient entry point for refreshing and exploring mathematical formalization opportunities.

A single `./start.sh update` command generates an offline HTML dashboard with the complete normalized JSP problem bank, source-linked problem details, current captured PR/Issue and award evidence, clear competition uncertainty, and corresponding reproducible JSON/CSV outputs.

The `report` and `inspect` commands work without a network refresh.

The dashboard remains a small local presentation layer over the existing deterministic Scanner and Assessment. Use `update` for a full GitHub refresh and `report` for offline viewing. Refresh manually each day during active research and before important proof/submission decisions; this iteration adds no scheduler.

No server, database, speculative framework, automatic prize claim or external Lean execution is introduced.

The iteration is complete when the CLI, dashboard, error handling, security checks, documentation and full Python regression suite pass independently.

---

## Stage 5 — Second complete mathematical formalization

### Purpose of stage

Complete a second substantial mathematical formalization by applying the source-audit, proof-dependency, milestone-loop and reproducibility lessons from JSP-000089 to JSP-000334.

This stage prioritizes mathematical correctness and proof progress over additional discovery infrastructure. It reuses the existing BeeJSP Lean project boundary, source-of-truth hierarchy, proof-loop skill and independent verification workflow.

Stage 5 contains Iteration 8. Preparation, mathematical feasibility, proof construction, correction and final independent verification belong to the same iteration.

### Iteration 8 — Complete JSP-000334 Lean Formalization

**Status:** PLANNED

#### Goal

Produce a complete, source-faithful, independently reviewable and reproducible Lean formalization of JSP-000334, corresponding to Erdős Problem #407 and Newman's conjecture on representations of integers as sums of powers of two, powers of three and their products.

The principal theorem must establish the complete mathematical content of the approved original problem. A bounded spike, partial source theorem, numerical experiment or weaker representation-count statement does not constitute completion.

Iteration 8 remains in progress through successive mathematical milestones until the principal Lean proof and required verification gates are complete. A genuine unresolved mathematical or source-level blocker must be recorded explicitly rather than bypassed with a weaker statement or unsupported completion claim.

#### Scope

Included:

**Mathematical sources and problem identity**

- review the exact JSP-000334 record and original Erdős/Newman problem identity;
- obtain and reconcile the original mathematical formulation, publication history and solution attribution;
- inspect the complete Tijdeman–Wang 1988 paper and its published correction;
- obtain and review the Evertse–Győry–Stewart–Tijdeman 1988 source as an original resolution of the boundedness problem;
- reconcile the Bajpai–Bennett 2023 preprint with the final 2024 Acta Arithmetica publication;
- identify source corrections, unstated hypotheses, omitted computations and dependencies on external theorems;
- record authoritative URLs, source editions, theorem numbers, relevant page ranges and source-file hashes;
- identify supplementary mathematical or computational evidence required by the selected proof route;
- preserve the distinction between the original boundedness question and stronger later quantitative results.

**Statement fidelity**

- establish the exact representation equation, exponent domains and quantifier structure;
- distinguish ordered exponent tuples from representations identified by equal multisets of summands;
- formally establish any conversion between these counting conventions used by the principal theorem;
- select and document a mathematically justified source-to-Lean proof route;
- prepare an inspectable Lean principal statement before large proof implementation;
- preserve the full domain, all boundary cases and the intended universal boundedness conclusion;
- prohibit silent strengthening of hypotheses, restriction to convenient subclasses or substitution of finite examples for the general theorem.

**Competing formalizations**

- refresh official PR and Issue evidence for JSP-000334 before full proof work and external submission preparation;
- inspect the relevant claimed Lean sources associated with PRs #720, #1677, #2000 and #2731;
- distinguish original proof claims, partial formalizations, duplicate repositories, source-linked evidence and independent verification;
- compare competing Lean statements with the exact JSP-000334 mathematical scope;
- preserve source authorship, mathematical solver attribution, formalizer attribution and verification provenance;
- avoid treating open PRs as accepted mathematics or closed-unmerged PRs as proof of mathematical invalidity;
- execute third-party proof projects only under an explicitly approved isolation and verification boundary.

**Lean proof project and dependencies**

- create one isolated `proofs/JSP-000334/` Lean project;
- pin Lean, Mathlib and all necessary proof dependencies;
- document the exact theorem, mathematical sources, provenance and proof architecture;
- construct a source-to-Lean dependency graph before substantial implementation;
- identify existing Mathlib definitions and theorems by actual pinned source references;
- distinguish routine local helper lemmas from missing substantial mathematical prerequisites;
- perform a bounded feasibility spike on the highest-risk prerequisite;
- record a source-grounded GO, CONDITIONAL GO or NO-GO for the selected proof route;
- resolve material route blockers before claiming progress toward the complete principal theorem.

**Complete formalization**

- implement all mathematical definitions, supporting lemmas and source theorem bridges necessary for the approved principal statement;
- use existing Mathlib definitions and results where mathematically appropriate;
- formalize required number-theoretic and Diophantine arguments without replacing them with unjustified assumptions;
- reproduce any finite computation or exhaustive case analysis relied upon by the final proof using independently checkable Lean evidence;
- distinguish exploratory computation from kernel-checked mathematical proof;
- develop the proof through substantial mathematical milestones, each with supporting local helpers and verification evidence;
- maintain a structured proof ledger recording completed declarations, exact unresolved Lean goals, rejected approaches and the next mathematical obligation;
- reuse prior verified results and avoid repeatedly attempting known-invalid proof approaches;
- complete every branch required by the original theorem;
- assemble one clearly identified principal Lean theorem proving the exact approved JSP-000334 statement.

**Proof-loop and verification discipline**

- use the existing `beejsp-proof-loop` skill for successive Codex implementation passes;
- perform source audit and dependency planning before expensive proof implementation;
- make one coherent mathematical milestone the unit of an ordinary executor pass;
- use the previous structured executor report and proof ledger as the normal handoff to the next pass;
- compile after substantial coherent proof changes and perform required checks at milestone boundaries;
- use BeeMCP checkpoints for suspicious blockers, contradictory reports, repeated lack of mathematical progress, substantial proof transitions and final review;
- avoid requiring full independent repository review after every routine helper;
- record exact source-to-Lean correspondence and explicit verification results;
- complete a full Lean build, principal theorem audit, forbidden-shortcut scan, axiom review and clean reproduction;
- complete independent final statement, proof, source and provenance verification.

#### Excluded

- declaring Iteration 8 complete after only mathematical research or a feasibility spike;
- replacing the exact JSP-000334 theorem with a finite computational sample or weaker special case;
- treating the stronger quantitative bounds of a later paper as automatically equivalent to the original counting convention;
- using an incorrect, uncorrected or insufficiently reconciled mathematical source as authoritative proof evidence;
- treating an unpublished or unverified competing formalization as an accepted complete proof;
- depending on unreviewed external Lean code, arbitrary remote execution or hidden mathematical assumptions;
- introducing `sorry`, `admit`, custom unproved axioms or equivalent proof shortcuts into completion evidence;
- copying unused architecture or unrelated proof code from JSP-000089;
- changing the already verified JSP-000089 principal statement or proof;
- modifying managed JSP vendor content by hand;
- unrelated changes to the Scanner, Discovery Dashboard, GitHub authentication or assessment contracts;
- creating a new generic AI-agent framework, hosted proof service, database, web interface or generalized theorem-proving platform;
- official JSP submission, candidate registration, award claims, entitlement assertions or payment processing as implementation deliverables;
- unapproved package, dependency, version or repository infrastructure changes.

#### Deliverable

One complete BeeJSP-owned Lean formalization of JSP-000334, supported by an auditable mathematical source package, exact formal statement, proof dependency graph, structured milestone ledger, pinned Lean environment and reproducible verification evidence.

The deliverable includes:

- exact original problem and statement-fidelity documentation;
- authoritative mathematical source and correction inventory;
- competing formalization and attribution audit;
- source-to-Lean mathematical dependency map;
- verified principal Lean theorem and supporting proof modules;
- reproducible build and principal-theorem axiom audit;
- independent final source, statement and proof verification report.

The final proof must remain understandable and reproducible independently of the development conversation and executor history.

#### Acceptance criteria

**Source correctness**

- The exact original JSP-000334 mathematical problem and its source identity are recorded.
- The selected mathematical proof route is supported by complete, appropriately authoritative sources.
- The Tijdeman–Wang correction is incorporated into every affected mathematical argument.
- The Bajpai–Bennett preprint and published-version relationship is explicitly reconciled before relying on version-sensitive statements.
- External source results and computations required by the principal proof are either independently justified, formalized or supported by an approved verified dependency.
- Missing source details are reported as unresolved obligations, not silently replaced with assumptions.
- Mathematical authorship and formalization authorship remain distinct.

**Statement fidelity**

- The principal Lean statement faithfully preserves the original representation-counting problem.
- Exponent domains, quantifiers, arithmetic operations, finiteness conditions and exceptional cases are exact.
- Ordered exponent tuples and unordered summand-multiset counts are distinguished and related by proved lemmas wherever necessary.
- The principal result is not restricted to finitely many integers or a convenient subclass unless the original mathematical statement itself requires that restriction.
- Stronger quantitative bounds may be established, but their relation to the original theorem must be explicitly proved.
- Principal statement changes after approval require mathematical justification and renewed statement review.

**Dependency and feasibility evidence**

- The mathematical dependency graph covers every substantial source theorem needed by the selected proof route.
- Existing Mathlib dependencies are identified against the actual pinned version.
- Major missing mathematical prerequisites are distinguished from routine local helper lemmas.
- The highest-risk prerequisite is investigated through a meaningful bounded Lean spike.
- The feasibility decision is supported by mathematical and Lean evidence rather than source metadata or apparent code volume.
- An unresolved major prerequisite cannot be marked complete merely because surrounding helper files compile.

**Complete proof**

- Every required mathematical case and source dependency of the approved principal theorem is discharged.
- The principal theorem is identified by its exact Lean declaration and complete statement.
- All proof modules build successfully in the pinned environment.
- No `sorry`, `admit`, placeholder axiom or unapproved proof shortcut remains in the principal theorem's dependency closure.
- The final theorem's axiom dependencies are explicitly audited.
- External proof computations needed for completeness are represented by checkable certificates, proved finite procedures or another approved sound verification mechanism.
- Supporting theorems establish the mathematical facts required by the principal theorem rather than easier unrelated statements.
- Successful Lean compilation is supplemented by independent statement-fidelity and source-mathematics review.

**Milestone continuity**

- Every substantial milestone identifies its completed Lean declarations and remaining mathematical obligations.
- The proof ledger records failed approaches, exact blockers and subsequent corrections without misrepresenting exploratory results as completed proofs.
- Executor reports contain concrete build, audit and source-change evidence.
- Verification checkpoints follow the existing proof-loop skill.
- Repeated stalled passes trigger mathematical diagnosis rather than uncontrolled helper accumulation.
- The work remains part of Iteration 8 until the principal proof and required final verification are complete.

**Provenance, competition and reproducibility**

- Current competing claims are inspected with their source links, states and relevant proof scope.
- Independent verification is not inferred from PR state or submitter claims.
- The project pins its Lean toolchain and dependency revisions.
- Clean reproduction succeeds without undocumented local patches or hidden source files.
- Mathematical solver, Lean formalizer and independent verifier contributions are accurately attributed.
- Protected vendor content, prior completed proofs and unrelated repository contracts remain unchanged.
- Local proof completion does not assert official JSP acceptance, priority, candidate status, an award or payment.

#### Checks

```text
exact JSP-000334 identity and source review
original Newman/Erdős statement reconciliation
Tijdeman–Wang original paper and published correction review
Evertse–Győry–Stewart–Tijdeman source review
Bajpai–Bennett preprint and published-version comparison
source URL, version, theorem number and SHA-256 inventory
competition PR/source audit
ordered-tuple versus summand-multiset statement audit
source-to-Lean dependency graph review
pinned Mathlib API inspection
highest-risk mathematical prerequisite spike
milestone-by-milestone lake env lean checks
lake build
principal theorem statement inspection
all mathematical cases and source-lemma coverage
sorry/admit and unproved-placeholder scan
principal theorem axiom audit
dependency and toolchain pin review
finite computation and certificate soundness review where applicable
clean Lean project reproduction
mathematical solver and formalizer attribution review
source-to-Lean provenance review
protected-file and unrelated-change inspection
git diff --check
applicable Python tests only if Python behavior changes
applicable security and dependency verification
independent final read-only review
```

#### DoD

BeeJSP contains one complete, source-faithful Lean formalization of JSP-000334 establishing the approved original mathematical theorem for all required inputs.

The principal theorem has no unresolved mathematical branches, unproved placeholders, hidden axioms, unjustified external computation or undocumented dependencies.

Its correspondence to the authoritative original problem and selected corrected mathematical sources is independently reviewed.

The complete proof reproduces under the pinned Lean and Mathlib environment, passes principal-theorem axiom inspection and preserves accurate provenance and attribution.

The milestone ledger and source-to-Lean mapping make the proof understandable and reproducible without reconstructing the full AI-assisted development conversation.

Iteration 8 is not DONE merely because its source audit, bounded spike, preliminary lemmas or a weaker quantitative theorem have been completed. Such results are intermediate milestones under the same iteration.

Official JSP acceptance, candidate registration, claim eligibility and award payment remain separate external processes.

The iteration is complete only when the entire approved principal theorem and independent final verification satisfy the acceptance criteria. No additional numbered proof-completion iteration is required.

## Post-Iteration 7 operational discovery gate

Iteration 6 establishes:

```text
pinned official catalog
→ normalized complete problem-bank records
→ current scoped competition and award evidence
→ independent classification of external proof claims
→ configurable selection profiles
→ reproducible candidate reports
→ targeted mathematical and Lean feasibility preflight
```

Before starting the next full formalization, the selected candidate should have an exact original statement, a reviewed complete mathematical source or explicit research gap, reviewed competition risks, a bounded hardest-lemma spike and an approved GO decision.

A high scientific-value estimate cannot waive source review or Lean feasibility. A score must not hide uncertainty. Not every external proof must be executed during mass screening; targeted isolated verification is a separate authorized research activity.

## Post-first-submission orientation

**Status:** FUTURE / orientation

Possible future work includes selecting a second JSP theorem, checking reusable Lean helpers across real proofs, improving reproduction automation, accepting community formalization contributions, expanding verified problem corpora or supporting additional mathematical sources only when actual repeated work establishes necessity.

Further numbered iterations beyond Iteration 7 require independently justified scope and approval.

### Related external boundary — The Justin Sun Prize

The official JSP repository supplies problem records, submission rules, verification requirements, candidate and award records and the claim process. BeeJSP observes these sources but does not control official status.

### Related project boundary — BeeMCP

BeeMCP remains a planning, development and read-only review tool. It is not a runtime or proof dependency of BeeJSP.

### Future roadmap rule

```text
real mathematical or tooling gap
→ evidence
→ necessity and ownership decision
→ roadmap item
→ approved Issue
→ implementation
→ independent verification
→ PR
```

The correct next step may require no architectural change at all: select a candidate, create a focused formalization Issue, prove it and publish independently verified evidence.

### Related process documents

- `docs/ARCHITECTURE.md` — architecture, ownership and repository boundaries;
- `docs/DEV_GUIDE.md` — local development and tooling instructions;
- `docs/FORMALIZATION.md` — exact mathematical statements, proofs, axioms, attribution and evidence;
- `docs/SECURITY.md` — trust, external input, permissions and privacy;
- `docs/SUBMISSION.md` — official JSP process and submission gates;
- `AGENTS.md` — repository-wide development and agent guidance.

### Summary

```text
build only enough tooling
→ identify a useful mathematical problem
→ inspect competition and proof evidence
→ test mathematical and Lean feasibility
→ prove the exact theorem
→ independently verify it
→ publish immutable evidence
→ submit where appropriate
→ improve the process from actual findings
```

Not:

```text
build a platform
→ add agents and dashboards
→ automate awards
→ eventually attempt real mathematics
```

BeeJSP must remain small, mathematically faithful, machine-checked, evidence-aware, reproducible, correctly attributed and honest about uncertainty.
