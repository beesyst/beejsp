# AGENTS.md — BeeJSP repository guidance

## Purpose

This file contains stable repository-wide rules for AI agents working with
`beejsp`.

Task-specific requirements belong in the approved Issue.

Detailed workflows belong in `.agents/skills/`.

Prompts should normally contain only:

- selected workflow;
- exact target information;
- approved Issue;
- implementation or verification evidence;
- task-specific constraints.

BeeJSP is an open-source project for producing, verifying and publishing
reproducible machine-checked mathematical results.

Its primary responsibilities are:

- mathematical-problem discovery and screening tooling;
- exact Lean formalization;
- reproducible proof verification;
- proof provenance and attribution;
- managed local reference material for supported external contribution and
  submission systems.

The Justin Sun Prize is a supported discovery, verification and submission
channel.

It is not the purpose of BeeJSP itself.

## Instruction precedence

Use this order:

1. Current explicit task instructions and approved Issue.
2. This `AGENTS.md`.
3. Selected repository skill.
4. Current repository contracts and documentation.
5. Managed external reference material where applicable.
6. Implementation reports and previous comments as supporting evidence only.

The actual target worktree, current files, diff, tests, package metadata, proof
contents, vendor provenance and verification evidence take precedence over stale
reports.

For official external-process facts, current official upstream material takes
precedence over stale local assumptions or snapshots.

When instructions materially conflict, stop and report the conflict.

## Agent role separation

Tool, authority and read-only restrictions apply only to the current task and
agent.

When producing a prompt for another agent, do not copy the current agent's tool
restrictions unless they are explicitly required for that executor.

Planning, prompt-preparation and final-review tasks may use Bee Dev MCP in
read-only mode.

Implementation and correction prompts are executed by Copilot or Codex.

They must instruct the executor to work in the exact local worktree using its
available repository tools.

They must not require:

- Bee Dev MCP;
- MCP target identifiers;
- MCP Mode;
- review mode;
- read-only behavior.

Canonical workflow:

```text
planning
→ approved Issue
→ implementation
→ independent verification and correction
→ final read-only review
→ commit / push / PR
```

Do not create separate agent workflows for:

- Lean formalization;
- JSP submission;
- vendor synchronization.

Those activities use the same canonical workflow with the applicable repository
contracts and upstream reference material.

## Bee Dev MCP rules

These rules apply only when the current task explicitly selects Bee Dev MCP for
read-only planning, prompt preparation or review.

Bee Dev MCP is read-only.

Available Bee Dev MCP tools include:

- `list_projects`;
- `list_worktrees`;
- `get_project_context`;
- `get_review_manifest`;
- `get_review_bundle_page`;
- `get_review_bundle` — compatibility only;
- `read_project_file`;
- `search_project`;
- `get_github_context`.

Do not refer to nonexistent tools such as `get_file`.

Use:

- `get_review_manifest`;
- `get_review_bundle_page`;

for complete reviews.

Do not repeatedly call `get_review_bundle` expecting pagination.

### GitHub context resolution

When any supplied input contains a supported GitHub Issue or Pull Request URL,
call `get_github_context` before interpreting that input.

For an Issue, read and consider:

- title;
- body;
- all available Issue comments.

For a Pull Request, read and consider:

- title;
- body;
- all available conversation comments;
- reviews;
- inline review comments.

A GitHub URL is an instruction to load its complete available context, not
merely a reference to include in output.

When pasted content and a GitHub URL are supplied together, consider both.

If they materially conflict, report the conflict instead of silently choosing
one.

Comments provide context and do not automatically expand approved scope.

Explicit accepted clarifications may refine the Issue or PR contract.

If mandatory GitHub context is unavailable, incomplete or reported as
truncated, return the applicable incomplete-workflow result instead of
proceeding from partial context.

### Exact target resolution

Before planning or review:

1. call `list_worktrees`;
2. match the requested worktree by exact `path`;
3. use the returned MCP `target`;
4. call `get_project_context`;
5. verify project, path, branch, HEAD and dirty state.

For final review, verify the expected base branch from the complete review
manifest.

Do not infer a target from a branch name.

Do not substitute the main worktree for a requested feature worktree.

### Complete reading

Repository inspection is incomplete while required data is:

- paginated;
- truncated;
- omitted;
- accompanied by continuation metadata.

For manifests and diffs, continue with the exact `next_cursor` while
`has_more=true`.

For files, continue with the exact `next_line` and `next_column` until both are
null.

Read required files listed under `omitted_files` or `related_omitted_files`
directly with `read_project_file`.

Treat `truncated=true` as incomplete review data.

Failure to retrieve mandatory MCP data is not a code defect.

When mandatory final-review inspection cannot be completed, return:

```text
REVIEW INCOMPLETE
```

Do not return `CHANGES REQUIRED` solely because MCP inspection is incomplete.

## Mandatory reading

Read documents required by the selected skill.

Common documents include:

- `AGENTS.md`;
- approved Issue;
- relevant `docs/ROADMAP.md` section;
- `docs/SECURITY.md`;
- `docs/DEV_GUIDE.md`;
- `README.md`.

When relevant, also read:

- `docs/ARCHITECTURE.md`;
- `docs/FORMALIZATION.md`;
- `docs/SUBMISSION.md`;
- `pyproject.toml`;
- BeeJSP Python implementation;
- relevant Lean proof project;
- vendor synchronization implementation;
- relevant managed upstream reference files.

For Lean verification procedures, use the managed upstream skill when
applicable:

```text
docs/vendor/jsp/skills/lean-verify/SKILL.md
```

Do not copy that procedure into BeeJSP agent skills.

ROADMAP status does not prove implementation.

Compare roadmap claims with current:

- code;
- contracts;
- tests;
- package metadata;
- proof contents;
- vendor provenance;
- verification evidence.

## Project boundary

BeeJSP supports this project flow:

```text
mathematical problem/source
→ evidence-based discovery and assessment
→ exact formal statement
→ complete Lean proof
→ reproducible verification
→ public reusable evidence
→ optional external contribution/submission
```

Core principle:

```text
Useful mathematical work first.
Machine-checkable and reproducible evidence before claims.
```

BeeJSP is not primarily:

- a generic theorem generator;
- a generic AI research agent;
- a prize-farming bot;
- a web application;
- a hosted SaaS;
- a generic workflow engine;
- a database platform;
- an automated award-claim bot.

Do not expand the project into adjacent categories without an approved project
and roadmap decision.

## Architecture boundary

Canonical responsibility direction:

```text
official/public mathematical sources
→ BeeJSP research/tooling
→ BeeJSP Lean formalizations
→ reproducible verification evidence
→ optional external contribution/submission
```

### BeeJSP Python tooling owns

- problem-bank ingestion;
- parsing and normalization;
- candidate discovery;
- deterministic filtering and scoring where defined;
- external-state reads where explicitly implemented;
- generated reports;
- local project automation;
- vendor synchronization tooling.

### BeeJSP Lean projects own

- exact formal statements;
- formal definitions required by the proof;
- complete machine-checked proofs;
- proof-local lemmas;
- pinned Lean toolchain;
- pinned proof dependencies;
- reproducibility metadata;
- proof verification evidence.

### Managed upstream snapshot

Canonical managed directory:

```text
docs/vendor/jsp/
```

It is a generated read-only snapshot of selected official upstream material.

It exists for:

- reproducible local reference;
- planning;
- discovery/scanner input;
- verification guidance;
- contribution/submission guidance.

It is not:

- a fork;
- a submodule;
- live GitHub state;
- a second authoritative upstream repository.

### Official upstream owns

Official upstream owns its own current:

- problem records;
- contribution rules;
- verification rules;
- candidate or award records;
- claim process;
- repository state.

BeeJSP must not redefine those facts as independent local truth.

## Architecture prohibitions

Do not:

- turn BeeJSP into a daemon or web service without approved need;
- add generic runtime orchestration without approved need;
- add a database merely for future scale;
- add a generic theorem-prover abstraction before a proven need;
- add a generic plugin/provider framework without current use;
- create a second manually maintained copy of official upstream truth;
- manually edit generated vendor content;
- treat successful compilation as proof of statement fidelity;
- weaken mathematical statements for implementation convenience;
- attribute another person's mathematical result to BeeJSP;
- claim official acceptance, priority, candidate or award status without
  evidence;
- introduce speculative abstractions without demonstrated project need.

## Dependency direction

BeeJSP's Python tooling and Lean proof projects are separate layers.

Python tooling must not become a hidden prerequisite for checking a Lean proof
unless the proof project explicitly and reproducibly requires it.

Each real proof under:

```text
proofs/JSP-XXXXXX/
```

should remain independently reproducible according to its committed toolchain
and dependency metadata.

The managed upstream snapshot is reference/input data, not a runtime library.

A related repository is not an implementation target unless the approved Issue
explicitly assigns changes to it.

## Sources of truth

Use:

- package metadata and Python package version:
  - `pyproject.toml`;

- Python dependencies:
  - `pyproject.toml`;

- resolved Python development environment:
  - `uv.lock`;

- BeeJSP Python implementation:
  - `src/beejsp/`;

- Lean proof implementation:
  - `proofs/`;

- architecture:
  - `docs/ARCHITECTURE.md`;

- development guidance:
  - `docs/DEV_GUIDE.md`;

- formalization contract:
  - `docs/FORMALIZATION.md`;

- security and trust boundaries:
  - `docs/SECURITY.md`;

- submission/contribution workflow:
  - `docs/SUBMISSION.md`;

- iteration scope:
  - approved Issue aligned with `docs/ROADMAP.md`;

- managed official reference snapshot:
  - `docs/vendor/jsp/`;

- vendored provenance:
  - `docs/vendor/jsp/UPSTREAM_REF`;
  - `docs/vendor/jsp/UPSTREAM_COMMIT`;

- current implementation evidence:
  - tests;
  - proof builds;
  - axiom audits;
  - deterministic generated evidence;
  - supplied current external-state evidence where required.

Rules:

- no hidden defaults for required behavior;
- no duplicate source of truth;
- package metadata must remain internally consistent;
- formal statements are compatibility and evidence surfaces;
- proof provenance is evidence;
- compilation alone is not statement-fidelity evidence;
- vendor snapshots are not live external state;
- preserve compatibility unless the approved Issue explicitly permits a
  breaking change.

## First-party package initializers

All first-party Python `__init__.py` files should remain byte-empty unless an
approved public-package contract explicitly requires otherwise.

Do not place:

- imports or re-exports;
- `__all__`;
- version constants;
- registration;
- initialization logic;
- side effects;
- package metadata;

in `src/beejsp/__init__.py`.

Stable public imports should use explicit public modules.

## Change classification

Use these repository-wide change levels.

### low-risk

Typical examples:

- documentation;
- agent guidance;
- narrow tests;
- metadata changes without executable behavior;
- explicitly approved non-behavioral cleanup.

### runtime-risk

Typical examples:

- Python parser/scanner behavior;
- scoring or filtering logic;
- report generation;
- shell scripts;
- CI behavior;
- vendor synchronization;
- network/API reads;
- package/public behavior.

### security-sensitive

Typical examples:

- credential or token handling;
- externally controlled filesystem paths;
- execution of downloaded or external code;
- shell commands constructed from untrusted values;
- external write operations;
- GitHub write automation;
- dependency additions materially expanding execution surface.

Additionally mark a task:

```text
formalization-sensitive
```

when it changes:

- Lean statements;
- Lean proofs;
- theorem scope;
- mathematical assumptions;
- proof dependencies;
- proof provenance;
- formalization attribution;
- axiom-audit behavior;
- submission evidence for a formalization.

Formalization sensitivity adds proof-specific verification requirements.

It does not replace the normal change level.

## Implementation rules

- Stay inside the approved Issue.
- Prefer the smallest complete solution.
- Follow KISS.
- Do not perform unrelated refactoring.
- Do not add speculative architecture.
- Reuse existing contracts and implementation before creating new abstractions.
- Do not duplicate existing contracts or logic.
- Do not create generic frameworks for future theorem classes, providers or
  integrations without demonstrated current need.
- Follow PEP 8 for Python.
- Keep public identifiers, generated data fields and documentation in English.
- Treat external values as untrusted.
- Preserve deterministic behavior where required by contract.
- Preserve reproducibility where required by contract.
- Fail closed when required provenance or verification evidence is missing or
  invalid.
- Do not change `pyproject.toml.version` for ordinary feature, fix, docs or
  chore work.

The correct solution may be:

```text
no change
```

when current implementation already satisfies the requirement.

## KISS rules

Do not add functionality only because it may be useful later.

Examples of speculative scope requiring explicit evidence and approval:

- server runtime;
- web UI;
- database;
- generic plugin framework;
- generic theorem-prover abstraction;
- hosted runner fleet;
- autonomous research agent;
- automated award-claim system;
- generalized submission framework for unrelated competitions.

## Managed upstream vendor rules

Canonical managed directory:

```text
docs/vendor/jsp/
```

Canonical synchronization entrypoint:

```text
scripts/sync_jsp_docs.sh
```

The managed directory is generated content.

Do not edit it manually.

Every valid snapshot must preserve:

```text
UPSTREAM_REF
UPSTREAM_COMMIT
```

where `UPSTREAM_COMMIT` identifies the exact resolved upstream revision.

Synchronization must be safe, complete and reproducible.

At minimum it must:

- use the configured official upstream source;
- stage replacement content before activating it;
- validate required content before replacement;
- fail rather than publish an incomplete snapshot;
- remove stale managed content;
- preserve required attribution and licensing;
- remain idempotent for the same upstream revision.

A failed synchronization must not leave partial content represented as a valid
current snapshot.

The managed snapshot does not establish current live:

- Pull Request state;
- Issue discussion;
- repository competition;
- external competing work;
- award or payment state.

When a task materially depends on current upstream state, obtain current
evidence separately or refresh the snapshot through the approved synchronization
flow as required by the task.

Detailed synchronization behavior belongs in the implementation, tests and
applicable documentation.

Do not duplicate it in agent skills.

## Formalization boundary

The canonical BeeJSP formalization contract is:

```text
docs/FORMALIZATION.md
```

That document owns detailed formalization requirements.

Repository-wide invariants are:

- identify the exact source problem;
- preserve statement fidelity;
- preserve source mathematical attribution;
- do not weaken a theorem for implementation convenience;
- do not use `sorry` or `admit` for a completed proof;
- do not replace missing mathematics with a custom unproved axiom;
- preserve reproducible Lean toolchain and dependency metadata;
- verify formalization-sensitive changes with the checks required by the
  formalization contract;
- distinguish mathematical authorship from Lean formalization and independent
  verification.

Successful Lean compilation is necessary evidence for a completed proof.

It is not sufficient evidence that the intended mathematical statement was
formalized faithfully.

When applicable, detailed Lean verification procedure comes from:

```text
docs/vendor/jsp/skills/lean-verify/SKILL.md
```

Do not create a duplicate local BeeJSP `lean-verify` skill.

## Submission boundary

The canonical BeeJSP submission/contribution runbook is:

```text
docs/SUBMISSION.md
```

That document owns detailed submission preparation.

Relevant official upstream rules are read from the managed upstream reference
material when applicable.

Submission preparation uses the same normal BeeJSP workflow.

Do not create a separate submission agent workflow.

Repository-wide invariants are:

- proof and provenance evidence must be complete before preparing a submission;
- current official process requirements must be verified when material;
- vendor snapshots must not be treated as live external state;
- vendored records must not be manually modified to represent a submission;
- no official acceptance, priority, candidate, award or payment claim may be
  made without supporting evidence.

Normal BeeJSP implementation and review workflows do not:

- commit;
- push;
- create external Pull Requests;
- merge;
- submit award claims;

unless an explicit approved workflow changes those rules.

They may prepare reviewed, copy-ready evidence or submission material for the
user or authorized tooling.

## Documentation and contracts

Update relevant documentation when implementation changes:

- Python package/public behavior;
- parser/scanner/report contracts;
- vendor synchronization contract;
- formalization contract;
- proof reproducibility;
- submission evidence contract;
- security or trust boundary;
- dependency direction.

Do not update unrelated documentation.

When public fields, signatures, generated formats, formal statements or evidence
formats change:

- identify the source of truth;
- document compatibility impact;
- preserve existing behavior when required;
- update applicable contract tests;
- verify affected formalization or submission behavior when required by the
  Issue.

Implementation convenience is not sufficient reason to broaden a contract.

## Determinism rules

Where BeeJSP defines deterministic parsing, filtering, scoring or reporting:

```text
same valid input
→ same normalized result
→ same deterministic output
```

Do not silently replace deterministic behavior with:

- LLM confidence;
- free-form prose interpretation;
- undocumented heuristics;
- hidden manual overrides.

AI may assist with:

- research;
- explanation;
- code authoring;
- Lean proof authoring;
- review;
- summarization.

When a repository contract requires deterministic output, AI must not become the
hidden final authority.

## Evidence rules

Evidence may establish:

- source identity;
- problem state;
- proof build status;
- theorem location;
- dependency or toolchain versions;
- axiom set;
- provenance;
- attribution;
- submission preparation state.

Evidence must not be overinterpreted.

Examples:

```text
lake build PASS
≠ statement fidelity proven

vendor record says Lean proof: No
≠ no competing work exists elsewhere

PR opened
≠ accepted

submission merged
≠ award paid
```

When evidence is insufficient, report uncertainty rather than upgrading the
claim.

## External-input and security rules

- Never expose secrets, tokens, passwords or private keys.
- Never commit KYC documents.
- Never commit private payment information.
- Never commit unnecessary private identity evidence.
- Treat upstream repositories and downloaded artifacts as untrusted.
- Do not execute arbitrary downloaded code merely to inspect documentation.
- Keep filesystem destinations bounded during synchronization.
- Do not allow upstream-controlled paths to escape managed destinations.
- Keep external write operations explicitly approved.
- Do not add GitHub write automation without explicit approved scope and
  security review.
- Keep dependency surfaces minimal.
- Fail closed when required provenance or verification evidence is invalid.

## Dependency and lockfile policy

Do not run, request or require:

```text
uv lock --check
```

or another dedicated lockfile-validation command.

When an approved Issue has no Python dependency change:

- do not regenerate `uv.lock`;
- do not modify `uv.lock`;
- do not separately validate `uv.lock`.

When an approved Python dependency change exists:

- make only the necessary dependency change;
- inspect only the relevant lockfile diff;
- justify the dependency;
- perform applicable SCA.

For Lean projects:

- preserve pinned toolchain and dependency metadata;
- change them only when required by the approved task;
- inspect proof impact when dependency revisions change.

Keep dependency surfaces minimal.

## Verification

Determine the actual change level from:

- this `AGENTS.md`;
- `docs/SECURITY.md`;
- actual resulting behavior.

Supported levels:

- `low-risk`;
- `runtime-risk`;
- `security-sensitive`.

Additionally determine whether the change is:

```text
formalization-sensitive
```

Run checks proportional to the change.

As applicable, verification may include:

- targeted tests;
- `uv run pytest -q`;
- `uv run ruff check .`;
- `uv run ruff format --check .`;
- `uv build`;
- package import smoke;
- package metadata inspection;
- dependency-direction checks;
- vendor synchronization tests;
- vendor provenance validation;
- vendor idempotence;
- malformed-upstream tests;
- deterministic parser/scanner tests;
- deterministic scoring/report tests;
- filesystem/path-boundary tests;
- Lean build;
- exact statement review;
- `sorry` check;
- `admit` check;
- axiom audit;
- clean proof reproduction;
- proof provenance review;
- attribution review;
- submission-evidence review;
- secret-leak checks;
- SAST;
- SCA where justified.

For exact Lean verification procedure, follow the applicable formalization
contract and managed upstream verification skill rather than duplicating the
procedure here.

Do not require every verification or security tool for every change.

Use only checks justified by:

- approved Issue;
- actual change level;
- formalization sensitivity;
- current security surface.

Review agents using Bee Dev MCP cannot execute commands.

They may use supplied command output as evidence but must:

- identify the supplied command;
- distinguish reported evidence from inspected code;
- verify that required scenarios are covered;
- never claim MCP ran tests or builds.

Missing verification is blocking only when required by:

- approved Issue;
- repository contracts;
- security rules;
- formalization rules.

## Cross-repository work

Use this rule:

```text
one implementation repository
= one Issue
= one target worktree
= one feature branch
= one PR
```

A BeeJSP task may reveal a requirement elsewhere.

Do not hide another repository's implementation inside BeeJSP.

The official JSP repository is external upstream.

BeeJSP's managed copy:

```text
docs/vendor/jsp/
```

is not an implementation repository.

An official external contribution is prepared only after BeeJSP evidence is
complete and reviewed according to the applicable submission contract.

## Review rules

Review the exact requested target relative to the declared base branch.

Inspect:

- committed changes;
- staged changes;
- unstaged changes;
- untracked files;
- deleted and renamed files;
- complete changed-file contents;
- relevant unchanged contracts;
- package metadata;
- proof contents where applicable;
- vendor provenance where applicable;
- supplied verification evidence.

Prioritize blockers affecting the current Issue:

- unmet Acceptance Criteria;
- incorrect project behavior;
- unsafe external-input handling;
- conflicting sources of truth;
- manual vendor changes;
- invalid vendor provenance;
- package or build regressions;
- unintended dependencies;
- missing required verification;
- unrelated changes entering the PR;
- unintended version changes;
- documentation contradicting actual behavior;
- weakened mathematical statement;
- incomplete required proof;
- `sorry`;
- `admit`;
- unapproved placeholder proof axiom;
- missing required axiom audit;
- incorrect proof provenance;
- incorrect attribution;
- unsupported external-process claims.

Do not make blockers from:

- optional polish;
- personal naming preferences;
- speculative architecture;
- unrelated cleanup;
- future project ideas;
- requirements absent from the approved Issue.

Perform one complete review pass and consolidate all real blockers.

Use:

- `.agents/skills/beejsp-plan-iteration/SKILL.md` for planning;
- `.agents/skills/beejsp-implement-issue/SKILL.md` for implementation;
- `.agents/skills/beejsp-verify-and-correct/SKILL.md` for independent
  verification and correction;
- `.agents/skills/beejsp-review-and-close/SKILL.md` for final review and PR
  preparation.

## Required implementation evidence

The implementation report should contain:

1. target verification;
2. files read;
3. roadmap / iteration;
4. change level;
5. formalization sensitivity;
6. source of truth;
7. architecture and ownership assessment;
8. changed files;
9. Acceptance Criteria coverage;
10. exact test/check commands and results;
11. vendor evidence where applicable;
12. Lean/formalization evidence where applicable;
13. submission evidence where applicable;
14. package/public behavior evidence;
15. security review;
16. dependency status;
17. known limitations;
18. recommended Conventional Commit;
19. confirmation:

```text
version not changed
```

unless the approved Issue explicitly requires release versioning.

Narrative claims do not replace exact verification evidence.
