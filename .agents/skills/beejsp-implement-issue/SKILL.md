---
name: beejsp-implement-issue
description: Implement one approved BeeJSP Issue in the exact target worktree and return complete implementation and verification evidence.
---

---

# BeeJSP approved Issue implementation workflow

## Purpose

Use this workflow after a BeeJSP Issue has been approved and a dedicated target worktree and branch have been prepared.

This workflow may modify the target repository and run local checks.

Do not:

- work outside the approved Issue;
- perform unrelated refactoring or cleanup;
- create speculative abstractions;
- manually edit managed upstream vendor content;
- weaken an approved mathematical statement for implementation convenience;
- claim unverified proof or external-process results;
- commit, push, create a PR or merge;
- change package version unless the Issue is explicitly release-related.

## Required inputs

Obtain:

- project;
- exact target worktree;
- expected branch;
- base branch;
- approved Issue or normalized approved task contract;
- Issue source when supplied;
- roadmap context;
- planning constraints;
- related repository contracts when explicitly supplied.

One implementation run owns one implementation repository.

If implementation is required in another repository, that work requires its own approved Issue, worktree and implementation run.

## Working contract

Read and follow `AGENTS.md`.

Before proposing or applying a change:

- read every declared file completely;
- keep a file inventory;
- add and fully read any newly required file before editing it;
- map the work to the approved Issue and roadmap context;
- determine the actual change level;
- determine whether the work is formalization-sensitive;
- derive required checks from the applicable repository contracts.

Make the smallest complete KISS change.

Use proportional tests for Acceptance Criteria and public behavior.

Prefer existing implementation, tests and helpers.

Create new files, helpers, models or abstractions only when demonstrably required by the approved task.

Before reporting completion, inspect the complete final diff and remove unrelated or accidental changes.

## Target safety gate

Before changing files:

1. verify the current working directory;
2. verify the current branch;
3. inspect `git status`;
4. verify that the worktree exactly matches the requested target;
5. identify pre-existing staged, unstaged and untracked changes;
6. determine whether pre-existing changes overlap the approved Issue.

Stop when:

- path differs from the requested target;
- branch differs from the expected branch;
- unrelated pre-existing changes make safe attribution impossible;
- the approved Issue materially conflicts with `AGENTS.md`;
- the approved Issue materially conflicts with current repository contracts;
- required implementation belongs to another repository without an approved
  Issue for that repository.

Do not silently:

- switch branches;
- substitute another worktree;
- discard existing work;
- absorb unrelated dirty changes into the task.

## Required reading

Read before implementation:

- `AGENTS.md`;
- approved Issue or normalized approved task contract;
- relevant `docs/ROADMAP.md` section;
- `docs/SECURITY.md`;
- directly relevant contracts;
- directly relevant implementation;
- directly relevant tests.

Read as applicable:

- `docs/ARCHITECTURE.md`;
- `docs/DEV_GUIDE.md`;
- `docs/FORMALIZATION.md`;
- `docs/SUBMISSION.md`;
- `README.md`;
- `pyproject.toml`;
- relevant Python package code;
- relevant Lean proof project;
- vendor synchronization implementation;
- relevant managed upstream material.

For formalization-sensitive work, read the formalization contract and the exact source/proof material required to establish statement scope and provenance.

For submission-related work, read the submission contract and the applicable managed upstream process material.

When the applicable formalization contract requires the managed upstream Lean verification procedure, follow:

```text
docs/vendor/jsp/skills/lean-verify/SKILL.md
```

Do not modify a related repository unless a separate approved task assigns work to it.

## Change classification

Determine the actual change level:

- `low-risk`;
- `runtime-risk`;
- `security-sensitive`.

Also determine whether the change is:

```text
formalization-sensitive
```

Use `AGENTS.md`, `docs/SECURITY.md` and actual resulting behavior to derive the classification.

Use `docs/FORMALIZATION.md` for proof-specific requirements.

If actual implementation requires a higher change level than declared by the Issue, report the mismatch before continuing.

Do not silently downgrade classification to reduce verification.

## Implementation

Implement the smallest complete solution satisfying Scope and Acceptance Criteria.

Requirements:

- follow KISS;
- preserve repository ownership and sources of truth;
- reuse existing contracts and implementation;
- do not introduce hidden defaults for required behavior;
- do not duplicate existing logic;
- preserve deterministic behavior where required;
- preserve proof reproducibility where required;
- preserve fail-closed behavior on trust and provenance boundaries;
- follow PEP 8 for Python;
- keep public identifiers, package metadata and documentation in English;
- preserve compatibility unless the Issue explicitly permits a breaking
  change;
- keep `pyproject.toml.version` unchanged for ordinary feature, fix, docs and
  chore work.

Apply the managed-vendor, formalization, submission, security, dependency and lockfile rules from `AGENTS.md` rather than duplicating them locally.

Do not introduce a separate agent workflow for formalization, vendor sync or submission.

## Tests and verification

Add or update only tests proportional to the approved Issue.

Prefer existing test files, fixtures and helpers.

Run all checks required by:

- Acceptance Criteria;
- actual change level;
- formalization sensitivity;
- applicable repository contracts.

As applicable this may include:

- targeted Python tests;
- full Python test suite;
- Ruff checks;
- package build/import checks;
- deterministic parser/scanner/report checks;
- vendor synchronization/provenance checks;
- vendor idempotence or failure-path checks;
- filesystem/path-boundary checks;
- Lean build;
- statement-fidelity review;
- `sorry` / `admit` checks;
- axiom audit;
- clean proof reproduction;
- provenance and attribution review;
- submission-evidence validation;
- secret-leak checks;
- SAST;
- SCA where justified.

Use `uv run` for Python commands when applicable.

Do not run or require:

```text
uv lock --check
```

Do not treat successful `lake build` alone as proof of statement fidelity.

Record exact:

- commands;
- exit codes;
- passed/failed/skipped counts where applicable;
- material warnings.

Do not claim a check passed when it was not executed.

## Cross-repository dependency

If implementation reveals that a required change belongs to another repository:

- identify the owning repository;
- do not create a BeeJSP-local workaround solely to avoid that ownership;
- stop the affected part of implementation when the current Issue cannot be
  completed safely without the external change;
- report the required separate Issue/worktree flow.

Official JSP upstream and `docs/vendor/jsp/` are not BeeJSP implementation repositories.

## Final diff review

Before reporting completion:

- inspect `git status`;
- inspect the complete final diff;
- inspect untracked files created by the task;
- confirm every change belongs to the approved Issue;
- confirm no required file is missing;
- confirm no unrelated file changed;
- confirm no accidental formatting sweep occurred;
- confirm no unintended dependency or version change occurred;
- confirm no secret/private identity/payment material was introduced;
- confirm managed upstream content changed only through the approved mechanism;
- confirm formalization and provenance contracts remain satisfied when
  applicable.

If final implementation materially differs from the approved Issue, report the difference instead of silently expanding scope.

## Implementation report

Return one report containing:

1. `Target verification`
2. `Files read`
3. `Roadmap / iteration`
4. `Change level`
5. `Formalization sensitivity`
6. `Required checks`
7. `Sources of truth`
8. `Architecture / ownership`
9. `Changed files`
10. `Acceptance Criteria coverage`
11. `Tests and commands`
12. `Vendor evidence`
13. `Lean / formalization evidence`
14. `Submission evidence`
15. `Package / public behavior`
16. `Security review`
17. `Dependencies`
18. `Known limitations`
19. `Recommended Conventional Commit`
20. `Version status`

For sections that do not apply, state `not applicable` rather than inventing evidence.

For every substantive correction made during implementation, describe:

```text
File:
`path/to/file`

Before:
<previous behavior>

After:
<implemented behavior>

Why:
<approved requirement and verification evidence>
```

Do not include a full diff.

Do not claim completion while required Acceptance Criteria or required checks remain unresolved.

End with:

```text
version not changed
```

unless the approved Issue explicitly requires release versioning.
