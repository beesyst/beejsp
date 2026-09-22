---
name: beejsp-verify-and-correct
description: Independently verify an implemented BeeJSP Issue, apply only necessary in-scope corrections, and return final evidence for read-only review.
---

---

# BeeJSP verification and correction workflow

## Purpose

Use this workflow after initial implementation or after a completed final review has returned blocking findings.

The executor may:

- inspect files;
- modify the exact target worktree;
- run local repository checks.

Use it once for independent post-implementation verification.

Reuse it only to address explicit blocking findings returned by final review.

Do not:

- expand the approved Issue;
- add optional polish;
- create speculative architecture;
- perform unrelated cleanup;
- create preventive patches without a demonstrated blocker;
- manually edit managed upstream vendor content;
- weaken mathematical statements or formalization requirements;
- commit, push, create a PR or merge;
- change package version unless the Issue is explicitly release-related.

## Required inputs

For every run obtain:

- project;
- exact target worktree;
- expected branch;
- base branch;
- related repository contracts when explicitly supplied.

For initial independent verification also obtain:

- approved Issue or normalized approved task contract;
- roadmap context;
- planning constraints.

For a correction run also obtain:

- explicit blocking findings from the completed final review.

Do not require:

- implementation report;
- previous verification report;
- previous executor reasoning.

The current target worktree is authoritative.

## Working contract

Read and follow `AGENTS.md`.

Before proposing or applying a correction:

- read every declared file completely;
- keep a file inventory;
- fully read newly required files before editing;
- determine actual change level;
- determine formalization sensitivity;
- derive required verification from applicable repository contracts.

For initial verification:

- verify the implementation independently against the approved task contract.

For a correction run:

- treat supplied review blockers as the complete correction scope;
- verify affected Acceptance Criteria and regression risk;
- do not reopen unrelated reviewed scope.

Make the smallest complete KISS correction.

Prefer existing implementation, tests, fixtures and helpers.

Create new files or abstractions only when demonstrably required by the approved task or a valid blocker.

Before reporting completion, inspect the complete final diff for accidental, unrelated or speculative changes.

## Target safety gate

Before verification:

1. verify the current working directory;
2. verify the current branch;
3. inspect `git status`;
4. inventory committed changes relative to base;
5. inventory staged changes;
6. inventory unstaged changes;
7. inventory untracked files;
8. distinguish current-task changes from unrelated work.

Stop when:

- path differs from requested target;
- branch differs from expected branch;
- unrelated changes prevent safe verification;
- mandatory target information is missing;
- approved task contract is missing for initial verification;
- review blockers are missing for a correction run;
- safe attribution of current changes is impossible;
- required correction belongs to another repository without approved scope.

Do not silently switch branches, replace the requested worktree, discard existing work or absorb unrelated changes.

## Required reading

Read for every run:

- `AGENTS.md`;
- `docs/SECURITY.md`;
- all changed and untracked files;
- directly related contracts;
- directly related implementation;
- directly related tests.

Read as applicable:

- `docs/ROADMAP.md`;
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

For initial verification also read:

- approved Issue or normalized approved task contract;
- relevant roadmap context;
- supplied planning constraints.

For a correction run also read:

- every supplied review blocker;
- directly affected files, contracts and tests.

When applicable use the managed upstream Lean verification procedure referenced by `AGENTS.md`.

Do not depend on previous executor reports.

Authoritative evidence is the current target worktree and current verification results.

## Verification

### Initial independent verification

Evaluate every Acceptance Criterion as exactly one:

```text
satisfied
partially satisfied
not satisfied
not verifiable
not applicable
```

Verify from current evidence, not from implementation claims.

As applicable inspect:

- code;
- contracts;
- tests;
- generated artifacts;
- proof contents;
- Lean verification evidence;
- vendor provenance;
- package/dependency state.

### Correction run

Verify:

- every supplied blocking finding;
- every affected Acceptance Criterion identified by those findings;
- behavior touched by the correction;
- regressions introduced by the correction.

Do not reopen unrelated already-reviewed scope.

## Verification dimensions

Verify only applicable dimensions:

- source of truth;
- architecture and repository ownership;
- package/public contracts;
- package metadata/build/import behavior;
- dependency direction;
- deterministic parsing/scoring/reporting;
- managed vendor synchronization;
- vendor provenance;
- external-input/path handling;
- exact mathematical statement;
- theorem scope and assumptions;
- proof completeness;
- Lean toolchain/dependency reproducibility;
- axiom audit;
- proof provenance and attribution;
- submission evidence;
- dependency/version status;
- security boundaries;
- required tests and checks.

Successful proof compilation is necessary when required but does not by itself establish statement fidelity.

Managed upstream material does not establish live external-process state.

## Corrections

Apply corrections only when required by:

- an unsatisfied Acceptance Criterion;
- a valid supplied review blocker;
- incorrect current-task behavior;
- unsafe current-task behavior;
- source-of-truth violation;
- managed-vendor violation;
- public-contract incompatibility;
- formalization statement/scope defect;
- incomplete proof;
- reproducibility defect;
- provenance or attribution defect;
- missing required verification.

Corrections must be:

- in scope;
- minimal;
- complete;
- consistent with current contracts;
- free of duplicate logic;
- free of duplicate sources of truth;
- free of unnecessary defaults or hardcoding;
- free of speculative abstractions;
- PEP 8 compliant for Python.

Do not create a preventive patch merely because a theoretical future problem might appear.

If a correction belongs to another repository, follow the cross-repository rule below instead of implementing a BeeJSP workaround.

## Cross-repository correction rule

If verification proves that a required correction belongs to another repository:

- identify the owning repository;
- do not implement it locally merely to close the BeeJSP task;
- require a separate approved Issue/worktree flow;
- report the dependency as blocking when it prevents current completion.

Official JSP upstream and BeeJSP's managed vendor snapshot are not normal implementation targets.

## Tests and checks

Run all checks required by:

- approved task;
- actual change level;
- formalization sensitivity;
- affected repository contracts;
- supplied blockers for correction runs.

As applicable include:

- targeted regression tests;
- full Python tests;
- Ruff checks;
- package build/import checks;
- dependency-direction checks;
- vendor synchronization/provenance checks;
- vendor idempotence/failure tests;
- malformed-input/path-boundary tests;
- deterministic parser/scanner/report checks;
- Lean build;
- `sorry` / `admit` checks;
- axiom audit;
- clean proof reproduction;
- statement-fidelity review;
- provenance/attribution checks;
- submission-evidence checks;
- secret-leak checks;
- SAST;
- SCA where justified.

Do not run or require:

```text
uv lock --check
```

Record exact:

- commands;
- exit codes;
- passed/failed/skipped counts where applicable;
- relevant warnings.

Do not claim a check passed when it was not executed.

## Final diff review

Before reporting completion:

1. inspect `git status`;
2. inspect the complete final diff;
3. inspect untracked files;
4. verify every changed file belongs to current scope;
5. verify no required correction remains missing;
6. verify no unrelated formatting/refactor occurred;
7. verify no unintended dependency/version change occurred;
8. verify no secret/private identity/payment material was introduced;
9. verify managed vendor boundaries remain intact;
10. verify formalization/provenance requirements remain intact when applicable.

For correction runs, also verify that corrections did not regress already correct behavior within the approved task.

## Final readiness

Return one of:

```text
ready for final read-only review
```

or:

```text
not ready for final read-only review
```

Use `ready for final read-only review` only when:

- required corrections are complete;
- required checks are successfully executed or explicitly accounted for;
- no known current-scope blocker remains;
- changed-file inventory is consistent with the task;
- no unresolved vendor, formalization or security problem remains.

Do not call the implementation merge-ready.

Final merge readiness belongs to final read-only review.

## Final report

Return one consolidated report containing:

1. `Target verification`
2. `Actual changed-file inventory`
3. `Roadmap / iteration`
4. `Acceptance Criteria coverage`
5. `Blocking findings received`
6. `Corrections made`
7. `Change level`
8. `Formalization sensitivity`
9. `Required checks`
10. `Tests and commands`
11. `Vendor evidence`
12. `Lean / formalization evidence`
13. `Submission evidence`
14. `Package / public behavior`
15. `Security review`
16. `Dependencies`
17. `Unrelated-file check`
18. `Known limitations`
19. `Recommended Conventional Commit`
20. `Final readiness`
21. `Version status`

For every substantive correction report:

```text
File:
`path/to/file`

Before:
<previous incorrect behavior>

After:
<implemented required behavior>

Why:
<approved requirement or supplied blocker and verification evidence>
```

Do not include a full diff.

When no correction was required, state exactly:

```text
No corrections required.
```

For initial verification, include every Acceptance Criterion with its status.

For a correction run, include every supplied blocker and its current status, affected Acceptance Criteria and regression result.

Do not claim verification that was not executed.

End with:

```text
version not changed
```

unless the approved Issue explicitly requires release versioning.
