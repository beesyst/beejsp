---
name: beejsp-review-and-close
description: Perform a complete read-only BeeJSP review against an approved Issue, using the exact worktree and base branch, then return one consolidated verdict and PR close package.
---

---

# BeeJSP review and close workflow

## Purpose

Use this workflow after implementation and independent verification are complete and the user has supplied:

- approved Issue or Acceptance Criteria;
- implementation/verification evidence;
- exact target worktree;
- expected branch and base branch.

This workflow is read-only.

Do not:

- modify files;
- run repository commands;
- switch branches;
- create commits;
- push;
- create or merge a PR.

Review only the approved scope.

Do not expand final review into optional improvements, future roadmap work, unrelated cleanup or independent review of unrelated repositories.

## Required inputs

Obtain:

- project;
- instruction worktree;
- expected target worktree path;
- expected branch;
- expected base branch;
- mode;
- roadmap context;
- approved Issue content or GitHub Issue URL;
- current PR description, GitHub Pull Request URL or `none`;
- implementation and verification evidence;
- additional target context when explicitly supplied;
- previous blocking findings for re-review when applicable.

## Working contract

Read and follow `AGENTS.md`.

Read every declared file completely before forming findings.

Keep a file inventory.

When another file becomes necessary, read it completely before evaluating it.

Evaluate only the approved Issue scope.

Determine from the Issue, actual changes and resulting behavior:

- actual change level;
- formalization sensitivity;
- required verification evidence.

Require the smallest complete KISS implementation.

The implementation report is supporting evidence.

The actual target worktree, complete diff, current contracts, proof contents, vendor provenance and verification evidence are authoritative.

Before returning a verdict, inspect the complete final change set for unrelated changes, ownership/source-of-truth violations, unexpected dependency/version changes and applicable vendor/formalization regressions.

Worktree path, MCP target and Git branch are separate identifiers.

## Phase 0 — Resolve supplied GitHub context

Follow the GitHub context resolution contract from `AGENTS.md`.

When approved Issue input contains a GitHub Issue URL:

1. call `get_github_context`;
2. read title;
3. read complete body;
4. read all available Issue comments;
5. use explicit accepted clarifications when establishing approved scope.

When current PR input contains a GitHub Pull Request URL:

1. call `get_github_context`;
2. read title;
3. read complete body;
4. read all available conversation comments;
5. read reviews;
6. read inline review comments.

The approved Issue establishes required scope and Acceptance Criteria.

The PR provides delivery and reviewer context.

It does not override the Issue, repository contracts or actual target state.

When pasted content and a URL are both supplied, consider both.

If they materially conflict, report the conflict.

If mandatory GitHub context cannot be read completely, return:

```text
REVIEW INCOMPLETE
```

Do not issue a code verdict from incomplete mandatory GitHub context.

## Phase 1 — Resolve the exact target

1. call `list_worktrees` for the project;
2. match the exact expected target worktree path;
3. use the returned MCP `target`;
4. call `get_project_context` using supplied mode;
5. verify:
   - project;
   - path;
   - branch;
   - HEAD;
   - dirty state.

If exact path or mandatory metadata is unavailable, return:

```text
REVIEW INCOMPLETE
```

If project or branch differs from expected:

- report expected and actual values;
- do not issue a code verdict.

Do not infer MCP target from a branch name.

Do not substitute another worktree.

## Phase 2 — Read the complete manifest and diff

### Review manifest

1. call `get_review_manifest` with an empty cursor;
2. append returned `content`;
3. continue with exact `next_cursor` while `has_more=true`;
4. require the same `snapshot_id` on every page;
5. parse the complete manifest.

Verify:

- project;
- target;
- branch;
- HEAD;
- expected base branch;
- dirty state;
- committed files;
- staged files;
- unstaged files;
- untracked files;
- deleted files;
- renamed files;
- omitted or redacted paths.

The manifest is the authoritative changed-file inventory.

### Review diff

1. call `get_review_bundle_page` with an empty cursor;
2. append returned `content`;
3. continue with exact `next_cursor` while `has_more=true`;
4. require the same snapshot as the manifest;
5. finish only when:
   - `has_more=false`;
   - `next_cursor=null`;
   - `truncated=false`.

Do not use compatibility `get_review_bundle` as a substitute.

If pagination fails, snapshot changes or required data is truncated, return:

```text
REVIEW INCOMPLETE
```

The complete diff is evidence of actual changes.

## Phase 3 — Resolve review instructions

Read from the primary target:

- `AGENTS.md`;
- `.agents/skills/beejsp-review-and-close/SKILL.md`.

If they are absent because the target worktree predates their introduction, use the explicitly supplied `INSTRUCTION_WORKTREE`.

Resolve that instruction worktree through Bee Dev MCP and verify its exact path and expected branch.

Use it only for review instructions.

Continue reviewing implementation exclusively from the original target worktree.

Absence of newer instruction files from a legacy target is not itself a code finding.

Do not silently choose another instruction source.

## Phase 4 — Read required files

Use `read_project_file`.

When continuation metadata is returned, continue using exact `next_line` and `next_column` until both are null.

Read completely:

- `AGENTS.md`;
- this skill;
- `.github/PULL_REQUEST_TEMPLATE/pr.md`;
- relevant roadmap section;
- `docs/SECURITY.md`;
- every changed and untracked text file;
- directly relevant tests;
- directly related unchanged contracts/implementation required to interpret the
  changes.

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
- relevant managed upstream material;
- proof/provenance evidence.

For deleted files inspect the complete diff and affected current references.

For renamed files inspect old/new paths, fully read the destination and verify updated references.

If a required relevant file is omitted, redacted or unreadable through the available safe MCP interface, return:

```text
REVIEW INCOMPLETE
```

Do not issue a verdict from partial mandatory inspection.

## Phase 5 — Related repository context

When an additional repository is explicitly supplied:

1. resolve its exact path;
2. verify expected branch;
3. follow supplied role/mode/skill;
4. read only context necessary for the primary review;
5. do not broaden review unnecessarily.

An additional repository supplied for context is not automatically an implementation target.

Official JSP upstream and `docs/vendor/jsp/` are not normal BeeJSP implementation targets.

## Phase 6 — Issue-specific contract review

Follow repository-wide architecture, vendor, formalization, submission, security, dependency and evidence rules from `AGENTS.md`.

Apply only the checks relevant to the approved Issue and actual changes.

### Vendor-sensitive changes

When vendor synchronization or managed content changed, verify as applicable:

- update path is consistent with the approved synchronization contract;
- provenance is valid;
- required managed content is present;
- incomplete synchronization cannot be represented as successful;
- stale managed content is handled correctly;
- no manual local truth was introduced into managed upstream content.

Do not treat managed material as live external-state evidence.

### Formalization-sensitive changes

Verify as applicable:

- exact source problem is identified;
- Lean statement preserves required scope;
- no materially weaker theorem is substituted;
- no unjustified stronger assumption was introduced;
- proof completeness meets the formalization contract;
- required reproducibility metadata exists;
- required Lean verification evidence exists;
- required axiom audit exists;
- provenance and attribution are correct.

Compilation alone does not establish statement fidelity.

### Submission-related changes

Verify as applicable:

- required proof/provenance evidence is complete;
- applicable external-process rules are sufficiently current;
- exact repository/commit/proof locations are supported by evidence;
- managed vendor content is not being used as live state;
- no unsupported claim of acceptance, priority, award or payment is made.

## Phase 7 — Evidence and Acceptance Criteria

Bee Dev MCP cannot execute tests or builds.

Treat supplied command output as reported evidence.

Never claim MCP ran:

- tests;
- package builds;
- vendor synchronization;
- Lean builds;
- axiom audits;
- SAST;
- SCA.

Evaluate every Acceptance Criterion as exactly one:

```text
satisfied
partially satisfied
not satisfied
not verifiable
not applicable
```

Check as applicable:

- observable project behavior;
- package/public behavior;
- deterministic behavior;
- vendor synchronization/provenance;
- external-input/path safety;
- formal statement scope;
- proof completeness/reproducibility;
- axiom/provenance evidence;
- submission evidence;
- documentation;
- dependency/version state;
- required verification evidence.

`not verifiable` is blocking only when required evidence is necessary for readiness under the Issue or repository contracts.

Do not require dedicated lockfile validation.

Never require:

```text
uv lock --check
```

## Phase 8 — Blocking findings

A blocker must affect readiness of the current approved Issue.

Examples include:

- unmet Acceptance Criterion;
- incorrect or unsafe current behavior;
- source-of-truth violation;
- manual managed-vendor truth;
- invalid required provenance;
- incompatible public/package contract;
- missing required verification;
- unrelated changes entering the PR;
- unintended dependency/version change;
- documentation contradicting actual behavior;
- statement-fidelity failure;
- incomplete required proof;
- prohibited proof placeholder;
- missing required axiom/provenance evidence;
- incorrect attribution;
- unsupported external-process claim;
- required cross-repository dependency absent.

Do not make blockers from:

- optional polish;
- personal style preferences;
- speculative future architecture;
- unrelated cleanup;
- future project ideas;
- requirements absent from the Issue;
- MCP limitations themselves;
- checks not required by actual scope/classification.

Find and consolidate all real blockers before returning a verdict.

## Phase 9 — Completeness gate

Before issuing a code verdict confirm:

- exact target/path/branch verified;
- expected base branch verified;
- complete manifest consumed;
- complete non-truncated diff consumed;
- manifest and diff use the same snapshot;
- committed/staged/unstaged/untracked changes inventoried;
- deleted and renamed paths inspected;
- every required changed file fully read;
- relevant unchanged contracts read;
- requested related-repository context evaluated;
- every Acceptance Criterion evaluated;
- verification evidence evaluated;
- applicable vendor/formalization/security boundaries evaluated;
- dependency/version scope checked;
- all blockers consolidated.

If mandatory inspection remains incomplete, return:

```text
REVIEW INCOMPLETE
```

Include only:

1. completed inspection;
2. exact missing data;
3. reason no code verdict was issued.

Do not include findings based on partial inspection, correction prompt, PR body or code verdict.

## Phase 10 — Verdict

Return exactly one completed-review verdict:

```text
APPROVED FOR PR
```

or:

```text
CHANGES REQUIRED
```

### APPROVED FOR PR

Use only when no blocking findings remain.

State exactly:

```text
No corrections required.
```

Then provide:

1. Acceptance Criteria coverage;
2. files reviewed;
3. supplied verification evidence;
4. non-blocking limitations;
5. reviewed branch;
6. recommended squash commit;
7. completed PR body using repository template;
8. merge readiness;
9. next actions:
   - commit reviewed changes;
   - push feature branch;
   - open or update PR;
   - wait for CI;
   - squash merge after approval.

Do not claim Bee Dev MCP ran commands.

### CHANGES REQUIRED

Provide every blocker using:

### <Finding title>

File:

`path/to/file`

Exact location:

<existing function, class, proof, contract, configuration or documentation section>

Current:

```<language>
<exact bounded current fragment or behavior>
```

Required:

```<language>
<complete bounded replacement, insertion or required behavior>
```

Why:

<Acceptance Criterion, repository contract and concrete blocking impact>

For evidence-only blockers, provide the exact missing verification command or scenario rather than inventing a code change.

Present all real blockers before the correction prompt.

Do not prepare a final PR body while blockers remain.

## Consolidated correction prompt

When changes are required, provide one concise executor prompt.

Select:

- **Copilot** for localized, clearly specified corrections;
- **Codex** for broader diagnosis, proof corrections, multi-contract or
  security-sensitive corrections.

The correction prompt must authorize local inspection, modification and required checks in the exact target worktree.

Do not copy reviewer-only restrictions such as Bee Dev MCP or read-only mode into the executor prompt.

Use:

```text
Executor: <Copilot or Codex>

Project: beejsp
Instruction worktree: <exact instruction worktree>
Target worktree: <exact target worktree>
Expected branch: <feature branch>
Base branch: <base branch>

Read instructions from:

- <instruction worktree>/AGENTS.md
- <instruction worktree>/.agents/skills/beejsp-verify-and-correct/SKILL.md

Use the instruction worktree only for reading instructions.
Inspect, modify and verify only the target worktree.

Fix only the blocking findings from the current final review.
Preserve already-correct behavior within the approved Issue.

For every blocker include:

File:
<path>

Exact location:
<location>

Current:
<bounded current fragment or behavior>

Required:
<bounded replacement, insertion or required behavior>

Why:
<blocking contract/Acceptance Criterion>

Run verification required by the blockers, actual change level and applicable
formalization/vendor/security contracts.

Include `git diff --check`, dependency/version verification and unrelated-file
check where applicable.

Return one consolidated report according to
`beejsp-verify-and-correct`.

Do not commit, push, create/update a PR or merge.
```

The prompt must include every blocking finding.

Do not copy the full Issue, full review report or stable repository rules.

Do not introduce optional cleanup or new requirements.

## Cross-repository correction rule

If a blocker belongs to another repository:

- identify the owning repository;
- do not instruct BeeJSP executor to implement it locally;
- require a separate Issue/worktree flow when needed;
- preserve one implementation repository per Issue/branch/PR.

Official JSP upstream is not a BeeJSP implementation target.

## Re-review

For re-review:

1. obtain a new complete manifest;
2. obtain a new complete paginated diff;
3. verify same target/path/branch/base;
4. verify every previous blocker;
5. evaluate original Acceptance Criteria again;
6. inspect regressions introduced by corrections;
7. re-evaluate applicable vendor/formalization/security boundaries;
8. return:
   - `APPROVED FOR PR`; or
   - only remaining current blockers.

Do not introduce unrelated optional findings.

Resolved blockers must not remain in the blocker list.

## PR close package

When approved, prepare the PR body using the actual repository template.

Reflect reviewed implementation, not planning intent.

Include only relevant reviewed evidence.

Do not claim MCP executed commands.

Do not present speculative future work as completed scope.

## Recommended squash commit

When approved, provide one Conventional Commit title that reflects the actual reviewed change.

Do not recommend a version bump unless the approved Issue is release-related.

## Close decision

When accurate, state:

```text
Merge readiness: ready after commit/push/CI/PR approval
```

When blockers remain:

```text
Merge readiness: not ready
```

Do not present a merge-ready close package while blockers remain.

## Output format

For a completed review return:

1. `Verdict`
2. `Blocking findings`
3. `Acceptance Criteria coverage`
4. `Files reviewed`
5. `Verification evidence`
6. `Unverified limitations`
7. `Close decision`
8. `PR body` when approved
9. `Consolidated correction prompt` when changes are required

For incomplete inspection return only:

1. `REVIEW INCOMPLETE`
2. `Completed inspection`
3. `Missing inspection data`
4. `Reason no code verdict was issued`

Do not mix incomplete-review output with a completed-review verdict, correction prompt or PR close package.

One review pass produces one consolidated outcome.
