---
name: beejsp-plan-iteration
description: Inspect the current BeeJSP implementation through Bee Dev MCP, critically validate task necessity, project fit, formalization requirements and repository ownership, reconcile the roadmap, and prepare a compact roadmap item or standalone task plus complete copy-ready Issues without modifying repositories.
---

---

# BeeJSP iteration planning workflow

## Purpose

Use this workflow when:

- a BeeJSP task or idea has not yet been approved;
- an existing roadmap item must be validated, refined or replaced;
- a proposed iteration may be stale relative to current implementation;
- the next meaningful BeeJSP increment must be selected;
- a mathematical problem is being considered for screening or formalization;
- formalization feasibility or scope must be validated;
- upstream JSP state may affect planned work;
- repository ownership is unclear;
- a complete Issue must be prepared from repository evidence.

Do not use this workflow when a complete Issue has already been approved and the task is ready for `.agents/prompts/02-implementation-tests.md`.

Planning must determine:

- what exists now;
- what is actually missing;
- whether work is necessary now;
- whether the proposed solution is correct;
- whether it advances BeeJSP's purpose;
- whether a smaller complete solution exists;
- which roadmap item owns the increment;
- which repository owns the implementation;
- whether formalization-sensitive work is involved;
- whether current upstream reference material is sufficient;
- what must remain excluded;
- what context prompt 02 needs.

This workflow is read-only.

Use only Bee Dev MCP for repository inspection.

Do not:

- modify files;
- switch branches;
- run shell or Git commands;
- run tests;
- create Issues, branches, commits or PRs;
- prepare implementation, verification, correction or review prompts;
- prepare PR bodies.

## Repository guidance

Read and follow `AGENTS.md`.

`AGENTS.md` owns stable repository-wide rules, including:

- Bee Dev MCP usage;
- exact target resolution;
- complete reading;
- project and architecture boundaries;
- sources of truth;
- managed vendor rules;
- formalization and submission boundaries;
- implementation rules;
- verification policy;
- dependency and version restrictions.

Do not repeat repository-wide rules from `AGENTS.md`, `docs/SECURITY.md`, `docs/FORMALIZATION.md` or `docs/SUBMISSION.md` in planning output or Issues.

This skill owns only:

- the planning decision algorithm;
- roadmap reconciliation;
- necessity validation;
- formalization-planning decisions;
- repository ownership decisions;
- roadmap and Issue output contracts;
- the planning handoff.

## Required inputs

The external prompt `.agents/prompts/01-planning.md` provides:

- `MAIN_WORKTREE`;
- `MODE`;
- `ROADMAP_CONTEXT`;
- `TASK_OR_IDEA`;
- `CONTEXT_OR_NONE`;
- `ADDITIONAL_PROJECTS_OR_NONE`;
- declared project;
- expected branch;
- base branch.

Treat paths, project names, branches, modes and repository roles as exact input values.

Pass `MODE` unchanged to applicable Bee Dev MCP calls.

Do not silently substitute another:

- worktree;
- repository;
- branch;
- roadmap;
- mode.

## Core planning rules

### Evidence before agreement

Treat the user's proposed task, roadmap reference, architectural assumption, formalization proposal, implementation report and candidate problem as hypotheses.

Validate material assumptions against current repository evidence.

As applicable inspect:

- code;
- tests;
- package metadata;
- public contracts;
- proof projects;
- Lean statements;
- proof dependencies;
- managed upstream reference material;
- repository documentation;
- dirty changes;
- related repository contracts explicitly required by the task.

Current BeeJSP repository files and contracts are authoritative for BeeJSP.

Managed upstream material is local reference evidence.

Current official upstream remains authoritative for current external-process facts.

Reports, screenshots, previous planning outputs and descriptions are supporting evidence only.

Do not automatically accept:

- the proposed iteration;
- the proposed roadmap stage;
- the proposed solution;
- the proposed urgency;
- the proposed candidate problem;
- the assumption that a proof is complete;
- the assumption that compilation proves statement fidelity;
- the assumption that managed upstream material represents live external state;
- the assumption that new infrastructure is required.

### Critical planning

Answer:

- What is the current behavior?
- What gap remains?
- Does the gap materially advance BeeJSP?
- Is it important now?
- Is it already implemented?
- Does another roadmap item cover it?
- Is the proposed repository correct?
- Is a smaller complete solution available?
- Does it preserve existing sources of truth?
- Does it preserve reproducibility and provenance?
- Does formalization-sensitive work require a separate feasibility step?
- What must not be built?
- What should BeeJSP prioritize next?

When the user's framing is wrong:

1. show the mismatch using repository evidence;
2. preserve the underlying intent where possible;
3. correct roadmap, scope, sequencing or ownership;
4. reject unnecessary architecture;
5. provide a usable corrected planning result.

### Formalization planning gate

For proposed Lean work, establish enough evidence to plan the next bounded step.

As applicable determine:

- exact source problem;
- source mathematical solution and provenance;
- solver attribution;
- intended Lean statement;
- required mathematical scope;
- material assumptions;
- available proof dependencies;
- likely Mathlib support;
- reproducibility requirements;
- applicable verification requirements.

Do not approve a complete-formalization Issue when an essential source, statement or mathematical prerequisite is still unknown.

When feasibility is materially uncertain, prefer a bounded research or formalization spike over pretending the complete proof is already plannable.

Do not use successful compilation of an existing fragment as proof that the full intended theorem has been formalized.

### Upstream freshness gate

When task correctness materially depends on current official JSP state:

- inspect managed provenance;
- inspect the relevant managed material;
- determine whether the snapshot is sufficient for the planning decision.

Do not treat the managed snapshot as live Pull Request, Issue, competition, award or payment state.

If fresher evidence is required, make refresh or live-state verification an explicit prerequisite or task constraint.

### KISS

Recommend the smallest complete increment that closes the verified gap.

Avoid:

- optional polish;
- unrelated cleanup;
- broad refactoring;
- speculative architecture;
- second sources of truth;
- premature abstractions;
- generic frameworks;
- unnecessary dependencies;
- unnecessary cross-repository changes;
- future work hidden inside current scope.

### Roadmap and Issue separation

The roadmap is a compact iteration-level contract.

The Issue is the detailed execution contract.

Do not turn the roadmap into a full implementation specification.

Do not make the Issue so vague that implementation must repeat planning.

## ROADMAP_CONTEXT

`ROADMAP_CONTEXT` is a hypothesis to validate, not an instruction to approve the referenced item.

### Known numbered iteration

Validate:

- roadmap existence;
- iteration existence and uniqueness;
- stage;
- status;
- scope;
- excluded scope;
- neighbouring completed and unfinished items;
- prerequisite completion;
- implementation evidence;
- overlapping or duplicate scope;
- whether the task still belongs to that item;
- whether the implementation order remains valid.

If the referenced iteration is `DONE`:

- preserve completed history;
- never return it to `PLANNED`;
- never reuse its identifier;
- determine whether the request is already implemented;
- use a new unique iteration only for genuine follow-up work.

Follow the repository's existing iteration numbering convention.

### Proposed standalone task

Standalone is appropriate only when the work:

- is narrow and local;
- creates no significant project capability;
- introduces no substantial public contract;
- does not materially change scanner or synchronization behavior;
- does not add or materially change a Lean formalization;
- does not materially change proof or submission evidence;
- does not create a new compatibility or dependency contract.

Use a numbered iteration for material project capability.

### No known iteration

Canonical value:

```text
none
```

Determine independently:

- whether work is required;
- whether an existing item should be reused;
- whether an unfinished item should be refined or replaced;
- whether a new iteration is justified;
- whether the task is standalone;
- which stage owns it;
- whether it should be deferred;
- whether it should be rejected.

Do not require `unknown`.

## Resolve repositories

Resolve the exact primary worktree before planning.

For each declared repository:

1. call `list_worktrees`;
2. match the exact absolute worktree path;
3. use the returned MCP target;
4. call `get_project_context` with the supplied mode;
5. verify project, path, branch, HEAD and dirty state.

Do not:

- infer targets from branch names;
- substitute a main worktree;
- inspect a similar-looking unrelated worktree;
- assume an additional project is an implementation target merely because it
  was supplied.

If the primary worktree cannot be resolved, return:

```text
PLANNING INCOMPLETE
```

Explain the mismatch and stop.

If a required additional repository cannot be resolved, return `PLANNING INCOMPLETE` when a material ownership or contract decision depends on it.

If the actual branch differs from the expected branch:

- report expected and actual values;
- do not prepare an implementation Issue for that target;
- continue only with read-only analysis that remains valid.

## Dirty worktrees

A dirty worktree is not automatically a blocker.

When relevant, inspect and distinguish:

- committed state;
- staged changes;
- unstaged changes;
- untracked files;
- deleted or renamed files.

Do not present uncommitted work as merged history.

State when a conclusion depends on uncommitted content.

When dirty work overlaps the proposed task:

- identify the overlap;
- avoid duplicate planning;
- determine whether the task should incorporate, replace or wait for it;
- add reconciliation constraints when needed.

Do not plan duplicate implementation over existing uncommitted work.

## Complete reading

Inspection is incomplete while mandatory content is truncated, omitted or paginated.

For files:

- continue with exact `next_line` and `next_column`;
- finish only when both are null.

For manifests and review bundles when used:

- continue with exact `next_cursor`;
- preserve the same snapshot;
- finish only when `has_more=false`;
- treat `truncated=true` as incomplete.

Read relevant omitted files directly with `read_project_file`.

If mandatory evidence cannot be read, return:

```text
PLANNING INCOMPLETE
```

State:

- what is missing;
- why it is required;
- which decision cannot be made.

Do not invent repository facts.

## Discovery workflow

Use this sequence:

1. parse `TASK_OR_IDEA`;
2. resolve declared worktrees;
3. inspect relevant dirty state;
4. identify candidate roadmap items;
5. read the referenced iteration and neighbours;
6. read repository guidance and applicable contracts;
7. inspect relevant implementation and tests;
8. inspect managed upstream material when applicable;
9. inspect relevant Lean project when applicable;
10. inspect package/dependency state when relevant;
11. inspect additional repositories only as required;
12. compare roadmap, implementation, contracts, tests and evidence;
13. identify the actual gap;
14. determine repository ownership;
15. assess necessity and timing;
16. compare valid solution options;
17. choose the planning decision;
18. prepare roadmap output, Issue and handoff.

Do not read repositories indiscriminately.

## Required inspection

Read at minimum in the primary BeeJSP repository:

- `AGENTS.md`;
- candidate roadmap item and neighbours;
- `docs/SECURITY.md`;
- `.github/ISSUE_TEMPLATE/issue.md`;
- directly relevant contract documentation;
- directly relevant implementation;
- directly relevant tests.

Read as applicable:

- `README.md`;
- `docs/ARCHITECTURE.md`;
- `docs/DEV_GUIDE.md`;
- `docs/FORMALIZATION.md`;
- `docs/SUBMISSION.md`;
- `pyproject.toml`;
- relevant files under `src/beejsp/`;
- relevant proof project under `proofs/`;
- `scripts/sync_jsp_docs.sh`;
- `.github/workflows/sync-jsp-docs.yml`;
- managed upstream provenance;
- relevant managed upstream documents.

For vendor/synchronization work, inspect the synchronization implementation, provenance contract and directly related tests.

For scanner/discovery work, inspect the parser/scanner, normalized contracts, filtering or scoring logic and related tests.

For formalization work, inspect the formalization contract, exact source problem, relevant proof project, statement, assumptions, dependencies and available verification evidence.

For submission-related work, inspect the submission contract, relevant managed upstream rules, completed proof evidence and any supplied current external-state evidence.

For package/build work, inspect package metadata, package layout and applicable build/import tests.

## Current state and actual gap

Determine:

- current stage;
- current roadmap state;
- completed neighbouring items;
- active planned work;
- prerequisite status;
- future/deferred scope;
- stale or duplicate roadmap scope;
- current implementation and contracts;
- current proof state when relevant;
- current managed upstream state when relevant;
- tests and verification evidence;
- blockers and limitations;
- implementation-roadmap drift;
- whether the task is already delivered;
- whether another item covers it.

Roadmap status is not implementation evidence.

Classify relevant drift using concise factual terms such as:

```text
implementation ahead of roadmap
roadmap ahead of implementation
stale future scope
duplicated scope
completed-history documentation debt
blocking implementation gap
blocking formalization gap
vendor/provenance gap
submission-evidence gap
dependency/compatibility gap
security-boundary gap
intentional sequencing difference
separate follow-up
```

Do not create product work solely to repair stale documentation.

State the verified gap using:

- current behavior;
- required behavior;
- evidence of absence or insufficiency;
- project impact;
- formalization impact when applicable;
- security/compatibility impact when applicable;
- why it matters now.

## Necessity verdict

Return exactly one:

```text
necessary now
necessary after prerequisite
useful but defer
already covered
already implemented
standalone maintenance
not justified
```

Consider:

- contribution to BeeJSP's purpose;
- roadmap sequencing;
- prerequisite readiness;
- reproducibility value;
- mathematical/formalization value;
- current contracts;
- implementation ownership;
- external/upstream uncertainty;
- opportunity cost versus higher-value work.

Do not approve work only because it is technically possible.

Do not approve work only because it could improve prize chances.

## Planning decision

Choose exactly one:

```text
reuse
refine
replace
insert
standalone
reject as unnecessary
```

Use `reuse` when an unfinished roadmap item already covers the verified task.

Use `refine` when an unfinished item is directionally correct but its scope, sequencing, ownership or checks need correction.

Use `replace` when unfinished future scope is materially stale or based on the wrong architecture.

Use `insert` when no existing item covers a verified coherent gap.

Use `standalone` only for genuinely small maintenance outside numbered project flow.

Use `reject as unnecessary` when the task is already covered, belongs outside BeeJSP, duplicates a source of truth or is premature.

Never rewrite completed history to make planning easier.

## Iteration versus standalone

A numbered iteration is normally required for substantial changes to:

- project behavior;
- discovery/scanner contracts;
- deterministic scoring/reporting;
- vendor synchronization;
- external integrations;
- Lean formalization;
- proof-verification contracts;
- submission evidence;
- package/public API;
- dependency surface;
- CI behavior;
- reusable BeeJSP capability.

Standalone is normally appropriate for:

- narrow documentation alignment;
- small test corrections;
- housekeeping;
- narrow local bugs without contract impact;
- small agent-skill/prompt maintenance;
- small packaging fixes without new public behavior.

## Solution options

Present no more than three materially valid options.

For each option state only what materially distinguishes it:

- implementation boundary;
- existing behavior reused;
- contracts changed;
- advantages;
- disadvantages;
- project/formalization/security impact;
- sequencing or dependency impact;
- main risk.

Recommend one using:

- smallest complete solution;
- strongest reuse;
- correct ownership;
- reproducible evidence;
- no second source of truth;
- minimum coupling;
- proportionate verification.

Do not manufacture alternatives.

If only one valid solution exists, say so.

## Roadmap reconciliation and numbering

Before proposing roadmap changes:

1. inspect the referenced item;
2. inspect neighbouring completed and unfinished items;
3. verify prerequisites;
4. check overlapping or duplicate scope;
5. check duplicate iteration identifiers;
6. compare implementation with roadmap claims;
7. select the correct stage and insertion point;
8. preserve completed history;
9. assess downstream unfinished items.

Rules:

- never change or renumber completed iteration identifiers;
- never reuse a completed identifier;
- never leave duplicate identifiers;
- preserve the repository's established numbering style;
- renumber unfinished items only when necessary;
- prefer retiring stale future scope over mass renumbering;
- do not automatically append every new item to the end.

## Cross-repository planning

Use:

```text
one implementation repository
= one Issue
= one target worktree
= one feature branch
= one PR
```

An additional repository supplied for context is not automatically an implementation target.

Prove necessity before assigning a separate Issue.

Official JSP upstream and `docs/vendor/jsp/` are not BeeJSP implementation targets.

## Implementation plan

For each genuine implementation target provide:

- repository and responsibility;
- current implementation to reuse;
- verified layers likely to change;
- behavior/contracts to change;
- source of truth;
- formalization/vendor impact when applicable;
- dependency/security constraints;
- required verification;
- documentation impact;
- implementation order;
- completion criteria.

Do not invent exact file paths.

When a concrete file is unconfirmed, identify the verified layer and require the executor to confirm the actual location.

Do not turn the plan into an executor prompt.

## Roadmap output contract

For a numbered item provide a compact copy-ready fragment with exactly these headings:

```text
Goal
Scope
Excluded
Deliverable
Acceptance criteria
Checks
DoD
```

Use:

```text
# Stage <number> — <English stage title>

## Iteration <number> — <English iteration title>

**Status:** PLANNED

### Goal

<English content>

### Scope

<English content>

### Excluded

<English content>

### Deliverable

<English content>

### Acceptance criteria

<English content>

### Checks

<English content>

### DoD

<English content>
```

Rules:

- roadmap content is English;
- technical identifiers remain unchanged;
- include only iteration-level information;
- place implementation detail in the Issue;
- do not add extra iteration headings;
- do not duplicate an existing stage heading unnecessarily.

For `reuse`, do not generate duplicate roadmap text.

For `refine` or `replace`, provide the complete replacement fragment.

For rejected work, provide no fake iteration.

## Standalone output contract

Use:

```text
Title:
Classification: standalone
Reason:
Scope:
Excluded:
Deliverable:
Checks:
DoD:
Roadmap insertion required: no
```

Use English.

Do not invent an iteration number.

## Issue preparation

Prepare one complete Issue in English for each implementation repository.

Read and follow that repository's actual:

```text
.github/ISSUE_TEMPLATE/issue.md
```

Rules:

- preserve actual heading order;
- fill relevant sections;
- use the correct roadmap;
- use observable and testable requirements;
- keep Issue scope aligned with the roadmap;
- do not duplicate stable rules from `AGENTS.md`;
- include only task-specific implementation and verification constraints.

For standalone work state:

```text
Iteration: none
```

Include formalization-sensitive status when applicable.

Without an approved dependency change:

- do not plan dependency changes;
- do not plan lockfile changes.

Never require:

```text
uv lock --check
```

Do not propose a version bump unless the task is release-related.

## Planning handoff constraints

Provide concise task-specific implementation constraints only.

As applicable include:

- ownership;
- implementation to reuse;
- source of truth;
- vendor boundary;
- exact formalization scope;
- provenance/reproducibility;
- dependency restrictions;
- sequencing;
- version restriction;
- dirty-worktree reconciliation.

Provide concise task-specific verification constraints only.

As applicable include:

- expected change level;
- formalization sensitivity;
- Acceptance Criteria scenarios;
- package checks;
- vendor/provenance checks;
- deterministic behavior checks;
- Lean/formalization checks;
- security checks;
- dependency status.

Do not prepare implementation or correction prompts.

Do not select Copilot or Codex.

## Naming

For each implementation repository provide:

- recommended branch name;
- recommended Conventional Commit title.

Follow repository conventions.

Do not propose commit, push, tag or release operations.

For ordinary work state:

```text
version not changed
```

## Output format

Return these sections in order:

```text
## Executive verdict
## Repository state
## Current implementation and contracts
## Roadmap selection
## Roadmap reconciliation
## Necessity verdict
## Architecture and repository ownership
## Solution options and recommendation
## Implementation plan
## Iteration numbering and insertion
## Copy-ready roadmap iteration or standalone task
## Copy-ready Issue
```

Use:

```text
## Copy-ready Issues
```

when multiple implementation repositories genuinely require separate Issues.

Then return:

```text
## Implementation order
## Verification and security
## Branch and commit naming
## Project-development recommendations
## Planning handoff
```

Add:

```text
## Assumptions or blockers
```

only when needed.

Write all output in English.

Keep technical identifiers, repository names, commands and paths unchanged.

Avoid repeating the same evidence across sections.

Do not claim Bee Dev MCP ran tests.

## Planning handoff

Return:

```text
Primary project repository:
Primary roadmap:
Stage:
Iteration:
Decision:
Necessity verdict:
Implementation targets:
Issue count:
Execution order:
Required separate prompt-02 runs:
Source of truth:
Public contracts:
Formalization-sensitive:
Task-specific implementation constraints:
Task-specific verification constraints:
Executor complexity factors:
Version status:
```

For standalone work:

```text
Iteration: none
```

For rejected work:

```text
Implementation targets: none
Issue count: 0
Required separate prompt-02 runs: 0
```

Do not create planning artifact files, roadmap edits, Issues, branches, commits or PRs.

Do not modify or execute anything.
