# BeeJSP implementation and test prompt preparation

Use only Bee Dev MCP.

Read:

- `AGENTS.md`
- `.agents/skills/beejsp-implement-issue/SKILL.md`
- `.agents/skills/beejsp-verify-and-correct/SKILL.md`

## Primary target

- Project: `beejsp`
- Worktree: `<TARGET_WORKTREE>`
- Expected branch: `<FEATURE_BRANCH>`
- Base branch: `main`
- Mode: `<MODE>`
- Roadmap context: `<ROADMAP_CONTEXT>`

## Planning context

```text
<PLANNING_CONTEXT_OR_NONE>
```

## Approved Issue

```text
<FULL_APPROVED_ISSUE>
```

## Additional projects

```text
<ADDITIONAL_PROJECTS_OR_NONE>
```

Verify the exact target, branch, Issue, repository boundaries, and applicable skills.

Do not implement the task, modify files, or run commands.

Prepare exactly two short copy-ready prompts:

1. `Copilot implementation`
   - implement Scope and Acceptance Criteria;
   - run required checks for the actual change level;
   - return a complete implementation and verification report.

2. `Codex verification and correction`
   - independently verify the actual target worktree;
   - verify every Acceptance Criterion without relying on the first executor's report;
   - make only necessary in-scope corrections;
   - rerun required checks;
   - return a complete consolidated verification report.

Both prompts must:

- be independent and self-contained;
- not require data or reports from the other executor;
- contain the exact worktree, branch, and base branch;
- reference `AGENTS.md` and the applicable skill;
- include the Issue source when supplied and the same compact snapshot of the approved task contract: Summary, Scope, Excluded, Deliverable, Acceptance Criteria, Change level, required checks, and task-specific constraints;
- include only task-specific constraints;
- not duplicate stable repository rules;
- prohibit commit, push, PR, and merge;
- not require Bee Dev MCP, MCP Mode, or read-only behavior from Copilot or Codex.

Return only the two copy-ready executor prompts with no additional analysis.
