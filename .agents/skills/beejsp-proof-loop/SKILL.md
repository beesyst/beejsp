---
name: beejsp-proof-loop
description: Coordinate long-running BeeJSP Lean formalization through milestone-based Codex passes, using executor reports as the default working state and BeeMCP only for checkpoints, suspicious blockers, major proof milestones and final review.
---

# BeeJSP Proof Loop

Use this workflow for long-running Lean formalization tasks.

## Goal

Maximize mathematical progress per Codex pass while preserving:

- source fidelity;
- reproducible Lean verification;
- statement fidelity;
- no proof shortcuts;
- minimal architectural churn.

## Normal iteration loop

The normal loop is:

1. Define one coherent mathematical milestone.
2. Give Codex a concrete implementation prompt.
3. Codex works directly in the local worktree using normal local tools:
   - file read/edit;
   - shell;
   - Lean/Lake;
   - rg/grep/git/sha256sum;
   - local Mathlib source inspection.
4. Codex returns a structured implementation report.
5. Use that report as the default working state.
6. Immediately define the next mathematical milestone.

Do not perform a full repository inspection after every pass.

## BeeMCP policy

BeeMCP is a control/checkpoint mechanism, not part of every proof iteration.

Do NOT use BeeMCP routinely when the Codex report is internally consistent
and contains:

- starting/final SHA;
- declarations added;
- exact remaining blocker;
- `lake env lean ...` result;
- `lake build` result;
- audit result;
- `git diff --check`;
- shortcut scan;
- unchanged statement/pins/dependencies/version confirmation.

Use BeeMCP when one of these conditions occurs:

1. Codex reports a suspicious or unclear blocker.
2. Two consecutive passes make little or no mathematical progress.
3. A report contradicts a previous report.
4. Statement, dependency, toolchain, Mathlib pin, or package version changes unexpectedly.
5. There is reason to suspect a helper theorem proves the wrong mathematical fact.
6. Before moving to a substantially new source theorem when the previous theorem was large or delicate.
7. Before final read-only review.

Also perform a checkpoint after major proof milestones such as:

- `sourceLemma37_complete`;
- Lemma 3.8 complete;
- Lemma 3.9 complete;
- Lemma 3.1 complete;
- Theorem 3.11 complete;
- principal theorem complete.

As a rough fallback, perform a BeeMCP checkpoint every 5–10 ordinary Codex passes.

## Prompt design

Each Codex pass should target one real mathematical milestone.

Avoid meaningless micro-passes such as:

- one arithmetic helper;
- one bounds lemma;
- one trivial wrapper theorem.

Helpers are allowed inside a pass when they directly support the milestone.

A good pass looks like:

    missing geometry
      → required local helpers
      → source theorem milestone
      → Lean verification

Do not ask Codex merely to investigate unless investigation itself is required.

If a missing convenience theorem is needed, Codex should normally prove it
rather than stop and report that it does not exist.

## Anti-stall rule

Absence of a pre-existing helper is not a blocker.

A valid blocker should be one of:

- actual mathematical inconsistency;
- representation mismatch;
- false previously established invariant;
- incompatible Lean type/API that cannot be repaired locally without changing an approved contract;
- ambiguity in the mathematical source that materially changes the proof.

If Codex stops, require:

- exact declaration names;
- exact incompatible goal/type;
- why a local helper cannot solve it;
- smallest next mathematical action.

## Verification discipline

During implementation, compile after each substantial coherent cluster.

At the end of a pass run the project-required Lean/build/audit checks and:

- `git diff --check`;
- forbidden-shortcut scan.

Do not perform final review after every helper.

Final review is appropriate only when the requested issue or major delivery
milestone is actually complete.

## Repository actions

Unless explicitly requested:

- no commit;
- no push;
- no PR;
- no merge.

## Source discipline

The mathematical source is authoritative.

Do not silently:

- weaken the statement;
- strengthen assumptions;
- change constants;
- replace source geometry with an easier different statement;
- introduce proof shortcuts.

When the paper omits an elementary step, formalize that step locally rather
than treating the omission itself as a blocker.
