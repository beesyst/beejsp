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

## Proof artifacts

`STATEMENT.md`, `EVIDENCE.md`, `PLAN.md` and `PROGRESS.md` are persistent proof documents. `PROGRESS.md` is the only canonical milestone ledger.

Return full intermediate implementation reports in the Codex response, not as additional Markdown files in the proof root. Store temporary Lean experiments, diagnostic logs and intermediate results in unique directories directly under `/tmp`, created with `mktemp -d`; for example, `mktemp -d /tmp/beejsp-22-m39-XXXXXX`. Do not use `/home/bee/.cache/tmp/` for evidence intended for BeeMCP review.

Files intended for BeeMCP review must be ordinary UTF-8 `.log`, `.txt`, `.json` or `.md` files, not symlinks. Return their exact absolute paths. Confirm that the current artifact path is readable through the configured BeeMCP access model when possible; otherwise record a regular text file's path for an independent BeeMCP read check. Do not change BeeMCP server security rules.

Preserve the active milestone directory and at most two previous reviewed milestone directories, while retaining all unreviewed evidence regardless of that limit. Remove only obsolete directories created by this workflow, after their essential evidence and unique mathematical facts, diagnostics and provenance have been preserved in the persistent proof documents or substantial proof-local verification evidence. Do not delete existing unreviewed artifacts, unrelated directories or other users' files, and do not perform broad `/tmp` cleanup.

Durable mathematical state remains in `STATEMENT.md`, `EVIDENCE.md`, `PLAN.md` and `PROGRESS.md`. Retain only substantial reproducibility and verification evidence under the proof project's `verification/` directory. Do not create `verification/local/`, a separate report framework, new agents or infrastructure.

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

If a missing convenience theorem is needed, Codex should normally prove it rather than stop and report that it does not exist.

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

Use three verification levels: FAST, CHECKPOINT and FINAL.

### FAST — every ordinary proof milestone

During implementation, compile after each substantial coherent cluster.

At the end of every milestone:

- directly compile changed Lean modules;
- build new and affected modules;
- run the full incremental `lake build`;
- independently check new theorem bodies and relevant source contracts;
- print exact theorem signatures and audit their axioms;
- scan for `sorry`, `admit`, custom proof axioms and forbidden shortcuts;
- run `git diff --check`;
- verify statement, toolchain, dependency pins and unrelated-file preservation;
- record exact commands, exit codes and relevant logs.

Previously accepted historical evidence may be reused when
its source files, contracts, dependencies and toolchain are unchanged.

Do not routinely rerun all historical replays, supplementary checks
or the standalone historical Audit for ordinary milestones.

Never report reused evidence as freshly executed.

### CHECKPOINT — mathematical or regression boundary

Perform a checkpoint when:

- a major source theorem or mathematical proof stage is completed;
- an accepted theorem statement, definition or proof dependency changes;
- the Lean toolchain or dependency pins change;
- statement fidelity, axioms or regression behavior become suspicious;
- approximately 3–5 substantial milestones have passed since the last checkpoint.

Run all FAST checks plus independent source/statement review and historical regression checks relevant to the affected dependency graph.

Run the complete historical suite when the affected scope or identified regression risk justifies it.

Do not rerun unrelated historical checks solely to increase the command count.

### FINAL — principal theorem and delivery

After the principal theorem and mandatory mathematical bridges are complete, perform independent final verification:

- full historical Audit, all replays and supplementary checks;
- complete axiom and forbidden-shortcut audit;
- independent statement-fidelity and source correspondence review;
- clean reproduction from a pinned, committed source revision;
- exact toolchain, dependency and provenance verification;
- final complete change-set and preservation review.

FINAL verification must not be replaced by previously cached or reported historical results.

### Evidence and execution efficiency

Store complete command output in files, not in the Codex response.

Return concise summaries of checks, exit codes, axiom results, changed declarations and the first unresolved inference.

Include detailed diagnostics only for failures or suspicious results.

Preserve accepted historical receipts and substantive proof evidence. Do not generate duplicate historical logs or redundant reports for unchanged proofs.

Never skip a check explicitly required by the approved Issue, formalization contract or applicable independent verifier.

Do not perform final review after every helper.

Final review is appropriate only when the requested issue or major delivery milestone is actually complete.

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

When the paper omits an elementary step, formalize that step locally rather than treating the omission itself as a blocker.
