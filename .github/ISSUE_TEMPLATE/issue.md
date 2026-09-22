---
name: Issue
about: "Use title prefixes: Feature:, Fix:, Docs:, Chore:, Idea:"
title: "Feature: <short title>"
labels: []
assignees: []
---

### Summary

One sentence: what needs to be done or explored.

### Type

Select one primary type:

- [ ] Feature
- [ ] Fix
- [ ] Docs
- [ ] Chore
- [ ] Idea

### Roadmap / iteration

- Iteration:
- Stage:
- Goal from `docs/ROADMAP.md`:

If this is not tied to a roadmap iteration, explain why.

### Context

Why this matters.

Include:

- current problem / limitation;
- why now;
- related Issue / PR / roadmap item if any;
- affected area if relevant (Python tooling, managed JSP reference, Lean formalization, submission workflow, etc.).

### Scope

What is included / excluded.

**Included**

- ...
- ...

**Excluded**

- ...
- ...

### Deliverable

What should exist when this is done.

Examples:

- new or updated BeeJSP Python tooling;
- updated problem-bank ingestion / normalization;
- updated candidate filtering / scoring;
- updated competition analysis;
- updated managed JSP vendor synchronization;
- new or updated Lean formalization;
- updated proof verification evidence;
- updated submission evidence / workflow;
- package / build metadata update;
- documentation update.

### Acceptance Criteria

What must be true for this task to be considered done.

- ...
- ...
- ...

Keep criteria observable and testable.

### Change level

Choose one:

- [ ] low-risk
- [ ] runtime-risk
- [ ] security-sensitive

> Use `AGENTS.md` / `docs/SECURITY.md` to classify the task.

### Formalization sensitivity

Choose one:

- [ ] not formalization-sensitive
- [ ] formalization-sensitive

> A change is formalization-sensitive when it affects Lean statements, proofs,
> theorem scope, mathematical assumptions, proof dependencies, provenance,
> attribution, axiom-audit behavior, or proof submission evidence.

### Package / Public API / Contract impact

Mark what is expected:

- [ ] no package, public API or contract change expected
- [ ] Python public / package behavior may change
- [ ] problem-bank / normalized data contract may change
- [ ] scanner / filtering / scoring behavior may change
- [ ] generated artifact / report contract may change
- [ ] managed JSP vendor contract may change
- [ ] Lean statement / proof may change
- [ ] Lean toolchain / dependency surface may change
- [ ] formalization provenance / attribution may change
- [ ] submission evidence / workflow may change
- [ ] package metadata / build behavior may change
- [ ] Python runtime dependency surface may change
- [ ] backward compatibility / migration impact expected
- [ ] docs update likely required

If known already, list affected files / contracts:

- `...`
- `...`

### Tests

What must be checked.

**Python / package**

- [ ] targeted tests
- [ ] `uv run pytest -q`
- [ ] `uv run ruff check .`
- [ ] `uv run ruff format --check .`
- [ ] `uv build` when package / build behavior is affected
- [ ] package import smoke when applicable

**Managed JSP reference**

- [ ] `scripts/sync_jsp_docs.sh` when applicable
- [ ] vendor provenance verified when applicable
- [ ] second-run sync idempotence verified when applicable
- [ ] malformed / incomplete upstream behavior checked when applicable

**Lean / formalization**

- [ ] `lake build` when applicable
- [ ] exact statement / scope checked when applicable
- [ ] no `sorry` / `admit` when applicable
- [ ] axiom audit when applicable
- [ ] clean proof reproduction when applicable
- [ ] provenance / attribution checked when applicable

**Quality / security**

Mark what is expected for this task:

- [ ] SAST
- [ ] SCA
- [ ] fuzzing
- [ ] some checks are not applicable

Describe the required scenarios briefly:

- ...
- ...
- ...

### Artifacts

What files / outputs should appear or be updated in tests, docs, package metadata, proof evidence, or build outputs.

Examples:

- `tests/...`
- `src/beejsp/...`
- `proofs/JSP-XXXXXX/...`
- `scripts/sync_jsp_docs.sh`
- `docs/vendor/jsp/...`
- `README.md`
- `docs/ROADMAP.md`
- `docs/ARCHITECTURE.md`
- `docs/FORMALIZATION.md`
- `docs/SUBMISSION.md`
- `docs/SECURITY.md`
- `docs/DEV_GUIDE.md`
- `pyproject.toml`
- `uv.lock` if an approved Python dependency change requires it
- built wheel / source distribution when package verification is required
- generated reports / proof-verification evidence when applicable

### Security notes

Fill if relevant:

- external / untrusted input involved:
- filesystem / path handling involved:
- shell / process execution involved:
- network / GitHub / external API integration involved:
- managed vendor synchronization involved:
- credentials / tokens involved:
- identity / KYC / payment data involved:
- dependency changes involved:
- cross-repository compatibility involved:

### Formalization notes

Fill if relevant:

- source mathematical problem:
- source mathematical solution:
- intended Lean statement:
- solver attribution:
- formalizer attribution:
- pinned Lean / dependency requirements:
- statement-fidelity risk:
- required axiom / reproducibility evidence:

### Definition of Done

Task is done when:

- [ ] behavior / contract is implemented within the declared scope
- [ ] public / package behavior remains explicit and documented when affected
- [ ] backward compatibility is preserved or migration is explicitly documented
- [ ] required Python checks are green
- [ ] package builds successfully when package behavior is affected
- [ ] managed vendor provenance remains valid when affected
- [ ] formalization requirements from `docs/FORMALIZATION.md` are satisfied when applicable
- [ ] exact mathematical scope is preserved when formalization-sensitive
- [ ] required Lean build / axiom / reproducibility evidence exists when applicable
- [ ] no unintended repository ownership or dependency-direction change was introduced
- [ ] dependencies remain unchanged unless explicitly approved
- [ ] no secrets, KYC material, private payment data, or unrelated private data are committed
- [ ] checks required by `AGENTS.md` / `docs/SECURITY.md` are completed
- [ ] docs are updated when architecture, formalization, security, submission, compatibility, or package behavior changed
- [ ] changelog / version decision is recorded when applicable
- [ ] result is ready to be closed through PR

### Notes

Constraints, assumptions, extra links.

Use this section for:

- follow-up ideas;
- explicit non-goals;
- source / proof references;
- upstream JSP references;
- migration notes;
- reviewer hints;
- compatibility notes;
- implementation constraints.
