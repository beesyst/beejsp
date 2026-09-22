# FORMALIZATION — BeeJSP

## Purpose

This document defines the canonical mathematical and Lean formalization rules for `beejsp`.

It applies whenever BeeJSP:

- formalizes a mathematical problem;
- reviews an existing Lean formalization;
- prepares proof evidence;
- evaluates whether a formalization is complete;
- prepares a formalization for external submission.

The primary requirement is:

> BeeJSP must prove the intended mathematical statement, not merely a convenient
> theorem that happens to compile.

Use this document together with:

- `docs/ARCHITECTURE.md`;
- `docs/DEV_GUIDE.md`;
- `docs/SECURITY.md`;
- `docs/SUBMISSION.md`;
- `docs/ROADMAP.md`;
- `AGENTS.md`.

## Core formalization principle

The required chain is:

```text
original mathematical problem
→ exact mathematical interpretation
→ exact Lean statement
→ complete Lean proof
→ reproducible verification
```

All transitions must be reviewable.

The proof is not complete merely because:

- Lean accepts some theorem;
- the theorem has a similar title;
- a finite example was proved for a general problem;
- a stronger assumption made the proof easy;
- an external summary says the result is solved.

## Terms

- **Problem** — the original mathematical question or theorem being targeted.
- **Problem source** — authoritative or relevant publication/source describing
  the problem.
- **Mathematical solution** — mathematical reasoning claimed to solve the
  problem.
- **Solver** — person or team credited with the mathematical solution.
- **Formal statement** — Lean theorem statement intended to represent the
  mathematical problem.
- **Formalization** — Lean representation of the statement and its complete
  proof.
- **Formalizer** — contributor responsible for the Lean formalization.
- **Verifier** — reviewer or process independently checking the formalization.
- **Statement fidelity** — correspondence between the original mathematical
  problem and the Lean statement.
- **Proof completeness** — absence of missing proof steps for the claimed
  theorem.
- **Proof provenance** — evidence connecting a formalization to repository,
  authorship, source and exact commit.
- **Axiom audit** — inspection of axioms required by the final theorem.
- **Reproduction** — rebuilding/checking the proof from committed sources and
  pinned environment.

## Formalization-sensitive change

A change is formalization-sensitive when it modifies any of:

- Lean theorem statement;
- theorem scope;
- definitions affecting theorem meaning;
- mathematical assumptions;
- proof;
- proof dependencies;
- Lean toolchain;
- formalization provenance;
- formalizer attribution;
- axiom-audit behavior;
- proof submission evidence.

Formalization-sensitive work requires proof-specific verification in addition to the normal repository change level.

## Formalization lifecycle

Canonical lifecycle:

```text
candidate selected
↓
problem sources collected
↓
mathematical solution reviewed
↓
exact statement designed
↓
bounded feasibility spike when needed
↓
proof implementation
↓
local build
↓
placeholder audit
↓
axiom audit
↓
statement-fidelity review
↓
clean reproduction
↓
provenance review
↓
final BeeJSP review
↓
submission-ready
```

Do not mark later stages complete when earlier stages remain uncertain.

## Problem identity

Before writing a real proof, record the exact problem being formalized.

Identify as applicable:

- JSP identifier;
- exact title;
- original problem source;
- official problem-bank record;
- historical formulation;
- problem author;
- publication date;
- relevant corrected formulation;
- known solution source.

If multiple materially different formulations exist, identify which one is being formalized.

Do not silently select the easiest formulation.

## Source hierarchy

Use source quality proportional to the claim.

Prefer, where available:

1. original paper or problem statement;
2. official problem repository/maintainer record;
3. published mathematical solution;
4. author-maintained solution;
5. peer-reviewed or recognized secondary source;
6. other public evidence.

A catalog summary is useful metadata.

It does not automatically replace the full mathematical source.

## Mathematical-solution gate

For formalization of an already solved problem, identify a complete mathematical solution before claiming the Lean work is a formalization of that solution.

Determine:

- who produced the solution;
- where the complete proof is available;
- whether corrections exist;
- whether the source proof covers the full problem;
- whether the formalization follows that proof or another valid proof.

If the source contains only:

- an answer without proof;
- a sketch;
- an informal claim;
- a partial case;
- a conjectural outline;

do not present it as a complete source proof.

A separate mathematical-research task may be required.

## New mathematical solutions

BeeJSP may also formalize new mathematical reasoning.

In that case:

- distinguish conjecture from proof;
- maintain clear authorship;
- require the same statement-fidelity and completeness gates;
- do not use Lean as a substitute for understanding the target theorem;
- preserve enough mathematical explanation for independent review.

## Statement-fidelity contract

The formal statement must preserve the mathematical content required by the problem.

Review at minimum:

- domains;
- quantifiers;
- hypotheses;
- conclusion;
- logical direction;
- existence conditions;
- uniqueness conditions;
- equality and inequality direction;
- finiteness assumptions;
- non-emptiness assumptions;
- positivity/non-negativity assumptions;
- indexing conventions;
- exceptional cases;
- boundary cases;
- implicit mathematical conventions made explicit in Lean.

Required property:

```text
Lean theorem
↔ intended mathematical statement
```

The exact logical relationship must be understood.

## No silent weakening

Do not replace:

```text
∀ x, P x
```

with:

```text
P specificExample
```

and claim the original theorem.

Do not replace:

```text
∃ x, P x ∧ Q x
```

with:

```text
∃ x, P x
```

Do not restrict a domain solely to make the proof easier unless that restriction is part of the original problem.

A weaker theorem may be useful as a lemma or spike.

It is not completion evidence for the original problem.

## No hidden strengthening of assumptions

Do not introduce assumptions such as:

- stronger regularity;
- stronger finiteness;
- positivity;
- decidability;
- non-zero conditions;
- additional ordering;
- additional algebraic structure;

unless justified by the original problem or proved from its assumptions.

Lean typeclass requirements should be reviewed for mathematical meaning.

An implementation convenience must not silently become a new theorem hypothesis.

## Definitions

Prefer existing standard Mathlib definitions when they accurately represent the required concept.

Create custom definitions only when:

- Mathlib lacks the concept;
- the source formulation requires a specific representation;
- a local abstraction makes the proof materially clearer.

When a custom definition affects theorem meaning, document its correspondence to the source mathematical concept.

## Theorem naming

Use stable, understandable names.

For a JSP proof, the final project should make the principal theorem easy to identify.

Example shape:

```lean
theorem jsp_000288 : ... := by
  ...
```

The exact name is not globally mandated by BeeJSP.

It must be recorded clearly in proof documentation and submission evidence.

## Proof-project isolation

Each real JSP proof should be independently reproducible from its own directory.

Typical boundary:

```text
proofs/JSP-XXXXXX/
```

The proof project should not depend on:

- uncommitted parent-repository Python state;
- another developer's local Mathlib edits;
- hidden generated source;
- manually patched external files;
- an undocumented filesystem path.

Shared BeeJSP proof utilities should be introduced only after multiple real proofs demonstrate a stable reusable need.

## Toolchain pinning

Every real proof must pin its required Lean environment.

At minimum this normally includes:

```text
lean-toolchain
```

When Lake dependencies are used, commit the applicable project/dependency metadata.

The objective is:

```text
selected BeeJSP commit
→ recover exact proof source
→ recover required Lean environment
→ check proof
```

## Mathlib and dependencies

Use Mathlib rather than reimplementing standard mathematics when suitable.

Dependency rules:

- minimum necessary dependencies;
- pinned revisions;
- reviewed source;
- no dependency added only for future convenience;
- no opaque binary proof dependency;
- no undocumented local patches.

A dependency update in a completed formalization is a proof-affecting change and requires re-verification.

## Proof completeness

A final formalization must prove the principal theorem completely.

The following are prohibited in accepted completion evidence:

```text
sorry
admit
```

A completed formalization must also not use a custom unproved axiom as a replacement for a missing theorem.

Examples of unacceptable shortcuts:

```lean
axiom missing_key_lemma : ImportantStatement
```

followed by a proof that merely applies `missing_key_lemma`.

## Exploratory placeholders

During local exploration, temporary placeholders may help isolate later work.

Before the formalization is reported complete:

```text
temporary placeholders
→ removed
→ proof rebuilt
→ audits rerun
```

No completion report may omit a surviving placeholder.

## Trusted axioms

Lean and Mathlib may rely on standard foundational axioms.

The relevant issue is not "zero axioms under all circumstances".

The relevant issue is whether the final theorem depends on:

- expected trusted foundations;
- or a custom assumption introduced to bypass missing mathematics.

Perform the axiom audit required by the approved task or current external verification contract.

Record the result.

## Axiom audit

For a completed proof, identify the principal theorem and inspect its axiom dependencies using the current repository-approved Lean verification method.

The audit evidence should identify:

- theorem;
- command/method;
- result;
- unexpected axioms if any.

Any unexpected custom proof axiom is blocking until understood and approved.

## Build verification

Primary proof build:

```bash
lake build
```

from the proof project directory unless the project explicitly defines another canonical command.

Record:

- exact directory;
- exact command;
- exit code;
- relevant failures/warnings.

Do not claim a build passed when it was not executed.

## Clean reproduction

A submission-sensitive formalization should be reproduced from committed source state.

The reproduction should establish that the proof does not rely on:

- uncommitted source;
- manually modified dependency checkout;
- editor cache;
- hidden generated theorem;
- developer-specific absolute path.

CI may provide additional evidence.

CI does not replace statement review.

## Statement review

Statement review is independent of proof compilation.

Reviewer should compare:

```text
original source
vs
formal mathematical interpretation
vs
Lean definitions
vs
top-level Lean theorem
```

Document material translations.

Examples:

```text
natural-language "positive integer"
→ Lean `n : ℕ` plus `0 < n`

"consecutive"
→ exact relation used in Lean

"for all sufficiently large"
→ explicit quantified threshold

"graph"
→ exact graph representation
```

The review should focus on mathematical equivalence, not cosmetic syntactic similarity.

## Source-proof mapping

When formalizing an existing proof, maintain enough structure to explain how the Lean proof corresponds to the mathematical reasoning.

For substantial proofs, a local proof README may include:

```text
source step
→ Lean lemma
```

This need not reproduce the original paper.

It should make verification practical.

## Counterexamples and explicit witnesses

Problems solved by explicit counterexample or witness can be especially suitable for formalization.

A valid formalization still must prove every required property of the witness.

Example:

```text
candidate value supplied
≠ proof

candidate value
+ proof all required properties
= formal evidence
```

Do not rely on external computation without representing and verifying the required result according to the proof contract.

## Computational proofs

When computation is part of the proof:

- identify what is being computed;
- identify what code or Lean reduction establishes;
- keep computation bounded and reproducible;
- distinguish trusted external computation from kernel-checked computation;
- document imported certificates when applicable.

Do not call an opaque external program result a machine-checked Lean proof without a verified bridge.

## Formalization status

Use conservative status semantics.

Suggested internal states:

```text
research
spike
in_progress
proof_complete
verified
submission_ready
```

Do not mark:

```text
verified
```

based only on code generation.

Do not mark:

```text
submission_ready
```

before provenance, statement fidelity and required external-process evidence are complete.

## Independent verification

Initial implementation and independent verification should be separate passes.

Verifier should not merely trust:

- implementer's report;
- AI explanation;
- README claim.

Verify from:

- source;
- theorem statement;
- build;
- audit;
- provenance;
- current contracts.

## Formalization evidence

For a completed real proof, retain enough evidence to identify:

```text
problem
source
mathematical solution
solver
formalizer
repository
selected commit
proof project
principal theorem
toolchain
dependencies
build command
build result
axiom audit
statement-fidelity review
```

Not every value must live in one file.

All must be recoverable for submission-sensitive work.

## Attribution

BeeJSP must distinguish credit accurately.

### Original problem

Credit problem source/author where applicable.

### Mathematical solution

Credit the mathematical solver.

### Lean formalization

Credit the actual formalization contributors.

### Verification

Credit independent verification where appropriate.

Do not collapse all roles into:

```text
BeeJSP solved the problem
```

unless BeeJSP contributors actually produced the mathematical solution and evidence supports that claim.

## AI attribution

AI may contribute to:

- research;
- proof search;
- Lean code;
- refactoring;
- debugging;
- documentation.

Human/project attribution must still follow the applicable repository and external-submission rules.

Do not invent a solver identity from tool usage.

## Originality and competition

Before investing heavily in a formalization intended for external submission, check available current evidence for existing formalizations.

Before final external submission, perform a fresh live competition check.

A vendored catalog value is not enough to prove that no competitor exists.

## Managed JSP verification guidance

For JSP-targeted work, consult current managed official verification material under:

```text
docs/vendor/jsp/
```

including the vendored Lean verification guidance when applicable.

Do not copy that upstream skill into a competing BeeJSP source of truth.

BeeJSP's rules should refer to the synchronized official reference.

## External-process changes

Official external requirements may change.

Before a submission-sensitive review:

```text
sync official JSP reference
→ inspect updated rules
→ reconcile BeeJSP evidence
```

Do not assume an old formalization package remains submission-ready after an external process change.

## Security

Formalization is also a supply-chain activity.

External:

- proof repositories;
- Lean packages;
- scripts;
- generated certificates;

may contain executable code.

Follow:

```text
docs/SECURITY.md
```

before executing untrusted third-party material.

## Versioning and proof identity

BeeJSP SemVer is project/tooling versioning.

It is not formal proof identity.

Proof evidence should use exact immutable source identity as required by the applicable workflow.

For JSP submission-sensitive work this normally includes an exact full commit SHA when required by the current official process.

## Definition of formalization complete

A formalization is complete only when all applicable items are true:

- exact problem identified;
- exact mathematical statement understood;
- Lean statement preserves required scope;
- no unapproved stronger assumptions;
- all required cases covered;
- proof contains no `sorry`;
- proof contains no `admit`;
- no custom unproved proof-placeholder axiom remains;
- pinned toolchain exists;
- pinned dependencies exist where needed;
- proof builds;
- required axiom audit is complete;
- clean reproduction is demonstrated when required;
- solver/formalizer attribution is accurate;
- source/provenance evidence is available;
- independent statement-fidelity review has no blocker.

## Definition of submission-ready

A proof is submission-ready only when it is formalization-complete and:

- final BeeJSP review is approved;
- selected public source state is fixed;
- required immutable commit evidence is available;
- current official external process has been rechecked;
- live competition check required by the task is complete;
- submission metadata and attribution are complete.

See:

```text
docs/SUBMISSION.md
```

## What not to do

Do not:

- formalize a weaker problem and claim the stronger one;
- introduce convenient hidden assumptions;
- leave `sorry`;
- leave `admit`;
- replace mathematics with custom axioms;
- rely on uncommitted dependencies;
- claim authorship inaccurately;
- call compilation proof of semantic equivalence;
- claim external priority from a local commit;
- claim external acceptance before official evidence;
- treat AI confidence as mathematical proof.

## Summary

BeeJSP formalization is complete only when:

```text
correct source problem
+ exact Lean statement
+ complete Lean proof
+ reproducible environment
+ acceptable axiom dependencies
+ verified provenance
+ accurate attribution
```

The goal is not merely code that compiles.

The goal is a mathematical result that another person can inspect, reproduce and trust.
