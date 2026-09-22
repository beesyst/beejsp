# SUBMISSION — BeeJSP

## Purpose

This document defines the BeeJSP operational workflow for preparing and submitting a completed formalization to The Justin Sun Prize.

This is a BeeJSP runbook.

The official external process may change.

Therefore:

> Current synchronized official material is authoritative for the actual
> external submission.

Before every real submission, refresh and reread the applicable official material.

## Scope

This document covers:

```text
completed BeeJSP formalization
→ submission readiness
→ public proof evidence
→ official contribution PR
→ official verification
→ claim workflow
→ recipient/payment workflow
```

It does not replace:

- official JSP rules;
- official JSP contribution instructions;
- official verification instructions;
- official claim forms.

## Sources of truth

BeeJSP operational source:

```text
docs/SUBMISSION.md
```

Current managed official reference:

```text
docs/vendor/jsp/
```

Important provenance:

```text
docs/vendor/jsp/UPSTREAM_REF
docs/vendor/jsp/UPSTREAM_COMMIT
```

Current external upstream:

```text
https://github.com/TheJustinSunPrize/awards
```

For a real submission, inspect at minimum the current synchronized versions of applicable:

```text
CONTRIBUTING.md
docs/award-process.md
docs/verification.md
docs/attribution.md
problems/README.md
skills/lean-verify/SKILL.md
.github/ISSUE_TEMPLATE/claim-award.yml
```

and the exact catalog file containing the target JSP entry.

## Core principle

Do not begin official submission until the BeeJSP proof is already complete and independently reviewed.

Correct order:

```text
formalize
→ verify
→ freeze evidence
→ submit
```

Incorrect order:

```text
open official PR
→ hope to finish proof later
```

## Submission is separate from BeeJSP development

BeeJSP remains the original proof repository.

The official JSP repository is an external contribution target.

Canonical separation:

```text
beesyst/beejsp
→ original proof and evidence

TheJustinSunPrize/awards
→ official problem / contribution / verification process
```

Do not convert BeeJSP into a permanent fork of the official repository.

## Managed vendor is not submission

Do not edit:

```text
docs/vendor/jsp/
```

to represent a contribution.

That directory is a generated read-only snapshot.

An official submission is made through the current official external contribution process.

## High-level lifecycle

Expected operational lifecycle:

```text
BeeJSP proof complete
↓
BeeJSP independent verification
↓
BeeJSP final review
↓
fresh JSP reference sync
↓
live competition check
↓
select public BeeJSP commit
↓
prepare official contribution
↓
official PR/review
↓
official verification
↓
official merge/status update
↓
claim workflow when applicable
↓
identity/recipient workflow
↓
award/payment when approved
```

Always reconcile this lifecycle with current official documentation before acting.

## Gate 1 — Formalization complete

A proof cannot enter submission preparation until it satisfies `docs/FORMALIZATION.md`.

At minimum verify:

- exact target problem identified;
- exact statement reviewed;
- full required scope represented;
- no unapproved stronger assumptions;
- no required case omitted;
- proof complete;
- no `sorry`;
- no `admit`;
- no custom unproved proof-placeholder axiom;
- pinned Lean environment;
- pinned dependencies when applicable;
- successful build;
- required axiom audit;
- source mathematical provenance;
- solver attribution;
- formalizer attribution.

If any item is unresolved:

```text
NOT SUBMISSION-READY
```

## Gate 2 — Final BeeJSP review

Run the normal BeeJSP agent pipeline.

Submission does not use a separate agent workflow.

Expected flow:

```text
Issue
→ implementation
→ independent verify-and-correct
→ final read-only review
```

The final BeeJSP PR for the proof must have no blocking findings before external submission preparation begins.

## Gate 3 — Refresh official reference

Immediately before submission-sensitive review:

```bash
./scripts/sync_jsp_docs.sh
```

Then review the resulting upstream provenance:

```text
docs/vendor/jsp/UPSTREAM_REF
docs/vendor/jsp/UPSTREAM_COMMIT
```

Commit/review the vendor update through the normal BeeJSP workflow when it changes tracked repository state.

Do not proceed from known stale official instructions.

## Gate 4 — Read the exact target record

Locate the target:

```text
JSP-XXXXXX
```

in the current synchronized problem catalog.

Record:

- exact JSP ID;
- exact current title;
- current problem-bank status;
- current Lean/formalization fields;
- current claim/status fields where applicable;
- source references;
- exact catalog file.

Do not edit the vendored record.

It is only reference material.

## Gate 5 — Recheck mathematical source

Before external submission, recheck:

- source problem;
- source solution;
- corrections or retractions;
- source attribution;
- exact scope.

A completed Lean proof should not be submitted against an obsolete or materially corrected formulation without review.

## Gate 6 — Live competition check

The managed snapshot is not current PR/Issue state.

Perform a live check for the target JSP as required by the current process.

Search applicable:

- open official PRs;
- merged official PRs;
- closed official PRs;
- Issues;
- exact JSP ID;
- exact problem title;
- known external Lean repositories.

Record material competing evidence.

Do not assume:

```text
Lean proof: No
```

in a catalog means:

```text
no one is currently formalizing it
```

## Gate 7 — Freeze public BeeJSP proof evidence

The submitted proof evidence must point to an immutable reviewed source state.

Before selecting the commit:

1. ensure the BeeJSP proof branch/repository state is public as required by the
   current official process;
2. verify the selected commit contains the complete reviewed proof;
3. verify the committed toolchain/dependencies;
4. rerun required proof checks against that state;
5. record the exact full commit SHA.

Do not use a short SHA when the official process requires a full commit.

Do not use an uncommitted working tree as submission evidence.

## Required proof evidence package

Prepare the exact fields required by the current official process.

BeeJSP should be able to supply at least, when applicable:

```text
Repository:
Branch:
Selected full commit SHA:
JSP ID:
Problem title:
Statement file:
Statement/theorem:
Proof file:
Proof entry point:
Lean toolchain:
Dependency state:
Build command:
Build result:
Axiom audit:
Mathematical source:
Solver:
Formalizer(s):
Verification evidence:
```

Do not invent values to complete the form.

## Repository ownership and contributor evidence

When the original proof repository belongs to an organization, ensure current official requirements for connecting the submitting GitHub account to the proof contribution are satisfied.

The contribution history should make the formalizer's work auditable.

Do not rewrite commit history solely to manufacture misleading attribution.

## Proof immutability after selection

Once a specific commit is used as official proof evidence:

- do not claim later uncommitted fixes are part of that evidence;
- if a blocking proof change is required, produce a new reviewed commit;
- update submission evidence according to the official process.

The selected SHA identifies a snapshot, not a moving branch.

## Gate 8 — Prepare official repository fork

Only after BeeJSP proof evidence is ready, prepare the official contribution repository according to the current official process.

Expected model:

```text
TheJustinSunPrize/awards
        ↓ fork
submitter fork
        ↓
submission branch
        ↓
official PR
```

The fork is used for contribution transport.

It is not a BeeJSP dependency.

## Sync the official fork

Before editing the submission branch:

- update from current official `main`;
- ensure the target catalog record has not materially changed;
- recheck competing official submissions.

Do not prepare a PR from a stale long-lived fork without reconciliation.

## Gate 9 — Modify only official contribution scope

Follow current official `CONTRIBUTING.md`.

For a formalization contribution, modify only the official repository content required by the current process.

Expected pattern is to update the existing relevant problem catalog entry and submission metadata.

Do not copy the full BeeJSP Lean project into the official repository unless current official instructions explicitly require it.

The BeeJSP repository remains the original proof source.

## Official catalog file

Use the exact current catalog file containing:

```text
JSP-XXXXXX
```

Do not guess the range from the ID without verifying the current repository layout.

Do not alter unrelated JSP entries.

## Official submission metadata

Populate current required metadata using exact evidence.

Possible fields may include:

- Lean proof availability;
- external source link;
- formalization contributors;
- publication/reference detail;
- attribution basis.

Use the current official template and contribution rules.

Do not add unsupported official status such as:

```text
verified
eligible
priority winner
award approved
paid
```

unless that state is assigned by the official process.

## Gate 10 — Official PR

Open the contribution PR using the current official PR template/process.

The PR should reference immutable BeeJSP proof evidence.

Before opening:

```text
proof complete
vendor fresh
official fork fresh
competition rechecked
selected SHA final
metadata complete
```

The objective is a reviewable submission, not merely the earliest possible incomplete PR.

## PR opening is not acceptance

Keep states distinct:

```text
PR opened
≠ verified

PR reviewed
≠ merged

PR merged
≠ award approved

award approved
≠ payment completed
```

Do not overstate status in BeeJSP documentation, README, social posts or reports.

## Official verification

After the official PR is opened, maintainers/verifiers may inspect:

- source repository;
- selected commit;
- theorem statement;
- proof;
- dependency/toolchain state;
- build reproducibility;
- axiom dependencies;
- mathematical scope;
- attribution.

Respond to verification findings with precise evidence.

If the proof itself requires correction:

```text
correct BeeJSP proof
→ independently verify
→ final BeeJSP review
→ publish corrected commit
→ update official evidence
```

Do not patch only the external catalog record when the original proof is wrong.

## Priority

Do not invent or infer priority semantics from memory.

Before a real submission, read the current synchronized official:

```text
award-process
verification
contribution rules
```

and follow the current mechanism by which formalization priority is established.

Record the official evidence supporting any priority claim.

A local/private commit timestamp must not be represented as official priority without official support.

## Candidate records

An official contribution may later produce or affect an official candidate record according to the current process.

BeeJSP must not manufacture official candidate records locally.

Track external state as evidence only.

## Claim workflow

Contribution and award claim are separate concepts when the current official process defines them separately.

After the contribution reaches the official state required for claiming:

1. refresh/recheck official claim instructions;
2. use the current official claim form;
3. submit from the account/identity required by current rules;
4. provide only requested public claim information;
5. follow private identity/compliance instructions separately.

Do not open a claim before the official prerequisites are satisfied.

## Identity verification

Identity/KYC data must not be stored in BeeJSP.

Do not commit:

- passport;
- government ID;
- address documents;
- tax documents;
- private email correspondence;
- compliance documents.

Use only the official private verification channel.

## Payment

Award/payment terms are external and may change.

Before providing payment information:

- verify current official award/recipient instructions;
- verify recipient identity;
- use only requested official/private channel;
- verify destination/network requirements independently.

Never expose:

- wallet private key;
- seed phrase;
- custodial credentials.

BeeJSP should track at most non-sensitive public status needed for project history.

## Public project status

BeeJSP README/report status should use factual labels.

Examples:

```text
formalization in progress
proof complete
BeeJSP verified
official PR submitted
official PR merged
claim submitted
award announced
```

Only use a label when evidence supports it.

Avoid ambiguous:

```text
won
first
verified by JSP
award secured
```

without official evidence.

## Failed external verification

If official verification rejects a proof:

1. identify whether the issue is:
   - statement fidelity;
   - proof completeness;
   - reproducibility;
   - axioms;
   - attribution;
   - submission metadata;
   - process mismatch;

2. correct the owning source;
3. rerun BeeJSP verification;
4. prepare updated immutable evidence;
5. follow the official correction/resubmission process.

Do not conceal the rejection by changing only wording.

## Competing submissions

If another valid formalization appears:

- preserve our proof if useful to the community;
- do not misrepresent first-publication or priority;
- continue only when independent value justifies the effort;
- follow official rules for priority/award questions.

BeeJSP remains useful even when another party is first.

## Multiple JSP proofs

Each JSP proof receives its own:

```text
proofs/JSP-XXXXXX/
```

and its own verification/submission evidence.

Do not bundle multiple unrelated JSP claims into one external contribution unless current official instructions explicitly call for it.

## Submission record inside BeeJSP

After a real external submission, BeeJSP may document non-sensitive public evidence such as:

- JSP ID;
- selected BeeJSP commit;
- official PR link/number;
- public status;
- public official candidate/award reference.

Do not create a second authoritative record of official status.

Link to official evidence.

## Automation boundary

BeeJSP may automate:

- validation;
- evidence preparation;
- competition queries;
- reference synchronization.

Normal agent workflows must not automatically:

- commit;
- push;
- open external PRs;
- merge;
- submit claims;
- send KYC;
- submit payment details.

Such external write actions require an explicitly approved workflow and appropriate authorization.

## Pre-submission checklist

Before official PR:

- [ ] exact JSP confirmed
- [ ] mathematical source confirmed
- [ ] solver attribution confirmed
- [ ] formalization complete
- [ ] statement fidelity approved
- [ ] no `sorry`
- [ ] no `admit`
- [ ] no custom proof-placeholder axiom
- [ ] pinned Lean environment
- [ ] proof builds
- [ ] axiom audit complete
- [ ] clean reproduction complete when required
- [ ] formalizer attribution confirmed
- [ ] BeeJSP final review approved
- [ ] JSP managed reference freshly synchronized
- [ ] current official contribution rules reread
- [ ] live competition checked
- [ ] final public BeeJSP commit selected
- [ ] full commit SHA recorded
- [ ] exact theorem/proof location recorded
- [ ] official fork synchronized
- [ ] correct catalog file identified
- [ ] official PR template/process confirmed

Any required unchecked critical item blocks submission.

## Post-PR checklist

After official PR:

- [ ] official PR URL recorded
- [ ] verifier feedback monitored
- [ ] corrections made in BeeJSP first when proof changes
- [ ] updated immutable evidence supplied when required
- [ ] official final PR status recorded
- [ ] claim prerequisites checked against current rules
- [ ] claim submitted only when eligible
- [ ] private identity/payment data kept outside BeeJSP
- [ ] public status documented without exaggeration

## What not to do

Do not:

- submit incomplete Lean;
- race with `sorry` placeholders;
- submit a weaker theorem as the original problem;
- edit vendored JSP files as an official contribution;
- maintain a permanent official fork as BeeJSP's source of truth;
- rely on stale contribution instructions;
- claim priority from unsupported evidence;
- claim an award before official confirmation;
- commit KYC documents;
- commit wallet secrets;
- overwrite solver attribution;
- hide proof corrections behind metadata-only changes.

## Summary

The BeeJSP submission rule is:

```text
proof first
→ verification second
→ immutable public evidence
→ fresh official process
→ contribution
→ official verification
→ claim/recipient process
```

Submission speed matters only after correctness, reproducibility and provenance are established.
