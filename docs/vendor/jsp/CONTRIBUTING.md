# Contributing

Contribute public problem records, solution and proof references, attribution,
and award evidence through reviewed PRs. The [award process](docs/award-process.md)
is the main guide for submission, claims, candidate publication, the 14-day public
review, challenges and delivery.

## Choose the right entry point

| Purpose | Where to start |
| --- | --- |
| Submit a complete solution, Lean proof reference or supported catalog update | [PR template](.github/PULL_REQUEST_TEMPLATE.md) and the submission requirements below. |
| Recommend a problem | [Recommendation form](.github/ISSUE_TEMPLATE/recommend-problem.yml). |
| Claim an award for your own contribution | [Claim form](.github/ISSUE_TEMPLATE/claim-award.yml), after the contribution PR merges or under the recorded-solver exception. Follow the [application and identity steps](docs/award-process.md#step-2-apply-and-participate-in-public-review). |
| Correct a record | [Correction form](.github/ISSUE_TEMPLATE/correction.yml), with the current text, proposed change and sources. |
| Challenge a candidate or announced award | [Dispute form](.github/ISSUE_TEMPLATE/dispute.yml), with the disputed claim and public evidence. Submit replacement proofs in a linked PR. |
| Share feedback, suggestions or questions | [Feedback form](.github/ISSUE_TEMPLATE/feedback.yml). |
| General conversation | [Discussions](docs/discussions-notice.md). |

Update existing PRs and issues for the same contribution instead of creating
duplicates. Maintainers respond to recommendations, claims, corrections,
disputes and feedback in their issue threads. Forms do not establish award entitlement.

## Pull requests

- Write repository documents and records in English. Keep documentation and templates consistent.
- Include public evidence and a clear reason for changes. Follow the [record guide](docs/records.md) when maintaining candidates and awards; its Markdown templates are optional.
- Disclose relevant conflicts using public professional information only.
- Review the complete diff and commit history for private material. Keep identity documents, private contacts, payment/delivery details and internal assessment materials out of the repository. Use the [official email](docs/award-process.md#before-you-start) for private information.
- Retain third-party attribution and licenses; submit only material you are entitled to contribute. See [LICENSE](LICENSE) and [LICENSE-CONTENT](LICENSE-CONTENT).

## Before opening a PR

We recommend checking whether someone has already submitted the same contribution
before opening a PR. You can search [all PRs](https://github.com/TheJustinSunPrize/awards/pulls?q=is%3Apr)
(open, merged and closed) by JSP problem ID, problem name and proof/publication
reference, and check the current catalog entry and candidate record. Compare
mathematical-solution information and Lean-formalization information separately:
a solver submission does not by itself duplicate a Lean contribution for the same
problem.

If you find related submissions, consider linking them and explaining how your
contribution differs. When the same contribution is already submitted or recorded,
we encourage reviewing the existing submission before opening another PR that
repeats the same information. This can help avoid duplicate work for contributors
and reviewers.

If you find a problem with an existing submission, it is helpful to identify the
affected PR and exact publication or proof commit, describe the error, and share
checkable evidence (such as a statement mismatch, missing case or reproducible
verification failure). You can comment on the existing PR or use the
correction/dispute route above, with a linked replacement PR when needed. Evidence-backed priority
or attribution corrections remain subject to the
[challenge process](docs/award-process.md#the-14-day-public-review).
An earlier PR opening time alone does not establish priority. For changes to your
own pending submission, we recommend updating the existing PR.

## External solver and Lean submissions

**Only complete solutions to the original problem are accepted, whether
mathematical or in Lean.** Special cases, intermediate lemmas, weaker results and
conditional arguments relying on additional unproved assumptions do not qualify.
A Lean statement alone or a proof depending on `sorry`, `admit` or assumptions
standing in for missing proof steps is incomplete.

Fork this repository and update the relevant existing
`problems/catalog-XXXX-XXXX.md` file using the PR template. External submissions
may change **Current status** (including **Proof contributors:**), **Lean proof**,
**Attribution basis**, and **Publication details**. Use **Open** or **Solved** as
the status in both the index and detail tables.
Maintainers reconcile the index and eligibility fields after review, and maintain
each role's claim status in the index using the candidate and confirmed award records.
Use an issue for other corrections or requests.

Provide evidence for the contribution you are submitting:

- **Mathematical solution:** public proof or publication, relevant theorem/pages and version or date, solver names and evidence supporting their contributions.
- **Lean formalization:** the original proof repository, owned by your submitting account or an organization; branch and full 40-character commit SHA; statement and proof locations; formalization authors; reproduction instructions, axiom audit and attribution evidence. For an organization repository, provide verifiable evidence connecting your account to the claimed proof contribution, following the [contribution checks](docs/attribution.md#lean-contributor-verification). The selected commit must be contained in the named branch. Do not register someone else's proof, a mirror or a copy on their behalf.
- **Both:** provide both sets of evidence and distinguish the contributions.

Mathematical review must pass before Lean acceptance. Identify the mathematical
solution and review evidence, or supply that evidence in the same PR for review.
The solver need not have registered or claimed an award. Solver-only submissions
need no Lean repository or self-check.

For Lean proofs, we recommend the optional
[`lean-verify` skill](skills/lean-verify/SKILL.md). Other verification methods are
welcome; self-check reports and log links are optional. See the
[verification guide](docs/verification.md#recommended-lean-pre-submission-check)
for checking a fixed version and sharing results. Maintainers independently
review the statement and reproduce proof verification before acceptance.

Submit references and catalog text only. Keep Lean source, project/build files,
dependencies, archives and binaries in the external proof repository; do not
paste proof source into catalog rows. Revise existing PRs containing source to
use this format; they are not automatically closed.

Maintainer approval is required before merging. Replacement proofs have the same
evidence and verification requirements as initial submissions. Priority and
candidate replacement follow the [challenge process](docs/award-process.md#the-14-day-public-review).
