# How to participate and claim an award

[Home](../README.md) · [Contribution guidelines](../CONTRIBUTING.md)

Submit contribution evidence → review the mathematical solution and verify any
submitted Lean proof → merge the participant PR where required → maintainers publish candidates
in `candidates/` → start 14-day public review for each published contribution type,
with claims and identity checks handled alongside it → written recipient
confirmation → announcement, prize money and medal.

Submission, acceptance and PR merge do not constitute an award. Verification,
public review, recipient confirmation and announcement are separate steps.

## Before you start

The official contact address is **thejustinsunprize@hejustinsun.com**. We send
official email only from **@hejustinsun.com** and never ask for private keys or
seed phrases. Send payment network/address, medal delivery address and private
identity materials only by email; do not post them on GitHub.

## Step 1: Submit your contribution for verification

Before opening a PR, we recommend [checking for existing submissions](../CONTRIBUTING.md#before-opening-a-pr)
for the same problem and contribution type, including open, merged and closed PRs.
Consider linking related submissions and explaining how your contribution differs.
If you find a problem with an existing submission, sharing specific details and
checkable evidence can help reviewers assess it.

Choose a problem from the [problem bank](../problems/README.md),
[fork this repository](https://github.com/TheJustinSunPrize/awards/fork), update
the relevant catalog entry in your fork, and open a PR. Complete the automatically
provided [PR template](../.github/PULL_REQUEST_TEMPLATE.md).
Only complete solutions and complete Lean proofs of the original problem are accepted.

The complete mathematical solution to the original problem and its proof or
publication evidence may be provided before the Lean formalization or together
with it in the same PR. The mathematical solver and Lean formalization author
may be different people. **A Lean submission without the mathematical solution
and its supporting evidence is invalid and will not be accepted.**

**The mathematical solution must pass review, but Lean verification and candidate
registration do not require the solver to have registered or claimed an award.**
A Lean submission links an earlier mathematical solution and any review evidence,
or supplies the solution evidence for review in the same PR. A proof build cannot
replace mathematical review. Review both contribution types independently when
submitted together; neither contributor must register before the other.
An accepted solver application may be retained while formalization is missing.

### Mathematical solution only

You do not need a Lean repository. Remove the Lean-only sections from the PR
template and supply the mathematical proof/publication, relevant theorem or pages,
solver contribution and public authorship evidence in the Problem and Attribution
sections. Maintainers check the result and attribution before merging.

After the solver PR passes review and merges, retain the solver application.
Solvers whose contributions were already recorded directly by the project may
apply under the [recorded-solver exception](#open-a-claim-award-issue) below.
If formalization is missing, preserve the application and its submission time
without starting the 14-day public review. A Lean contributor can be verified and
registered independently of whether the solver has applied or been registered.
Once formalization is available, notify the solver and add the candidate to
`candidates/` for public notice. The applicable review starts when that public
notice begins. Formalization is a prerequisite for the timed public review
and award payment, not for initial solver candidate registration.

### Lean formalization or both roles

Register the original repository containing your Lean contribution. It may be
owned by your submitting GitHub account or an organization. For organization
repositories, provide [verifiable contribution evidence](attribution.md#lean-contributor-verification)
connecting your account to the claimed work. Do not register a mirror or copy of
someone else's proof or submit on another person's behalf. Repository ownership
or organization membership alone does not establish authorship.

Keep Lean source and build artifacts in that external repository. Supply its URL,
branch and full 40-character commit SHA in the PR, together with the statement,
proof entry, reproduction instructions and attribution evidence requested by the
template. The selected commit is both the version reviewed and the time anchor
used for the formalization priority comparison.

For a pre-submission self-check, we recommend the optional
[`lean-verify` skill](../skills/lean-verify/SKILL.md). Other methods are welcome;
reports and log links are optional. Follow the
[verification guide](verification.md#recommended-lean-pre-submission-check)
to check the exact proof commit and describe any supplied results.
Maintainers independently check the statement and reproduce verification before
acceptance, whether or not a self-check report is supplied.

After the mathematical solution has passed review, maintainers verify the Lean
proof before comparing priority. Solver registration is not a prerequisite. If no formalization
source is already recorded, the accepted submission becomes the earliest recorded
source. If multiple submissions pass verification in the same review period,
the earliest selected commit in the accepted original proof repositories takes priority.
If a source is already recorded, a new submission replaces it on priority grounds
only after verification establishes that the selected complete proof is earlier.
A later or unproven priority claim does not replace the source or restart public
review merely because the proof builds successfully.
PR opening time does not determine priority. Maintainers check the selected
commit's time and supporting public history when reviewing a priority claim.
Commit timestamps alone are insufficient evidence of when a proof was completed:
[Git permits author and committer dates to be supplied by the user](https://git-scm.com/docs/git-commit#_commit_information).
Supply independently checkable public history tying the selected proof version
to the claimed date. Resolve conflicting or uncorroborated dates before accepting
a priority replacement.

For example, a complete proof committed on March 1 and submitted here on September
20 precedes a complete proof committed on June 1 and submitted here on September
18, subject to verification of the selected proofs and their history.

The accepted contribution PR records the current formalization source. After
it merges, maintainers publish candidates under the
[public-review rules](#the-14-day-public-review) below.

### Keep notifications enabled

Check that email notifications for your GitHub account are enabled so you receive
PR review results and requests for corrections. Consider watching this repository
for pull requests or mentions as well.

## Step 2: Apply and participate in public review

### Open a claim-award issue

After your contribution PR in **TheJustinSunPrize/awards** has merged into **main**,
or if you meet the recorded-solver exception below, open a
[claim-award issue](https://github.com/TheJustinSunPrize/awards/issues/new?template=claim-award.yml)
and complete the JSP number in its `[Award claim] JSP-` title. Include the
problem-bank link and any required merged PR. Apply only for yourself using your own
GitHub account; proxy applications and collection for others are not accepted.
Choose mathematical solution, Lean formalization, or both.

A pending PR or a proof repository URL does not satisfy the merged-PR requirement.
Maintainers check the linked PR's merge status before accepting the application.
For an early claim, explain that the requirement is not yet met and defer
acceptance until the contribution PR merges. The applicant should then update
the existing issue rather than open a duplicate.

**Recorded-solver exception:** A solver already credited in the problem bank whose
contribution was directly recorded by the project and has no applicant-submitted
PR may leave **Merged submission PR** blank for their mathematical-solution claim.
Reference the recorded contribution and attribution evidence in **Contribution
evidence and attribution clarification**. Maintainers verify those records before
accepting the claim. This applies to all such recorded solvers, not only the
initial award recipients. Lean formalization claims, including the Lean role in
a both-role claim, still require a merged contribution PR.

Fill **Original Lean proof repository** according to your role:

| Claim role | What to enter |
| --- | --- |
| Lean formalization or both | The original repository already recorded as the problem's formalization source, owned by your account or an organization. Organization repositories require verifiable evidence of your contribution. |
| Mathematical solution only | Leave this field blank. |

The form accepts a blank repository field so solver-only applicants can submit.
For Lean or both-role claims, the repository remains a review requirement;
maintainers request a missing URL before approving the claim.

Both awards require an accepted mathematical solution and a verified complete
Lean proof. The catalog's shared **Eligible to claim** flag is **Yes** only when
**Current status** is **Solved** and **Lean proof** is **Yes**. The two claim-status
columns are maintained only in the index. While eligibility
is **No** or **Pending verification**, both **Solver claim status** and **Lean
claim status** are **Unavailable**. Once eligible, each role is **Unclaimed**
until registered in `candidates/`, then **Claimed**. The role remains **Claimed**
when it moves to a confirmed award record in `awards/`, even after its candidate
entry is removed. A claim issue alone does not change the status to **Claimed**.
A solver whose complete solution PR has merged, or who meets the
recorded-solver exception, may register an application while formalization is
missing. Both claim statuses remain **Unavailable**; the application does not
start public review or permit payment. Once a complete Lean formalization has
been verified and accepted, the solver's claim can proceed through public review,
identity verification and recipient confirmation under the same award process.

The **Follow-up contact email** in the issue is your public correspondence address;
no extra comment is needed to designate it. Use your GitHub account as your public
identity in the issue. Private identity materials and private contact details go
by email.

### Complete identity verification by email

Every applicant must send an identity-verification email from the follow-up
address in their claim issue to **thejustinsunprize@hejustinsun.com**, linking the
issue and any merged submission PR and using the [email template below](#email-template).
This applies to mathematical-solution-only, Lean-only and both-role claims.
Existing source attribution does not waive the email requirement. Maintainers
verify the applicant's identity and claimed contribution; written recipient
confirmation is still required before an award.

You may verify through an author email listed in the publication, an established
institutional or author website, a historical signing key already linked to the
author, or another independently verifiable method. If the listed author mailbox
differs from your follow-up address, maintainers independently verify and connect
the two channels. A message from a newly supplied contact email alone does not
establish identity. Keep private evidence in email. See the
[identity requirements](attribution.md#claiming-an-award).

### The 14-day public review

The [public notice table](../candidates/README.md#candidate-register) lists separate start
times for mathematical solution and Lean formalization. After the mathematical
solution has passed review and formalization has been verified, maintainers
publish the candidates in
`candidates/` after any required participant PR merges. **Each contribution type's 14-day
clock starts when its candidate is added to the public register and public
notice begins.** Record the actual public-notice start in UTC; the scheduled end
is 14 full days later. Do not derive the start from a PR's merge time.
Retain date-only precision for historical entries; do not invent a time of day.
Verification completion or receipt of a claim issue alone does not start the
clock. Adding the candidate to the published register is the public-notice step.
Each contribution type can be registered independently; an unregistered solver
does not block publication of an accepted Lean candidate.
Opening the claim issue or
finishing identity checks does not restart or delay an already running clock.
Routine catalog corrections, documentation updates and additional evidence for an
unchanged accepted contribution do not create a new candidate or restart its clock.

Anyone may challenge a public candidate's result, attribution, priority, identity
or eligibility through the
[Formal dispute issue form](https://github.com/TheJustinSunPrize/awards/issues/new?template=dispute.yml).
Identify the candidate, problem, related claim and supporting public evidence.
For ordinary record corrections, use the
[Correction issue form](https://github.com/TheJustinSunPrize/awards/issues/new?template=correction.yml).
If you propose a replacement proof or catalog update, open a linked PR using the
[normal submission template](../.github/PULL_REQUEST_TEMPLATE.md) and supply its
applicable evidence. Reporting a flaw does not require a replacement proof.

A Lean priority challenger must identify an earlier selected commit in the
original repository containing their contribution and pass the same verification
and attribution review as an initial submission, including for organization repositories.
A verified earlier Lean proof replaces the current source. A mathematical-solution
priority challenger supplies the earlier complete proof or publication, dated
public evidence and authorship evidence; a Lean repository is not required for
that challenge. Maintainers review the claimed mathematical contribution separately.

When a priority challenge succeeds and a verified replacement is accepted,
maintainers explain the replacement in the displaced
claim issue and close the displaced claim. For an issue claiming both roles,
only the displaced role is closed out; the issue remains open if the other role
is still active. If no claim issue exists yet, explain the outcome in the relevant
dispute issue and update the candidate record and notice table; no claim issue needs to be
created just to close it. The replacement starts a new full 14-day period when
it is added to `candidates/` and its public notice begins.
An unaffected role keeps its own review clock. If a challenge affects the validity
of the underlying solution or proof, maintainers reassess the affected eligibility.

A correctness challenge can succeed without providing a replacement. In that
case, withdraw the invalid contribution from active public review, correct the
catalog and stop the affected award process; do not start a new 14-day period
without an accepted candidate. If no valid formalization remains, a solver's
award cannot proceed. A replacement contributor must submit their own claim and
complete their applicable identity checks and written confirmation; the displaced
contributor's confirmation and delivery details cannot be reused.

If a challenge is raised during a review period, that period cannot conclude
before the challenge has been verified and resolved. An unsuccessful challenge
does not restart the original clock.

Before concluding public review, maintainers check the current PR list for the
same problem and contribution type (mathematical solution or Lean formalization),
regardless of who submitted the PR. If a pending PR could affect correctness,
contribution attribution or priority, wait until its review is complete before
concluding public review. Unrelated changes, including routine documentation
updates, do not hold up the process. Waiting does not itself restart the clock;
an accepted replacement starts a new period under the publication rule above.
Record the check time, relevant PRs, review outcomes and completion decision using
the [citation template](templates/citation.md) or an equivalent maintainer record.
After 14 full days, with no unresolved challenges or relevant pending PR reviews,
the contribution can proceed to recipient confirmation and award.

For identity or recipient-eligibility objections, use a
[dispute issue](https://github.com/TheJustinSunPrize/awards/issues/new?template=dispute.yml)
with public evidence; send private identity materials to the official email.
Such unresolved objections must also be addressed before award confirmation.
For an already announced award, use the dispute process.

## Step 3: Recipient confirmation and award delivery

Maintainers complete written recipient confirmation and identity checks by email.
Until confirmation is complete, the record remains a candidate and does not
enter the confirmed award list, even if the 14-day review has finished.

Send any outstanding payment network/address and medal delivery address by email.
Before announcement, maintainers check that the claim and written confirmation
belong to the currently accepted contributor and role, the applicable full 14-day
period has elapsed, and no unresolved challenge, eligibility objection or relevant
pending PR review remains.
An elapsed clock alone does not permit an award.

Once the applicable review and confirmation requirements are complete, maintainers
publish the confirmed contribution record in Markdown under
[awards/](../awards/README.md) and publish the announcement. They then send the
prize money and medal and confirm delivery.

## Email template

This template is for email, **not a GitHub issue**.

```text
To: thejustinsunprize@hejustinsun.com
Subject: [Award claim] JSP-000305

Required:
- Name or organization name:
- JSP problem ID:
- Claim issue link:
- Merged submission PR links (if required):
- Role: mathematical solution / Lean formalization / both
- Identity-verification method and corresponding public records:

Recommended, if available:
- Public evidence connecting me to the credited author: ORCID, paper DOI,
  attributed repository/commit links, or other public records:

May be supplied at the award-delivery stage:
- Payment network and address:
- Medal delivery address:
```
