# Record maintenance

[Home](../README.md)

Maintain public records in Markdown through reviewed PRs. The
[award process](award-process.md) defines submission, public review, challenges,
identity checks and award confirmation.

## Where to record information

| Location | Purpose |
| --- | --- |
| [Problem bank](../problems/README.md) | Original problems, mathematical solutions, pinned Lean proof sources and attribution. |
| [Candidate register](../candidates/README.md#candidate-register) | Public candidates and each contribution type's public-review start. |
| Claim issues and submission PRs | Applications, review evidence and public conclusions, including solver applications awaiting formalization. |
| [Awards](../awards/README.md) | Confirmed, publicly announced awards and supporting evidence. |

## Maintaining the records

The eligibility/claim-status conventions below apply to legacy records. For
[MathDB pilot problems](../problems/mathdb-pilot.md), index/detail eligibility
links to the pilot process. The index shows Solver and Lean claim status; the
pilot page also shows Exposition. These cells are blank when no public record
exists, or show `Candidate` or `Awarded` independently.
A shared Solved/Lean flag does not determine all three categories. Maintain category-specific claim, candidate and award
outcomes through the [new process](award-process-mathdb.md), including Exposition
and Solution public review before complete Lean verification is available. Both
categories require that verification before announcement and payment. Do not
infer qualification from problem status or assign a level or estimated reward.

Identify contributions by JSP problem ID and contribution type. Keep contributor
names, accepted PRs, proof references and public-review dates consistent with the
[award process](award-process.md). Record public challenge outcomes in the relevant
PR or issue and update the candidate register accordingly.

Keep **Current status: Open/Solved** consistent between the index and detail
tables, and preserve proof evidence qualifications.
Keep **Eligible to claim** synchronized between the index and detail tables.
Maintain **Solver claim status** and **Lean claim status** only in the index.
Eligibility requires **Current status** to be **Solved** and **Lean proof**
to be **Yes**. When eligibility is
**No** or **Pending verification**, both claim statuses are **Unavailable**.
When eligibility is **Yes**, mark each role **Claimed** if it is registered in
`candidates/` or has a confirmed award record in `awards/`; otherwise mark it
**Unclaimed**. Update the shared eligibility and
both statuses if a solution or proof is invalidated; update the corresponding
role when a candidate is registered or withdrawn. A claim
issue alone does not mark a role **Claimed**. Retain **Claimed** when a registered
contribution moves to a confirmed award record in `awards/`, even after its
candidate entry is removed, preserving its registration history.

Before concluding review, use the optional [citation template](templates/citation.md)
to record the check for relevant pending PRs and its outcome. Record candidate
start and end dates in UTC; retain date-only precision for historical entries.

For an announced award, record the problem, contribution type, recipients,
announcement link, completed review dates and public evidence
in English Markdown under `awards/`. Update the register for that contribution;
the other contribution type keeps its own review period. The optional
[attribution template](templates/recipients.md) helps record contributors and
supporting sources.

## Verification evidence and private information

Follow the [verification guide](verification.md) for the original problem,
pinned proof commit, statement correspondence, reproduction results and public
evidence links. Reports may be included in the PR or linked from the proof
repository or a stable public archive. Keep Lean source and build artifacts out
of this repository.

Keep private identity documents, correspondence, payment and delivery details,
and internal assessment materials out of repository files and commits. Reviewers
check mathematical content, attribution and award eligibility.

## MathDB pilot maintenance

`problems/mathdb-pilot.json` is the source for approved scope, JSP/MathDB mappings,
mapping evidence and rollout metadata. Keep mathematical statements and proof
attribution in the existing catalog volumes. The generated pilot Markdown and
catalog workflow rows display that same mapping; do not maintain a separate manual
list or add problem levels/reward estimates. Preserve existing JSP anchors and
legacy records. The MathDB pilot additions extended the last volume through JSP-001050.
The [2026-10-13 OpenAI source review](../problems/openai-source-review-2026-10-13.md)
extends that volume through JSP-001072. The mirror-symmetry scope update retains
JSP-001024 for metric SYZ and adds JSP-001073 for Hodge-theoretic mirror symmetry.
The volume's original filename is retained so existing external links keep working.

Store public identifiers, catalog titles, mathematical scope and public evidence
in the register. Keep names, original wording and line numbers of internal working
materials outside this repository.

Use `confirmed` only after statement correspondence is checked. Keep `pending`
for an unresolved formulation or contradictory page statement; both block automatic
handoff. If no complete matching page is located, leave the mapping ID, URL, title
and check date null and its evidence list empty. Keep any related page in the note
as a reference, not as the approved mapping. Links display no status prefix;
pending formulations and page-statement corrections remain in catalog metadata.
`Matching page pending` describes a missing full match,
independently of `Candidate` claim status.

Public registration is derived separately for Solution, Lean and Exposition from
the MathDB tables in `candidates/README.md` and `awards/README.md`. Use exactly those
category labels and the recorded rule version in each row. After publishing or
moving a category record, rebuild the index and pilot page in the same PR. This
updates only that category; Exposition appears only on the pilot page. It does
not infer committee approval, eligibility, claim-issue state or payment from
mathematical status. Retained award records may have subsequent corrections
or revocation; their detailed record determines the current outcome.

Run `python3 scripts/mathdb_pilot.py build` after manifest changes, then
`python3 scripts/mathdb_pilot.py check` and
`python3 -m unittest discover -s tests -v`. The checker validates pilot membership,
catalog/index correspondence, generated rows, safe canonical MathDB URLs, mapping
evidence, duplicates and rollout metadata. It does not certify mathematics,
qualification, priority, identity, committee decisions, live agent integration or
payment. Current upstream uses Markdown registers and has no old JSON award
generator to modify; the pilot check supplements this structure.

The [candidate](../candidates/README.md#mathdb-pilot-candidates) and
[award](../awards/README.md#mathdb-pilot-awards) pilot tables stay in the existing
README registers, with one category/claimant record and preserved public-review
history. No hypothetical candidates, awarded recipients or payments are created
when preparing a cohort. The official agent follows [its contract](../agent-scope.md)
and the [claim/update templates](templates/mathdb-claim-reward.md).
