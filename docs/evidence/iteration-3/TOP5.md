# Evidence-backed TOP-5

Scanner commit: bcf1866ea9a4ae82b32bd95b82ffd812b9ee80d2
Competition observation: 2026-09-22T08:03:27Z

## 1. JSP-000089 — primary
Is there a density-zero set of positive integers such that every sufficiently dense graph has a cycle with length in that set?
Problem status: Solved
Recorded Lean status: No
Solution evidence: complete
Mathematical sources: Unavoidable cycle lengths in graphs (https://doi.org/10.1002/jgt.20072)
Competition evidence: issue #998 open (exact_jsp_id); pull_request #958 closed-unmerged (exact_jsp_id); pull_request #996 open (exact_jsp_id); pull_request #1414 open (exact_jsp_id); pull_request #1730 closed-unmerged (exact_jsp_id); pull_request #2648 open (exact_jsp_id)
Formalization evidence: Official JSP PR #1414 reports an existing Lean formalization (plby/lean-proofs) [unknown; risk only: The captured PR title reports an existing formalization, but no external repository or proof was executed or verified in this review.] (https://github.com/TheJustinSunPrize/awards/pull/1414)
Complexity: low
Mathlib/domain risk: Finite graphs and paths have baseline support; the specialized cycle-length lemma may be proof-local.
Statement risk: The exact density and sufficiently-large conventions must be transcribed from the source before proof work.
Provenance/date risk: The cited publication dates the solution evidence but Iteration 4 must establish exact statement correspondence.
Submission/process risk: A GitHub snapshot is not an official priority, eligibility, or award determination.
Selection score: 15
Decision: GO: no reviewed evidence establishes an Iteration 4 blocker
Reason: selected by published deterministic score; captured competition and formalization evidence remain explicit risk penalties; primary-vs-reserve: JSP-000089 score 15 > JSP-000076 score 12; JSP-000089 score 15 > JSP-000077 score 12; JSP-000089 score 15 > JSP-000104 score 12; JSP-000089 score 15 > JSP-000007 score 9

Iteration 4 bounded spike: In a scratch Lean file only, define the finite graph and cycle-length predicate used by the exact source statement, then prove one small equivalence between that predicate and the finite-set formulation. Stop after that boundary and record missing library support.

## 2. JSP-000076 — reserve
How sparse can a set be if every two-coloring represents every sufficiently large integer as a sum of distinct same-colored elements? Improve the growth bounds.
Problem status: Solved
Recorded Lean status: No
Solution evidence: complete
Mathematical sources: Subset sums, completeness and colorings (https://arxiv.org/abs/2104.14766)
Competition evidence: pull_request #959 closed-unmerged (exact_jsp_id); pull_request #1357 open (exact_jsp_id); pull_request #1982 closed-unmerged (exact_jsp_id); pull_request #2212 open (exact_jsp_id); pull_request #2641 open (exact_jsp_id)
Formalization evidence: Official JSP PR #1357 reports an existing Lean formalization (plby/lean-proofs) [unknown; risk only: The captured PR title reports an existing formalization, but no external repository or proof was executed or verified in this review.] (https://github.com/TheJustinSunPrize/awards/pull/1357)
Complexity: medium
Mathlib/domain risk: Finite sums are supported, while the additive-combinatorial asymptotic argument is likely proof-local.
Statement risk: The improvement claim must not be substituted for the exact theorem.
Provenance/date risk: The cited preprint date is explicit; solver attribution is not asserted beyond the source.
Submission/process risk: Live competition observations are necessarily time-bounded.
Selection score: 12
Decision: GO: no reviewed evidence establishes an Iteration 4 blocker
Reason: selected by published deterministic score; captured competition and formalization evidence remain explicit risk penalties

## 3. JSP-000077 — reserve
How fast must a set grow if every coloring with more than two colors represents all sufficiently large integers as sums of distinct same-colored elements?
Problem status: Solved
Recorded Lean status: No
Solution evidence: complete
Mathematical sources: Subset sums, completeness and colorings (https://arxiv.org/abs/2104.14766)
Competition evidence: pull_request #960 closed-unmerged (exact_jsp_id); pull_request #1358 open (exact_jsp_id); pull_request #1983 closed-unmerged (exact_jsp_id); pull_request #2227 open (exact_jsp_id); pull_request #2642 open (exact_jsp_id)
Formalization evidence: Official JSP PR #1358 reports an existing Lean formalization (plby/lean-proofs) [unknown; risk only: The captured PR title reports an existing formalization, but no external repository or proof was executed or verified in this review.] (https://github.com/TheJustinSunPrize/awards/pull/1358)
Complexity: medium
Mathlib/domain risk: The central finite-sum components are available, but the general coloring theorem may require substantial local infrastructure.
Statement risk: The source's number-of-colors parameter is a material part of the statement.
Provenance/date risk: The source date is recorded, with exact correspondence deferred to the statement package.
Submission/process risk: No absence or priority inference is drawn from the bounded live search.
Selection score: 12
Decision: GO: no reviewed evidence establishes an Iteration 4 blocker
Reason: selected by published deterministic score; captured competition and formalization evidence remain explicit risk penalties

## 4. JSP-000104 — reserve
If a graph has neither a large clique nor a large independent set, how many distinct edge counts do its induced subgraphs attain?
Problem status: Solved
Recorded Lean status: No
Solution evidence: complete
Mathematical sources: Anticoncentration in Ramsey graphs and a proof of the Erdős-McKay conjecture (https://arxiv.org/abs/2208.02874)
Competition evidence: pull_request #949 closed-unmerged (exact_jsp_id); pull_request #1417 open (exact_jsp_id); pull_request #1734 closed-unmerged (exact_jsp_id); pull_request #2652 open (exact_jsp_id)
Formalization evidence: Official JSP PR #1417 reports an existing Lean formalization (plby/lean-proofs) [unknown; risk only: The captured PR title reports an existing formalization, but no external repository or proof was executed or verified in this review.] (https://github.com/TheJustinSunPrize/awards/pull/1417)
Complexity: medium
Mathlib/domain risk: Finite graph enumeration is available in principle; probabilistic anticoncentration support is a risk.
Statement risk: Clique and independence thresholds need exact source recovery.
Provenance/date risk: The arXiv record provides a dated source, not a completed provenance package.
Submission/process risk: Read-only GitHub evidence cannot establish external priority.
Selection score: 12
Decision: GO: no reviewed evidence establishes an Iteration 4 blocker
Reason: selected by published deterministic score; captured competition and formalization evidence remain explicit risk penalties

## 5. JSP-000007 — reserve
Poincaré conjecture
Problem status: Solved<br>Proof contributors: Grigori (Grisha) Perelman (solution; papers [P1–P3]).
Recorded Lean status: No
Solution evidence: complete
Mathematical sources: Ricci flow with surgery on three-manifolds (https://arxiv.org/abs/math/0303109)
Competition evidence: issue #988 open (exact_jsp_id); pull_request #438 open (exact_jsp_id); pull_request #1598 closed-unmerged (exact_jsp_id); pull_request #1980 closed-unmerged (exact_jsp_id); pull_request #2636 open (exact_jsp_id); pull_request #2923 open (exact_jsp_id)
Formalization evidence: Official JSP PR #2923 records Lean formalization activity [activity; risk only: The captured PR title records formalization activity only and does not establish completion of the exact theorem.] (https://github.com/TheJustinSunPrize/awards/pull/2923)
Complexity: high
Mathlib/domain risk: Geometric-analysis and surgery infrastructure are high risk.
Statement risk: Closedness, simple connectivity, and homeomorphism must retain their source meanings.
Provenance/date risk: The source dates the mathematical evidence; no priority inference follows from the capture.
Submission/process risk: Current official-repository evidence requires review before any spike.
Selection score: 9
Decision: GO: no reviewed evidence establishes an Iteration 4 blocker
Reason: selected by published deterministic score; captured competition and formalization evidence remain explicit risk penalties
