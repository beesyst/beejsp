# JSP-000089 statement contract

## Source and attribution

The target is JSP-000089, “Is there a density-zero set of positive integers
such that every sufficiently dense graph has a cycle with length in that set?”
The managed record is
[`catalog-0001-0100.md#JSP-000089`](../../docs/vendor/jsp/problems/catalog-0001-0100.md#JSP-000089),
at managed upstream commit `bcf1866ea9a4ae82b32bd95b82ffd812b9ee80d2`.

The complete solution source is Jacques Verstraëte, _Unavoidable cycle lengths
in graphs_, _Journal of Graph Theory_ 49(2), 151–167 (2005),
<https://doi.org/10.1002/jgt.20072>. The authoritative local source for this
route is the final Version of Record,
`.local-source/verstraete-2005-jgt-version-of-record.pdf` (17 pages; SHA-256
`bb7e48cc2cfb0c0c5554bf3fc8b394c17ab6df966b521bb844b7d0584762b2e2`). The
author-hosted `.local-source/ucycles.pdf` (SHA-256
`e25ddf863980d44e9d1b76296ffe28f305be168c582db9aaa58ad4574946146e`) is an
earlier manuscript used only for comparison. Mathematical solver attribution
is **Jacques Verstraëte**, from the authored paper and its Theorem 1; BeeJSP
claims no mathematical authorship.
The current Lean formalization contributor is **Codex (OpenAI)**, operating
under the user's direction. This records formalization work separately from
the mathematical solution and does not claim a complete proof or independent
verification.

## Exact source theorem and interpretation

Theorem 1 in the Version of Record states that there exists a set `S` such that
`|S ∩ {1, …, n}| = O(n^0.99)` and every graph of average degree at least ten
contains a cycle with length in `S`. The abstract and introduction call a set
unavoidable when an absolute average-degree threshold forces such a cycle.
Page 2 defines `C(G)` as the set of cycle lengths in `G`; page 15 proves
Theorem 1 using `S = S' ∪ [2^120]`.

Density zero means that for every positive rational `a / b` there is a positive
`N` such that, for every `n ≥ N`, `b |S ∩ {1, …, n}| ≤ a n`. This is the
division-free `DensityZero` in `Statement.lean`; it is equivalent to the usual
real-`ε` definition. The source's stronger explicit sparsity bound implies it
because `n^0.99 / n → 0`. It is the theorem's actual statement, so the
intended target retains it rather than silently replacing it by a bare
density-zero assertion.

| Source notion              | Lean contract                                                                                        |
| -------------------------- | ---------------------------------------------------------------------------------------------------- |
| set of positive lengths    | `S : Set ℕ`; the actual cycle predicate excludes zero-length walks                                   |
| cycle and its length       | `SimpleGraph.Walk.IsCycle` and `Walk.length`                                                         |
| `C(G)`                     | `IsCycleLength G length`; `cycleLengths G` is its exact finite enumeration                           |
| average degree at least 10 | `0 < card(V) ∧ 10 * card(V) ≤ 2 * card(E)`, avoiding division and retaining the nonempty denominator |
| `O(n^0.99)`                | `SourceSparsity099 S`, a division-free 100th-power form of the explicit exponent bound               |
| conclusion                 | `HasCycleLengthIn G S`                                                                               |

`Statement.lean` defines the unproved `jsp_000089_statement` with precisely
these quantifiers. It is a statement contract, not a theorem declaration or a
claim of proof completion.

## Statement-fidelity review

The graph domain is finite simple graphs represented by `SimpleGraph V` with
`Fintype V`. This matches the source's ordinary finite graph setting used in
the counting argument. The average-degree condition is cross-multiplied only;
it adds no regularity, connectedness, girth, or minimum-degree assumption.
The explicit positive-cardinality conjunct prevents the empty graph from
vacuously satisfying a division-free average-degree condition. The source
theorem has universal graph quantification after existentially choosing `S`;
the Lean contract has the same order. No strength is claimed for the bounded
spike lemma beyond this representation bridge.

## Remaining Iteration 5 work

`Main.lean` now formalizes the direct short-cycle branch: positive girth at
most `2^120` gives a cycle length in the prefix `[2^120]` of the final source
set. It deliberately does not yet derive positive girth from the average-degree
hypothesis.

`Construction.lean` proves that this finite prefix satisfies
`SourceSparsity099`. It also gives the exact finite-sumset representation used
by source Lemma 4.1 and a finite fixed-size counting reformulation of its
selection argument. The exact fixed-witness cardinality, collision union bound,
and strict comparison with the complete fixed-size sample space are proved for
the source-valid selected size. `sourceLemma41_complete` therefore gives the
complete finite-counting form of source Lemma 4.1, including the selected-set
and sumset conclusions and the division-free fourth-root-scale bounds
`k ≤ 16m^4` and `m^4 ≤ 16k` for `k ≥ 2^24`.

For source Lemma 4.2, `Construction.lean` now defines the finite ambient
interval, the reduced family of Lemma 4.1 sumsets, and bounded candidate
sets. It proves that hitting that reduced family hits every range-contained
large pair, and that a strict bad-candidate cardinality bound yields a bounded
hitting set. The repaired range-contained source Lemma 4.2 is complete: finite colouring proves both its semantic hitting result and the division-free quantitative budget bound `sourceLemma42_finalBudget_quantitative_bound` with fixed constant `68`. This BeeJSP/Codex repair replaces the defective printed Bernoulli parameter argument; it does not claim that the unrestricted printed wording is correct as written.
The earlier `ucycles.pdf` manuscript's Lemma 4.2 wording places `S(n,k)` in `[n]` while discussing
ordinary integer sumsets; the range condition needed for this invocation is
explicit in the Lean bridge rather than silently assumed. No declaration here
claims to be the complete printed Lemma 4.2.
On page 14 of that manuscript, the statement places `S(n,k)` in `[n]` and
requires it to meet `A + B` for all `A, B ⊂ [n]` of the stated size. Under the
ordinary integer sumset used in Lemma 4.1, this cannot hold as written: take
`n = 2`, `k = 1`, and `A = B = {2}`; then `A + B = {4}` is disjoint from every
subset of `[2]`. The Lemma 4.3 proof later explicitly invokes Lemma 4.2 only
for a range-contained sumset (`A + B ⊂ [n]`) and interval sums contained in
`I_j ∪ I_{j+1}`. Thus the intended range-contained use is identifiable. The
proof-local repaired result must state that range condition explicitly; it is
not a claim that the unrestricted printed wording is correct.

This `[n]` defect is not present in the authoritative Version of Record:
published Lemma 4.2 states `S(n,k) ⊂ [2n]`. The range-contained Lean bridge
remains a deliberately narrow formalization of the Lemma 4.3 invocation, not
a correction to that published ambient range.
The printed nondegenerate proof also chooses
`p = 16 * k^(-1/4) * log_2(n)` after assuming only
`k ≥ (log_2 n)^4` and `k ≥ 2^24`. Those hypotheses do not imply `p ≤ 1`:
for `n = 2^100` and `k = 2^24`, they hold while `p = 25`. Consequently the
claimed Bernoulli selection is not defined throughout the stated regime. The
planned repair is a direct finite-colouring count: use the full interval in
the coarse regime, and otherwise choose each ambient element through a uniform
`q`-colouring with `q` chosen at the fourth-root/logarithm scale. A union bound
for missed reduced sumsets and a first-moment bound for selected elements can
then prove a range-contained hitting set with the required asymptotic scale.
The Lean theorem `sourceLemma42_rangeContained_of_universe_budget` proves the
coarse-budget branch. This is new BeeJSP/Codex formalization work, distinct
from Verstraëte's published wording; its quantitative Lean proof is complete with fixed constant `68`.

For the proof-local Lemma 4.3 construction, an earlier BeeJSP translation
incorrectly used a natural ceiling of `c * j^-2 * 2^(eta * (j - 1))`. The
manuscript instead defines `k_j` as the natural floor of
`c * j^-1 * 2^(eta * (j - 1)) - j^-1`; this explicitly permits its printed
`k_j = 0` branch. `Construction.lean` now uses that source-faithful floor
definition and represents the zero branch by retaining the two dyadic blocks,
with nonemptiness of the input sets made explicit where that branch needs it.
The top-level statement is unchanged.

The source Lemma 4.3 construction, its global hitting result, and its quantitative `SourceSparsity099 sourceLemma43Set` bound are formalized; the sparse side is complete. In source Lemma 3.6's decreasing Case-B branch, the concrete boundary cycle `C′` now has checked first- and second-arc traversal order; after reversing the middle-rung index, it certifies the source Section-2 `k`-ladder `H`.

The Version of Record Section 3 audit found a distinct unresolved source gap. Its definition says that a `k`-subgraph is rooted in `Z` only when every off-cycle attachment has an endpoint in `Z`. In Lemma 3.7, `eᵢ` is a ladder chord rooted in `Z`, but the crossing chord `fᵢ` is merely chosen as a chord crossing `eᵢ`; the published hypotheses give no endpoint-incidence fact for `fᵢ`. Consequently neither the SameSide claim that `C + {fᵢ : i ∈ I}` is a rooted proper truncation nor the CrossSide claim that `C + {eᵢ, fᵢ : i ∈ I'}` is a rooted mesh follows. The unrooted conclusion would suffice for the first Lemma-3.9 branch, but has not been formalized.

The published Lemma 3.8 K4 hypothesis resolves a limited label fact: a K4 containing a root-labelled ladder edge has the same designated root, by independence in `F - E(C)`; this is formalized as `sourceLemma38_shadowK4_root_label`, with the resulting label injectivity formalized as `sourceLemma38_shadow_labels_injective`. This repairs the outside-region lift: among the `2k - 1` crossed ladder rungs, no rung can use the K4 label of the cross path, and their labels are distinct. The cross path and selected rungs can therefore be lifted through distinct components.

`sourceLemma36_kCrossladder_insideBoundarySubpath_middle_order` records the corresponding decreasing order of the retained middle first endpoints on the concrete inside boundary arc. It is a recovered cycle-geometry prerequisite only: no declaration yet packages all Lemma 3.6 alternatives or states the sufficient unrooted Lemma 3.7 result.

The inner-region `1 : 3` configuration remains compatible with the full hypotheses, but it is not a no-go. Its same-side chord can be non-rooted because the final Lemma-3.9 target is unrooted; its K4 label still selects the good path in the corresponding component. The nested-K4 example in `EVIDENCE.md` refutes only an unnecessarily strong shadow-level requirement that every attachment be root-incident and have a distinct label. It is neither a full Lemma-3.9 obstruction nor evidence of a genuine source defect. Full Lean integration of the unrooted Lemmas 3.7--3.9 bridge remains incomplete. No Lean declaration claims Lemma 3.7, Lemma 3.8, Lemma 3.9, or later Section 3 results. The overall JSP-000089 theorem remains incomplete and this is not an independent-verification or submission claim.
