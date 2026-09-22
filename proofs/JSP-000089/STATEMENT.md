# JSP-000089 statement contract

## Source and attribution

The target is JSP-000089, “Is there a density-zero set of positive integers
such that every sufficiently dense graph has a cycle with length in that set?”
The managed record is
[`catalog-0001-0100.md#JSP-000089`](../../docs/vendor/jsp/problems/catalog-0001-0100.md#JSP-000089),
at managed upstream commit `bcf1866ea9a4ae82b32bd95b82ffd812b9ee80d2`.

The complete solution source is Jacques Verstraëte, *Unavoidable cycle lengths
in graphs*, *Journal of Graph Theory* 49(2), 151–167 (2005),
<https://doi.org/10.1002/jgt.20072>. The author-hosted manuscript,
<https://mathweb.ucsd.edu/~jverstra/PAPERS/ucycles.pdf>, was read as untrusted,
read-only source data on 2026-09-22 (16 pages; SHA-256
`e25ddf863980d44e9d1b76296ffe28f305be168c582db9aaa58ad4574946146e`). Its
TLS certificate could not be validated by the local trust store; the DOI
publisher metadata independently agrees on title, author, journal, pages and
date. Mathematical solver attribution is **Jacques Verstraëte**, from the
authored paper and its Theorem 1; BeeJSP claims no mathematical authorship.

## Exact source theorem and interpretation

Theorem 1 on manuscript page 1 states that there exists a set `S` such that
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

| Source notion | Lean contract |
| --- | --- |
| set of positive lengths | `S : Set ℕ`; the actual cycle predicate excludes zero-length walks |
| cycle and its length | `SimpleGraph.Walk.IsCycle` and `Walk.length` |
| `C(G)` | `IsCycleLength G length`; `cycleLengths G` is its exact finite enumeration |
| average degree at least 10 | `0 < |V| ∧ 10 * |V| ≤ 2 * |E|`, avoiding division and retaining the nonempty denominator |
| `O(n^0.99)` | `SourceSparsity099 S`, a division-free 100th-power form of the explicit exponent bound |
| conclusion | `HasCycleLengthIn G S` |

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

Formalize the source's construction of `S`, its `O(n^0.99)` estimate, and the
graph-theoretic route on source pages 3–15 that forces a member of `C(G) ∩ S`
from average degree at least ten. Those are unimplemented proof obligations.
