# Mathematical problem bank

[Repository home](../README.md) · [Problem bank sources](../docs/problem-bank-sources.md)

This catalog contains **1,022 mathematical problems**.

Problems are numbered consecutively and grouped into volumes of 100 records (22 in the final volume), with a heading, a field table, and any review notes for each problem. The index shows **Current status**, **Lean proof**, **Eligible to claim**, **Solver claim status**, and **Lean claim status**. The index and detail tables both use **Current status: Open/Solved**; the two claim-status columns appear only in the index.

Some dates are explicitly marked as assumptions or pending confirmation. Formal nominations and award records remain in [candidates/](../candidates/README.md) and [awards/](../awards/README.md).

**Submission requirements:** only complete solutions to the original problem are
accepted. Partial mathematical progress and incomplete Lean formalizations are not
eligible for submission. The catalog records complete solutions only, without
intermediate results. The complete mathematical solution and its proof or publication
evidence may be provided before the Lean formalization or together with it in the
same PR. The mathematical solver and Lean formalization author may be different
people. **A Lean submission without the mathematical solution and its supporting
evidence is invalid and will not be accepted.** See the
[contribution guidelines](../CONTRIBUTING.md#external-solver-and-lean-submissions).

For submission, claims, public review and challenges, follow the
[award process](../docs/award-process.md). Current candidates and review dates
appear in the [public notice table](../candidates/README.md#candidate-register).

## Disclaimer and corrections

Information in this problem bank—including problem descriptions, dates, solution status, contributor attributions, Lean proof records, historical bounties, and references—is compiled from publicly available online sources and the project's summaries and assessments of those sources. It is provided for reference and may contain errors, omissions, or outdated information. Inclusion does not by itself constitute independent verification of a result or confirmation of an award or entitlement to payment.

If you find inaccurate, incomplete, or outdated information, please contact the maintainers by [opening a correction issue](https://github.com/TheJustinSunPrize/awards/issues/new?template=correction.yml). Include the JSP identifier, the information in question, your proposed correction, and supporting public sources so the record can be reviewed and corrected.


## Reading conventions

Each introduction has three rows: **Date proposed**, **Mathematical area**, and **Problem description**. Date proposed identifies when the mathematical problem was posed; it is not an application submission date for this award.

The catalogs retain solution status, Lean proof status, historical bounty, elapsed years, publication details, and scholarly recognition. **Scholarly recognition** records external academic recognition or review of the result. Review notes document evidence limitations and eligibility considerations. Dated review records retain the field names and status values used at the time.

**Current status** uses **Open** or **Solved** in both the index and detail tables. Detail tables include any complete-solution contributor credits after **Proof contributors:**. **Open** means a complete solution to the stated problem is not recorded; partial results and unconfirmed solutions do not change this status. **Solved** means a complete resolution is recorded, including a disproof or an independence result where applicable. For a combined record, the full stated scope must be resolved before marking **Solved**. Solution explanations belong in **Review notes**. The catalog does not track intermediate mathematical results or incomplete Lean formalizations. **Publication details** records complete-solution references and supporting literature, with titles, dates, venues and links, without repeating author lists. A link labeled **bibliographic record** is a reference entry, not a verified direct link to the paper.

**Lean proof** in the index uses **Yes** when a complete formal proof is recorded and **No** otherwise. Detail tables retain their existing proof descriptions, source links, formalization contributor credits and evidence qualifications. **No** does not mean that no related formalization work exists. Mathematical discovery, formalization, and **Independent verification** can have different contributors. A repository owner, commit author, statement author, or AI tool is not automatically the mathematical solver. Credits follow explicit source statements or a display convention identified in **Attribution basis**; unresolved attribution is otherwise marked as unverified. A successful kernel check does not by itself establish independent human review or award eligibility.

<a id="attribution-conventions"></a>

**Attribution conventions (updated 2026-09-16).** The 66 records with an **Attribution basis** row describe credits for the selected completed proof version. Each row provides sources and any problem-specific qualifications. **Solver attribution source** links to evidence supporting the listed solver credits; **Lean attribution source** links to evidence supporting the listed Lean credits.

Short attribution notes mean:

- **Paper/report authors:** mathematical credit follows the corresponding author list. This does not establish each author's role as an AI operator or proof discoverer.
- **Repository-owner attribution:** when individual Lean authorship is missing, the owner of the selected completed proof repository supplies the display credit. Ownership or a completion commit does not establish who personally wrote every proof step.
- **Project authorship and evaluation/publication role:** Lean credit follows the named project role in `formalization.yaml`.

Other credits follow explicit authorship or documented participation. Earlier conditional versions and independent proof routes are not accumulated into these display credits. Lists longer than three names show the first three followed by “et al.”; individual AI models are omitted.

These credits do not establish first-discovery priority, sole manual authorship, independent verification or recipient eligibility.

The index preserves Lean evidence qualifications: **No — reported; standalone source not located** means a complete Lean proof of that problem has not been confirmed. A linked proof of a related problem is identified as such in the full record.

**Eligible to claim** records the shared prerequisite for both awards. **Yes** requires **Current status** to be **Solved** and **Lean proof** to be **Yes**. **No** means this prerequisite is not met. **Pending verification** means evidence needs further review and eligibility has not been established. These are catalog screening flags; award processing requires mathematical review and verification of the complete Lean proof.

**Solver claim status** and **Lean claim status** appear only in the index. They use that shared eligibility flag, then track each role's candidate registration or confirmed award separately:

| Eligible to claim | Role recorded in candidates/ or awards/ | Claim status |
| --- | --- | --- |
| No or Pending verification | — | Unavailable |
| Yes | No | Unclaimed |
| Yes | Yes | Claimed |

If either the mathematical solution or complete Lean proof is missing, both claim statuses are **Unavailable**. Once eligible, registering one role changes only that role's claim status. Opening a claim issue alone does not mark a role **Claimed**. A solver may register an application while formalization is missing, but both statuses remain **Unavailable**; such an application does not start public review or permit payment.

**Claimed** covers a role registered in [candidates/](../candidates/README.md) or recorded as a confirmed award in [awards/](../awards/README.md). Moving a contribution from candidates to awards preserves **Claimed**, even after its candidate entry is removed. The status alone does not indicate award approval or payment. Public review requires mathematical review and verified complete Lean formalization; awards also require completed public review, resolution of relevant challenges, identity verification and written recipient confirmation. See the [award process](../docs/award-process.md) and the candidate or award record for each role's outcome and review dates.

## Volumes

| Problem range | File |
| --- | --- |
| 1–100 | [catalog-0001-0100.md](catalog-0001-0100.md) |
| 101–200 | [catalog-0101-0200.md](catalog-0101-0200.md) |
| 201–300 | [catalog-0201-0300.md](catalog-0201-0300.md) |
| 301–400 | [catalog-0301-0400.md](catalog-0301-0400.md) |
| 401–500 | [catalog-0401-0500.md](catalog-0401-0500.md) |
| 501–600 | [catalog-0501-0600.md](catalog-0501-0600.md) |
| 601–700 | [catalog-0601-0700.md](catalog-0601-0700.md) |
| 701–800 | [catalog-0701-0800.md](catalog-0701-0800.md) |
| 801–900 | [catalog-0801-0900.md](catalog-0801-0900.md) |
| 901–1000 | [catalog-0901-1000.md](catalog-0901-1000.md) |
| 1001–1022 | [catalog-1001-1022.md](catalog-1001-1022.md) |

## Problem index

The **No.** column runs consecutively from **JSP-000001** to **JSP-001022** in display order. The **Problem** column contains only the linked problem title. Catalog headings and anchors use the same number, such as `JSP-000001 · problem title` and `#JSP-000001`. Each volume contains the numbered range shown above. These catalog numbers are separate from the original Erdős problem numbers cited in the sources.

### Problems 1–100

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000001 | [Riemann hypothesis](catalog-0001-0100.md#JSP-000001) | Open | No | No | Unavailable | Unavailable |
| JSP-000002 | [P versus NP problem](catalog-0001-0100.md#JSP-000002) | Open | No | No | Unavailable | Unavailable |
| JSP-000003 | [Birch–Swinnerton-Dyer conjecture (BSD)](catalog-0001-0100.md#JSP-000003) | Open | No | No | Unavailable | Unavailable |
| JSP-000004 | [Hodge conjecture](catalog-0001-0100.md#JSP-000004) | Open | No | No | Unavailable | Unavailable |
| JSP-000005 | [Existence and smoothness of the 3D Navier–Stokes equations](catalog-0001-0100.md#JSP-000005) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000006 | [Yang–Mills existence and mass gap](catalog-0001-0100.md#JSP-000006) | Open | No | No | Unavailable | Unavailable |
| JSP-000007 | [Poincaré conjecture](catalog-0001-0100.md#JSP-000007) | Solved | No | No | Unavailable | Unavailable |
| JSP-000008 | [Goldbach conjecture (strong Goldbach)](catalog-0001-0100.md#JSP-000008) | Open | No | No | Unavailable | Unavailable |
| JSP-000009 | [Twin prime conjecture](catalog-0001-0100.md#JSP-000009) | Open | No | No | Unavailable | Unavailable |
| JSP-000010 | [abc conjecture](catalog-0001-0100.md#JSP-000010) | Open | No | No | Unavailable | Unavailable |
| JSP-000011 | [Beal conjecture](catalog-0001-0100.md#JSP-000011) | Open | No | No | Unavailable | Unavailable |
| JSP-000012 | [Legendre conjecture](catalog-0001-0100.md#JSP-000012) | Open | No | No | Unavailable | Unavailable |
| JSP-000013 | [Hadamard matrix conjecture](catalog-0001-0100.md#JSP-000013) | Open | No | No | Unavailable | Unavailable |
| JSP-000014 | [Inverse Galois problem](catalog-0001-0100.md#JSP-000014) | Open | No | No | Unavailable | Unavailable |
| JSP-000015 | [Kakeya dimension conjecture (general dimension)](catalog-0001-0100.md#JSP-000015) | Open | No | No | Unavailable | Unavailable |
| JSP-000016 | [Littlewood conjecture](catalog-0001-0100.md#JSP-000016) | Open | No | No | Unavailable | Unavailable |
| JSP-000017 | [Lonely runner conjecture](catalog-0001-0100.md#JSP-000017) | Open | No | No | Unavailable | Unavailable |
| JSP-000018 | [Moving sofa problem (maximum area)](catalog-0001-0100.md#JSP-000018) | Solved | No | No | Unavailable | Unavailable |
| JSP-000019 | [Existence of odd perfect numbers](catalog-0001-0100.md#JSP-000019) | Open | No | No | Unavailable | Unavailable |
| JSP-000020 | [Infinitude of Mersenne primes](catalog-0001-0100.md#JSP-000020) | Open | No | No | Unavailable | Unavailable |
| JSP-000021 | [Schanuel conjecture](catalog-0001-0100.md#JSP-000021) | Open | No | No | Unavailable | Unavailable |
| JSP-000022 | [Černý conjecture](catalog-0001-0100.md#JSP-000022) | Open | No | No | Unavailable | Unavailable |
| JSP-000023 | [Inscribed square problem (Toeplitz conjecture)](catalog-0001-0100.md#JSP-000023) | Open | No | No | Unavailable | Unavailable |
| JSP-000024 | [Invariant subspace problem for Hilbert spaces](catalog-0001-0100.md#JSP-000024) | Open | No | No | Unavailable | Unavailable |
| JSP-000025 | [Lehmer–Mahler measure problem](catalog-0001-0100.md#JSP-000025) | Open | No | No | Unavailable | Unavailable |
| JSP-000026 | [Decimal normality of pi](catalog-0001-0100.md#JSP-000026) | Open | No | No | Unavailable | Unavailable |
| JSP-000027 | [Artin primitive root conjecture](catalog-0001-0100.md#JSP-000027) | Open | No | No | Unavailable | Unavailable |
| JSP-000028 | [Bateman–Horn conjecture](catalog-0001-0100.md#JSP-000028) | Open | No | No | Unavailable | Unavailable |
| JSP-000029 | [Dickson conjecture](catalog-0001-0100.md#JSP-000029) | Open | No | No | Unavailable | Unavailable |
| JSP-000030 | [Elliott–Halberstam conjecture](catalog-0001-0100.md#JSP-000030) | Open | No | No | Unavailable | Unavailable |
| JSP-000031 | [Fermat–Catalan conjecture](catalog-0001-0100.md#JSP-000031) | Open | No | No | Unavailable | Unavailable |
| JSP-000032 | [Fuglede conjecture (dimensions one and two)](catalog-0001-0100.md#JSP-000032) | Open | No | No | Unavailable | Unavailable |
| JSP-000033 | [Rational distances to the unit square](catalog-0001-0100.md#JSP-000033) | Open | No | No | Unavailable | Unavailable |
| JSP-000034 | [Sidorenko conjecture](catalog-0001-0100.md#JSP-000034) | Open | No | No | Unavailable | Unavailable |
| JSP-000035 | [Catalan conjecture](catalog-0001-0100.md#JSP-000035) | Solved | No | No | Unavailable | Unavailable |
| JSP-000036 | [Modularity theorem for rational elliptic curves (Taniyama–Shimura–Weil conjecture)](catalog-0001-0100.md#JSP-000036) | Solved | No | No | Unavailable | Unavailable |
| JSP-000037 | [Jacobian conjecture](catalog-0001-0100.md#JSP-000037) | Open | No | No | Unavailable | Unavailable |
| JSP-000038 | [Sendov conjecture](catalog-0001-0100.md#JSP-000038) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000039 | [DGG cost-preserving conjecture](catalog-0001-0100.md#JSP-000039) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000040 | [Anderson problem on weakly quasi-complete local rings](catalog-0001-0100.md#JSP-000040) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000041 | [Consecutive prime gap bound of 186](catalog-0001-0100.md#JSP-000041) | Open | No | No | Unavailable | Unavailable |
| JSP-000042 | [Crouzeix conjecture](catalog-0001-0100.md#JSP-000042) | Open | No | No | Unavailable | Unavailable |
| JSP-000043 | [Must the largest element of a positive-integer set with distinct subset sums be at least a fixed positive multiple of 2 raised to the set's size?](catalog-0001-0100.md#JSP-000043) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000044 | [Must a set of positive integers whose reciprocals have divergent sum contain arithmetic progressions of every finite length?](catalog-0001-0100.md#JSP-000044) | Open | No | No | Unavailable | Unavailable |
| JSP-000045 | [How large can gaps between consecutive primes be? Are infinitely many gaps larger than the proposed lower bound?](catalog-0001-0100.md#JSP-000045) | Solved | No | No | Unavailable | Unavailable |
| JSP-000046 | [Can consecutive prime gaps, divided by the logarithm of the prime index, approach every prescribed nonnegative real number along a subsequence?](catalog-0001-0100.md#JSP-000046) | Open | No | No | Unavailable | Unavailable |
| JSP-000047 | [Can finitely many congruence classes with distinct odd moduli cover all integers?](catalog-0001-0100.md#JSP-000047) | Open | No | No | Unavailable | Unavailable |
| JSP-000048 | [Do the positive odd integers not expressible as a prime plus two nonnegative powers of 2 have positive upper density?](catalog-0001-0100.md#JSP-000048) | Open | No | No | Unavailable | Unavailable |
| JSP-000049 | [Is there a fixed bound on the number of powers of 2 needed, together with one prime, to represent every sufficiently large integer?](catalog-0001-0100.md#JSP-000049) | Open | No | No | Unavailable | Unavailable |
| JSP-000050 | [Is every sufficiently large odd integer the sum of a squarefree positive integer and a power of 2?](catalog-0001-0100.md#JSP-000050) | Open | No | No | Unavailable | Unavailable |
| JSP-000051 | [How dense can an infinite integer set be if no element divides the sum of two larger elements? Must its reciprocal sum converge?](catalog-0001-0100.md#JSP-000051) | Open | No | No | Unavailable | Unavailable |
| JSP-000052 | [How numerous, or how sparse, can the integers without a unique representation as a sum of two elements of a given positive-integer set be?](catalog-0001-0100.md#JSP-000052) | Open | No | No | Unavailable | Unavailable |
| JSP-000053 | [Does the alternating series formed by weighting reciprocal primes by their indices converge?](catalog-0001-0100.md#JSP-000053) | Open | No | No | Unavailable | Unavailable |
| JSP-000054 | [cluster primes](catalog-0001-0100.md#JSP-000054) | Open | No | No | Unavailable | Unavailable |
| JSP-000055 | [practical numbers](catalog-0001-0100.md#JSP-000055) | Open | No | No | Unavailable | Unavailable |
| JSP-000056 | [Is the union of n edge-disjoint complete graphs, each on n vertices, always properly colorable with n colors?](catalog-0001-0100.md#JSP-000056) | Open | No | No | Unavailable | Unavailable |
| JSP-000057 | [sunflower conjecture](catalog-0001-0100.md#JSP-000057) | Open | No | No | Unavailable | Unavailable |
| JSP-000058 | [Can every triangle-free graph on 5k vertices be made bipartite by deleting at most k² edges?](catalog-0001-0100.md#JSP-000058) | Open | No | No | Unavailable | Unavailable |
| JSP-000059 | [Do the integers remaining after successively avoiding the prescribed congruence classes necessarily have logarithmic density?](catalog-0001-0100.md#JSP-000059) | Open | No | No | Unavailable | Unavailable |
| JSP-000060 | [Can congruence classes cover almost all integers when their moduli are restricted to a prescribed range?](catalog-0001-0100.md#JSP-000060) | Solved | No | No | Unavailable | Unavailable |
| JSP-000061 | [If every sufficiently large integer is a sum of two elements of a set, must the numbers of such representations be unbounded?](catalog-0001-0100.md#JSP-000061) | Open | No | No | Unavailable | Unavailable |
| JSP-000062 | [How large can a set with distinct two-element sums in a finite integer interval be, and how large is the error from the leading term?](catalog-0001-0100.md#JSP-000062) | Open | No | No | Unavailable | Unavailable |
| JSP-000063 | [How sparse can an additive complement of the primes be if every sufficiently large integer must be a prime plus an element of that complement?](catalog-0001-0100.md#JSP-000063) | Open | No | No | Unavailable | Unavailable |
| JSP-000064 | [What is the smallest possible size of an additive complement of the squares that represents every sufficiently large integer?](catalog-0001-0100.md#JSP-000064) | Open | No | No | Unavailable | Unavailable |
| JSP-000065 | [minimum overlap problem](catalog-0001-0100.md#JSP-000065) | Open | No | No | Unavailable | Unavailable |
| JSP-000066 | [How much can adding a set that is not an additive basis increase another set's Schnirelmann density?](catalog-0001-0100.md#JSP-000066) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000067 | [Can an infinite positive-integer set have distinct two-element sums and nearly square-root growth in arbitrarily large intervals?](catalog-0001-0100.md#JSP-000067) | Open | No | No | Unavailable | Unavailable |
| JSP-000068 | [What constraints relate the growth of an integer set to the numbers of representations as sums of two of its elements?](catalog-0001-0100.md#JSP-000068) | Open | No | No | Unavailable | Unavailable |
| JSP-000069 | [How dense can an integer set be if distinct triples have distinct sums?](catalog-0001-0100.md#JSP-000069) | Open | No | No | Unavailable | Unavailable |
| JSP-000070 | [For any integer set with distinct two-element sums, can another such set be found with no common nonzero differences?](catalog-0001-0100.md#JSP-000070) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000071 | [How large can two sets with distinct two-element sums be in total if their nonzero difference sets are disjoint?](catalog-0001-0100.md#JSP-000071) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000072 | [Can every finite set with distinct two-element sums be extended to a nearly optimal set with the same property?](catalog-0001-0100.md#JSP-000072) | Open | No | No | Unavailable | Unavailable |
| JSP-000073 | [Where is the distribution function of the ratio of Euler's totient to its argument differentiable, and what properties do its derivatives have?](catalog-0001-0100.md#JSP-000073) | Open | No | No | Unavailable | Unavailable |
| JSP-000074 | [For each value attained by Euler's totient, study the ratio of its smallest preimage to that value.](catalog-0001-0100.md#JSP-000074) | Open | No | No | Unavailable | Unavailable |
| JSP-000075 | [sum-product problem](catalog-0001-0100.md#JSP-000075) | Open | No | No | Unavailable | Unavailable |
| JSP-000076 | [How sparse can a set be if every two-coloring represents every sufficiently large integer as a sum of distinct same-colored elements? Improve the growth bounds.](catalog-0001-0100.md#JSP-000076) | Solved | No | No | Unavailable | Unavailable |
| JSP-000077 | [How fast must a set grow if every coloring with more than two colors represents all sufficiently large integers as sums of distinct same-colored elements?](catalog-0001-0100.md#JSP-000077) | Solved | No | No | Unavailable | Unavailable |
| JSP-000078 | [How does the number of distinct odd cycle lengths constrain a graph's chromatic number?](catalog-0001-0100.md#JSP-000078) | Solved | No | No | Unavailable | Unavailable |
| JSP-000079 | [How many quadrilaterals are forced when a graph's edge count exceeds the threshold for containing one?](catalog-0001-0100.md#JSP-000079) | Open | No | No | Unavailable | Unavailable |
| JSP-000080 | [Must a graph excluding a prescribed induced subgraph contain a sufficiently large clique or independent set?](catalog-0001-0100.md#JSP-000080) | Open | No | No | Unavailable | Unavailable |
| JSP-000081 | [Must two graphs of uncountable chromatic number have a common subgraph of large chromatic number?](catalog-0001-0100.md#JSP-000081) | Open | No | No | Unavailable | Unavailable |
| JSP-000082 | [Does every graph of minimum degree at least three contain a cycle whose length is a power of 2?](catalog-0001-0100.md#JSP-000082) | Open | No | No | Unavailable | Unavailable |
| JSP-000083 | [What lower bounds hold for the sum of reciprocals of a graph's distinct cycle lengths, and how does this sum reflect its structure?](catalog-0001-0100.md#JSP-000083) | Open | No | No | Unavailable | Unavailable |
| JSP-000084 | [Can an integer set have a number of two-element sum representations growing asymptotically like a logarithm?](catalog-0001-0100.md#JSP-000084) | Open | No | No | Unavailable | Unavailable |
| JSP-000085 | [Unbounded discrepancy on homogeneous arithmetic progressions](catalog-0001-0100.md#JSP-000085) | Solved | No | No | Unavailable | Unavailable |
| JSP-000086 | [Is the series obtained by summing the reciprocals of factorials minus one irrational?](catalog-0001-0100.md#JSP-000086) | Open | No | No | Unavailable | Unavailable |
| JSP-000087 | [Is the specified generating series involving the number of distinct prime factors of an integer irrational?](catalog-0001-0100.md#JSP-000087) | Solved | No | No | Unavailable | Unavailable |
| JSP-000088 | [Does every two-coloring of triples from a set of continuum cardinality contain a monochromatic subset of the prescribed order type?](catalog-0001-0100.md#JSP-000088) | Open | No | No | Unavailable | Unavailable |
| JSP-000089 | [Is there a density-zero set of positive integers such that every sufficiently dense graph has a cycle with length in that set?](catalog-0001-0100.md#JSP-000089) | Solved | No | No | Unavailable | Unavailable |
| JSP-000090 | [If local subgraphs have large independent sets, must the whole graph be close to bipartite after few modifications?](catalog-0001-0100.md#JSP-000090) | Solved | No | No | Unavailable | Unavailable |
| JSP-000091 | [Can a graph have infinite chromatic number while its finite local subgraphs satisfy the prescribed property after very few edge deletions?](catalog-0001-0100.md#JSP-000091) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000092 | [Can a graph have uncountable chromatic number while all its finite subgraphs have relatively large independent sets?](catalog-0001-0100.md#JSP-000092) | Open | No | No | Unavailable | Unavailable |
| JSP-000093 | [How many edge-disjoint monochromatic triangles are guaranteed in a two-coloring of the edges of a complete graph?](catalog-0001-0100.md#JSP-000093) | Solved | No | No | Unavailable | Unavailable |
| JSP-000094 | [What is the exact exponential growth constant for the number of vertices forcing a monochromatic clique of prescribed size in every two-coloring?](catalog-0001-0100.md#JSP-000094) | Open | No | No | Unavailable | Unavailable |
| JSP-000095 | [Can explicit graphs or colorings attain the predicted exponential lower bounds for diagonal Ramsey numbers?](catalog-0001-0100.md#JSP-000095) | Open | No | No | Unavailable | Unavailable |
| JSP-000096 | [Which minimal graphs prevent Ramsey numbers from growing linearly with the number of edges? Characterize these obstructions.](catalog-0001-0100.md#JSP-000096) | Solved | No | No | Unavailable | Unavailable |
| JSP-000097 | [How many triangles sharing one edge must a sufficiently dense graph contain?](catalog-0001-0100.md#JSP-000097) | Open | No | No | Unavailable | Unavailable |
| JSP-000098 | [What is the minimum number of cliques whose edge sets partition all edges of a chordal graph?](catalog-0001-0100.md#JSP-000098) | Open | No | No | Unavailable | Unavailable |
| JSP-000099 | [How large a regular induced subgraph is guaranteed in an arbitrary graph of given size?](catalog-0001-0100.md#JSP-000099) | Open | No | No | Unavailable | Unavailable |
| JSP-000100 | [How many different sets of cycle lengths occur among graphs with a given number of vertices?](catalog-0001-0100.md#JSP-000100) | Open | No | No | Unavailable | Unavailable |

### Problems 101–200

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000101 | [Is the minimum-degree threshold forcing a quadrilateral monotone in the relevant size parameter?](catalog-0101-0200.md#JSP-000101) | Open | No | No | Unavailable | Unavailable |
| JSP-000102 | [What proportion of the edges of a high-dimensional hypercube can be retained without creating a quadrilateral?](catalog-0101-0200.md#JSP-000102) | Open | No | No | Unavailable | Unavailable |
| JSP-000103 | [How strong a lower bound on a graph's Ramsey number follows from its chromatic number?](catalog-0101-0200.md#JSP-000103) | Open | No | No | Unavailable | Unavailable |
| JSP-000104 | [If a graph has neither a large clique nor a large independent set, how many distinct edge counts do its induced subgraphs attain?](catalog-0101-0200.md#JSP-000104) | Solved | No | No | Unavailable | Unavailable |
| JSP-000105 | [Distinct distances determined by planar point sets](catalog-0101-0200.md#JSP-000105) | Open | No | No | Unavailable | Unavailable |
| JSP-000106 | [unit distance problem](catalog-0101-0200.md#JSP-000106) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000107 | [Are there essentially different geometric configurations minimizing the number of distinct distances among planar points?](catalog-0101-0200.md#JSP-000107) | Open | No | No | Unavailable | Unavailable |
| JSP-000108 | [If every point has many neighbors at one common distance from it, how large a count can be guaranteed at every point? Is it smaller than every fixed positive power of the number of points?](catalog-0101-0200.md#JSP-000108) | Solved | No | No | Unavailable | Unavailable |
| JSP-000109 | [What is the maximum number of unit-distance pairs among the vertices of a convex polygon?](catalog-0101-0200.md#JSP-000109) | Open | No | No | Unavailable | Unavailable |
| JSP-000110 | [Does every convex polygon have a vertex from which no distance to the other vertices repeats too often?](catalog-0101-0200.md#JSP-000110) | Open | No | No | Unavailable | Unavailable |
| JSP-000111 | [How many distinct distances must a planar point set in general position determine?](catalog-0101-0200.md#JSP-000111) | Open | No | No | Unavailable | Unavailable |
| JSP-000112 | [Must a minimum-diameter point set satisfying the prescribed distance constraints contain an equilateral triangle of side length one?](catalog-0101-0200.md#JSP-000112) | Open | No | No | Unavailable | Unavailable |
| JSP-000113 | [How large must a planar point set's diameter be if its distinct distances have the prescribed separation?](catalog-0101-0200.md#JSP-000113) | Open | No | No | Unavailable | Unavailable |
| JSP-000114 | [How many lines can contain exactly four points of a planar point set with no five collinear?](catalog-0101-0200.md#JSP-000114) | Open | No | No | Unavailable | Unavailable |
| JSP-000115 | [If a planar point set determines many four-point lines, must more points lie on a common line?](catalog-0101-0200.md#JSP-000115) | Open | No | No | Unavailable | Unavailable |
| JSP-000116 | [For a given number of points and distance constraints, how many noncongruent configurations attain the minimum diameter?](catalog-0101-0200.md#JSP-000116) | Open | No | No | Unavailable | Unavailable |
| JSP-000117 | [How many unit circles can pass through at least three points of a finite planar point set?](catalog-0101-0200.md#JSP-000117) | Open | No | No | Unavailable | Unavailable |
| JSP-000118 | [What is the maximum sum of side lengths of nonoverlapping squares contained in the unit square?](catalog-0101-0200.md#JSP-000118) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000119 | ['Happy Ending' problem](catalog-0101-0200.md#JSP-000119) | Open | No | No | Unavailable | Unavailable |
| JSP-000120 | [Must a graph of sufficiently large chromatic number contain a subgraph with both large girth and large chromatic number?](catalog-0101-0200.md#JSP-000120) | Open | No | No | Unavailable | Unavailable |
| JSP-000121 | [How many vertices are needed to find a finite subgraph of a prescribed chromatic number in a graph of uncountable chromatic number?](catalog-0101-0200.md#JSP-000121) | Solved | No | No | Unavailable | Unavailable |
| JSP-000122 | [Can every finite subgraph of a graph with uncountable chromatic number be made bipartite by deleting very few edges?](catalog-0101-0200.md#JSP-000122) | Open | No | No | Unavailable | Unavailable |
| JSP-000123 | [How large must a directed graph be to force an independent set or a transitive tournament of a prescribed size?](catalog-0101-0200.md#JSP-000123) | Open | No | No | Unavailable | Unavailable |
| JSP-000124 | [How long can the complex-plane curve where a monic polynomial has absolute value one be?](catalog-0101-0200.md#JSP-000124) | Open | No | No | Unavailable | Unavailable |
| JSP-000125 | [If the size of a pairwise noncommuting subset of a group is bounded, how many abelian subgroups are needed to cover the group?](catalog-0101-0200.md#JSP-000125) | Open | No | No | Unavailable | Unavailable |
| JSP-000126 | [If every two-coloring of an infinite graph's edges gives a monochromatic triangle, does the analogous property hold for every finite clique?](catalog-0101-0200.md#JSP-000126) | Solved | No | No | Unavailable | Unavailable |
| JSP-000127 | [If all zeros of a polynomial lie on the unit circle, how does its maximum modulus on the prescribed region grow with its degree?](catalog-0101-0200.md#JSP-000127) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000128 | [Avoiding affine copies of infinite real sets](catalog-0101-0200.md#JSP-000128) | Open | No | No | Unavailable | Unavailable |
| JSP-000129 | [How strongly can values of integer sequences perturbed by arithmetic functions concentrate in short intervals?](catalog-0101-0200.md#JSP-000129) | Open | No | No | Unavailable | Unavailable |
| JSP-000130 | [Can integers be represented using products of powers of three pairwise coprime bases, with no chosen term dividing another?](catalog-0101-0200.md#JSP-000130) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000131 | [Can sets of integers using only a few allowed digits in different bases together represent every sufficiently large integer?](catalog-0101-0200.md#JSP-000131) | Open | No | No | Unavailable | Unavailable |
| JSP-000132 | [How dense is the sumset of integers with only digits 0 and 1 in base 3 and those with only digits 0 and 1 in base 4?](catalog-0101-0200.md#JSP-000132) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000133 | [How many distinct prime factors must occur in the product of all pairwise sums from an integer set?](catalog-0101-0200.md#JSP-000133) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000134 | [Must a graph contain a triangle if every induced subgraph on roughly half its vertices is sufficiently dense?](catalog-0101-0200.md#JSP-000134) | Open | No | No | Unavailable | Unavailable |
| JSP-000135 | [ambiguous statement](catalog-0101-0200.md#JSP-000135) | Open | No | No | Unavailable | Unavailable |
| JSP-000136 | [How many colors are needed for the graph joining integer-distance pairs of planar points in general position?](catalog-0101-0200.md#JSP-000136) | Open | No | No | Unavailable | Unavailable |
| JSP-000137 | [How large can a subset of a finite integer interval be if no element divides the sum of a prescribed number of other elements?](catalog-0101-0200.md#JSP-000137) | Open | No | No | Unavailable | Unavailable |
| JSP-000138 | [How many distances determined by a finite planar point set must occur relatively infrequently?](catalog-0101-0200.md#JSP-000138) | Open | No | No | Unavailable | Unavailable |
| JSP-000139 | [How large must the maximum degree of a triangle-free graph of diameter at most two be?](catalog-0101-0200.md#JSP-000139) | Solved | No | No | Unavailable | Unavailable |
| JSP-000140 | [How many edge colors are necessary if every four-vertex clique must contain at least five colors?](catalog-0101-0200.md#JSP-000140) | Solved | No | No | Unavailable | Unavailable |
| JSP-000141 | [Can a product of consecutive positive integers have every prime factor occurring with exponent at least two?](catalog-0101-0200.md#JSP-000141) | Open | No | No | Unavailable | Unavailable |
| JSP-000142 | [How fast does the interval length forcing a monochromatic arithmetic progression of prescribed length in every two-coloring grow?](catalog-0101-0200.md#JSP-000142) | Open | No | No | Unavailable | Unavailable |
| JSP-000143 | [Are there arbitrarily long arithmetic progressions whose terms are consecutive primes in the full prime sequence?](catalog-0101-0200.md#JSP-000143) | Open | No | No | Unavailable | Unavailable |
| JSP-000144 | [How large can a subset of a finite integer interval be if it contains no arithmetic progression of a specified length?](catalog-0101-0200.md#JSP-000144) | Open | No | No | Unavailable | Unavailable |
| JSP-000145 | [How dense can a set of real numbers be if distinct elements avoid prescribed neighborhoods of one another's integer multiples?](catalog-0101-0200.md#JSP-000145) | Open | No | No | Unavailable | Unavailable |
| JSP-000146 | [Determine the average and growth of fixed powers of gaps between consecutive squarefree numbers.](catalog-0101-0200.md#JSP-000146) | Open | No | No | Unavailable | Unavailable |
| JSP-000147 | [How many edges can a graph have while excluding a given bipartite graph of bounded degeneracy?](catalog-0101-0200.md#JSP-000147) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000148 | [How many representations of one are there as a sum of a prescribed number of distinct positive unit fractions?](catalog-0101-0200.md#JSP-000148) | Open | No | No | Unavailable | Unavailable |
| JSP-000149 | [How does the minimum number of colors needed to give nearby edges different colors depend on the maximum degree?](catalog-0101-0200.md#JSP-000149) | Open | No | No | Unavailable | Unavailable |
| JSP-000150 | [What is the smallest vertex set meeting every maximal clique of a graph?](catalog-0101-0200.md#JSP-000150) | Open | No | No | Unavailable | Unavailable |
| JSP-000151 | [For an integer set with distinct pairwise sums, how many elements of its sumset have neither neighboring integer in the sumset?](catalog-0101-0200.md#JSP-000151) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000152 | [For an integer set with distinct pairwise sums, determine the average squared gap between consecutive elements of its sumset.](catalog-0101-0200.md#JSP-000152) | Open | No | No | Unavailable | Unavailable |
| JSP-000153 | [How much can the largest size of a Sidon set increase when the endpoint of its containing interval increases slightly?](catalog-0101-0200.md#JSP-000153) | Open | No | No | Unavailable | Unavailable |
| JSP-000154 | [How small can an inclusion-maximal Sidon set in a finite integer interval be?](catalog-0101-0200.md#JSP-000154) | Open | No | No | Unavailable | Unavailable |
| JSP-000155 | [Is there an infinite Sidon set whose three-term sums represent every sufficiently large integer?](catalog-0101-0200.md#JSP-000155) | Solved | No | No | Unavailable | Unavailable |
| JSP-000156 | [How dense can an integer set be if each integer has at most two representations as a sum of two of its elements?](catalog-0101-0200.md#JSP-000156) | Open | No | No | Unavailable | Unavailable |
| JSP-000157 | [How many vertices force a four-cycle in one color or a clique of prescribed size in the other color in every two-coloring of a complete graph?](catalog-0101-0200.md#JSP-000157) | Open | No | No | Unavailable | Unavailable |
| JSP-000158 | [How many colors are needed to color consecutive integers so that every four-term arithmetic progression uses at least three colors?](catalog-0101-0200.md#JSP-000158) | Open | No | No | Unavailable | Unavailable |
| JSP-000159 | [How does density affect the threshold for finding the specified color-balanced structure in a two-colored hypergraph?](catalog-0101-0200.md#JSP-000159) | Open | No | No | Unavailable | Unavailable |
| JSP-000160 | [Locally balanced two-colorings of complete graphs](catalog-0101-0200.md#JSP-000160) | Open | No | No | Unavailable | Unavailable |
| JSP-000161 | [Linear Ramsey bounds for graphs of bounded degeneracy](catalog-0101-0200.md#JSP-000161) | Solved | No | No | Unavailable | Unavailable |
| JSP-000162 | [What is the precise asymptotic growth of the Ramsey number for a triangle versus a large clique?](catalog-0101-0200.md#JSP-000162) | Open | No | No | Unavailable | Unavailable |
| JSP-000163 | [How many vertices can a two-colored complete graph have while avoiding a four-vertex clique in one color and a prescribed large clique in the other?](catalog-0101-0200.md#JSP-000163) | Solved | No | No | Unavailable | Unavailable |
| JSP-000164 | [How does the minimum number of edges needed to make a graph triangle-free compare with its maximum number of edge-disjoint triangles?](catalog-0101-0200.md#JSP-000164) | Open | No | No | Unavailable | Unavailable |
| JSP-000165 | [What is the maximum density of an integer set containing no number together with both its double and its triple?](catalog-0101-0200.md#JSP-000165) | Open | No | No | Unavailable | Unavailable |
| JSP-000166 | [How large can the sum of reciprocals of an integer set be if it contains no arithmetic progression of a specified length?](catalog-0101-0200.md#JSP-000166) | Open | No | No | Unavailable | Unavailable |
| JSP-000167 | [sparse ruler problem](catalog-0101-0200.md#JSP-000167) | Open | No | No | Unavailable | Unavailable |
| JSP-000168 | [Does every finite coloring of the positive integers contain a large set whose specified sums and products all have the same color?](catalog-0101-0200.md#JSP-000168) | Open | No | No | Unavailable | Unavailable |
| JSP-000169 | [Does every two-coloring of the plane contain a monochromatic congruent copy of a prescribed triangle?](catalog-0101-0200.md#JSP-000169) | Open | No | No | Unavailable | Unavailable |
| JSP-000170 | [Which finite point configurations have a monochromatic congruent copy under every finite coloring in sufficiently high dimension?](catalog-0101-0200.md#JSP-000170) | Open | No | No | Unavailable | Unavailable |
| JSP-000171 | [How small can one make the discrepancy of signed sums along arithmetic progressions?](catalog-0101-0200.md#JSP-000171) | Open | No | No | Unavailable | Unavailable |
| JSP-000172 | [Can signs be assigned to the positive integers so that discrepancy along each arithmetic progression satisfies an optimal bound depending only on its common difference?](catalog-0101-0200.md#JSP-000172) | Open | No | No | Unavailable | Unavailable |
| JSP-000173 | [How many short arithmetic progressions in an integer set force a longer arithmetic progression?](catalog-0101-0200.md#JSP-000173) | Solved | No | No | Unavailable | Unavailable |
| JSP-000174 | [How much can forbidding several subgraphs reduce the extremal edge count compared with forbidding just one of them?](catalog-0101-0200.md#JSP-000174) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000175 | [Is the Ramsey number of a high-dimensional hypercube bounded by a constant times its number of vertices?](catalog-0101-0200.md#JSP-000175) | Open | No | No | Unavailable | Unavailable |
| JSP-000176 | [How many edges can a graph have if it contains no regular subgraph of a prescribed degree?](catalog-0101-0200.md#JSP-000176) | Solved | No | No | Unavailable | Unavailable |
| JSP-000177 | [What is the exponential growth rate of the number of vertices needed to force a monochromatic triangle as the number of edge colors increases?](catalog-0101-0200.md#JSP-000177) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000178 | [Can the edges of every finite graph be partitioned into linearly many cycles and single edges, in terms of its number of vertices?](catalog-0101-0200.md#JSP-000178) | Open | No | No | Unavailable | Unavailable |
| JSP-000179 | [How large can a subset of an integer interval be if no element is the average of some other elements?](catalog-0101-0200.md#JSP-000179) | Solved | No | No | Unavailable | Unavailable |
| JSP-000180 | [In every two-coloring of the positive integers, what relationship between length and common difference can be guaranteed for a monochromatic arithmetic progression?](catalog-0101-0200.md#JSP-000180) | Open | No | No | Unavailable | Unavailable |
| JSP-000181 | [Can the plane be colored red and blue while avoiding both a red unit-distance pair and a blue equally spaced collinear configuration?](catalog-0101-0200.md#JSP-000181) | Open | No | No | Unavailable | Unavailable |
| JSP-000182 | [How long must an integer interval be to force either a monochromatic or a rainbow arithmetic progression under every coloring?](catalog-0101-0200.md#JSP-000182) | Solved | No | No | Unavailable | Unavailable |
| JSP-000183 | [Must an infinite walk in three-dimensional space using a finite set of step vectors visit three collinear points?](catalog-0101-0200.md#JSP-000183) | Solved | No | No | Unavailable | Unavailable |
| JSP-000184 | [How long a monotone arithmetic progression is guaranteed in every permutation of a finite interval of integers?](catalog-0101-0200.md#JSP-000184) | Open | No | No | Unavailable | Unavailable |
| JSP-000185 | [Must every permutation of the natural numbers contain a four-term arithmetic progression appearing in monotone order?](catalog-0101-0200.md#JSP-000185) | Open | No | No | Unavailable | Unavailable |
| JSP-000186 | [Can the natural numbers be partitioned into two sets and each set ordered to avoid monotone three-term arithmetic progressions?](catalog-0101-0200.md#JSP-000186) | Open | No | No | Unavailable | Unavailable |
| JSP-000187 | [What upper bounds hold for the length of arithmetic progressions of primes in a prescribed range?](catalog-0101-0200.md#JSP-000187) | Open | No | No | Unavailable | Unavailable |
| JSP-000188 | [How large a subset avoiding arithmetic progressions of a prescribed length must every finite integer set contain?](catalog-0101-0200.md#JSP-000188) | Open | No | No | Unavailable | Unavailable |
| JSP-000189 | [How many pairwise disjoint residue classes with distinct moduli can be selected?](catalog-0101-0200.md#JSP-000189) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000190 | [Which integers remain composite after multiplication by arbitrary powers of two and three followed by addition of one?](catalog-0101-0200.md#JSP-000190) | Open | No | No | Unavailable | Unavailable |
| JSP-000191 | [Can every sufficiently large integer be written as a power of two plus an integer with few prime factors?](catalog-0101-0200.md#JSP-000191) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000192 | [Are there Steiner triple systems avoiding all short cyclic configurations specified in the problem, with arbitrarily large girth of this kind?](catalog-0101-0200.md#JSP-000192) | Solved | No | No | Unavailable | Unavailable |
| JSP-000193 | [How large can the gap between consecutive positive squarefree integers be?](catalog-0101-0200.md#JSP-000193) | Open | No | No | Unavailable | Unavailable |
| JSP-000194 | [How many ordinary lines, each containing exactly two of the points, must a finite noncollinear planar point set determine?](catalog-0101-0200.md#JSP-000194) | Solved | No | No | Unavailable | Unavailable |
| JSP-000195 | [If the number of points on any one line is bounded, how many distinct lines must a planar point set determine?](catalog-0101-0200.md#JSP-000195) | Solved | No | No | Unavailable | Unavailable |
| JSP-000196 | [Is there a dense subset of the plane in which every pairwise distance is rational?](catalog-0101-0200.md#JSP-000196) | Open | No | No | Unavailable | Unavailable |
| JSP-000197 | [How many planar points in general position can have all pairwise distances integral?](catalog-0101-0200.md#JSP-000197) | Open | No | No | Unavailable | Unavailable |
| JSP-000198 | [How many points in general position force an empty convex polygon of a prescribed size?](catalog-0101-0200.md#JSP-000198) | Solved | No | No | Unavailable | Unavailable |
| JSP-000199 | [For which n do planar crescent configurations exist?](catalog-0101-0200.md#JSP-000199) | Open | No | No | Unavailable | Unavailable |
| JSP-000200 | [Determine how consecutive prime gaps increase, decrease, or remain equal, and how frequently each pattern occurs.](catalog-0101-0200.md#JSP-000200) | Open | No | No | Unavailable | Unavailable |

### Problems 201–300

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000201 | [How large can gaps between consecutive integers representable as sums of two squares be?](catalog-0201-0300.md#JSP-000201) | Open | No | No | Unavailable | Unavailable |
| JSP-000202 | [For a finite point set of fixed diameter in higher-dimensional space, how many pairs can attain that diameter?](catalog-0201-0300.md#JSP-000202) | Solved | No | No | Unavailable | Unavailable |
| JSP-000203 | [How large can the specified integral of a trigonometric polynomial be under the problem's real-zero conditions?](catalog-0201-0300.md#JSP-000203) | Solved | No | No | Unavailable | Unavailable |
| JSP-000204 | [For a transcendental entire function, determine the limiting ratio between its largest power-series term and its maximum modulus on a circle.](catalog-0201-0300.md#JSP-000204) | Solved | No | No | Unavailable | Unavailable |
| JSP-000205 | [What is the maximum density of a measurable planar set containing no pair at distance one?](catalog-0201-0300.md#JSP-000205) | Solved | No | No | Unavailable | Unavailable |
| JSP-000206 | [What is the smallest upper bound for the sum of squared consecutive prime gaps in a prescribed range?](catalog-0201-0300.md#JSP-000206) | Open | No | No | Unavailable | Unavailable |
| JSP-000207 | [Do prime gaps, normalized by their average scale, have a limiting distribution?](catalog-0201-0300.md#JSP-000207) | Open | No | No | Unavailable | Unavailable |
| JSP-000208 | [Determine the gap distribution among consecutive integers coprime to a product of the first several primes.](catalog-0201-0300.md#JSP-000208) | Solved | No | No | Unavailable | Unavailable |
| JSP-000209 | [How many representations can a single integer have as a prime plus a power of two?](catalog-0201-0300.md#JSP-000209) | Open | No | No | Unavailable | Unavailable |
| JSP-000210 | [How long a run of unusually large consecutive prime gaps can occur?](catalog-0201-0300.md#JSP-000210) | Open | No | No | Unavailable | Unavailable |
| JSP-000211 | [For integers generated by an arbitrary infinite set of primes, can the gaps between consecutive terms tend to infinity?](catalog-0201-0300.md#JSP-000211) | Solved | No | No | Unavailable | Unavailable |
| JSP-000212 | [How large can a subset of an integer interval be if all distinct three-element subsets have different sums?](catalog-0201-0300.md#JSP-000212) | Open | No | No | Unavailable | Unavailable |
| JSP-000213 | [Representing 4/n as a sum of three unit fractions](catalog-0201-0300.md#JSP-000213) | Open | No | No | Unavailable | Unavailable |
| JSP-000214 | [What structure must a nearly quadratically growing integer sequence have if its reciprocal sum is rational?](catalog-0201-0300.md#JSP-000214) | Open | No | No | Unavailable | Unavailable |
| JSP-000215 | [What is the density of integers representable as a prime plus the floor of the specified exponential expression?](catalog-0201-0300.md#JSP-000215) | Open | No | No | Unavailable | Unavailable |
| JSP-000216 | [How much larger than a zero-density integer set can its sumset with itself be?](catalog-0201-0300.md#JSP-000216) | Solved | No | No | Unavailable | Unavailable |
| JSP-000217 | [Is the infinite series defined by sparse nonzero binary digits transcendental?](catalog-0201-0300.md#JSP-000217) | Open | No | No | Unavailable | Unavailable |
| JSP-000218 | [Is the series with Euler totient values as numerators and powers of two as denominators irrational?](catalog-0201-0300.md#JSP-000218) | Open | No | No | Unavailable | Unavailable |
| JSP-000219 | [Is the binary generating series constructed from primes irrational?](catalog-0201-0300.md#JSP-000219) | Open | No | No | Unavailable | Unavailable |
| JSP-000220 | [Are the series with divisor-power sums as numerators and factorials as denominators irrational?](catalog-0201-0300.md#JSP-000220) | Open | No | No | Unavailable | Unavailable |
| JSP-000221 | [What conditions ensure that finite sums of distinct elements of an integer set represent every sufficiently large integer?](catalog-0201-0300.md#JSP-000221) | Open | No | No | Unavailable | Unavailable |
| JSP-000222 | [How large must the maximum modulus of the specified product of binomials on the unit circle be?](catalog-0201-0300.md#JSP-000222) | Open | No | No | Unavailable | Unavailable |
| JSP-000223 | [Under the stated conditions, is every infinite subsum of reciprocals of powers of two minus one irrational?](catalog-0201-0300.md#JSP-000223) | Open | No | No | Unavailable | Unavailable |
| JSP-000224 | [Is the reciprocal series with product denominators constructed from the divisor-counting function irrational?](catalog-0201-0300.md#JSP-000224) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000225 | [Must the binary-weighted infinite sum associated with the specified sparse integer sequence be irrational?](catalog-0201-0300.md#JSP-000225) | Open | No | No | Unavailable | Unavailable |
| JSP-000226 | [Determine how binary-weighted terms can be decomposed and how finite decompositions relate to infinite-series representations.](catalog-0201-0300.md#JSP-000226) | Open | No | No | Unavailable | Unavailable |
| JSP-000227 | [Is there an integer sequence whose reciprocal sum remains irrational after every term undergoes the prescribed asymptotically small perturbation?](catalog-0201-0300.md#JSP-000227) | Open | No | No | Unavailable | Unavailable |
| JSP-000228 | [Is there an integer sequence whose reciprocal sum remains irrational under arbitrary bounded perturbations of its terms?](catalog-0201-0300.md#JSP-000228) | Open | No | No | Unavailable | Unavailable |
| JSP-000229 | [ambiguous statement](catalog-0201-0300.md#JSP-000229) | Open | No | No | Unavailable | Unavailable |
| JSP-000230 | [When must the reciprocal sum of a sparse subsequence of Fibonacci numbers be irrational?](catalog-0201-0300.md#JSP-000230) | Open | No | No | Unavailable | Unavailable |
| JSP-000231 | [Determine the arithmetic properties of the specified reciprocal sum of least common multiples for integers generated by finitely many primes.](catalog-0201-0300.md#JSP-000231) | Open | No | No | Unavailable | Unavailable |
| JSP-000232 | [Stanley sequences](catalog-0201-0300.md#JSP-000232) | Open | No | No | Unavailable | Unavailable |
| JSP-000233 | [How large can a family of sets be if every pairwise intersection is a nonempty arithmetic progression?](catalog-0201-0300.md#JSP-000233) | Open | No | No | Unavailable | Unavailable |
| JSP-000234 | [Can the integers be covered by residue classes whose moduli are all one less than a prime?](catalog-0201-0300.md#JSP-000234) | Open | No | No | Unavailable | Unavailable |
| JSP-000235 | [Herzog-Schönheim conjecture](catalog-0201-0300.md#JSP-000235) | Open | No | No | Unavailable | Unavailable |
| JSP-000236 | [Is there a Lucas sequence consisting entirely of composite terms but with no fixed nontrivial divisor common to all terms?](catalog-0201-0300.md#JSP-000236) | Open | No | No | Unavailable | Unavailable |
| JSP-000237 | [For prescribed moduli, what are the largest and smallest proportions of integers covered by a choice of corresponding residue classes?](catalog-0201-0300.md#JSP-000237) | Open | No | No | Unavailable | Unavailable |
| JSP-000238 | [Can residue classes with prime moduli cover every sufficiently large integer?](catalog-0201-0300.md#JSP-000238) | Open | No | No | Unavailable | Unavailable |
| JSP-000239 | [Can an infinite covering by residue classes be uniformly approximated in density by finite subfamilies?](catalog-0201-0300.md#JSP-000239) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000240 | [Does the greedy Egyptian-fraction algorithm restricted to odd denominators always terminate for rational inputs?](catalog-0201-0300.md#JSP-000240) | Open | No | No | Unavailable | Unavailable |
| JSP-000241 | [Can the denominators in Egyptian-fraction representations be used to combine the specified polynomial values into every sufficiently large integer?](catalog-0201-0300.md#JSP-000241) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000242 | [In a representation of one as a prescribed number of positive unit fractions, how large can the smallest denominator be?](catalog-0201-0300.md#JSP-000242) | Solved | No | No | Unavailable | Unavailable |
| JSP-000243 | [What is the shortest integer interval containing distinct denominators whose reciprocals sum to one?](catalog-0201-0300.md#JSP-000243) | Solved | No | No | Unavailable | Unavailable |
| JSP-000244 | [Must every representation of one by distinct positive unit fractions have two consecutive ordered denominators differing by at least three?](catalog-0201-0300.md#JSP-000244) | Open | No | No | Unavailable | Unavailable |
| JSP-000245 | [How many pairs of integer intervals have reciprocal sums whose total is an integer?](catalog-0201-0300.md#JSP-000245) | Open | No | No | Unavailable | Unavailable |
| JSP-000246 | [Can separated integer intervals be chosen so that the reciprocals of all their integers sum to one?](catalog-0201-0300.md#JSP-000246) | Open | No | No | Unavailable | Unavailable |
| JSP-000247 | [When can a finite harmonic sum, expressed over the least common multiple of its initial integers, be reduced further?](catalog-0201-0300.md#JSP-000247) | Open | No | No | Unavailable | Unavailable |
| JSP-000248 | [Which positive integers can be the largest denominator in a representation of one by distinct unit fractions?](catalog-0201-0300.md#JSP-000248) | Solved | No | No | Unavailable | Unavailable |
| JSP-000249 | [ambiguous statement](catalog-0201-0300.md#JSP-000249) | Open | No | No | Unavailable | Unavailable |
| JSP-000250 | [Within the prescribed finite denominator range, which initial denominators cannot occur in a representation of one, and where is the smallest exception?](catalog-0201-0300.md#JSP-000250) | Solved | No | No | Unavailable | Unavailable |
| JSP-000251 | [How many unit fractions are needed to represent one if every denominator must exceed a prescribed threshold?](catalog-0201-0300.md#JSP-000251) | Open | No | No | Unavailable | Unavailable |
| JSP-000252 | [How many subsets of a finite integer range have reciprocal sum exactly one?](catalog-0201-0300.md#JSP-000252) | Solved | No | No | Unavailable | Unavailable |
| JSP-000253 | [How large can a subset of an integer interval be if no element's reciprocal is a sum of reciprocals of other elements?](catalog-0201-0300.md#JSP-000253) | Open | No | No | Unavailable | Unavailable |
| JSP-000254 | [How large can a subset of an integer interval be if no element's reciprocal equals the sum of two other elements' reciprocals?](catalog-0201-0300.md#JSP-000254) | Open | No | No | Unavailable | Unavailable |
| JSP-000255 | [What is the minimum number of distinct positive unit fractions needed to represent a given positive rational number?](catalog-0201-0300.md#JSP-000255) | Open | No | No | Unavailable | Unavailable |
| JSP-000256 | [How small can the largest denominator be in a representation of a given positive rational number by distinct unit fractions?](catalog-0201-0300.md#JSP-000256) | Solved | No | No | Unavailable | Unavailable |
| JSP-000257 | [Which positive rational numbers are sums of unit fractions whose denominators are products of two distinct primes?](catalog-0201-0300.md#JSP-000257) | Open | No | No | Unavailable | Unavailable |
| JSP-000258 | [Can two finite sets of primes have reciprocal sums whose product is exactly one?](catalog-0201-0300.md#JSP-000258) | Open | No | No | Unavailable | Unavailable |
| JSP-000259 | [Which integers can be represented by sums of distinct unit fractions with denominators in a finite range?](catalog-0201-0300.md#JSP-000259) | Solved | No | No | Unavailable | Unavailable |
| JSP-000260 | [How closely can a subsum of positive unit fractions with denominators in a finite range approximate one?](catalog-0201-0300.md#JSP-000260) | Open | No | No | Unavailable | Unavailable |
| JSP-000261 | [If a collection of positive unit fractions sums to more than one, how closely can a subsum approximate one from below?](catalog-0201-0300.md#JSP-000261) | Open | No | No | Unavailable | Unavailable |
| JSP-000262 | [Which finite sums of reciprocals of primes equal one minus the reciprocal of a positive integer?](catalog-0201-0300.md#JSP-000262) | Open | No | No | Unavailable | Unavailable |
| JSP-000263 | [How close to zero can a nonzero signed subsum of a finite harmonic series be?](catalog-0201-0300.md#JSP-000263) | Open | No | No | Unavailable | Unavailable |
| JSP-000264 | [Does every assignment of signs to the specified reciprocal set admit a nonempty zero-sum subset?](catalog-0201-0300.md#JSP-000264) | Solved | No | No | Unavailable | Unavailable |
| JSP-000265 | [How large can a minimal nonempty zero-sum collection of signed integer reciprocals be?](catalog-0201-0300.md#JSP-000265) | Open | No | No | Unavailable | Unavailable |
| JSP-000266 | [How many distinct subset sums do the reciprocals of the first several positive integers have?](catalog-0201-0300.md#JSP-000266) | Solved | No | No | Unavailable | Unavailable |
| JSP-000267 | [How many integers can be selected from a finite range so that all subset sums of their reciprocals are distinct?](catalog-0201-0300.md#JSP-000267) | Solved | No | No | Unavailable | Unavailable |
| JSP-000268 | [How many representations can an integer have as a prescribed number of integer powers of the same degree?](catalog-0201-0300.md#JSP-000268) | Open | No | No | Unavailable | Unavailable |
| JSP-000269 | [How many integers in a finite interval are sums of a prescribed number of like powers?](catalog-0201-0300.md#JSP-000269) | Open | No | No | Unavailable | Unavailable |
| JSP-000270 | [Can the integer values of a polynomial form a Sidon sequence?](catalog-0201-0300.md#JSP-000270) | Open | No | No | Unavailable | Unavailable |
| JSP-000271 | [How many integers in a finite interval are sums of three like powers?](catalog-0201-0300.md#JSP-000271) | Open | No | No | Unavailable | Unavailable |
| JSP-000272 | [Can a quadratically growing integer set be a minimal asymptotic basis of order two, losing that property upon deletion of any element?](catalog-0201-0300.md#JSP-000272) | Open | No | No | Unavailable | Unavailable |
| JSP-000273 | [How large can a subset of an integer interval be if the sum of any two distinct elements never divides their product?](catalog-0201-0300.md#JSP-000273) | Open | No | No | Unavailable | Unavailable |
| JSP-000274 | [For an infinite Sidon set, how large can the limsup of its counting function divided by the square root of the interval length be?](catalog-0201-0300.md#JSP-000274) | Open | No | No | Unavailable | Unavailable |
| JSP-000275 | [Can an asymptotic additive basis of positive density be minimal under deletion of any element?](catalog-0201-0300.md#JSP-000275) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000276 | [What conditions ensure uniformly bounded gaps between differences occurring repeatedly in an integer set?](catalog-0201-0300.md#JSP-000276) | Open | No | No | Unavailable | Unavailable |
| JSP-000277 | [How small a prime-factor bound suffices to express an integer as a sum of two integers having only small prime factors?](catalog-0201-0300.md#JSP-000277) | Open | No | No | Unavailable | Unavailable |
| JSP-000278 | [What structure is forced when the density of a sumset equals the sum of the densities of its two summand sets?](catalog-0201-0300.md#JSP-000278) | Open | No | No | Unavailable | Unavailable |
| JSP-000279 | [How much can the required order differ between additive bases allowing at most a prescribed number of summands and those requiring exactly that number?](catalog-0201-0300.md#JSP-000279) | Open | No | No | Unavailable | Unavailable |
| JSP-000280 | [What conditions make a set an additive basis of prescribed order when summands must be distinct?](catalog-0201-0300.md#JSP-000280) | Open | No | No | Unavailable | Unavailable |
| JSP-000281 | [Must the set of sums of distinct elements of an additive basis have positive lower density?](catalog-0201-0300.md#JSP-000281) | Solved | No | No | Unavailable | Unavailable |
| JSP-000282 | [How fast does the greedy Sidon sequence grow?](catalog-0201-0300.md#JSP-000282) | Open | No | No | Unavailable | Unavailable |
| JSP-000283 | [Does the sequence obtained by repeatedly adjoining the smallest integer not expressible as a sum of two existing terms eventually become periodic?](catalog-0201-0300.md#JSP-000283) | Open | No | No | Unavailable | Unavailable |
| JSP-000284 | [What density and gap patterns arise when each new term must have exactly one representation as a sum of two earlier terms?](catalog-0201-0300.md#JSP-000284) | Open | No | No | Unavailable | Unavailable |
| JSP-000285 | [Must the finite subset sums of a positive-density integer multiset contain an infinite arithmetic progression?](catalog-0201-0300.md#JSP-000285) | Solved | No | No | Unavailable | Unavailable |
| JSP-000286 | [If an integer set has at least square-root-scale size in large intervals, must its finite subset sums contain an infinite arithmetic progression?](catalog-0201-0300.md#JSP-000286) | Solved | No | No | Unavailable | Unavailable |
| JSP-000287 | [How do the thresholds for representing all large integers by distinct-element sums compare for the sequences built from adjacent powers?](catalog-0201-0300.md#JSP-000287) | Open | No | No | Unavailable | Unavailable |
| JSP-000288 | [Must ratios of consecutive terms in the specified minimal stably complete sequences converge to the golden ratio?](catalog-0201-0300.md#JSP-000288) | Solved | No | No | Unavailable | Unavailable |
| JSP-000289 | [Can every tail of a nearly doubling sequence have finite subset sums covering a set of integers of density one?](catalog-0201-0300.md#JSP-000289) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000290 | [How does deleting a prescribed number of elements affect a set's ability to represent all large integers as sums of distinct elements?](catalog-0201-0300.md#JSP-000290) | Open | No | No | Unavailable | Unavailable |
| JSP-000291 | [When do distinct-element sums of a sequence of floors of exponential values represent every sufficiently large integer?](catalog-0201-0300.md#JSP-000291) | Open | No | No | Unavailable | Unavailable |
| JSP-000292 | [For the sequence built from polynomial values and reciprocal terms, do distinct-element sums still represent every sufficiently large integer after deleting any finite initial segment?](catalog-0201-0300.md#JSP-000292) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000293 | [Must every measurable planar set of sufficiently large area contain a triangle of area exactly one?](catalog-0201-0300.md#JSP-000293) | Open | No | No | Unavailable | Unavailable |
| JSP-000294 | [Can distinct-element sums from the union of two floored exponential sequences represent every sufficiently large integer?](catalog-0201-0300.md#JSP-000294) | Open | No | No | Unavailable | Unavailable |
| JSP-000295 | [How long can an increasing integer sequence in a prescribed range be if all sums of consecutive terms are distinct?](catalog-0201-0300.md#JSP-000295) | Open | No | No | Unavailable | Unavailable |
| JSP-000296 | [How many representations can an integer have as a sum of consecutive terms of a given increasing integer sequence?](catalog-0201-0300.md#JSP-000296) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000297 | [segmented numbers](catalog-0201-0300.md#JSP-000297) | Open | No | No | Unavailable | Unavailable |
| JSP-000298 | [How many colors are needed to color the positive integers so that a prescribed integer is not a monochromatic subset sum?](catalog-0201-0300.md#JSP-000298) | Solved | No | No | Unavailable | Unavailable |
| JSP-000299 | [How large can a subset of a finite integer range be if none of its subset sums equals a prescribed target?](catalog-0201-0300.md#JSP-000299) | Open | No | No | Unavailable | Unavailable |
| JSP-000300 | [Are there three consecutive powerful positive integers, each divisible by the square of every prime dividing it?](catalog-0201-0300.md#JSP-000300) | Open | No | No | Unavailable | Unavailable |

### Problems 301–400

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000301 | [If two consecutive positive integers are powerful, must at least one be a perfect square?](catalog-0301-0400.md#JSP-000301) | Solved | No | No | Unavailable | Unavailable |
| JSP-000302 | [ambiguous statement](catalog-0301-0400.md#JSP-000302) | Open | No | No | Unavailable | Unavailable |
| JSP-000303 | [How large can the product of the powerful parts of consecutive integers be?](catalog-0301-0400.md#JSP-000303) | Open | No | No | Unavailable | Unavailable |
| JSP-000304 | [How large a prime factor must the product of two consecutive positive integers have?](catalog-0301-0400.md#JSP-000304) | Open | No | No | Unavailable | Unavailable |
| JSP-000305 | [Are there arbitrarily long runs of consecutive integers whose prime factors all lie below the specified bound?](catalog-0301-0400.md#JSP-000305) | Solved | Yes | Yes | Unclaimed | Claimed |
| JSP-000306 | [What is the density of integers whose largest prime factor is smaller than that of the next integer?](catalog-0301-0400.md#JSP-000306) | Open | No | No | Unavailable | Unavailable |
| JSP-000307 | [Can three consecutive integers have strictly decreasing largest prime factors?](catalog-0301-0400.md#JSP-000307) | Solved | No | No | Unavailable | Unavailable |
| JSP-000308 | [Under the stated restrictions, are there only finitely many factorials equal to products of smaller factorials?](catalog-0301-0400.md#JSP-000308) | Open | No | No | Unavailable | Unavailable |
| JSP-000309 | [How many factorials are needed to obtain a square product, and how is this minimum distributed?](catalog-0301-0400.md#JSP-000309) | Open | No | No | Unavailable | Unavailable |
| JSP-000310 | [Can distinct prime divisors be assigned to the terms of every run of consecutive composite integers?](catalog-0301-0400.md#JSP-000310) | Open | No | No | Unavailable | Unavailable |
| JSP-000311 | [Are infinitely many central binomial coefficients coprime to 105, hence divisible by none of 3, 5, and 7?](catalog-0301-0400.md#JSP-000311) | Open | No | No | Unavailable | Unavailable |
| JSP-000312 | [How large is the reciprocal sum of primes that do not divide the specified central binomial coefficient?](catalog-0301-0400.md#JSP-000312) | Open | No | No | Unavailable | Unavailable |
| JSP-000313 | [What is the density of rows of Pascal's triangle containing exactly a prescribed number of squarefree entries?](catalog-0301-0400.md#JSP-000313) | Solved | No | No | Unavailable | Unavailable |
| JSP-000314 | [How many starting points make the largest prime factor repeat in a product of consecutive integers, and what is their density?](catalog-0301-0400.md#JSP-000314) | Solved | No | No | Unavailable | Unavailable |
| JSP-000315 | [Determine the growth of the counting function of highly composite numbers, whose divisor counts exceed those of all smaller positive integers.](catalog-0301-0400.md#JSP-000315) | Solved | No | No | Unavailable | Unavailable |
| JSP-000316 | [How long can a consecutive-integer interval be if its product's largest prime factor must occur repeatedly?](catalog-0301-0400.md#JSP-000316) | Open | No | No | Unavailable | Unavailable |
| JSP-000317 | [Can a prime square be followed by several consecutive integers having no prime factor larger than that prime?](catalog-0301-0400.md#JSP-000317) | Open | No | No | Unavailable | Unavailable |
| JSP-000318 | [How far beyond an interval's right endpoint can a composite integer in that interval plus its least prime factor lie?](catalog-0301-0400.md#JSP-000318) | Open | No | No | Unavailable | Unavailable |
| JSP-000319 | [Are infinitely many binomial coefficients products of consecutive primes?](catalog-0301-0400.md#JSP-000319) | Open | No | No | Unavailable | Unavailable |
| JSP-000320 | [Must a binomial coefficient have a divisor close in size to its upper parameter?](catalog-0301-0400.md#JSP-000320) | Solved | No | No | Unavailable | Unavailable |
| JSP-000321 | [When can two disjoint intervals of consecutive positive integers have equal products?](catalog-0301-0400.md#JSP-000321) | Open | No | No | Unavailable | Unavailable |
| JSP-000322 | [When does the product of the first half of a consecutive-integer interval divide the product of the second half?](catalog-0301-0400.md#JSP-000322) | Open | No | No | Unavailable | Unavailable |
| JSP-000323 | [When a factorial is a product of distinct integers all larger than its index, how small can the largest factor be?](catalog-0301-0400.md#JSP-000323) | Open | No | No | Unavailable | Unavailable |
| JSP-000324 | [How narrow an interval can contain all the distinct factors in a factorization of a factorial?](catalog-0301-0400.md#JSP-000324) | Open | No | No | Unavailable | Unavailable |
| JSP-000325 | [What conditions on an interval's starting point make its consecutive-integer product divisible by a prescribed integer?](catalog-0301-0400.md#JSP-000325) | Open | No | No | Unavailable | Unavailable |
| JSP-000326 | [Can a central binomial coefficient be divisible by the specified descending product of arbitrarily many consecutive integers?](catalog-0301-0400.md#JSP-000326) | Open | No | No | Unavailable | Unavailable |
| JSP-000327 | [Under the stated restrictions, are there only finitely many equalities between products of distinct central binomial coefficients?](catalog-0301-0400.md#JSP-000327) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000328 | [Brocard-Ramanujan conjecture](catalog-0301-0400.md#JSP-000328) | Open | No | No | Unavailable | Unavailable |
| JSP-000329 | [If a product of factorials divides another factorial, by how much can the sum of its indices exceed the latter index?](catalog-0301-0400.md#JSP-000329) | Open | No | No | Unavailable | Unavailable |
| JSP-000330 | [Which otherwise invalid divisibility relations between factorial products can be obtained by inserting powers of specified small primes?](catalog-0301-0400.md#JSP-000330) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000331 | [Must every sufficiently large finite integer set contain two elements with relatively small greatest common divisor?](catalog-0301-0400.md#JSP-000331) | Solved | No | No | Unavailable | Unavailable |
| JSP-000332 | [How high a power of a prescribed prime can divide a sum of distinct factorials?](catalog-0301-0400.md#JSP-000332) | Open | No | No | Unavailable | Unavailable |
| JSP-000333 | [Are there only finitely many powers of two whose ternary expansions contain no digit two?](catalog-0301-0400.md#JSP-000333) | Open | No | No | Unavailable | Unavailable |
| JSP-000334 | [How many representations can an integer have as a sum of powers of two, powers of three, and their products?](catalog-0301-0400.md#JSP-000334) | Solved | No | No | Unavailable | Unavailable |
| JSP-000335 | [What is the distribution of the number of totient iterations needed to reach one?](catalog-0301-0400.md#JSP-000335) | Open | No | No | Unavailable | Unavailable |
| JSP-000336 | [When does iterating the map sending an integer to its totient plus one reach a prime, and what is its long-term behavior?](catalog-0301-0400.md#JSP-000336) | Open | No | No | Unavailable | Unavailable |
| JSP-000337 | [How fast do iterates of the sum-of-divisors function grow?](catalog-0301-0400.md#JSP-000337) | Open | No | No | Unavailable | Unavailable |
| JSP-000338 | [When does iteration of the map sending an integer to itself plus its totient eventually follow a doubling pattern?](catalog-0301-0400.md#JSP-000338) | Open | No | No | Unavailable | Unavailable |
| JSP-000339 | [Do sum-of-divisors iteration trajectories from different starting integers eventually meet?](catalog-0301-0400.md#JSP-000339) | Open | No | No | Unavailable | Unavailable |
| JSP-000340 | [Are there infinitely many bounds such that every smaller integer plus its number of distinct prime factors stays below the bound? Does this remain true with any fixed positive multiplier on the prime-factor count?](catalog-0301-0400.md#JSP-000340) | Open | No | No | Unavailable | Unavailable |
| JSP-000341 | [Do trajectories obtained by repeatedly adding an integer's divisor count eventually meet when started at different integers?](catalog-0301-0400.md#JSP-000341) | Open | No | No | Unavailable | Unavailable |
| JSP-000342 | [Which orderings of totient values at consecutive integers occur, and with what frequencies?](catalog-0301-0400.md#JSP-000342) | Open | No | No | Unavailable | Unavailable |
| JSP-000343 | [What is the precise asymptotic number of distinct totient values in a prescribed range?](catalog-0301-0400.md#JSP-000343) | Open | No | No | Unavailable | Unavailable |
| JSP-000344 | [How much does the number of distinct totient values differ when bounding the input versus bounding the output by the same limit?](catalog-0301-0400.md#JSP-000344) | Open | No | No | Unavailable | Unavailable |
| JSP-000345 | [What is the distribution of the ratio of divisor counts of factorials with nearby indices?](catalog-0301-0400.md#JSP-000345) | Open | No | No | Unavailable | Unavailable |
| JSP-000346 | [Is there an increasing integer sequence of density one whose products over distinct consecutive blocks are always different?](catalog-0301-0400.md#JSP-000346) | Solved | No | No | Unavailable | Unavailable |
| JSP-000347 | [Which positive integers are omitted by the specified self-referential recurrence?](catalog-0301-0400.md#JSP-000347) | Open | No | No | Unavailable | Unavailable |
| JSP-000348 | [Determine the long-term growth of the integer sequence generated greedily by the prescribed consecutive-sum rule.](catalog-0301-0400.md#JSP-000348) | Open | No | No | Unavailable | Unavailable |
| JSP-000349 | [How dense is the integer set generated by repeatedly adjoining products of two existing elements minus one?](catalog-0301-0400.md#JSP-000349) | Open | No | No | Unavailable | Unavailable |
| JSP-000350 | [How large can a subset of an integer interval be if the specified distinct element combinations always have different products?](catalog-0301-0400.md#JSP-000350) | Open | No | No | Unavailable | Unavailable |
| JSP-000351 | [Can a relatively dense integer set have prime differences with each of infinitely many other integers?](catalog-0301-0400.md#JSP-000351) | Open | No | No | Unavailable | Unavailable |
| JSP-000352 | [Must the decreasing sequence generated by the specified prime-factor rule contain a composite number?](catalog-0301-0400.md#JSP-000352) | Open | No | No | Unavailable | Unavailable |
| JSP-000353 | [inverse Goldbach problem](catalog-0301-0400.md#JSP-000353) | Open | No | No | Unavailable | Unavailable |
| JSP-000354 | [How dense can the sumset of two infinite integer sets be if all its distinct elements are pairwise coprime?](catalog-0301-0400.md#JSP-000354) | Open | No | No | Unavailable | Unavailable |
| JSP-000355 | [How small can the starting point of a run of consecutive prescribed power residues modulo a prime be?](catalog-0301-0400.md#JSP-000355) | Open | No | No | Unavailable | Unavailable |
| JSP-000356 | [How many initial products of an increasing integer sequence can be squares?](catalog-0301-0400.md#JSP-000356) | Solved | No | No | Unavailable | Unavailable |
| JSP-000357 | [How large can a subset of an integer interval be if no two elements sum to a square?](catalog-0301-0400.md#JSP-000357) | Solved | No | No | Unavailable | Unavailable |
| JSP-000358 | [Must every finite coloring of the positive integers contain two same-colored integers whose sum is a perfect power?](catalog-0301-0400.md#JSP-000358) | Solved | No | No | Unavailable | Unavailable |
| JSP-000359 | [How often can consecutive terms of the specified integer sequence have a small least common multiple?](catalog-0301-0400.md#JSP-000359) | Solved | No | No | Unavailable | Unavailable |
| JSP-000360 | [How large can an integer set be if every pairwise least common multiple is bounded by a prescribed value?](catalog-0301-0400.md#JSP-000360) | Solved | No | No | Unavailable | Unavailable |
| JSP-000361 | [For a fixed infinite integer set, how many divisors of a single integer can belong to that set?](catalog-0301-0400.md#JSP-000361) | Solved | No | No | Unavailable | Unavailable |
| JSP-000362 | [Must a sufficiently short integer interval contain two numbers whose product is one modulo a prime?](catalog-0301-0400.md#JSP-000362) | Open | No | No | Unavailable | Unavailable |
| JSP-000363 | [What proportion of integers have a divisor in the specified interval with endpoint ratio two?](catalog-0301-0400.md#JSP-000363) | Solved | No | No | Unavailable | Unavailable |
| JSP-000364 | [What proportion of an integer's divisors can be paired with divisors of comparable size?](catalog-0301-0400.md#JSP-000364) | Solved | No | No | Unavailable | Unavailable |
| JSP-000365 | [How many integers in a short interval have a divisor in a prescribed size range?](catalog-0301-0400.md#JSP-000365) | Open | No | No | Unavailable | Unavailable |
| JSP-000366 | [How large must the starting point be for a consecutive-integer product to have no prime factor in a prescribed interval?](catalog-0301-0400.md#JSP-000366) | Open | No | No | Unavailable | Unavailable |
| JSP-000367 | [Are there long runs of consecutive integers each having more distinct prime factors than the usual average?](catalog-0301-0400.md#JSP-000367) | Open | No | No | Unavailable | Unavailable |
| JSP-000368 | [Determine the difference between the sum of symmetrically placed primes in the prime sequence and twice the middle prime.](catalog-0301-0400.md#JSP-000368) | Open | No | No | Unavailable | Unavailable |
| JSP-000369 | [How fast must an increasing prime sequence with nondecreasing gaps grow?](catalog-0301-0400.md#JSP-000369) | Open | No | No | Unavailable | Unavailable |
| JSP-000370 | [How large can the smallest integer whose totient is divisible by a prescribed positive integer be?](catalog-0301-0400.md#JSP-000370) | Open | No | No | Unavailable | Unavailable |
| JSP-000371 | [Can the product of a short run of consecutive integers contain every small prime in a prescribed range?](catalog-0301-0400.md#JSP-000371) | Solved | Yes | Yes | Unclaimed | Claimed |
| JSP-000372 | [Is the least common multiple up to one less than the next prime always smaller than a given prime times the least common multiple up to that prime?](catalog-0301-0400.md#JSP-000372) | Open | No | No | Unavailable | Unavailable |
| JSP-000373 | [ambiguous statement](catalog-0301-0400.md#JSP-000373) | Open | No | No | Unavailable | Unavailable |
| JSP-000374 | [How many distinct small-prime parts can occur among integers in a short interval?](catalog-0301-0400.md#JSP-000374) | Open | No | No | Unavailable | Unavailable |
| JSP-000375 | [The sum over composites of least prime factor divided by the integer has known global asymptotics. Is there a uniform positive lower bound on the prescribed short intervals?](catalog-0301-0400.md#JSP-000375) | Open | No | No | Unavailable | Unavailable |
| JSP-000376 | [How close to a given integer can one find a composite number whose least prime factor satisfies the prescribed size conditions?](catalog-0301-0400.md#JSP-000376) | Open | No | No | Unavailable | Unavailable |
| JSP-000377 | [Can the size of a planar point set whose distances all stay away from integers be bounded in terms of the specified parameters?](catalog-0301-0400.md#JSP-000377) | Solved | No | No | Unavailable | Unavailable |
| JSP-000378 | [Can arbitrarily large planar point sets have all pairwise distances uniformly bounded away from the nearest integer?](catalog-0301-0400.md#JSP-000378) | Solved | No | No | Unavailable | Unavailable |
| JSP-000379 | [ambiguous statement](catalog-0301-0400.md#JSP-000379) | Open | No | No | Unavailable | Unavailable |
| JSP-000380 | [Successively sum the divisors greater than one of an integer. Which sums have not appeared before, and how small can the original integer representing a target be?](catalog-0301-0400.md#JSP-000380) | Open | No | No | Unavailable | Unavailable |
| JSP-000381 | [A primitive semiperfect number is a sum of some of its proper divisors, with no smaller divisor having that property. Does the reciprocal sum of these numbers converge?](catalog-0301-0400.md#JSP-000381) | Solved | Yes | Yes | Unclaimed | Claimed |
| JSP-000382 | [Are there odd weird numbers, whose proper divisors sum to more than the number but no subset sums to it? Are infinitely many weird numbers primitive?](catalog-0301-0400.md#JSP-000382) | Open | No | No | Unavailable | Unavailable |
| JSP-000383 | [Starting from a set of primes, can repeatedly adjoining prime sums of three distinct existing primes generate infinitely many primes?](catalog-0301-0400.md#JSP-000383) | Solved | No | No | Unavailable | Unavailable |
| JSP-000384 | [Can the greedy process seeking a new prime equal to the current prime plus an earlier prime minus one continue forever?](catalog-0301-0400.md#JSP-000384) | Open | No | No | Unavailable | Unavailable |
| JSP-000385 | [Can all natural numbers be permuted so that every adjacent pair has prime sum?](catalog-0301-0400.md#JSP-000385) | Solved | No | No | Unavailable | Unavailable |
| JSP-000386 | [Can pairs of real numbers be colored so that every uncountable subset realizes all prescribed colors?](catalog-0301-0400.md#JSP-000386) | Open | No | No | Unavailable | Unavailable |
| JSP-000387 | [Can the nonzero elements of a finite field be ordered so that all initial partial sums are distinct?](catalog-0301-0400.md#JSP-000387) | Open | No | No | Unavailable | Unavailable |
| JSP-000388 | [Can the integer value set of a polynomial have an additive complement giving each integer exactly one representation?](catalog-0301-0400.md#JSP-000388) | Solved | No | No | Unavailable | Unavailable |
| JSP-000389 | [How many distinct factorial residues occur modulo a prime?](catalog-0301-0400.md#JSP-000389) | Open | No | No | Unavailable | Unavailable |
| JSP-000390 | [For a prescribed remainder, are there infinitely many positive integers whose corresponding powers of two have that remainder upon division by the integer?](catalog-0301-0400.md#JSP-000390) | Open | No | No | Unavailable | Unavailable |
| JSP-000391 | [Can the specified floor recurrence generate the digits of an algebraic number in a prescribed base?](catalog-0301-0400.md#JSP-000391) | Solved | No | No | Unavailable | Unavailable |
| JSP-000392 | [How long an integer interval forces monochromatic integers satisfying the specified additive equation under every coloring with a given number of colors?](catalog-0301-0400.md#JSP-000392) | Open | No | No | Unavailable | Unavailable |
| JSP-000393 | [What bounds relate the number of nonzero terms of a polynomial to that of its square?](catalog-0301-0400.md#JSP-000393) | Solved | No | No | Unavailable | Unavailable |
| JSP-000394 | [Must the integers remaining after removal of the specified residue classes have logarithmic density?](catalog-0301-0400.md#JSP-000394) | Open | No | No | Unavailable | Unavailable |
| JSP-000395 | [How do the densities of multiples of a given finite integer set compare across different intervals?](catalog-0301-0400.md#JSP-000395) | Open | No | No | Unavailable | Unavailable |
| JSP-000396 | [After excluding all multiples of a sparse integer set, what is the mean squared gap between consecutive remaining integers?](catalog-0301-0400.md#JSP-000396) | Open | No | No | Unavailable | Unavailable |
| JSP-000397 | [If an additive arithmetic function has uniformly bounded differences at consecutive integers, must it be close to a logarithmic function?](catalog-0301-0400.md#JSP-000397) | Solved | No | No | Unavailable | Unavailable |
| JSP-000398 | [If consecutive ratios of an increasing integer sequence tend to one, are the relative positions of scaled integers within its gaps uniformly distributed for almost every real scale factor?](catalog-0301-0400.md#JSP-000398) | Solved | No | No | Unavailable | Unavailable |
| JSP-000399 | [Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number of distinct elements?](catalog-0301-0400.md#JSP-000399) | Solved | No | No | Unavailable | Unavailable |
| JSP-000400 | [Can a sum of two integer squares approximate an irrational multiple of an integer square sufficiently closely?](catalog-0301-0400.md#JSP-000400) | Solved | No | No | Unavailable | Unavailable |

### Problems 401–500

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000401 | [How many edges can a three-uniform hypergraph have while excluding the complete three-uniform hypergraph on four vertices?](catalog-0401-0500.md#JSP-000401) | Open | No | No | Unavailable | Unavailable |
| JSP-000402 | [Under the specified measure restrictions on a set mapping, must there be a sufficiently large set whose elements avoid one another's images?](catalog-0401-0500.md#JSP-000402) | Solved | No | No | Unavailable | Unavailable |
| JSP-000403 | [How large can a point set in higher dimensions be if every three points form an isosceles triangle?](catalog-0401-0500.md#JSP-000403) | Open | No | No | Unavailable | Unavailable |
| JSP-000404 | [Blumenthal's problem](catalog-0401-0500.md#JSP-000404) | Solved | No | No | Unavailable | Unavailable |
| JSP-000405 | [How many distinct circles must a planar point set determine if its points are not all concyclic?](catalog-0401-0500.md#JSP-000405) | Open | No | No | Unavailable | Unavailable |
| JSP-000406 | [Heilbronn's triangle problem](catalog-0401-0500.md#JSP-000406) | Open | No | No | Unavailable | Unavailable |
| JSP-000407 | [What is the minimum number of colors needed to color the plane so that points at distance one have different colors?](catalog-0401-0500.md#JSP-000407) | Open | No | No | Unavailable | Unavailable |
| JSP-000408 | [How small can the total radii of disks covering the set where a polynomial has modulus at most one be?](catalog-0401-0500.md#JSP-000408) | Open | No | No | Unavailable | Unavailable |
| JSP-000409 | [Chowla's cosine problem](catalog-0401-0500.md#JSP-000409) | Open | No | No | Unavailable | Unavailable |
| JSP-000410 | [How many components of the region where a polynomial has modulus at most one can exceed a prescribed diameter?](catalog-0401-0500.md#JSP-000410) | Solved | No | No | Unavailable | Unavailable |
| JSP-000411 | [What is the optimal guaranteed liminf of the ratio of the largest series term of a transcendental entire function to its maximum modulus on a circle?](catalog-0401-0500.md#JSP-000411) | Open | No | No | Unavailable | Unavailable |
| JSP-000412 | [Does every transcendental entire function have a path to infinity along which its modulus grows faster than every polynomial?](catalog-0401-0500.md#JSP-000412) | Open | No | No | Unavailable | Unavailable |
| JSP-000413 | [Does a transcendental entire function have a path to infinity on which a specified negative power of its modulus is integrable?](catalog-0401-0500.md#JSP-000413) | Solved | No | No | Unavailable | Unavailable |
| JSP-000414 | [Must an entire function with sufficiently sparse nonzero power-series terms attain every complex value infinitely often?](catalog-0401-0500.md#JSP-000414) | Open | No | No | Unavailable | Unavailable |
| JSP-000415 | [Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?](catalog-0401-0500.md#JSP-000415) | Solved | No | No | Unavailable | Unavailable |
| JSP-000416 | [Do partial sums of a random multiplicative function satisfy the predicted law of the iterated logarithm and fluctuation scale?](catalog-0401-0500.md#JSP-000416) | Open | No | No | Unavailable | Unavailable |
| JSP-000417 | [Does the number of real roots of a polynomial with independent random sign coefficients almost surely follow the specified asymptotic law?](catalog-0401-0500.md#JSP-000417) | Open | No | No | Unavailable | Unavailable |
| JSP-000418 | [How many roots of a polynomial with random sign coefficients lie inside the unit circle?](catalog-0401-0500.md#JSP-000418) | Open | No | No | Unavailable | Unavailable |
| JSP-000419 | [What is the typical maximum modulus on the unit circle of a polynomial with random sign coefficients?](catalog-0401-0500.md#JSP-000419) | Solved | No | No | Unavailable | Unavailable |
| JSP-000420 | [What is the typical maximum on the specified real interval of a polynomial with random sign coefficients?](catalog-0401-0500.md#JSP-000420) | Open | No | No | Unavailable | Unavailable |
| JSP-000421 | [How small is the typical minimum modulus on the unit circle of a polynomial with random sign coefficients?](catalog-0401-0500.md#JSP-000421) | Solved | No | No | Unavailable | Unavailable |
| JSP-000422 | [What conditions on arc lengths make randomly placed arcs cover the entire circle almost surely?](catalog-0401-0500.md#JSP-000422) | Solved | No | No | Unavailable | Unavailable |
| JSP-000423 | [Does a power series with randomly signed coefficients converge at some point of the unit circle?](catalog-0401-0500.md#JSP-000423) | Solved | No | No | Unavailable | Unavailable |
| JSP-000424 | [What exponential growth constant governs the number of self-avoiding lattice walks of a given length?](catalog-0401-0500.md#JSP-000424) | Open | No | No | Unavailable | Unavailable |
| JSP-000425 | [How fast does the mean endpoint distance of a random self-avoiding lattice walk grow with its length?](catalog-0401-0500.md#JSP-000425) | Open | No | No | Unavailable | Unavailable |
| JSP-000426 | [How large a subset with distinct pairwise sums must every finite real set contain?](catalog-0401-0500.md#JSP-000426) | Open | No | No | Unavailable | Unavailable |
| JSP-000427 | [How long an integer interval forces, under every two-coloring, a prescribed-size set whose nonempty subset sums are all the same color?](catalog-0401-0500.md#JSP-000427) | Open | No | No | Unavailable | Unavailable |
| JSP-000428 | [How large can a pairwise noncoprime subset of an integer interval containing a specified integer be?](catalog-0401-0500.md#JSP-000428) | Solved | No | No | Unavailable | Unavailable |
| JSP-000429 | [How large can an integer set be if it contains no prescribed-size subset with all pairwise greatest common divisors equal?](catalog-0401-0500.md#JSP-000429) | Open | No | No | Unavailable | Unavailable |
| JSP-000430 | [How large can an integer set be if it contains no three elements with equal pairwise least common multiples?](catalog-0401-0500.md#JSP-000430) | Open | No | No | Unavailable | Unavailable |
| JSP-000431 | [How large can an integer set's reciprocal sum be if the number of representations of any integer as a prime times a set element is restricted?](catalog-0401-0500.md#JSP-000431) | Open | No | No | Unavailable | Unavailable |
| JSP-000432 | [How many distinct quotients of one set element by its greatest common divisor with another must occur?](catalog-0401-0500.md#JSP-000432) | Open | No | No | Unavailable | Unavailable |
| JSP-000433 | [How large can the reciprocal sum of integers in an interval be if every pairwise least common multiple exceeds the interval's upper endpoint?](catalog-0401-0500.md#JSP-000433) | Solved | No | No | Unavailable | Unavailable |
| JSP-000434 | [How many random elements of a finite abelian group make their subset sums cover the group with probability at least one half? Does the binary logarithm of the group order plus a small correction suffice?](catalog-0401-0500.md#JSP-000434) | Solved | No | No | Unavailable | Unavailable |
| JSP-000435 | [How much must the triangle-versus-clique Ramsey number increase when the clique gains one vertex?](catalog-0401-0500.md#JSP-000435) | Open | No | No | Unavailable | Unavailable |
| JSP-000436 | [Which graph with a prescribed number of edges has the largest Ramsey number?](catalog-0401-0500.md#JSP-000436) | Open | No | No | Unavailable | Unavailable |
| JSP-000437 | [Can every graph's Ramsey number be bounded exponentially in the square root of its edge count?](catalog-0401-0500.md#JSP-000437) | Solved | No | No | Unavailable | Unavailable |
| JSP-000438 | [What is the optimal upper bound for the two-color Ramsey number of an arbitrary tree?](catalog-0401-0500.md#JSP-000438) | Open | No | No | Unavailable | Unavailable |
| JSP-000439 | [Does sufficiently large average degree force a graph to contain every tree of a prescribed order?](catalog-0401-0500.md#JSP-000439) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000440 | [What is the two-color Ramsey number of a tree whose bipartition sizes have ratio one to two?](catalog-0401-0500.md#JSP-000440) | Solved | No | No | Unavailable | Unavailable |
| JSP-000441 | [What is the Ramsey number of a prescribed tree versus a complete multipartite graph?](catalog-0401-0500.md#JSP-000441) | Open | No | No | Unavailable | Unavailable |
| JSP-000442 | [What is the exact Ramsey number of a prescribed cycle versus a clique?](catalog-0401-0500.md#JSP-000442) | Open | No | No | Unavailable | Unavailable |
| JSP-000443 | [What is the Ramsey number of a four-cycle versus a prescribed star?](catalog-0401-0500.md#JSP-000443) | Open | No | No | Unavailable | Unavailable |
| JSP-000444 | [How fast does the three-color Ramsey number grow for a triangle in either of the first two colors versus a large clique in the third?](catalog-0401-0500.md#JSP-000444) | Solved | No | No | Unavailable | Unavailable |
| JSP-000445 | [Compare the multicolor thresholds forcing a monochromatic odd cycle and a monochromatic triangle.](catalog-0401-0500.md#JSP-000445) | Open | No | No | Unavailable | Unavailable |
| JSP-000446 | [What is the multicolor Ramsey number of an even cycle of prescribed length?](catalog-0401-0500.md#JSP-000446) | Open | No | No | Unavailable | Unavailable |
| JSP-000447 | [What is the optimal upper bound for the three-color Ramsey number of a prescribed cycle?](catalog-0401-0500.md#JSP-000447) | Open | No | No | Unavailable | Unavailable |
| JSP-000448 | [Does the multicolor Ramsey number of a tree grow linearly with its order?](catalog-0401-0500.md#JSP-000448) | Solved | No — reported; standalone source not located | Pending verification | Unavailable | Unavailable |
| JSP-000449 | [What is the multicolor Ramsey number of a prescribed complete bipartite graph?](catalog-0401-0500.md#JSP-000449) | Open | No | No | Unavailable | Unavailable |
| JSP-000450 | [Do graphs of bounded maximum degree have two-color size Ramsey numbers linear in their order?](catalog-0401-0500.md#JSP-000450) | Solved | No | No | Unavailable | Unavailable |
| JSP-000451 | [What is the minimum host edge count forcing a monochromatic prescribed balanced complete bipartite graph under every two-coloring?](catalog-0401-0500.md#JSP-000451) | Open | No | No | Unavailable | Unavailable |
| JSP-000452 | [What is the minimum host edge count forcing the corresponding monochromatic copy of one of two prescribed star forests?](catalog-0401-0500.md#JSP-000452) | Open | No | No | Unavailable | Unavailable |
| JSP-000453 | [How many levels in an exponential tower are needed to describe the growth of uniform-hypergraph Ramsey numbers?](catalog-0401-0500.md#JSP-000453) | Open | No | No | Unavailable | Unavailable |
| JSP-000454 | [Do two-color Ramsey numbers of three-uniform hypergraphs satisfy the predicted double-exponential lower bound?](catalog-0401-0500.md#JSP-000454) | Open | No | No | Unavailable | Unavailable |
| JSP-000455 | [Is the two-color induced Ramsey number at most exponential in the order of the target graph?](catalog-0401-0500.md#JSP-000455) | Solved | No | No | Unavailable | Unavailable |
| JSP-000456 | [Under the specified local edge restrictions on one graph, is its Ramsey number against another graph linear in the latter's edge count?](catalog-0401-0500.md#JSP-000456) | Open | No | No | Unavailable | Unavailable |
| JSP-000457 | [For specified graphs such as the cube, is the Ramsey number against an arbitrary graph bounded by a fixed multiple of the latter's edge count?](catalog-0401-0500.md#JSP-000457) | Open | No | No | Unavailable | Unavailable |
| JSP-000458 | [Can Ramsey bounds against trees and cliques yield a bound linear in edge count against general graphs?](catalog-0401-0500.md#JSP-000458) | Open | No | No | Unavailable | Unavailable |
| JSP-000459 | [What is the optimal linear coefficient for the Ramsey number of a fixed odd cycle against an arbitrary graph, measured by the latter's edge count?](catalog-0401-0500.md#JSP-000459) | Open | No | No | Unavailable | Unavailable |
| JSP-000460 | [Is the Ramsey number of the prescribed cycle against any graph at most twice the latter's edge count plus the allowed correction?](catalog-0401-0500.md#JSP-000460) | Solved | No | No | Unavailable | Unavailable |
| JSP-000461 | [Which rational numbers occur as extremal exponents of bipartite graphs?](catalog-0401-0500.md#JSP-000461) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000462 | [How many edges can a graph excluding a prescribed even cycle have? Seek constructions attaining the predicted order of growth.](catalog-0401-0500.md#JSP-000462) | Open | No | No | Unavailable | Unavailable |
| JSP-000463 | [What is the maximum edge count of a graph containing neither triangles nor four-cycles?](catalog-0401-0500.md#JSP-000463) | Open | No | No | Unavailable | Unavailable |
| JSP-000464 | [How many edges can a graph have while excluding an odd cycle and an even cycle of adjacent lengths?](catalog-0401-0500.md#JSP-000464) | Solved | No | No | Unavailable | Unavailable |
| JSP-000465 | [For a forbidden family containing a bipartite graph, can the asymptotic extremal problem be reduced to forbidding a single graph?](catalog-0401-0500.md#JSP-000465) | Solved | No | No | Unavailable | Unavailable |
| JSP-000466 | [How many edges can a graph have while excluding a hypercube of prescribed dimension?](catalog-0401-0500.md#JSP-000466) | Open | No | No | Unavailable | Unavailable |
| JSP-000467 | [What minimum degree forces a spanning collection of vertex-disjoint four-cycles?](catalog-0401-0500.md#JSP-000467) | Solved | No | No | Unavailable | Unavailable |
| JSP-000468 | [Under suitable parameters, does a random graph contain a spanning hypercube with probability tending to one?](catalog-0401-0500.md#JSP-000468) | Solved | No | No | Unavailable | Unavailable |
| JSP-000469 | [Must a dense graph excluding a prescribed complete tripartite graph contain a sufficiently large independent set?](catalog-0401-0500.md#JSP-000469) | Open | No | No | Unavailable | Unavailable |
| JSP-000470 | [If at least half the vertices have sufficiently large degree, must a graph contain every tree of a prescribed order?](catalog-0401-0500.md#JSP-000470) | Open | No | No | Unavailable | Unavailable |
| JSP-000471 | [How many edges can always be retained in a bipartite subgraph of a triangle-free graph?](catalog-0401-0500.md#JSP-000471) | Solved | No | No | Unavailable | Unavailable |
| JSP-000472 | [Can the edges of every connected graph be decomposed into at most about half its number of vertices many paths?](catalog-0401-0500.md#JSP-000472) | Open | No | No | Unavailable | Unavailable |
| JSP-000473 | [Must a dense graph contain a large subgraph in which every two edges lie on a common short cycle?](catalog-0401-0500.md#JSP-000473) | Open | No | No | Unavailable | Unavailable |
| JSP-000474 | [How many edges can a graph have if no two edge-disjoint cycles have the same vertex set?](catalog-0401-0500.md#JSP-000474) | Open | No | No | Unavailable | Unavailable |
| JSP-000475 | [Can finitely many residue classes cover all integers with no modulus dividing another?](catalog-0401-0500.md#JSP-000475) | Solved | No | No | Unavailable | Unavailable |
| JSP-000476 | [How large can a subset of an integer interval be if none of its nonempty subset sums is a square?](catalog-0401-0500.md#JSP-000476) | Solved | No | No | Unavailable | Unavailable |
| JSP-000477 | [How many rich lines can a planar point set determine when the number of points on each line is bounded?](catalog-0401-0500.md#JSP-000477) | Open | No | No | Unavailable | Unavailable |
| JSP-000478 | [How large a subset with no three collinear points must every planar set with no four collinear points contain?](catalog-0401-0500.md#JSP-000478) | Open | No | No | Unavailable | Unavailable |
| JSP-000479 | [Does every red-blue coloring of pairs from the prescribed countable ordinal contain a red clique of the same order type or a blue triangle?](catalog-0401-0500.md#JSP-000479) | Solved | No | No | Unavailable | Unavailable |
| JSP-000480 | [Which ordinal powers have the partition property forcing a clique of the same order type in one color or a triangle in the other?](catalog-0401-0500.md#JSP-000480) | Open | No | No | Unavailable | Unavailable |
| JSP-000481 | [Which finite hypergraphs must occur in every three-uniform hypergraph of uncountable chromatic number?](catalog-0401-0500.md#JSP-000481) | Open | No | No | Unavailable | Unavailable |
| JSP-000482 | [Is there an infinite graph with no four-vertex clique that cannot be partitioned into countably many triangle-free parts?](catalog-0401-0500.md#JSP-000482) | Open | No | No | Unavailable | Unavailable |
| JSP-000483 | [Where does the specified Ramsey property differ between finitely many and countably infinitely many colors?](catalog-0401-0500.md#JSP-000483) | Open | No | No | Unavailable | Unavailable |
| JSP-000484 | [Which order-isomorphic structures are forced in two-color partitions of uncountable ordinals after excluding the specified cliques?](catalog-0401-0500.md#JSP-000484) | Open | No | No | Unavailable | Unavailable |
| JSP-000485 | [Can countable subsets be colored so that the countable subsets of every sufficiently large set realize all colors?](catalog-0401-0500.md#JSP-000485) | Open | No | No | Unavailable | Unavailable |
| JSP-000486 | [Disjoint paths and separating sets in infinite graphs](catalog-0401-0500.md#JSP-000486) | Solved | No | No | Unavailable | Unavailable |
| JSP-000487 | [How does the edge threshold forcing many triangles sharing one edge depend on the parameters?](catalog-0401-0500.md#JSP-000487) | Open | No | No | Unavailable | Unavailable |
| JSP-000488 | [For which ordinals does every graph on the ordinal have an infinite path or an independent set of the full order type?](catalog-0401-0500.md#JSP-000488) | Open | No | No | Unavailable | Unavailable |
| JSP-000489 | [Property B](catalog-0401-0500.md#JSP-000489) | Open | No | No | Unavailable | Unavailable |
| JSP-000490 | [How many colors suffice to avoid monochromatic members of a family of countably infinite sets whose pairwise intersections never have size two?](catalog-0401-0500.md#JSP-000490) | Solved | No | No | Unavailable | Unavailable |
| JSP-000491 | [pinned distance problem](catalog-0401-0500.md#JSP-000491) | Open | No | No | Unavailable | Unavailable |
| JSP-000492 | [Can the number of pairs at one distance in a finite spherical point set grow superlinearly?](catalog-0401-0500.md#JSP-000492) | Solved | No | No | Unavailable | Unavailable |
| JSP-000493 | [Which total numbers of determined lines are possible for a planar set of a prescribed number of points?](catalog-0401-0500.md#JSP-000493) | Solved | No | No | Unavailable | Unavailable |
| JSP-000494 | [How many different sets of line multiplicities can planar point configurations determine?](catalog-0401-0500.md#JSP-000494) | Solved | No | No | Unavailable | Unavailable |
| JSP-000495 | [How long can the shortest guaranteed monochromatic odd cycle be in a multicolored complete graph?](catalog-0401-0500.md#JSP-000495) | Open | No | No | Unavailable | Unavailable |
| JSP-000496 | [If every maximal clique is large, how many vertices suffice to meet them all?](catalog-0401-0500.md#JSP-000496) | Open | No | No | Unavailable | Unavailable |
| JSP-000497 | [Can minimum degree bound the diameter of a graph excluding a clique of prescribed size?](catalog-0401-0500.md#JSP-000497) | Open | No | No | Unavailable | Unavailable |
| JSP-000498 | [How many edges are needed to make every local subgraph of prescribed size satisfy the specified maximum-degree condition?](catalog-0401-0500.md#JSP-000498) | Open | No | No | Unavailable | Unavailable |
| JSP-000499 | [If every prescribed-size local edge family in a uniform hypergraph has a common vertex, how many vertices suffice to cover all edges?](catalog-0401-0500.md#JSP-000499) | Open | No | No | Unavailable | Unavailable |
| JSP-000500 | [Must a multicolored complete graph contain a vertex subset of the required size missing at least one color?](catalog-0401-0500.md#JSP-000500) | Open | No | No | Unavailable | Unavailable |

### Problems 501–600

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000501 | [How many edges must be added to a triangle-free graph to reduce its diameter to at most four while keeping it triangle-free?](catalog-0501-0600.md#JSP-000501) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000502 | [Large triangle-free induced subgraphs in K4-free graphs](catalog-0501-0600.md#JSP-000502) | Open | No | No | Unavailable | Unavailable |
| JSP-000503 | [How many vertex subsets of a high-degree regular graph are exactly the vertex sets of cycles?](catalog-0501-0600.md#JSP-000503) | Solved | No | No | Unavailable | Unavailable |
| JSP-000504 | [Must the specified set mapping on a set of singular cardinality have an infinite free set?](catalog-0501-0600.md#JSP-000504) | Open | No | No | Unavailable | Unavailable |
| JSP-000505 | [How small a starting subset suffices to cover the whole set by applying the given mapping to it and its small subsets?](catalog-0501-0600.md#JSP-000505) | Open | No | No | Unavailable | Unavailable |
| JSP-000506 | [In a random graph, how much smaller than the chromatic number is the minimum number of parts in a partition into cliques and independent sets?](catalog-0501-0600.md#JSP-000506) | Solved | No | No | Unavailable | Unavailable |
| JSP-000507 | [What is the largest girth of a graph with prescribed order and chromatic number, including its asymptotic constant?](catalog-0501-0600.md#JSP-000507) | Open | No | No | Unavailable | Unavailable |
| JSP-000508 | [What is the largest asymptotic ratio of chromatic number to clique number at the prescribed graph size?](catalog-0501-0600.md#JSP-000508) | Open | No | No | Unavailable | Unavailable |
| JSP-000509 | [Partitioning graphs with prescribed chromatic bounds](catalog-0501-0600.md#JSP-000509) | Open | No | No | Unavailable | Unavailable |
| JSP-000510 | [How few vertices can a bipartite graph have if it is not colorable from lists of the prescribed size?](catalog-0501-0600.md#JSP-000510) | Open | No | No | Unavailable | Unavailable |
| JSP-000511 | [Is every planar bipartite graph colorable from arbitrary lists of three colors per vertex?](catalog-0501-0600.md#JSP-000511) | Solved | No | No | Unavailable | Unavailable |
| JSP-000512 | [What list size guarantees proper list coloring of every planar graph?](catalog-0501-0600.md#JSP-000512) | Solved | No | No | Unavailable | Unavailable |
| JSP-000513 | [Does list multicolorability persist when both the available-list size and the required number of colors per vertex are doubled?](catalog-0501-0600.md#JSP-000513) | Solved | No | No | Unavailable | Unavailable |
| JSP-000514 | [Which triangles can be dissected into congruent triangles only when their number is a square?](catalog-0501-0600.md#JSP-000514) | Solved | No | No | Unavailable | Unavailable |
| JSP-000515 | [For a given triangle, which numbers of congruent smaller triangles can tile it?](catalog-0501-0600.md#JSP-000515) | Open | No | No | Unavailable | Unavailable |
| JSP-000516 | [If sufficiently large pairwise differences in an integer set never divide the larger element, is its size at most half the containing interval plus a lower-order error?](catalog-0501-0600.md#JSP-000516) | Open | No | No | Unavailable | Unavailable |
| JSP-000517 | [If a graph has no clique or independent set larger than logarithmic size, must it have many induced subgraphs with distinct pairs of vertex and edge counts?](catalog-0501-0600.md#JSP-000517) | Solved | No | No | Unavailable | Unavailable |
| JSP-000518 | [If a graph has neither large cliques nor large independent sets, must a large induced subgraph have many distinct vertex degrees?](catalog-0501-0600.md#JSP-000518) | Solved | No | No | Unavailable | Unavailable |
| JSP-000519 | [Can the property of forcing a monochromatic triangle under every finite edge coloring be extended to infinite cardinal sizes?](catalog-0501-0600.md#JSP-000519) | Open | No | No | Unavailable | Unavailable |
| JSP-000520 | [Must a graph of high chromatic number contain an odd cycle whose vertex-induced subgraph also has high chromatic number?](catalog-0501-0600.md#JSP-000520) | Open | No | No | Unavailable | Unavailable |
| JSP-000521 | [Does sufficiently high chromatic number force several edge-disjoint cycles on the same vertex set?](catalog-0501-0600.md#JSP-000521) | Solved | No | No | Unavailable | Unavailable |
| JSP-000522 | [How many edges can a graph have if every cycle has fewer chords than vertices?](catalog-0501-0600.md#JSP-000522) | Open | No | No | Unavailable | Unavailable |
| JSP-000523 | [How many edges force a uniform hypergraph to contain two distinct pairs of disjoint edges with the same union?](catalog-0501-0600.md#JSP-000523) | Open | No | No | Unavailable | Unavailable |
| JSP-000524 | [If each prescribed local part of a set family has a two-point transversal, how many points suffice to meet the whole family?](catalog-0501-0600.md#JSP-000524) | Open | No | No | Unavailable | Unavailable |
| JSP-000525 | [Does adding each integer's divisor count produce the specified new lower barriers or uncrossable numerical thresholds?](catalog-0501-0600.md#JSP-000525) | Open | No | No | Unavailable | Unavailable |
| JSP-000526 | [For distinct given integers, how many distinct representatives divisible by their respective integers can be chosen in the specified interval?](catalog-0501-0600.md#JSP-000526) | Solved | Yes | Yes | Claimed | Claimed |
| JSP-000527 | [In higher-dimensional general position, is the number of points forcing a convex subset exponential in the target size?](catalog-0501-0600.md#JSP-000527) | Solved | No | No | Unavailable | Unavailable |
| JSP-000528 | [How many points of a planar set can each determine only a small number of distances to the other points?](catalog-0501-0600.md#JSP-000528) | Solved | No | No | Unavailable | Unavailable |
| JSP-000529 | [How many distinct values can the per-point counts of distinct distances have in a planar point set?](catalog-0501-0600.md#JSP-000529) | Open | No | No | Unavailable | Unavailable |
| JSP-000530 | [If no four planar points are concyclic, must some point determine sufficiently many distinct distances?](catalog-0501-0600.md#JSP-000530) | Open | No | No | Unavailable | Unavailable |
| JSP-000531 | [ambiguous statement](catalog-0501-0600.md#JSP-000531) | Open | No | No | Unavailable | Unavailable |
| JSP-000532 | [Must every positive-density integer set contain a translate of all pairwise sums from some infinite set?](catalog-0501-0600.md#JSP-000532) | Solved | No | No | Unavailable | Unavailable |
| JSP-000533 | [Must a planar point set with no isosceles triangle determine superlinearly many distinct distances?](catalog-0501-0600.md#JSP-000533) | Open | No | No | Unavailable | Unavailable |
| JSP-000534 | [If every four points determine at least three distances, how many distinct distances must the whole set determine?](catalog-0501-0600.md#JSP-000534) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000535 | [ambiguous statement](catalog-0501-0600.md#JSP-000535) | Open | No | No | Unavailable | Unavailable |
| JSP-000536 | [Can two equal-size planar sets determine between them asymptotically fewer distances than their size divided by the square root of its logarithm?](catalog-0501-0600.md#JSP-000536) | Open | No | No | Unavailable | Unavailable |
| JSP-000537 | [ambiguous statement](catalog-0501-0600.md#JSP-000537) | Open | No | No | Unavailable | Unavailable |
| JSP-000538 | [How large can the smallest prime not dividing a consecutive-integer product be?](catalog-0501-0600.md#JSP-000538) | Open | No | No | Unavailable | Unavailable |
| JSP-000539 | [Does a large set family with small pairwise intersections admit a transversal meeting each member in a uniformly bounded number of elements?](catalog-0501-0600.md#JSP-000539) | Solved | No | No | Unavailable | Unavailable |
| JSP-000540 | [Can pairwise balanced designs be constructed with prescribed pair multiplicity and block sizes close to the square root of the number of points?](catalog-0501-0600.md#JSP-000540) | Open | No | No | Unavailable | Unavailable |
| JSP-000541 | [As local edge lower bounds strengthen, does the growth exponent of the guaranteed clique size strictly increase?](catalog-0501-0600.md#JSP-000541) | Open | No | No | Unavailable | Unavailable |
| JSP-000542 | [Does the number of distinct planar configurations maximizing unit-distance pairs tend to infinity with the number of points?](catalog-0501-0600.md#JSP-000542) | Open | No | No | Unavailable | Unavailable |
| JSP-000543 | [orchard problems](catalog-0501-0600.md#JSP-000543) | Open | No | No | Unavailable | Unavailable |
| JSP-000544 | [How large a diameter is forced in higher dimensions when all pairwise distances are distinct and separated by a prescribed amount?](catalog-0501-0600.md#JSP-000544) | Open | No | No | Unavailable | Unavailable |
| JSP-000545 | [If interpolation amplification factors diverge at every point, can every continuous function still have a point of interpolation convergence?](catalog-0501-0600.md#JSP-000545) | Open | No | No | Unavailable | Unavailable |
| JSP-000546 | [Can a product of consecutive terms of an arithmetic progression with coprime initial term and common difference be a perfect power?](catalog-0501-0600.md#JSP-000546) | Open | No | No | Unavailable | Unavailable |
| JSP-000547 | [What is the typical growth of the sum of ratios of consecutive ordered divisors of an integer?](catalog-0501-0600.md#JSP-000547) | Solved | No | No | Unavailable | Unavailable |
| JSP-000548 | [Within special integer sets such as sums of two squares, must every occurring finite additive pattern recur after translation?](catalog-0501-0600.md#JSP-000548) | Open | No | No | Unavailable | Unavailable |
| JSP-000549 | [Is every sufficiently large integer a positive multiple of a prime square plus a nonnegative remainder smaller than that prime?](catalog-0501-0600.md#JSP-000549) | Open | No | No | Unavailable | Unavailable |
| JSP-000550 | [Must two disjoint equal-length intervals of consecutive integers have different least common multiples?](catalog-0501-0600.md#JSP-000550) | Open | No | No | Unavailable | Unavailable |
| JSP-000551 | [Is there an integer such that distinct-prime-factor counts at all preceding positions are uniformly controlled by distance from it?](catalog-0501-0600.md#JSP-000551) | Open | No | No | Unavailable | Unavailable |
| JSP-000552 | [Near every integer, is there another integer whose least prime factor exceeds the square of their distance?](catalog-0501-0600.md#JSP-000552) | Open | No | No | Unavailable | Unavailable |
| JSP-000553 | [Near every integer, is there a composite integer whose least prime factor exceeds the square of their distance?](catalog-0501-0600.md#JSP-000553) | Open | No | No | Unavailable | Unavailable |
| JSP-000554 | [Between consecutive primes, is there an integer whose least prime factor is at least their gap?](catalog-0501-0600.md#JSP-000554) | Solved | No | No | Unavailable | Unavailable |
| JSP-000555 | [Large prime factors of binomial coefficients and runs of smooth integers](catalog-0501-0600.md#JSP-000555) | Open | No | No | Unavailable | Unavailable |
| JSP-000556 | [When does the small-prime part of a binomial coefficient exceed the square of its upper parameter?](catalog-0501-0600.md#JSP-000556) | Open | No | No | Unavailable | Unavailable |
| JSP-000557 | [What asymptotic formulas describe the number of distinct prime factors of binomial coefficients as their parameters vary?](catalog-0501-0600.md#JSP-000557) | Open | No | No | Unavailable | Unavailable |
| JSP-000558 | [Can every integer at least two be a ratio of products of two disjoint equal-length positive-integer intervals, each of length at least two?](catalog-0501-0600.md#JSP-000558) | Open | No | No | Unavailable | Unavailable |
| JSP-000559 | [How long a consecutive-integer interval can be covered by choosing one residue class for each small prime?](catalog-0501-0600.md#JSP-000559) | Open | No | No | Unavailable | Unavailable |
| JSP-000560 | [Using only large prime moduli, how wide a prime range is needed to cover an initial integer interval?](catalog-0501-0600.md#JSP-000560) | Open | No | No | Unavailable | Unavailable |
| JSP-000561 | [Can one residue class per prescribed prime be chosen to cover each integer in a given interval at least twice?](catalog-0501-0600.md#JSP-000561) | Open | No | No | Unavailable | Unavailable |
| JSP-000562 | [Is the density distribution of the prime factor at a prescribed position among ordered distinct prime factors unimodal?](catalog-0501-0600.md#JSP-000562) | Solved | No | No | Unavailable | Unavailable |
| JSP-000563 | [What conditions on an integer set are equivalent to its multiples having density one?](catalog-0501-0600.md#JSP-000563) | Open | No | No | Unavailable | Unavailable |
| JSP-000564 | [How large are the maximum gaps among integers having a divisor in a prescribed size range?](catalog-0501-0600.md#JSP-000564) | Open | No | No | Unavailable | Unavailable |
| JSP-000565 | [How large can the ratio of the largest to smallest positive integer with a common totient value be?](catalog-0501-0600.md#JSP-000565) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000566 | [How fast can prime chains grow when each prime divides one less than the next?](catalog-0501-0600.md#JSP-000566) | Open | No | No | Unavailable | Unavailable |
| JSP-000567 | [How long an increasing chain of divisors can an integer have if each term is one modulo its predecessor?](catalog-0501-0600.md#JSP-000567) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000568 | [Does the density of integers having a divisor in a prescribed residue class exhibit a phase transition as parameters vary?](catalog-0501-0600.md#JSP-000568) | Solved | No | No | Unavailable | Unavailable |
| JSP-000569 | [Must two binomial coefficients in the same row have a sufficiently large common prime factor?](catalog-0501-0600.md#JSP-000569) | Open | No | No | Unavailable | Unavailable |
| JSP-000570 | [How small can the greatest common divisor of an integer and a binomial coefficient with that upper parameter be?](catalog-0501-0600.md#JSP-000570) | Open | No | No | Unavailable | Unavailable |
| JSP-000571 | [In a hereditary set family, is a largest pairwise-intersecting subfamily always obtainable by taking all members containing one fixed element?](catalog-0501-0600.md#JSP-000571) | Open | No | No | Unavailable | Unavailable |
| JSP-000572 | [Must every sufficiently large uniform set family contain two members intersecting in exactly one element?](catalog-0501-0600.md#JSP-000572) | Solved | No | No | Unavailable | Unavailable |
| JSP-000573 | [How large can a set family be if a prescribed pairwise intersection size is forbidden?](catalog-0501-0600.md#JSP-000573) | Solved | No | No | Unavailable | Unavailable |
| JSP-000574 | [How fast does the chromatic number of Euclidean space grow with dimension when unit-distance pairs must receive different colors?](catalog-0501-0600.md#JSP-000574) | Open | No | No | Unavailable | Unavailable |
| JSP-000575 | [Is every planar unit-distance graph of sufficiently large girth three-colorable?](catalog-0501-0600.md#JSP-000575) | Solved | No | No | Unavailable | Unavailable |
| JSP-000576 | [What uniform chromatic bound holds for planar graphs joining pairs whose distances lie in a prescribed finite set?](catalog-0501-0600.md#JSP-000576) | Open | No | No | Unavailable | Unavailable |
| JSP-000577 | [How few integers from the specified interval can have a product divisible by the product of a given integer set?](catalog-0501-0600.md#JSP-000577) | Open | No | No | Unavailable | Unavailable |
| JSP-000578 | [How short an interval can contain distinct multiples representing every element of an arbitrary finite integer set?](catalog-0501-0600.md#JSP-000578) | Open | No | No | Unavailable | Unavailable |
| JSP-000579 | [How short an interval beyond the first several positive integers can contain distinct multiples representing each of them?](catalog-0501-0600.md#JSP-000579) | Open | No | No | Unavailable | Unavailable |
| JSP-000580 | [From an arbitrary starting point, what is the worst-case interval length needed for distinct multiples of the first several positive integers?](catalog-0501-0600.md#JSP-000580) | Open | No | No | Unavailable | Unavailable |
| JSP-000581 | [What is the maximum edge density of a uniform hypergraph excluding a prescribed complete uniform hypergraph?](catalog-0501-0600.md#JSP-000581) | Open | No | No | Unavailable | Unavailable |
| JSP-000582 | [Does every fixed bipartite graph have an extremal function asymptotic to a constant times a rational power?](catalog-0501-0600.md#JSP-000582) | Open | No | No | Unavailable | Unavailable |
| JSP-000583 | [Can graphs excluding a prescribed balanced complete bipartite graph attain the predicted extremal lower bound?](catalog-0501-0600.md#JSP-000583) | Open | No | No | Unavailable | Unavailable |
| JSP-000584 | [Must every regular graph of the specified degree contain a three-regular subgraph?](catalog-0501-0600.md#JSP-000584) | Solved | No | No | Unavailable | Unavailable |
| JSP-000585 | [How does a graph's chromatic number relate to the order of its largest complete-graph subdivision?](catalog-0501-0600.md#JSP-000585) | Solved | No | No | Unavailable | Unavailable |
| JSP-000586 | [What average degree forces a subdivision of a complete graph of prescribed order?](catalog-0501-0600.md#JSP-000586) | Solved | No | No | Unavailable | Unavailable |
| JSP-000587 | [How many complete uniform hypergraphs suffice to partition the edges of an arbitrary uniform hypergraph?](catalog-0501-0600.md#JSP-000587) | Open | No | No | Unavailable | Unavailable |
| JSP-000588 | [How fast do the two-color size Ramsey numbers of prescribed paths and cycles grow?](catalog-0501-0600.md#JSP-000588) | Solved | No | No | Unavailable | Unavailable |
| JSP-000589 | [How long an interval forces a three-term arithmetic progression in one color or a prescribed longer progression in the other?](catalog-0501-0600.md#JSP-000589) | Solved | No | No | Unavailable | Unavailable |
| JSP-000590 | [For sufficiently large order satisfying the necessary divisibility conditions, do designs exist in which each prescribed-size point subset lies in exactly one fixed-size block?](catalog-0501-0600.md#JSP-000590) | Solved | No | No | Unavailable | Unavailable |
| JSP-000591 | [Must the order of every finite projective plane be a prime power?](catalog-0501-0600.md#JSP-000591) | Open | No | No | Unavailable | Unavailable |
| JSP-000592 | [How many mutually orthogonal Latin squares can always be constructed at a given order?](catalog-0501-0600.md#JSP-000592) | Open | No | No | Unavailable | Unavailable |
| JSP-000593 | [What is the asymptotic number of Latin rectangles with prescribed dimensions?](catalog-0501-0600.md#JSP-000593) | Open | No | No | Unavailable | Unavailable |
| JSP-000594 | [How large is the reciprocal sum of primes for which a given integer's residue lies in the upper half of the residue range?](catalog-0501-0600.md#JSP-000594) | Open | No | No | Unavailable | Unavailable |
| JSP-000595 | [Can the square of a factorial with index slightly above a reference value divide the factorial of twice that reference value?](catalog-0501-0600.md#JSP-000595) | Open | No | No | Unavailable | Unavailable |
| JSP-000596 | [If one product of two factorials divides another, how far apart can the sums of their indices be?](catalog-0501-0600.md#JSP-000596) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000597 | [What restrictions on factorial indices follow when the reduced denominator of their ratio has only small prime factors?](catalog-0501-0600.md#JSP-000597) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000598 | [Can two distinct central binomial coefficients have exactly the same prime divisors?](catalog-0501-0600.md#JSP-000598) | Solved | No | No | Unavailable | Unavailable |
| JSP-000599 | [How large is the smallest positive integer not dividing a central binomial coefficient, typically?](catalog-0501-0600.md#JSP-000599) | Open | No | No | Unavailable | Unavailable |
| JSP-000600 | [Which prescribed block-size sequences admit a pairwise balanced design in which every pair occurs exactly once?](catalog-0501-0600.md#JSP-000600) | Solved | No | No | Unavailable | Unavailable |

### Problems 601–700

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000601 | [How many distinct line-multiplicity counting sequences can planar point sets determine?](catalog-0601-0700.md#JSP-000601) | Solved | No | No | Unavailable | Unavailable |
| JSP-000602 | [Which pairwise balanced designs exist when repeated block sizes have bounded multiplicity?](catalog-0601-0700.md#JSP-000602) | Open | No | No | Unavailable | Unavailable |
| JSP-000603 | [When can a planar point set receive positive weights so that every line containing at least two points has the same total weight?](catalog-0601-0700.md#JSP-000603) | Solved | No | No | Unavailable | Unavailable |
| JSP-000604 | [Can graphs of arbitrarily high chromatic number be constructed without changing the finite subgraph types that occur?](catalog-0601-0700.md#JSP-000604) | Open | No | No | Unavailable | Unavailable |
| JSP-000605 | [Must every graph of uncountable chromatic number have an edge lying on cycles of every sufficiently large length?](catalog-0601-0700.md#JSP-000605) | Solved | No | No | Unavailable | Unavailable |
| JSP-000606 | [Must every triangle-free graph of infinite chromatic number contain every prescribed tree as an induced subgraph?](catalog-0601-0700.md#JSP-000606) | Open | No | No | Unavailable | Unavailable |
| JSP-000607 | [Does a graph of infinite chromatic number have subgraphs of every smaller infinite chromatic number?](catalog-0601-0700.md#JSP-000607) | Open | No | No | Unavailable | Unavailable |
| JSP-000608 | [Can short-odd-cycle structures be removed from a graph of infinite chromatic number while preserving its chromatic number?](catalog-0601-0700.md#JSP-000608) | Open | No | No | Unavailable | Unavailable |
| JSP-000609 | [If an integer set's self-sumset has positive density, can it be partitioned into two parts whose self-sumsets both have positive density?](catalog-0601-0700.md#JSP-000609) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000610 | [How many edges can a diameter-two graph have if deleting any edge increases its diameter?](catalog-0601-0700.md#JSP-000610) | Open | No | No | Unavailable | Unavailable |
| JSP-000611 | [tree packing conjecture](catalog-0601-0700.md#JSP-000611) | Open | No | No | Unavailable | Unavailable |
| JSP-000612 | [How many edges must be deleted from a chromatic-critical graph to make it bipartite?](catalog-0601-0700.md#JSP-000612) | Solved | No | No | Unavailable | Unavailable |
| JSP-000613 | [How large is the second-largest component of a random graph in the critical transition window?](catalog-0601-0700.md#JSP-000613) | Solved | No | No | Unavailable | Unavailable |
| JSP-000614 | [What is the edge threshold for Hamilton cycles in a random graph?](catalog-0601-0700.md#JSP-000614) | Solved | No | No | Unavailable | Unavailable |
| JSP-000615 | [What is the density threshold for a perfect matching in a random three-uniform hypergraph?](catalog-0601-0700.md#JSP-000615) | Solved | No | No | Unavailable | Unavailable |
| JSP-000616 | [Counting sum-free subsets of integer intervals](catalog-0601-0700.md#JSP-000616) | Solved | No | No | Unavailable | Unavailable |
| JSP-000617 | [Can an integer set have uniformly bounded two-term representation counts while its sumset density is arbitrarily close to one?](catalog-0601-0700.md#JSP-000617) | Open | No | No | Unavailable | Unavailable |
| JSP-000618 | [Can an infinite-chromatic graph have an independent set of nearly half the vertices in every finite subgraph?](catalog-0601-0700.md#JSP-000618) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000619 | [How many distinct cycle lengths are forced by large minimum degree and large girth?](catalog-0601-0700.md#JSP-000619) | Solved | No | No | Unavailable | Unavailable |
| JSP-000620 | [In a finite four-dimensional point set, how many other points can be at the same distance from one point?](catalog-0601-0700.md#JSP-000620) | Solved | No | No | Unavailable | Unavailable |
| JSP-000621 | [If all local parts of a real set have many differences, must it contain a Sidon subset of fixed positive proportion?](catalog-0601-0700.md#JSP-000621) | Open | No | No | Unavailable | Unavailable |
| JSP-000622 | [For a prescribed small graph order, what is the worst-case minimum number of clique or independent-set parts in a vertex partition?](catalog-0601-0700.md#JSP-000622) | Solved | No | No | Unavailable | Unavailable |
| JSP-000623 | [How does the minimum number of clique or independent-set parts for graphs on a surface grow with the surface's complexity?](catalog-0601-0700.md#JSP-000623) | Solved | No | No | Unavailable | Unavailable |
| JSP-000624 | [How does ordinary chromatic number relate to the number of acyclic vertex classes needed after orienting edges?](catalog-0601-0700.md#JSP-000624) | Open | No | No | Unavailable | Unavailable |
| JSP-000625 | [Can cumulative two-term additive representation counts grow linearly with bounded error?](catalog-0601-0700.md#JSP-000625) | Solved | No | No | Unavailable | Unavailable |
| JSP-000626 | [Can cumulative three-term additive representation counts grow linearly with bounded error?](catalog-0601-0700.md#JSP-000626) | Solved | No | No | Unavailable | Unavailable |
| JSP-000627 | [Among forbidden graphs with fixed vertex and edge counts, which minimizes the extremal function? Is this minimum strictly monotone in the forbidden graph's edge count?](catalog-0601-0700.md#JSP-000627) | Open | No | No | Unavailable | Unavailable |
| JSP-000628 | [How many edges can a graph have if no vertex of a cycle is incident to several specified chords?](catalog-0601-0700.md#JSP-000628) | Solved | No | No | Unavailable | Unavailable |
| JSP-000629 | [If each prime divisor of an integer has a divisor of that integer greater than one and congruent to one modulo the prime, does the density of such integers decay as predicted?](catalog-0601-0700.md#JSP-000629) | Open | No | No | Unavailable | Unavailable |
| JSP-000630 | [Into how many smaller axis-parallel cubes can a higher-dimensional cube be dissected?](catalog-0601-0700.md#JSP-000630) | Open | No | No | Unavailable | Unavailable |
| JSP-000631 | [What conditions on bases or exponent ensure the prescribed coprimality relations among like powers minus one?](catalog-0601-0700.md#JSP-000631) | Open | No | No | Unavailable | Unavailable |
| JSP-000632 | [How large a subset of an arbitrary finite integer set can have every subset sum avoid a prescribed target?](catalog-0601-0700.md#JSP-000632) | Solved | No | No | Unavailable | Unavailable |
| JSP-000633 | [If two-term representation counts are bounded, how large a Sidon subset is guaranteed?](catalog-0601-0700.md#JSP-000633) | Solved | No | No | Unavailable | Unavailable |
| JSP-000634 | [How large a Sidon set can be chosen among squares in a prescribed range?](catalog-0601-0700.md#JSP-000634) | Open | No | No | Unavailable | Unavailable |
| JSP-000635 | [If every finite part of a set contains a fixed proportion with distinct subset sums, can the whole set be partitioned into finitely many such sets?](catalog-0601-0700.md#JSP-000635) | Open | No | No | Unavailable | Unavailable |
| JSP-000636 | [How many different set sizes can an antichain realize if each size must occur with prescribed multiplicity?](catalog-0601-0700.md#JSP-000636) | Open | No | No | Unavailable | Unavailable |
| JSP-000637 | [How many edges can the containment graph of a set family have?](catalog-0601-0700.md#JSP-000637) | Solved | No | No | Unavailable | Unavailable |
| JSP-000638 | [In the game where players alternately color edges to build the largest monochromatic clique, what outcomes and optimal strategies can each guarantee?](catalog-0601-0700.md#JSP-000638) | Open | No | No | Unavailable | Unavailable |
| JSP-000639 | [For a product of the first several primes, is there always a prime between its largest factor and the product whose sum with the product is also prime?](catalog-0601-0700.md#JSP-000639) | Open | No | No | Unavailable | Unavailable |
| JSP-000640 | [What size of a multicolored uniform hypergraph forces a prescribed number of disjoint edges of one color?](catalog-0601-0700.md#JSP-000640) | Solved | No | No | Unavailable | Unavailable |
| JSP-000641 | [How long an interval forces a prescribed-length monochromatic increasing sequence with nonincreasing gaps under every two-coloring? Is the predicted exact quadratic threshold correct?](catalog-0601-0700.md#JSP-000641) | Solved | No | No | Unavailable | Unavailable |
| JSP-000642 | [Do the squares contain arbitrarily long approximate arithmetic progressions and arbitrarily large additive cubes with independent directions?](catalog-0601-0700.md#JSP-000642) | Open | No | No | Unavailable | Unavailable |
| JSP-000643 | [Among pairwise coprime integer sets with bounded reciprocal sum, which have multiples covering the largest proportion of integers?](catalog-0601-0700.md#JSP-000643) | Solved | No | No | Unavailable | Unavailable |
| JSP-000644 | [If an integer set's reciprocal sum is bounded, what proportion of integers must avoid divisibility by every set element?](catalog-0601-0700.md#JSP-000644) | Solved | No | No | Unavailable | Unavailable |
| JSP-000645 | [Can a dense integer set have the property that equal products always use the same number of factors?](catalog-0601-0700.md#JSP-000645) | Open | No | No | Unavailable | Unavailable |
| JSP-000646 | [How large a subset of an arbitrary finite real set can have all pairwise sums outside the original set?](catalog-0601-0700.md#JSP-000646) | Open | No | No | Unavailable | Unavailable |
| JSP-000647 | [What tradeoff relates the size of a subset whose pairwise sums avoid a given set to the number of forbidden sums?](catalog-0601-0700.md#JSP-000647) | Open | No | No | Unavailable | Unavailable |
| JSP-000648 | [How large a subset of an arbitrary finite set can have no equal sums using different numbers of terms?](catalog-0601-0700.md#JSP-000648) | Open | No | No | Unavailable | Unavailable |
| JSP-000649 | [How large a subset of an arbitrary finite integer set can have no element equal to a sum of distinct other elements?](catalog-0601-0700.md#JSP-000649) | Open | No | No | Unavailable | Unavailable |
| JSP-000650 | [How small can an integer set be if its two-term sums cover an initial integer interval?](catalog-0601-0700.md#JSP-000650) | Open | No | No | Unavailable | Unavailable |
| JSP-000651 | [How large a sum-free subset must every finite integer set contain?](catalog-0601-0700.md#JSP-000651) | Open | No | No | Unavailable | Unavailable |
| JSP-000652 | [How large can a subset of an integer interval be if no element divides the product of two others?](catalog-0601-0700.md#JSP-000652) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000653 | [How large can a subset of an integer interval be if all subset products are distinct?](catalog-0601-0700.md#JSP-000653) | Solved | No | No | Unavailable | Unavailable |
| JSP-000654 | [How large can an integer set be under a bound on each integer's number of multiplicative representations?](catalog-0601-0700.md#JSP-000654) | Open | No | No | Unavailable | Unavailable |
| JSP-000655 | [How many colors are needed for an acyclic coloring of a bounded-maximum-degree graph, with every two color classes inducing a forest?](catalog-0601-0700.md#JSP-000655) | Solved | No | No | Unavailable | Unavailable |
| JSP-000656 | [Is the list chromatic number of a random graph sublinear in its number of vertices?](catalog-0601-0700.md#JSP-000656) | Solved | No | No | Unavailable | Unavailable |
| JSP-000657 | [If all high-degree vertices are pairwise nonadjacent, is the graph's Ramsey number linear in its size?](catalog-0601-0700.md#JSP-000657) | Solved | No | No | Unavailable | Unavailable |
| JSP-000658 | [Does a graph with small independence number contain a small but dense subgraph?](catalog-0601-0700.md#JSP-000658) | Solved | No | No | Unavailable | Unavailable |
| JSP-000659 | [How large an independent set is guaranteed by average degree in a graph excluding a prescribed clique?](catalog-0601-0700.md#JSP-000659) | Open | No | No | Unavailable | Unavailable |
| JSP-000660 | [Does every dense graph contain a sufficiently dense subgraph whose vertex degrees are comparable?](catalog-0601-0700.md#JSP-000660) | Solved | No | No | Unavailable | Unavailable |
| JSP-000661 | [If every local part has a large independent set, how large an independent set must the whole graph have?](catalog-0601-0700.md#JSP-000661) | Solved | No | No | Unavailable | Unavailable |
| JSP-000662 | [Can every medium-size subgraph of a graph contain both a large clique and a large independent set?](catalog-0601-0700.md#JSP-000662) | Open | No | No | Unavailable | Unavailable |
| JSP-000663 | [Can an integer set of square-root-scale size be covered by the two-term sumset of a smaller set?](catalog-0601-0700.md#JSP-000663) | Solved | No | No | Unavailable | Unavailable |
| JSP-000664 | [How many complete bipartite graphs are typically needed to partition a random graph's edges?](catalog-0601-0700.md#JSP-000664) | Solved | No | No | Unavailable | Unavailable |
| JSP-000665 | [When sums and products are taken only along edges of a dense graph on integers, how large must one of the resulting value sets be?](catalog-0601-0700.md#JSP-000665) | Solved | No | No | Unavailable | Unavailable |
| JSP-000666 | [How many edge colors are needed to make every odd cycle rainbow?](catalog-0601-0700.md#JSP-000666) | Open | No | No | Unavailable | Unavailable |
| JSP-000667 | [Can a dense graph be edge-colored with linearly many colors so that every four-cycle is rainbow?](catalog-0601-0700.md#JSP-000667) | Open | No | No | Unavailable | Unavailable |
| JSP-000668 | [Which rainbow subgraphs are forced by the specified balanced restrictions on edge-color usage?](catalog-0601-0700.md#JSP-000668) | Open | No | No | Unavailable | Unavailable |
| JSP-000669 | [How much must the ratio and difference of successive clique Ramsey thresholds grow when the target order increases by one?](catalog-0601-0700.md#JSP-000669) | Open | No | No | Unavailable | Unavailable |
| JSP-000670 | [If every seven vertices contain a triangle, how large a clique is guaranteed?](catalog-0601-0700.md#JSP-000670) | Open | No | No | Unavailable | Unavailable |
| JSP-000671 | [Does slightly exceeding the specified edge threshold force a small subgraph of high minimum degree?](catalog-0601-0700.md#JSP-000671) | Solved | No | No | Unavailable | Unavailable |
| JSP-000672 | [Do sufficiently large critical graphs satisfying the specified local minimum-degree restrictions contain every fixed cycle length?](catalog-0601-0700.md#JSP-000672) | Solved | No | No | Unavailable | Unavailable |
| JSP-000673 | [Must a dense graph of odd order have two equal-degree vertices joined by a three-edge path?](catalog-0601-0700.md#JSP-000673) | Solved | No | No | Unavailable | Unavailable |
| JSP-000674 | [How large a containing interval is necessary if all subset sums avoid arithmetic progressions of a prescribed length?](catalog-0601-0700.md#JSP-000674) | Open | No | No | Unavailable | Unavailable |
| JSP-000675 | [For a square-root-size subset of an integer interval, how many distinct two-term sums can still lie in that interval?](catalog-0601-0700.md#JSP-000675) | Open | No | No | Unavailable | Unavailable |
| JSP-000676 | [How does the smallest base satisfying the prescribed coprimality of like powers minus one depend on the exponent?](catalog-0601-0700.md#JSP-000676) | Open | No | No | Unavailable | Unavailable |
| JSP-000677 | [Which numbers of positive-integer preimages can a totient value have?](catalog-0601-0700.md#JSP-000677) | Open | No | No | Unavailable | Unavailable |
| JSP-000678 | [Does the set of values of an integer plus its totient have positive density?](catalog-0601-0700.md#JSP-000678) | Solved | No | No | Unavailable | Unavailable |
| JSP-000679 | [Which positive real numbers can be approximated arbitrarily closely by ratios of integers having equal divisor sums?](catalog-0601-0700.md#JSP-000679) | Solved | No | No | Unavailable | Unavailable |
| JSP-000680 | [How many coprime pairs of positive integers have equal divisor sums, and how does their count grow?](catalog-0601-0700.md#JSP-000680) | Open | No | No | Unavailable | Unavailable |
| JSP-000681 | [Does a sufficiently large divisor sum ensure that an integer is a sum of some of its proper divisors?](catalog-0601-0700.md#JSP-000681) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000682 | [Is there an integer whose succeeding positions have divisor counts bounded linearly in their distance from it?](catalog-0601-0700.md#JSP-000682) | Open | No | No | Unavailable | Unavailable |
| JSP-000683 | [How many planar points force a prescribed-size subset whose distinct triples have distinct circumradii?](catalog-0601-0700.md#JSP-000683) | Open | No | No | Unavailable | Unavailable |
| JSP-000684 | [For a fixed constant, are there infinitely many integers whose totient divides the integer plus that constant?](catalog-0601-0700.md#JSP-000684) | Open | No | No | Unavailable | Unavailable |
| JSP-000685 | [How many representations can one integer have as a sum of two integer cubes?](catalog-0601-0700.md#JSP-000685) | Open | No | No | Unavailable | Unavailable |
| JSP-000686 | [Are there infinitely many amicable pairs, in which each number's proper divisors sum to the other, and how fast does their count grow?](catalog-0601-0700.md#JSP-000686) | Open | No | No | Unavailable | Unavailable |
| JSP-000687 | [How many distinct circumradii must the triples of a planar point set in general position determine?](catalog-0601-0700.md#JSP-000687) | Open | No | No | Unavailable | Unavailable |
| JSP-000688 | [How many edges are needed for a uniform hypergraph to attain a prescribed chromatic number?](catalog-0601-0700.md#JSP-000688) | Solved | No | No | Unavailable | Unavailable |
| JSP-000689 | [Must a uniform hypergraph requiring three colors have maximum degree exponential in its edge size?](catalog-0601-0700.md#JSP-000689) | Solved | No | No | Unavailable | Unavailable |
| JSP-000690 | [Is there a three-uniform, three-chromatic-critical hypergraph with minimum degree at least seven?](catalog-0601-0700.md#JSP-000690) | Solved | No | No | Unavailable | Unavailable |
| JSP-000691 | [Can fixed-size subsets be colored so that every set of the next larger size contains subsets of every color?](catalog-0601-0700.md#JSP-000691) | Open | No | No | Unavailable | Unavailable |
| JSP-000692 | [What restrictions relate vertex count and pairwise edge-intersection sizes in intersecting three-chromatic uniform hypergraphs?](catalog-0601-0700.md#JSP-000692) | Open | No | No | Unavailable | Unavailable |
| JSP-000693 | [Which edge densities are jumps for three-uniform hypergraphs, where slightly exceeding the density forces a definite local increase?](catalog-0601-0700.md#JSP-000693) | Open | No | No | Unavailable | Unavailable |
| JSP-000694 | [How many subsets of a planar point set in general position are in convex position?](catalog-0601-0700.md#JSP-000694) | Open | No | No | Unavailable | Unavailable |
| JSP-000695 | [How dense can an integer sequence be if no new term is a sum of consecutive earlier terms?](catalog-0601-0700.md#JSP-000695) | Open | No | No | Unavailable | Unavailable |
| JSP-000696 | [How much can allowing very few repeated pairwise sums increase the maximum size over that of a Sidon set?](catalog-0601-0700.md#JSP-000696) | Open | No | No | Unavailable | Unavailable |
| JSP-000697 | [How short a following interval supplies larger integers whose product with a given integer is a square?](catalog-0601-0700.md#JSP-000697) | Solved | No | No | Unavailable | Unavailable |
| JSP-000698 | [Is every graph formed by vertex-disjoint triangles and a spanning Hamilton cycle three-colorable?](catalog-0601-0700.md#JSP-000698) | Solved | No | No | Unavailable | Unavailable |
| JSP-000699 | [Under every two-coloring of the squares, is every sufficiently large integer a sum of distinct squares of one color?](catalog-0601-0700.md#JSP-000699) | Solved | No | No | Unavailable | Unavailable |
| JSP-000700 | [If every finite part of a planar set contains a fixed proportion in general position, can the whole set be partitioned into finitely many general-position sets?](catalog-0601-0700.md#JSP-000700) | Solved | Yes | Yes | Unclaimed | Unclaimed |

### Problems 701–800

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000701 | [How large can an integer-interval subset be if every pairwise product plus one has a nontrivial square factor?](catalog-0701-0800.md#JSP-000701) | Open | No | No | Unavailable | Unavailable |
| JSP-000702 | [Singmaster's conjecture](catalog-0701-0800.md#JSP-000702) | Open | No | No | Unavailable | Unavailable |
| JSP-000703 | [Matching prime-factor sets across shifted integer pairs](catalog-0701-0800.md#JSP-000703) | Open | No | No | Unavailable | Unavailable |
| JSP-000704 | [Can a density-one set of integers be represented as a power of two plus a number with few prime factors?](catalog-0701-0800.md#JSP-000704) | Solved | No | No | Unavailable | Unavailable |
| JSP-000705 | [How long a run of pairwise distinct consecutive prime gaps can occur?](catalog-0701-0800.md#JSP-000705) | Open | No | No | Unavailable | Unavailable |
| JSP-000706 | [How large is the smallest positive even number not yet seen among the prime gaps up to a given point?](catalog-0701-0800.md#JSP-000706) | Open | No | No | Unavailable | Unavailable |
| JSP-000707 | [Which gaps occur among consecutive integers coprime to a primorial?](catalog-0701-0800.md#JSP-000707) | Open | No | No | Unavailable | Unavailable |
| JSP-000708 | [second Hardy-Littlewood conjecture](catalog-0701-0800.md#JSP-000708) | Open | No | No | Unavailable | Unavailable |
| JSP-000709 | [How large can an integer set's reciprocal sum be if it has no prescribed-size subset with all pairwise least common multiples equal?](catalog-0701-0800.md#JSP-000709) | Open | No | No | Unavailable | Unavailable |
| JSP-000710 | [weak sunflower problem](catalog-0701-0800.md#JSP-000710) | Open | No | No | Unavailable | Unavailable |
| JSP-000711 | [How large can an integer set's reciprocal sum be when the specified pairs linked by large prime factors and divisibility are forbidden?](catalog-0701-0800.md#JSP-000711) | Solved | No | No | Unavailable | Unavailable |
| JSP-000712 | [What proportion of integers have a subset of distinct divisors summing to a prescribed target?](catalog-0701-0800.md#JSP-000712) | Open | No | No | Unavailable | Unavailable |
| JSP-000713 | [How short an interval can contain a different multiple of each of the first several primes?](catalog-0701-0800.md#JSP-000713) | Open | No | No | Unavailable | Unavailable |
| JSP-000714 | [How many Sidon subsets do the first several positive integers have?](catalog-0701-0800.md#JSP-000714) | Solved | No | No | Unavailable | Unavailable |
| JSP-000715 | [How do extremal sizes compare between integer sets with bounded sum multiplicities and those with bounded difference multiplicities?](catalog-0701-0800.md#JSP-000715) | Solved | No | No | Unavailable | Unavailable |
| JSP-000716 | [How large can an integer-interval subset be if at most one sum has multiple representations?](catalog-0701-0800.md#JSP-000716) | Open | No | No | Unavailable | Unavailable |
| JSP-000717 | [Must every sufficiently dense integer set contain three elements together with all their pairwise sums?](catalog-0701-0800.md#JSP-000717) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000718 | [How far above one half must density be to force all pairwise sums of a large set?](catalog-0701-0800.md#JSP-000718) | Open | No | No | Unavailable | Unavailable |
| JSP-000719 | [Does every order-two additive basis with growing representation counts contain a minimal order-two basis?](catalog-0701-0800.md#JSP-000719) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000720 | [Does the union of two disjoint order-two additive bases contain a minimal order-two basis?](catalog-0701-0800.md#JSP-000720) | Solved | No | No | Unavailable | Unavailable |
| JSP-000721 | [What growth conditions on representation counts ensure that a higher-order additive basis contains a minimal basis of the same order?](catalog-0701-0800.md#JSP-000721) | Open | No | No | Unavailable | Unavailable |
| JSP-000722 | [If two-term representation counts tend to infinity, can the set be partitioned into two order-two additive bases?](catalog-0701-0800.md#JSP-000722) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000723 | [How long does optimal play last when players alternately choose integers incomparable by divisibility with all previously chosen integers?](catalog-0701-0800.md#JSP-000723) | Open | No | No | Unavailable | Unavailable |
| JSP-000724 | [How often can a prescribed number of consecutive terms of an increasing integer sequence have small least common multiple?](catalog-0701-0800.md#JSP-000724) | Open | No | No | Unavailable | Unavailable |
| JSP-000725 | [How large can an integer-interval subset be if subset sums using different numbers of terms are never equal?](catalog-0701-0800.md#JSP-000725) | Solved | No | No | Unavailable | Unavailable |
| JSP-000726 | [How large must gaps in an infinite integer sequence be if subset sums with different numbers of terms are always distinct?](catalog-0701-0800.md#JSP-000726) | Open | No | No | Unavailable | Unavailable |
| JSP-000727 | [How small can consecutive gaps be in an infinite increasing integer sequence with no term a subset sum of earlier distinct terms?](catalog-0701-0800.md#JSP-000727) | Open | No | No | Unavailable | Unavailable |
| JSP-000728 | [How many inclusion-maximal sum-free subsets does a finite integer interval have?](catalog-0701-0800.md#JSP-000728) | Solved | No | No | Unavailable | Unavailable |
| JSP-000729 | [How does the sum of an integer's prime-power factors compare with the maximum sum of pairwise coprime divisors?](catalog-0701-0800.md#JSP-000729) | Open | No | No | Unavailable | Unavailable |
| JSP-000730 | [What is the largest sum of pairwise coprime integers in a finite interval, and what are the extremizing sets?](catalog-0701-0800.md#JSP-000730) | Open | No | No | Unavailable | Unavailable |
| JSP-000731 | [Must the distinct-element sumset of an additive basis have bounded gaps?](catalog-0701-0800.md#JSP-000731) | Solved | No | No | Unavailable | Unavailable |
| JSP-000732 | [After deleting infinitely many elements of a minimal additive basis, can every sufficiently large integer still be represented using one additional summand?](catalog-0701-0800.md#JSP-000732) | Open | No | No | Unavailable | Unavailable |
| JSP-000733 | [How large can an integer-interval subset be if its distinct subset sums never divide one another?](catalog-0701-0800.md#JSP-000733) | Solved | No | No | Unavailable | Unavailable |
| JSP-000734 | [Which odd cycles and complete multipartite graphs must occur in the coprimality graph of a dense integer set?](catalog-0701-0800.md#JSP-000734) | Open | No | No | Unavailable | Unavailable |
| JSP-000735 | [How does the reciprocal sum of all distinct divisor differences compare with that of consecutive divisor differences?](catalog-0701-0800.md#JSP-000735) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000736 | [Can the divisor-difference sets of two distinct integers have arbitrarily many common values?](catalog-0701-0800.md#JSP-000736) | Open | No | No | Unavailable | Unavailable |
| JSP-000737 | [How many divisors can an integer have in a short interval near its square root?](catalog-0701-0800.md#JSP-000737) | Open | No | No | Unavailable | Unavailable |
| JSP-000738 | [Is there a uniform constant bound on the number of divisors in a fourth-root-length interval near an integer's square root?](catalog-0701-0800.md#JSP-000738) | Open | No | No | Unavailable | Unavailable |
| JSP-000739 | [How large can an integer set be if every square product of four elements forces equality of the corresponding cross products?](catalog-0701-0800.md#JSP-000739) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000740 | [How many previously unseen prime factors can each successive term of a consecutive-integer interval introduce?](catalog-0701-0800.md#JSP-000740) | Open | No | No | Unavailable | Unavailable |
| JSP-000741 | [What are the largest and smallest possible numbers of distinct prime factors in a short consecutive-integer interval?](catalog-0701-0800.md#JSP-000741) | Open | No | No | Unavailable | Unavailable |
| JSP-000742 | [Must every interval of primorial length contain an integer with more distinct prime factors than that primorial?](catalog-0701-0800.md#JSP-000742) | Open | No | No | Unavailable | Unavailable |
| JSP-000743 | [Which growth rates and densities can primitive integer sequences, with no term dividing another, realize?](catalog-0701-0800.md#JSP-000743) | Open | No | No | Unavailable | Unavailable |
| JSP-000744 | [How does the cumulative divisor count of powers of two minus one grow as the range expands?](catalog-0701-0800.md#JSP-000744) | Open | No | No | Unavailable | Unavailable |
| JSP-000745 | [Can the integers be finitely colored so that no same-colored pair has difference in a prescribed sparse set?](catalog-0701-0800.md#JSP-000745) | Solved | No | No | Unavailable | Unavailable |
| JSP-000746 | [Must every triangle-free graph on the integers have three independent vertices, one equal to the sum of the other two?](catalog-0701-0800.md#JSP-000746) | Solved | No | No | Unavailable | Unavailable |
| JSP-000747 | [Under the stated restrictions, how many uniquely represented products can two integer sets have?](catalog-0701-0800.md#JSP-000747) | Solved | No | No | Unavailable | Unavailable |
| JSP-000748 | [Just above the giant-component threshold, how long a path proportional to the vertex count does a random graph contain?](catalog-0701-0800.md#JSP-000748) | Solved | No | No | Unavailable | Unavailable |
| JSP-000749 | [How many edges must a uniform hypergraph have to force a monochromatic edge under every two-coloring?](catalog-0701-0800.md#JSP-000749) | Open | No | No | Unavailable | Unavailable |
| JSP-000750 | [How small can a tournament be if every small vertex set has a common external vertex dominating it?](catalog-0701-0800.md#JSP-000750) | Open | No | No | Unavailable | Unavailable |
| JSP-000751 | [Are there gaps in the possible block counts of pairwise balanced designs with parameters close to those of finite projective planes?](catalog-0701-0800.md#JSP-000751) | Solved | No | No | Unavailable | Unavailable |
| JSP-000752 | [Is there an entire function such that the union of zeros of any infinite selection of its derivatives is dense in the complex plane?](catalog-0701-0800.md#JSP-000752) | Open | No | No | Unavailable | Unavailable |
| JSP-000753 | [If every translation difference of a function is measurable, does the function decompose into parts with the specified regularity?](catalog-0701-0800.md#JSP-000753) | Solved | No | No | Unavailable | Unavailable |
| JSP-000754 | [Can a space and its Cartesian square have the same nontrivial finite dimension?](catalog-0701-0800.md#JSP-000754) | Solved | No | No | Unavailable | Unavailable |
| JSP-000755 | [Must a connected Euclidean set contain connected subsets of several distinct homeomorphism types?](catalog-0701-0800.md#JSP-000755) | Solved | No | No | Unavailable | Unavailable |
| JSP-000756 | [How does the size Ramsey number grow with the target graph's average degree?](catalog-0701-0800.md#JSP-000756) | Open | No | No | Unavailable | Unavailable |
| JSP-000757 | [How many distinct exponent values occur in the prime factorization of a factorial?](catalog-0701-0800.md#JSP-000757) | Open | No | No | Unavailable | Unavailable |
| JSP-000758 | [Can the product of consecutive integers have pairwise distinct prime-factor exponents?](catalog-0701-0800.md#JSP-000758) | Open | No | No | Unavailable | Unavailable |
| JSP-000759 | [What edge count forces many internally disjoint paths between two vertices?](catalog-0701-0800.md#JSP-000759) | Solved | No | No | Unavailable | Unavailable |
| JSP-000760 | [Can a linear edge bound force a cycle and an external vertex adjacent to three of its vertices?](catalog-0701-0800.md#JSP-000760) | Solved | No | No | Unavailable | Unavailable |
| JSP-000761 | [How many edges can a graph critical under the specified chromatic-reducing deletions have?](catalog-0701-0800.md#JSP-000761) | Open | No | No | Unavailable | Unavailable |
| JSP-000762 | [Can a large graph have uncountable chromatic number while all subgraphs of the specified smaller size have countable chromatic number?](catalog-0701-0800.md#JSP-000762) | Open | No | No | Unavailable | Unavailable |
| JSP-000763 | [Can a graph's high chromatic number be absent from all subgraphs whose vertex sets have restricted order type?](catalog-0701-0800.md#JSP-000763) | Open | No | No | Unavailable | Unavailable |
| JSP-000764 | [What is the largest chromatic number at a prescribed order when a fixed clique is forbidden?](catalog-0701-0800.md#JSP-000764) | Solved | No | No | Unavailable | Unavailable |
| JSP-000765 | [What is the largest odd girth of a graph with prescribed order and chromatic number?](catalog-0701-0800.md#JSP-000765) | Solved | No | No | Unavailable | Unavailable |
| JSP-000766 | [If every finite local subgraph has an independent set of nearly half its vertices, is the whole graph's chromatic number bounded?](catalog-0701-0800.md#JSP-000766) | Solved | No | No | Unavailable | Unavailable |
| JSP-000767 | [Can a graph exclude a larger clique while forcing a smaller monochromatic clique under every prescribed multicolor edge coloring?](catalog-0701-0800.md#JSP-000767) | Solved | No | No | Unavailable | Unavailable |
| JSP-000768 | [If a graph admits an edge coloring with no monochromatic triangle, must it have a sufficiently large independent set?](catalog-0701-0800.md#JSP-000768) | Solved | No | No | Unavailable | Unavailable |
| JSP-000769 | [How many edges can a graph have while excluding the specified complete-graph subdivision with a common center?](catalog-0701-0800.md#JSP-000769) | Solved | No | No | Unavailable | Unavailable |
| JSP-000770 | [What is the joint density distribution of the largest prime factors of consecutive integers in prescribed ranges?](catalog-0701-0800.md#JSP-000770) | Open | No | No | Unavailable | Unavailable |
| JSP-000771 | [How large a small-prime range is necessary to supply a prime divisor for every integer in a consecutive interval?](catalog-0701-0800.md#JSP-000771) | Open | No | No | Unavailable | Unavailable |
| JSP-000772 | [Can products of several long consecutive-integer intervals combine to form a perfect power?](catalog-0701-0800.md#JSP-000772) | Open | No | No | Unavailable | Unavailable |
| JSP-000773 | [Which disjoint consecutive-integer intervals have products with exactly the same prime-factor set?](catalog-0701-0800.md#JSP-000773) | Open | No | No | Unavailable | Unavailable |
| JSP-000774 | [How often do consecutive primes enclose at least two integers having only sufficiently small prime factors?](catalog-0701-0800.md#JSP-000774) | Open | No | No | Unavailable | Unavailable |
| JSP-000775 | [How large can the part supported on powers of two and three in a product of consecutive integers be?](catalog-0701-0800.md#JSP-000775) | Open | No | No | Unavailable | Unavailable |
| JSP-000776 | [Under a maximum-degree bound, how many edges force two edges sufficiently far apart in the graph?](catalog-0701-0800.md#JSP-000776) | Open | No | No | Unavailable | Unavailable |
| JSP-000777 | [How small an upper bound controls the powerful part of a product of consecutive integers?](catalog-0701-0800.md#JSP-000777) | Open | No | No | Unavailable | Unavailable |
| JSP-000778 | [How often are powers of two or factorials plus or minus one powerful numbers?](catalog-0701-0800.md#JSP-000778) | Open | No | No | Unavailable | Unavailable |
| JSP-000779 | [How often do three consecutive members of the ordered powerful numbers form an arithmetic progression?](catalog-0701-0800.md#JSP-000779) | Open | No | No | Unavailable | Unavailable |
| JSP-000780 | [Can higher-powerful integers satisfying the required coprimality conditions obey an additive relation in which one is the sum of the other two?](catalog-0701-0800.md#JSP-000780) | Open | No | No | Unavailable | Unavailable |
| JSP-000781 | [How many integers are sums of a bounded number of higher-powerful numbers, and what density do they have?](catalog-0701-0800.md#JSP-000781) | Open | No | No | Unavailable | Unavailable |
| JSP-000782 | [Is every sufficiently large integer a sum of three powerful numbers, each divisible by the square of every prime dividing it?](catalog-0701-0800.md#JSP-000782) | Solved | No | No | Unavailable | Unavailable |
| JSP-000783 | [How many powerful numbers can lie between consecutive squares?](catalog-0701-0800.md#JSP-000783) | Open | No | No | Unavailable | Unavailable |
| JSP-000784 | [What upper bounds and growth laws govern the number of representations of an integer as a sum of two powerful numbers?](catalog-0701-0800.md#JSP-000784) | Open | No | No | Unavailable | Unavailable |
| JSP-000785 | [Can a graph be vertex-critical for chromatic number while deletion of any small number of edges never lowers its chromatic number?](catalog-0701-0800.md#JSP-000785) | Open | No | No | Unavailable | Unavailable |
| JSP-000786 | [How long a run of consecutive integers can have pairwise distinct divisor counts?](catalog-0701-0800.md#JSP-000786) | Open | No | No | Unavailable | Unavailable |
| JSP-000787 | [Are there infinitely many consecutive positive integers with equal divisor counts?](catalog-0701-0800.md#JSP-000787) | Solved | No | No | Unavailable | Unavailable |
| JSP-000788 | [Under a finite coloring of the positive integers, can the specified sparse sequence be found whose subset sums omit at least one color?](catalog-0701-0800.md#JSP-000788) | Solved | No | No | Unavailable | Unavailable |
| JSP-000789 | [If a real set is sum-free, does its complement contain a large set together with all its pairwise sums?](catalog-0701-0800.md#JSP-000789) | Open | No | No | Unavailable | Unavailable |
| JSP-000790 | [For a fixed integer, how large is the reciprocal sum of its positive differences from preceding primes, and how does it vary?](catalog-0701-0800.md#JSP-000790) | Open | No | No | Unavailable | Unavailable |
| JSP-000791 | [How dense can a real sequence be if all the specified distinct power products differ by at least one?](catalog-0701-0800.md#JSP-000791) | Open | No | No | Unavailable | Unavailable |
| JSP-000792 | [Gaussian moat problem](catalog-0701-0800.md#JSP-000792) | Open | No | No | Unavailable | Unavailable |
| JSP-000793 | [What is the largest area of a measurable subset of a given disk containing no pair at a positive integer distance?](catalog-0701-0800.md#JSP-000793) | Open | No | No | Unavailable | Unavailable |
| JSP-000794 | [For a sequence generated greedily to match cumulative additive representation targets, how small can the error be?](catalog-0701-0800.md#JSP-000794) | Open | No | No | Unavailable | Unavailable |
| JSP-000795 | [If an integer set has density zero, must the integers whose proper-divisor sums lie in that set also have density zero?](catalog-0701-0800.md#JSP-000795) | Open | No | No | Unavailable | Unavailable |
| JSP-000796 | [How many unit-distance pairs can occur between disjoint translated copies of a convex set?](catalog-0701-0800.md#JSP-000796) | Open | No | No | Unavailable | Unavailable |
| JSP-000797 | [What uniform upper bound holds for the product of the multiplicities of the shortest and longest distances in a finite point set?](catalog-0701-0800.md#JSP-000797) | Solved | No | No | Unavailable | Unavailable |
| JSP-000798 | [How large can the difference between the two largest distance multiplicities of a planar point set be?](catalog-0701-0800.md#JSP-000798) | Open | No | No | Unavailable | Unavailable |
| JSP-000799 | [If a point set determines many ordinary lines, must it have a large subset whose every joining line is ordinary in the original set?](catalog-0701-0800.md#JSP-000799) | Solved | No | No | Unavailable | Unavailable |
| JSP-000800 | [How long can a consecutive-integer interval be if each term has a prime factor larger than its length?](catalog-0701-0800.md#JSP-000800) | Open | No | No | Unavailable | Unavailable |

### Problems 801–900

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000801 | [How large a subset with all subset sums distinct must every finite real set contain?](catalog-0801-0900.md#JSP-000801) | Open | No | No | Unavailable | Unavailable |
| JSP-000802 | [What is the density of indices where a prime divided by its index exceeds the corresponding ratio at the preceding index?](catalog-0801-0900.md#JSP-000802) | Open | No | No | Unavailable | Unavailable |
| JSP-000803 | [What is the smallest possible order of the error in counting squarefree positive integers?](catalog-0801-0900.md#JSP-000803) | Open | No | No | Unavailable | Unavailable |
| JSP-000804 | [Jacobsthal's function](catalog-0801-0900.md#JSP-000804) | Open | No | No | Unavailable | Unavailable |
| JSP-000805 | [For a fixed modulus, how many coprime residue classes have an unusually large least prime?](catalog-0801-0900.md#JSP-000805) | Open | No | No | Unavailable | Unavailable |
| JSP-000806 | [For an irrational number satisfying the stated conditions, are infinitely many floors of its products with primes also prime?](catalog-0801-0900.md#JSP-000806) | Open | No | No | Unavailable | Unavailable |
| JSP-000807 | [For a complex number outside the unit circle, can sums of consecutive powers approach zero exponentially fast?](catalog-0801-0900.md#JSP-000807) | Open | No | No | Unavailable | Unavailable |
| JSP-000808 | [How fast does the average divisor count of integer values of an irreducible polynomial grow?](catalog-0801-0900.md#JSP-000808) | Open | No | No | Unavailable | Unavailable |
| JSP-000809 | [How large a prime factor must a product of consecutive integer values of an irreducible polynomial have?](catalog-0801-0900.md#JSP-000809) | Open | No | No | Unavailable | Unavailable |
| JSP-000810 | [Does the ratio of the largest prime factor of a power of two minus one to its exponent grow as predicted?](catalog-0801-0900.md#JSP-000810) | Solved | No | No | Unavailable | Unavailable |
| JSP-000811 | [Does an irreducible integer polynomial take infinitely many values free of a prescribed higher-power factor?](catalog-0801-0900.md#JSP-000811) | Open | No | No | Unavailable | Unavailable |
| JSP-000812 | [Are representation counts as sums of prime powers unbounded when the number of summands equals the exponent?](catalog-0801-0900.md#JSP-000812) | Open | No | No | Unavailable | Unavailable |
| JSP-000813 | [What is the average least prescribed power nonresidue over prime moduli?](catalog-0801-0900.md#JSP-000813) | Solved | No | No | Unavailable | Unavailable |
| JSP-000814 | [For quadratic-character partial sums, what is the average initial range needed to reach the specified relative balance, over primes?](catalog-0801-0900.md#JSP-000814) | Solved | No | No | Unavailable | Unavailable |
| JSP-000815 | [Must every convex polygon have a vertex determining about half as many distinct distances as the total number of vertices?](catalog-0801-0900.md#JSP-000815) | Open | No | No | Unavailable | Unavailable |
| JSP-000816 | [If an integer set is larger than the prime count in its range, must some collection of its elements be supported on relatively few small primes?](catalog-0801-0900.md#JSP-000816) | Open | No | No | Unavailable | Unavailable |
| JSP-000817 | [Can integers be two-colored so that every monochromatic arithmetic progression has length bounded by a very slowly growing function of its starting point?](catalog-0801-0900.md#JSP-000817) | Solved | No | No | Unavailable | Unavailable |
| JSP-000818 | [Does every prime modulus have a relatively small prime primitive root?](catalog-0801-0900.md#JSP-000818) | Open | No | No | Unavailable | Unavailable |
| JSP-000819 | [What lower bounds hold for off-diagonal clique Ramsey numbers with one target fixed and the other growing?](catalog-0801-0900.md#JSP-000819) | Solved | No | No | Unavailable | Unavailable |
| JSP-000820 | [For exponential sums from an arbitrary infinite real sequence, how much growth in partial sums is forced as frequency varies?](catalog-0801-0900.md#JSP-000820) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000821 | [As the number of spherical points grows, must discrepancies between cap counts and area predictions be unbounded?](catalog-0801-0900.md#JSP-000821) | Solved | No | No | Unavailable | Unavailable |
| JSP-000822 | [Can an infinite discrete planar set have uniformly bounded differences between disk point counts and disk areas? What is the minimum discrepancy scale?](catalog-0801-0900.md#JSP-000822) | Solved | No | No | Unavailable | Unavailable |
| JSP-000823 | [How far from uniform can the arguments of roots of a sparse polynomial be?](catalog-0801-0900.md#JSP-000823) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000824 | [Do spherical configurations maximizing the product of pairwise distances become uniformly distributed as their size grows?](catalog-0801-0900.md#JSP-000824) | Solved | No | No | Unavailable | Unavailable |
| JSP-000825 | [For typical irrational scale factors, what is the discrepancy of fractional parts of a scaled integer sequence?](catalog-0801-0900.md#JSP-000825) | Solved | No | No | Unavailable | Unavailable |
| JSP-000826 | [Is the sequence counting independent sets by size in a tree or forest unimodal?](catalog-0801-0900.md#JSP-000826) | Open | No | No | Unavailable | Unavailable |
| JSP-000827 | [Under repeated irrational rotation of a circle, does the visiting frequency of a measurable set equal its measure?](catalog-0801-0900.md#JSP-000827) | Solved | No | No | Unavailable | Unavailable |
| JSP-000828 | [For a square-integrable function sampled along dilations from a sparse integer sequence, how fast do partial sums grow for typical inputs?](catalog-0801-0900.md#JSP-000828) | Open | No | No | Unavailable | Unavailable |
| JSP-000829 | [Does sufficiently fast decay of Fourier approximation error ensure convergence of averages along the prescribed sparse sequence?](catalog-0801-0900.md#JSP-000829) | Open | No | No | Unavailable | Unavailable |
| JSP-000830 | [Can the fractional parts of primes multiplied by an irrational number satisfy the specified stronger uniform-distribution property?](catalog-0801-0900.md#JSP-000830) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000831 | [What necessary and sufficient conditions on interval endpoints give bounded counting discrepancy for an irrational rotation?](catalog-0801-0900.md#JSP-000831) | Solved | No | No | Unavailable | Unavailable |
| JSP-000832 | [Duffin-Schaeffer conjecture](catalog-0801-0900.md#JSP-000832) | Solved | No | No | Unavailable | Unavailable |
| JSP-000833 | [What limiting measure is covered by approximation intervals using rational numbers with denominators in the specified range?](catalog-0801-0900.md#JSP-000833) | Solved | No | No | Unavailable | Unavailable |
| JSP-000834 | [What limiting distribution arises from normalized cumulative centered fractional parts of an irrational rotation?](catalog-0801-0900.md#JSP-000834) | Open | No | No | Unavailable | Unavailable |
| JSP-000835 | [Are there infinitely many consecutive positive integers with equal totients?](catalog-0801-0900.md#JSP-000835) | Open | No | No | Unavailable | Unavailable |
| JSP-000836 | [How long a consecutive-integer interval can have pairwise distinct totient values?](catalog-0801-0900.md#JSP-000836) | Open | No | No | Unavailable | Unavailable |
| JSP-000837 | [How far can local Farey-sequence segments extend when numerators and denominators vary in the same direction?](catalog-0801-0900.md#JSP-000837) | Solved | No | No | Unavailable | Unavailable |
| JSP-000838 | [Can every graph without triangles or four-cycles be acyclically oriented so that reversing any single edge still leaves it acyclic?](catalog-0801-0900.md#JSP-000838) | Solved | No | No | Unavailable | Unavailable |
| JSP-000839 | [Just above the maximum bipartite edge count, how many edge-disjoint triangles are guaranteed?](catalog-0801-0900.md#JSP-000839) | Solved | No | No | Unavailable | Unavailable |
| JSP-000840 | [How many triangles must a graph have once its edge count exceeds the maximum bipartite edge count?](catalog-0801-0900.md#JSP-000840) | Solved | No | No | Unavailable | Unavailable |
| JSP-000841 | [Under a high-chromatic-number condition, how many edges force a triangle?](catalog-0801-0900.md#JSP-000841) | Open | No | No | Unavailable | Unavailable |
| JSP-000842 | [What graph density forces a cycle containing nearly all vertices?](catalog-0801-0900.md#JSP-000842) | Solved | No | No | Unavailable | Unavailable |
| JSP-000843 | [Chromatic number and minimum order of triangle-free graphs](catalog-0801-0900.md#JSP-000843) | Open | No | No | Unavailable | Unavailable |
| JSP-000844 | [With one off-diagonal Ramsey parameter fixed, does the ratio of successive values in the other parameter tend to one?](catalog-0801-0900.md#JSP-000844) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000845 | [How few vertices need remain uncovered by disjoint monochromatic cliques in an edge-colored complete graph?](catalog-0801-0900.md#JSP-000845) | Solved | No | No | Unavailable | Unavailable |
| JSP-000846 | [pancyclic graphs](catalog-0801-0900.md#JSP-000846) | Open | No | No | Unavailable | Unavailable |
| JSP-000847 | [How many cliques are needed to partition all edges of a dense graph?](catalog-0801-0900.md#JSP-000847) | Open | No | No | Unavailable | Unavailable |
| JSP-000848 | [Does superlinear edge count force a nonplanar subgraph of uniformly bounded order?](catalog-0801-0900.md#JSP-000848) | Solved | No | No | Unavailable | Unavailable |
| JSP-000849 | [Must every dense graph contain a nontrivial maximal planar subgraph?](catalog-0801-0900.md#JSP-000849) | Solved | No | No | Unavailable | Unavailable |
| JSP-000850 | [Maximum edge counts in uniform hypergraphs with bounded matchings](catalog-0801-0900.md#JSP-000850) | Open | No | No | Unavailable | Unavailable |
| JSP-000851 | [How many edges can a graph have while excluding a complete graph with every edge subdivided once?](catalog-0801-0900.md#JSP-000851) | Solved | No | No | Unavailable | Unavailable |
| JSP-000852 | [How large an independent set is guaranteed in a three-uniform hypergraph whose edges intersect pairwise in at most one vertex?](catalog-0801-0900.md#JSP-000852) | Solved | No | No | Unavailable | Unavailable |
| JSP-000853 | [How large a free set is guaranteed for the specified mapping from element pairs to sets?](catalog-0801-0900.md#JSP-000853) | Solved | No | No | Unavailable | Unavailable |
| JSP-000854 | [How many vertex subsets meet every hyperedge while containing none of them in full?](catalog-0801-0900.md#JSP-000854) | Solved | No | No | Unavailable | Unavailable |
| JSP-000855 | [Can the classical exponential lower bound for diagonal Ramsey numbers be improved by an unbounded factor?](catalog-0801-0900.md#JSP-000855) | Open | No | No | Unavailable | Unavailable |
| JSP-000856 | [Does the ratio of off-diagonal to corresponding diagonal Ramsey numbers satisfy a uniform parameter-dependent growth lower bound?](catalog-0801-0900.md#JSP-000856) | Open | No | No | Unavailable | Unavailable |
| JSP-000857 | [Must a graph with neither large cliques nor large independent sets contain a nontrivial regular induced subgraph?](catalog-0801-0900.md#JSP-000857) | Solved | No | No | Unavailable | Unavailable |
| JSP-000858 | [Can a four-chromatic-critical graph have minimum degree proportional to its order?](catalog-0801-0900.md#JSP-000858) | Open | No | No | Unavailable | Unavailable |
| JSP-000859 | [How large a sum of ambient vertex degrees is guaranteed for some triangle in a dense graph?](catalog-0801-0900.md#JSP-000859) | Open | No | No | Unavailable | Unavailable |
| JSP-000860 | [Does sufficiently high minimum degree force a spanning hypercube?](catalog-0801-0900.md#JSP-000860) | Open | No | No | Unavailable | Unavailable |
| JSP-000861 | [For a monic real-rooted polynomial, how long in total can the real intervals on which its absolute value is less than one be?](catalog-0801-0900.md#JSP-000861) | Open | No | No | Unavailable | Unavailable |
| JSP-000862 | [How large a disk can lie in the region where a polynomial has modulus at most one?](catalog-0801-0900.md#JSP-000862) | Open | No | No | Unavailable | Unavailable |
| JSP-000863 | [Under restrictions on polynomial zeros, how do the area and transfinite diameter of a modulus sublevel set relate?](catalog-0801-0900.md#JSP-000863) | Open | No | No | Unavailable | Unavailable |
| JSP-000864 | [Can two polynomial zeros be joined within its unit-modulus sublevel set by a path of uniformly bounded length?](catalog-0801-0900.md#JSP-000864) | Open | No | No | Unavailable | Unavailable |
| JSP-000865 | [How does the transfinite diameter of the zero set bound the number of components of a polynomial sublevel set?](catalog-0801-0900.md#JSP-000865) | Solved | No | No | Unavailable | Unavailable |
| JSP-000866 | [Among the allowed polynomials, how small can the maximum boundary length of their sublevel sets be?](catalog-0801-0900.md#JSP-000866) | Solved | Yes | Yes | Claimed | Unclaimed |
| JSP-000867 | [For a complex point set of fixed diameter, how large can the product of all pairwise distances be?](catalog-0801-0900.md#JSP-000867) | Open | No | No | Unavailable | Unavailable |
| JSP-000868 | [If a polynomial's unit-modulus sublevel set is connected, must it lie in a disk of radius two?](catalog-0801-0900.md#JSP-000868) | Solved | No | No | Unavailable | Unavailable |
| JSP-000869 | [Under the stated conditions, is the reciprocal sum of powers of a rational number minus one irrational?](catalog-0801-0900.md#JSP-000869) | Open | No | No | Unavailable | Unavailable |
| JSP-000870 | [Is the series of reciprocals of powers of two minus three irrational?](catalog-0801-0900.md#JSP-000870) | Solved | No | No | Unavailable | Unavailable |
| JSP-000871 | [For a doubly exponentially growing integer sequence, is the reciprocal sum of consecutive-term products irrational?](catalog-0801-0900.md#JSP-000871) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000872 | [unitary perfect numbers](catalog-0801-0900.md#JSP-000872) | Open | No | No | Unavailable | Unavailable |
| JSP-000873 | [multiply perfect numbers](catalog-0801-0900.md#JSP-000873) | Open | No | No | Unavailable | Unavailable |
| JSP-000874 | [How can a target integer be represented as the sum of an initial segment of another integer's ordered nontrivial divisors?](catalog-0801-0900.md#JSP-000874) | Open | No | No | Unavailable | Unavailable |
| JSP-000875 | [How many primes lie in each recursively defined level determined by prime divisors of a prime plus one?](catalog-0801-0900.md#JSP-000875) | Open | No | No | Unavailable | Unavailable |
| JSP-000876 | [Can several consecutive integer intervals each have product congruent to one modulo the same prime?](catalog-0801-0900.md#JSP-000876) | Open | No | No | Unavailable | Unavailable |
| JSP-000877 | [Carmichael numbers](catalog-0801-0900.md#JSP-000877) | Open | No | No | Unavailable | Unavailable |
| JSP-000878 | [Are there only finitely many factorials plus one supported on the specified next two primes?](catalog-0801-0900.md#JSP-000878) | Solved | No | No | Unavailable | Unavailable |
| JSP-000879 | [Is there a prime whose difference from every permitted smaller factorial is composite?](catalog-0801-0900.md#JSP-000879) | Open | No | No | Unavailable | Unavailable |
| JSP-000880 | [How many integers can have a prescribed value of the integer times its divisor sum?](catalog-0801-0900.md#JSP-000880) | Open | No | No | Unavailable | Unavailable |
| JSP-000881 | [How many integer solutions satisfy the specified additive equation involving the sum-of-divisors function?](catalog-0801-0900.md#JSP-000881) | Open | No | No | Unavailable | Unavailable |
| JSP-000882 | [How large can an integer-interval subset be if no element divides two other elements?](catalog-0801-0900.md#JSP-000882) | Open | No | No | Unavailable | Unavailable |
| JSP-000883 | [Which starting points permit a binomial coefficient to be divisible by all but one term of the specified descending consecutive-integer block?](catalog-0801-0900.md#JSP-000883) | Open | No | No | Unavailable | Unavailable |
| JSP-000884 | [How does an integer's totient compare with the totient of the integer minus its totient?](catalog-0801-0900.md#JSP-000884) | Solved | No | No | Unavailable | Unavailable |
| JSP-000885 | [Are there infinitely many primes that are one more than a power of two times another prime?](catalog-0801-0900.md#JSP-000885) | Open | No | No | Unavailable | Unavailable |
| JSP-000886 | [For a planar point set of minimum separation one, how large an independent set must its unit-distance graph have?](catalog-0801-0900.md#JSP-000886) | Open | No | No | Unavailable | Unavailable |
| JSP-000887 | [Must a graph of uncountable chromatic number contain a countable subgraph that remains connected after every finite vertex deletion?](catalog-0801-0900.md#JSP-000887) | Open | No | No | Unavailable | Unavailable |
| JSP-000888 | [How many lines can contain at least a prescribed number of points of a finite planar set?](catalog-0801-0900.md#JSP-000888) | Solved | No | No | Unavailable | Unavailable |
| JSP-000889 | [What proportion of every finite planar point set can be selected with no pair at unit distance?](catalog-0801-0900.md#JSP-000889) | Open | No | No | Unavailable | Unavailable |
| JSP-000890 | [Can a maximal family of pairwise disjoint unit segments in the specified planar region be finite or countable?](catalog-0801-0900.md#JSP-000890) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000891 | [How small can the first factorial index congruent to minus one modulo a prime be?](catalog-0801-0900.md#JSP-000891) | Open | No | No | Unavailable | Unavailable |
| JSP-000892 | [How many composite integers divide some factorial plus one, and how are they distributed?](catalog-0801-0900.md#JSP-000892) | Open | No | No | Unavailable | Unavailable |
| JSP-000893 | [What is the density of cases where prime factors of a factorial plus one fail the specified congruence relation?](catalog-0801-0900.md#JSP-000893) | Open | No | No | Unavailable | Unavailable |
| JSP-000894 | [Does exceeding the complete multipartite construction's edge density force a uniform hypergraph to have a noticeably denser local subgraph?](catalog-0801-0900.md#JSP-000894) | Open | No | No | Unavailable | Unavailable |
| JSP-000895 | [How many edges can a three-uniform hypergraph have while excluding configurations with a prescribed vertex count and two fewer edges?](catalog-0801-0900.md#JSP-000895) | Solved | No | No | Unavailable | Unavailable |
| JSP-000896 | [What minimum degree forces a transversal clique in a balanced multipartite graph?](catalog-0801-0900.md#JSP-000896) | Solved | No | No | Unavailable | Unavailable |
| JSP-000897 | [At the corresponding Turán edge threshold, must some vertex neighborhood contain sufficiently many edges?](catalog-0801-0900.md#JSP-000897) | Solved | No | No | Unavailable | Unavailable |
| JSP-000898 | [What is the precise asymptotic count of integers representable as sums of two powerful numbers?](catalog-0801-0900.md#JSP-000898) | Solved | No | No | Unavailable | Unavailable |
| JSP-000899 | [Must a planar set with no three collinear points determine at least half as many distinct distances as points?](catalog-0801-0900.md#JSP-000899) | Open | No | No | Unavailable | Unavailable |
| JSP-000900 | [What is the minimum distinct-distance count for a prescribed number of points in fixed higher dimension?](catalog-0801-0900.md#JSP-000900) | Open | No | No | Unavailable | Unavailable |

### Problems 901–1000

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000901 | [contact number problem](catalog-0901-1000.md#JSP-000901) | Open | No | No | Unavailable | Unavailable |
| JSP-000902 | [How many unit-distance pairs can a finite point set in the specified higher-dimensional space have?](catalog-0901-1000.md#JSP-000902) | Open | No | No | Unavailable | Unavailable |
| JSP-000903 | [How many triangles of the same area can a finite planar point set determine?](catalog-0901-1000.md#JSP-000903) | Open | No | No | Unavailable | Unavailable |
| JSP-000904 | [How many four-point subsets of a finite point set can have a repeated distance?](catalog-0901-1000.md#JSP-000904) | Open | No | No | Unavailable | Unavailable |
| JSP-000905 | [How many points in higher dimensions force a prescribed-size subset with all pairwise distances distinct?](catalog-0901-1000.md#JSP-000905) | Open | No | No | Unavailable | Unavailable |
| JSP-000906 | [In fixed dimension, how many points force a prescribed number of distinct distances?](catalog-0901-1000.md#JSP-000906) | Solved | No | No | Unavailable | Unavailable |
| JSP-000907 | [Must every four-chromatic graph contain an odd cycle with the prescribed number of chords?](catalog-0901-1000.md#JSP-000907) | Solved | No | No | Unavailable | Unavailable |
| JSP-000908 | [If a binomial coefficient has no small prime factors, how many smooth terms must be absent from its corresponding consecutive-integer block?](catalog-0901-1000.md#JSP-000908) | Open | No | No | Unavailable | Unavailable |
| JSP-000909 | [Can the least prime factor of a binomial coefficient be bounded by a uniform function of its two parameters?](catalog-0901-1000.md#JSP-000909) | Open | No | No | Unavailable | Unavailable |
| JSP-000910 | [How large must the upper parameter be for a binomial coefficient to have no prime factor smaller than its lower parameter?](catalog-0901-1000.md#JSP-000910) | Open | No | No | Unavailable | Unavailable |
| JSP-000911 | [How many distinct common differences can three-term arithmetic progressions in a finite integer set have?](catalog-0901-1000.md#JSP-000911) | Open | No | No | Unavailable | Unavailable |
| JSP-000912 | [What bounds hold for the sum of prescribed powers of consecutive divisor ratios minus one?](catalog-0901-1000.md#JSP-000912) | Solved | No | No | Unavailable | Unavailable |
| JSP-000913 | [How many consecutive ordered divisor pairs are coprime, and how does this count grow?](catalog-0901-1000.md#JSP-000913) | Open | No | No | Unavailable | Unavailable |
| JSP-000914 | [Can a pairwise coprime integer sequence leave relatively small gaps after all its multiples are excluded?](catalog-0901-1000.md#JSP-000914) | Open | No | No | Unavailable | Unavailable |
| JSP-000915 | [Is there an infinite integer sequence with every pairwise sum squarefree, and how slowly can it grow?](catalog-0901-1000.md#JSP-000915) | Open | No | No | Unavailable | Unavailable |
| JSP-000916 | [How many edge colors can be used while avoiding the specified rainbow cycle or path?](catalog-0901-1000.md#JSP-000916) | Solved | No | No | Unavailable | Unavailable |
| JSP-000917 | [How many distinct prime factors occur among a sequence of integer partition numbers?](catalog-0901-1000.md#JSP-000917) | Open | No | No | Unavailable | Unavailable |
| JSP-000918 | [For each prescribed order, is every sufficiently large integer a sum of one more than that order many integers whose prime-factor exponents are all at least that order?](catalog-0901-1000.md#JSP-000918) | Open | No | No | Unavailable | Unavailable |
| JSP-000919 | [Under the stated restrictions, are only finitely many sums of distinct factorials perfect powers or powerful numbers?](catalog-0901-1000.md#JSP-000919) | Open | No | No | Unavailable | Unavailable |
| JSP-000920 | [How large can an integer-interval subset be if every pairwise sum is nonsquarefree?](catalog-0901-1000.md#JSP-000920) | Open | No | No | Unavailable | Unavailable |
| JSP-000921 | [Which integers are sums of products of powers of two fixed bases when no chosen summand may divide another?](catalog-0901-1000.md#JSP-000921) | Open | No | No | Unavailable | Unavailable |
| JSP-000922 | [Does high chromatic number and small clique number force two anticomplete vertex subsets each of high chromatic number?](catalog-0901-1000.md#JSP-000922) | Open | No | No | Unavailable | Unavailable |
| JSP-000923 | [Can an integer sequence with bounded gaps have an iterated sumset entirely avoiding the prescribed sparse integer set?](catalog-0901-1000.md#JSP-000923) | Open | No | No | Unavailable | Unavailable |
| JSP-000924 | [Sierpinski numbers](catalog-0901-1000.md#JSP-000924) | Open | No | No | Unavailable | Unavailable |
| JSP-000925 | [For a real-rooted polynomial with equally spaced zeros, do gaps between consecutive derivative zeros satisfy the specified monotonicity?](catalog-0901-1000.md#JSP-000925) | Solved | No | No | Unavailable | Unavailable |
| JSP-000926 | [How short can a path to infinity be along which a given entire function tends to infinity?](catalog-0901-1000.md#JSP-000926) | Solved | No | No | Unavailable | Unavailable |
| JSP-000927 | [Under the stated conditions, can a meromorphic function's counts of taking two distinct values have arbitrarily extreme ratios?](catalog-0901-1000.md#JSP-000927) | Solved | No | No | Unavailable | Unavailable |
| JSP-000928 | [At how many points of one circle can an entire function attain its maximum modulus?](catalog-0901-1000.md#JSP-000928) | Open | No | No | Unavailable | Unavailable |
| JSP-000929 | [How fast must an entire function grow if the region above a prescribed modulus threshold has finite area?](catalog-0901-1000.md#JSP-000929) | Solved | No | No | Unavailable | Unavailable |
| JSP-000930 | [How large can a family of entire functions be if the number of possible values at each point is restricted?](catalog-0901-1000.md#JSP-000930) | Solved | No | No | Unavailable | Unavailable |
| JSP-000931 | [Within the specified polynomial modulus region, how short a path joins the origin to the unit circle?](catalog-0901-1000.md#JSP-000931) | Open | No | No | Unavailable | Unavailable |
| JSP-000932 | [If an additive arithmetic function is nondecreasing outside a zero-density exception set, must it be a constant multiple of the logarithm?](catalog-0901-1000.md#JSP-000932) | Open | No | No | Unavailable | Unavailable |
| JSP-000933 | [Are the Boolean algebras of integer sets modulo zero natural density and modulo zero logarithmic density isomorphic?](catalog-0901-1000.md#JSP-000933) | Solved | No | No | Unavailable | Unavailable |
| JSP-000934 | [Can a square and a disk of equal area be partitioned into finitely many pieces and reassembled into each other using the prescribed rigid motions?](catalog-0901-1000.md#JSP-000934) | Solved | No | No | Unavailable | Unavailable |
| JSP-000935 | [Can Euclidean space be partitioned into countably many sets each having all pairwise distances distinct?](catalog-0901-1000.md#JSP-000935) | Solved | No | No | Unavailable | Unavailable |
| JSP-000936 | [Which Lagrange interpolation nodes minimize the maximum amplification of input errors?](catalog-0901-1000.md#JSP-000936) | Solved | No | No | Unavailable | Unavailable |
| JSP-000937 | [Which interpolation nodes maximize the smallest peak error-amplification factor among intervals between consecutive nodes?](catalog-0901-1000.md#JSP-000937) | Solved | No | No | Unavailable | Unavailable |
| JSP-000938 | [What is the minimum sum of squared integrals of the Lagrange basis functions?](catalog-0901-1000.md#JSP-000938) | Open | No | No | Unavailable | Unavailable |
| JSP-000939 | [For interpolation built from successive initial segments of an infinite node sequence, what lower bound must the amplification factor satisfy at a fixed point?](catalog-0901-1000.md#JSP-000939) | Open | No | No | Unavailable | Unavailable |
| JSP-000940 | [Even allowing degree slightly above the minimum, can bounded interpolation data force every interpolating polynomial to have large amplitude?](catalog-0901-1000.md#JSP-000940) | Open | No | No | Unavailable | Unavailable |
| JSP-000941 | [Does repeatedly halving even integers and replacing odd integers by three times the integer plus one always reach one?](catalog-0901-1000.md#JSP-000941) | Open | No | No | Unavailable | Unavailable |
| JSP-000942 | [What is the limiting ratio of the product of consecutive prime gaps to the square of the specified maximum gap?](catalog-0901-1000.md#JSP-000942) | Open | No | No | Unavailable | Unavailable |
| JSP-000943 | [How are prime counts and local distributions governed in intervals comparable in length to the largest prime gap?](catalog-0901-1000.md#JSP-000943) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000944 | [Among integers with at most two prime factors, are normalized consecutive gaps unbounded?](catalog-0901-1000.md#JSP-000944) | Open | No | No | Unavailable | Unavailable |
| JSP-000945 | [Is there an integer whose differences from twice every permitted smaller square are all prime?](catalog-0901-1000.md#JSP-000945) | Solved | No | No | Unavailable | Unavailable |
| JSP-000946 | [Is there an integer whose differences from every sufficiently small square coprime to it are all prime?](catalog-0901-1000.md#JSP-000946) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000947 | [Is there an integer whose differences from every permitted smaller power of two are all prime?](catalog-0901-1000.md#JSP-000947) | Open | No | No | Unavailable | Unavailable |
| JSP-000948 | [How many multiples of primes from a specified set are guaranteed in every given short integer interval?](catalog-0901-1000.md#JSP-000948) | Open | No | No | Unavailable | Unavailable |
| JSP-000949 | [Do partial sums of a random completely multiplicative function infinitely often exceed every fixed multiple of the square root of the summation range?](catalog-0901-1000.md#JSP-000949) | Open | No | No | Unavailable | Unavailable |
| JSP-000950 | [If two complementary additive sets have asymptotically equal growth, must their cross-sum representation counts be unbounded?](catalog-0901-1000.md#JSP-000950) | Open | No | No | Unavailable | Unavailable |
| JSP-000951 | [Does adding the integers generated by powers of two and three always strictly increase another integer set's Schnirelmann density?](catalog-0901-1000.md#JSP-000951) | Open | No | No | Unavailable | Unavailable |
| JSP-000952 | [For a fixed irrational number, do integers whose squared multiples of it lie close to integers form an asymptotic basis of order two?](catalog-0901-1000.md#JSP-000952) | Solved | No | No | Unavailable | Unavailable |
| JSP-000953 | [Is every sufficiently large integer a sum of two squares minus a third square, with each square at most the original integer?](catalog-0901-1000.md#JSP-000953) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000954 | [What is the density of integers coprime to the floor of a fixed nonintegral power of themselves?](catalog-0901-1000.md#JSP-000954) | Solved | No | No | Unavailable | Unavailable |
| JSP-000955 | [For sign-coefficient polynomials, must the maximum modulus on the unit circle exceed the square root of the number of terms by a fixed proportion?](catalog-0901-1000.md#JSP-000955) | Open | No | No | Unavailable | Unavailable |
| JSP-000956 | [With Chebyshev interpolation nodes, can all limit points of the interpolation sequence at the specified positions be prescribed?](catalog-0901-1000.md#JSP-000956) | Open | No | No | Unavailable | Unavailable |
| JSP-000957 | [Can a slight increase in interpolation degree avoid almost-everywhere divergence for continuous functions?](catalog-0901-1000.md#JSP-000957) | Open | No | No | Unavailable | Unavailable |
| JSP-000958 | [For every choice of interpolation nodes, must error amplification on each fixed subinterval grow at least logarithmically?](catalog-0901-1000.md#JSP-000958) | Solved | No | No | Unavailable | Unavailable |
| JSP-000959 | [Can subrings or subfields of the reals have any prescribed Hausdorff dimension strictly between zero and one?](catalog-0901-1000.md#JSP-000959) | Open | No | No | Unavailable | Unavailable |
| JSP-000960 | [After repeatedly choosing random triangles and deleting their edges, how many graph edges remain and what structure results?](catalog-0901-1000.md#JSP-000960) | Open | No | No | Unavailable | Unavailable |
| JSP-000961 | [How narrow an integer range typically contains the chromatic number of a random graph?](catalog-0901-1000.md#JSP-000961) | Open | No | No | Unavailable | Unavailable |
| JSP-000962 | [How many hyperedges remain possible after forbidding all local configurations with prescribed vertex and edge counts?](catalog-0901-1000.md#JSP-000962) | Open | No | No | Unavailable | Unavailable |
| JSP-000963 | [What extremal lower bounds can be constructed for uniform hypergraphs excluding a prescribed complete multipartite hypergraph?](catalog-0901-1000.md#JSP-000963) | Open | No | No | Unavailable | Unavailable |
| JSP-000964 | [Does a finite projective plane have a blocking set meeting every line in a uniformly bounded number of points?](catalog-0901-1000.md#JSP-000964) | Open | No | No | Unavailable | Unavailable |
| JSP-000965 | [Among group orders up to a bound, is the greatest number of nonisomorphic groups attained at a power-of-two order?](catalog-0901-1000.md#JSP-000965) | Open | No | No | Unavailable | Unavailable |
| JSP-000966 | [Which element order is shared by the most permutations in a symmetric group?](catalog-0901-1000.md#JSP-000966) | Solved | No | No | Unavailable | Unavailable |
| JSP-000967 | [How many subgroups does a symmetric group have, and how are their orders distributed?](catalog-0901-1000.md#JSP-000967) | Open | No | No | Unavailable | Unavailable |
| JSP-000968 | [ambiguous statement](catalog-0901-1000.md#JSP-000968) | Open | No | No | Unavailable | Unavailable |
| JSP-000969 | [How fast does the radius of a disk whose lattice points have all been visited by a planar random walk grow with the number of steps?](catalog-0901-1000.md#JSP-000969) | Solved | No | No | Unavailable | Unavailable |
| JSP-000970 | [What is the probability that multiple sites tie for most visited in a planar random walk?](catalog-0901-1000.md#JSP-000970) | Solved | No | No | Unavailable | Unavailable |
| JSP-000971 | [How many distinct sites have ever been most visited during a planar random walk?](catalog-0901-1000.md#JSP-000971) | Solved | No | No | Unavailable | Unavailable |
| JSP-000972 | [Does a partition relation for an infinite cardinal imply a corresponding relation for smaller subset sizes?](catalog-0901-1000.md#JSP-000972) | Open | No | No | Unavailable | Unavailable |
| JSP-000973 | [Can the specified negative partition relations at successors of singular cardinals be proved without the generalized continuum hypothesis?](catalog-0901-1000.md#JSP-000973) | Open | No | No | Unavailable | Unavailable |
| JSP-000974 | [Can pairs on the ordinal square of the first uncountable ordinal be two-colored to avoid the specified monochromatic order types?](catalog-0901-1000.md#JSP-000974) | Open | No | No | Unavailable | Unavailable |
| JSP-000975 | [Is the specified two-color partition property of the second uncountable ordinal for all smaller order types consistent with the usual set-theoretic axioms?](catalog-0901-1000.md#JSP-000975) | Open | No | No | Unavailable | Unavailable |
| JSP-000976 | [Which monochromatic triangles or order types are forced by multicolorings on the ordinal square of the first uncountable ordinal?](catalog-0901-1000.md#JSP-000976) | Open | No | No | Unavailable | Unavailable |
| JSP-000977 | [Under the generalized continuum hypothesis, which specified partition relations hold at higher uncountable ordinals?](catalog-0901-1000.md#JSP-000977) | Open | No | No | Unavailable | Unavailable |
| JSP-000978 | [At a successor of a singular cardinal, do the specified intersection restrictions on a set mapping force a sufficiently large free set?](catalog-0901-1000.md#JSP-000978) | Open | No | No | Unavailable | Unavailable |
| JSP-000979 | [Can graphs exclude a large clique while forcing a prescribed smaller monochromatic clique under every countable coloring?](catalog-0901-1000.md#JSP-000979) | Open | No | No | Unavailable | Unavailable |
| JSP-000980 | [Does sufficiently high chromatic number force a triangle-free subgraph whose chromatic number reaches a prescribed uncountable cardinal?](catalog-0901-1000.md#JSP-000980) | Open | No | No | Unavailable | Unavailable |
| JSP-000981 | [Can edges of an uncountable-chromatic graph be colored so that every prescribed vertex coloring has a color class realizing all edge colors?](catalog-0901-1000.md#JSP-000981) | Open | No | No | Unavailable | Unavailable |
| JSP-000982 | [When does forbidding a finite three-uniform hypergraph still allow hypergraphs of uncountable chromatic number?](catalog-0901-1000.md#JSP-000982) | Open | No | No | Unavailable | Unavailable |
| JSP-000983 | [What vertex threshold for forbidden uniform-hypergraph configurations forces a subquadratic extremal edge count?](catalog-0901-1000.md#JSP-000983) | Open | No | No | Unavailable | Unavailable |
| JSP-000984 | [How many random elements of a finite abelian group make subset-sum representation counts approximately uniform?](catalog-0901-1000.md#JSP-000984) | Solved | No | No | Unavailable | Unavailable |
| JSP-000985 | [Do boundedly many sums of modular inverses of a short initial integer interval cover all residues modulo a prime?](catalog-0901-1000.md#JSP-000985) | Solved | No | No | Unavailable | Unavailable |
| JSP-000986 | [How large is the smallest prime not dividing the product of a logarithmically short consecutive-integer interval?](catalog-0901-1000.md#JSP-000986) | Open | No | No | Unavailable | Unavailable |
| JSP-000987 | [If a connected graph's Ramsey number against a triangle is twice its order minus one, what edge counts are possible?](catalog-0901-1000.md#JSP-000987) | Open | No | No | Unavailable | Unavailable |
| JSP-000988 | [Does every two-coloring of the power set contain a large monochromatic family closed under unions and intersections?](catalog-0901-1000.md#JSP-000988) | Open | No | No | Unavailable | Unavailable |
| JSP-000989 | [What proportion of integers in a short interval must, or typically do, have a large prime factor?](catalog-0901-1000.md#JSP-000989) | Open | No | No | Unavailable | Unavailable |
| JSP-000990 | [Can long arithmetic progressions in dense integer sets be required to have common difference in another specified set's difference set?](catalog-0901-1000.md#JSP-000990) | Solved | No | No | Unavailable | Unavailable |
| JSP-000991 | [What is the minimum number of monochromatic arithmetic progressions of prescribed length in a two-colored integer interval?](catalog-0901-1000.md#JSP-000991) | Open | No | No | Unavailable | Unavailable |
| JSP-000992 | [Does every finite coloring of the positive integers contain the specified monochromatic progression of primes or a monochromatic progression with prime common difference?](catalog-0901-1000.md#JSP-000992) | Solved | No | No | Unavailable | Unavailable |
| JSP-000993 | [With bounded moduli, how many irredundant distinct covering systems exist?](catalog-0901-1000.md#JSP-000993) | Open | No | No | Unavailable | Unavailable |
| JSP-000994 | [How many modulus sets support irreducible coverings, and what size restrictions must they satisfy?](catalog-0901-1000.md#JSP-000994) | Open | No | No | Unavailable | Unavailable |
| JSP-000995 | [How large can the reciprocal sum of large moduli be when their residue classes are pairwise disjoint?](catalog-0901-1000.md#JSP-000995) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000996 | [Can the square-root density restriction for infinite Sidon sets be strengthened by the predicted logarithmic correction?](catalog-0901-1000.md#JSP-000996) | Open | No | No | Unavailable | Unavailable |
| JSP-000997 | [Can the mean square of representation counts in an additive basis remain bounded?](catalog-0901-1000.md#JSP-000997) | Open | No | No | Unavailable | Unavailable |
| JSP-000998 | [How large a density can integers have on which additive representation counts equal a prescribed positive monotone function?](catalog-0901-1000.md#JSP-000998) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-000999 | [How fast must an integer set grow if each positive integer has exactly one representation as a difference of two of its elements?](catalog-0901-1000.md#JSP-000999) | Open | No | No | Unavailable | Unavailable |
| JSP-001000 | [How fast can the measure of a real set grow if no ratio of distinct elements is an integer?](catalog-0901-1000.md#JSP-001000) | Solved | No | No | Unavailable | Unavailable |

### Problems 1001–1022

| No. | Problem | Current status | Lean proof | Eligible to claim | Solver claim status | Lean claim status |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-001001 | [How large can the sum of reciprocal integer-logarithm weights be over a primitive set of large integers?](catalog-1001-1022.md#JSP-001001) | Solved | Yes | Yes | Claimed | Unclaimed |
| JSP-001002 | [Can integer dilates of a positive-measure real set cover all sufficiently distant lattice points along almost every prescribed ray?](catalog-1001-1022.md#JSP-001002) | Solved | Yes | Yes | Unclaimed | Unclaimed |
| JSP-001003 | [Does every two-coloring of the positive integers contain an infinite set with all the specified mixed sum-product structures monochromatic?](catalog-1001-1022.md#JSP-001003) | Solved | No | No | Unavailable | Unavailable |
| JSP-001004 | [Does every two-coloring of the natural numbers contain an infinite set whose specified pairwise sums all have one color?](catalog-1001-1022.md#JSP-001004) | Open | No | No | Unavailable | Unavailable |
| JSP-001005 | [Can prime residue classes with bounded reciprocal sum of moduli still cover a long initial integer interval?](catalog-1001-1022.md#JSP-001005) | Open | No | No | Unavailable | Unavailable |
| JSP-001006 | [Does a consecutive-integer product typically have a prime factor comparable to the interval's location?](catalog-1001-1022.md#JSP-001006) | Open | No | No | Unavailable | Unavailable |
| JSP-001007 | [How many integers can simultaneously avoid about half the residue classes modulo each of several primes?](catalog-1001-1022.md#JSP-001007) | Solved | No | No | Unavailable | Unavailable |
| JSP-001008 | [Must the maximum distance-weighted distinct-prime-factor count among positions following an integer tend to infinity?](catalog-1001-1022.md#JSP-001008) | Open | No | No | Unavailable | Unavailable |
| JSP-001009 | [How small can the span and average position of admissible prime tuples be?](catalog-1001-1022.md#JSP-001009) | Open | No | No | Unavailable | Unavailable |
| JSP-001010 | [Choosing one residue class for each permitted modulus, what minimum coverage multiplicity can be achieved throughout the specified integer interval?](catalog-1001-1022.md#JSP-001010) | Solved | No | No | Unavailable | Unavailable |
| JSP-001011 | [Must every collection of cubes contain a Sidon subset of fixed positive proportion?](catalog-1001-1022.md#JSP-001011) | Open | No | No | Unavailable | Unavailable |
| JSP-001012 | [How large a subset with no isosceles triangle must every finite higher-dimensional point set contain?](catalog-1001-1022.md#JSP-001012) | Open | No | No | Unavailable | Unavailable |
| JSP-001013 | [In fixed dimension, how large a subset with all pairwise distances distinct must every finite point set contain?](catalog-1001-1022.md#JSP-001013) | Open | No | No | Unavailable | Unavailable |
| JSP-001014 | [Can a rapidly growing integer sequence admit infinitely many integer shifts making all its terms prime?](catalog-1001-1022.md#JSP-001014) | Open | No | No | Unavailable | Unavailable |
| JSP-001015 | [For pairwise coprime integers in an interval, how large can the reciprocal sum of their distances to the endpoint be?](catalog-1001-1022.md#JSP-001015) | Open | No | No | Unavailable | Unavailable |
| JSP-001016 | [In every partition of the natural numbers into two parts, must one part's finite subset sums have a uniform positive lower logarithmic density?](catalog-1001-1022.md#JSP-001016) | Solved | No | No | Unavailable | Unavailable |
| JSP-001017 | [In the lattice graph of coprime coordinate pairs, is there an infinite path avoiding every point with both coordinates prime?](catalog-1001-1022.md#JSP-001017) | Open | No | No | Unavailable | Unavailable |
| JSP-001018 | [Must every sufficiently long integer sequence with bounded gaps have two distinct consecutive blocks with equal sums?](catalog-1001-1022.md#JSP-001018) | Solved | No | No | Unavailable | Unavailable |
| JSP-001019 | [If corresponding powers of two bases minus one always have identical prime-factor sets, must the bases be equal?](catalog-1001-1022.md#JSP-001019) | Solved | No | No | Unavailable | Unavailable |
| JSP-001020 | [For a polynomial whose zeros all lie on the unit circle, is there a uniformly bounded-length path in the specified modulus region?](catalog-1001-1022.md#JSP-001020) | Solved | No | No | Unavailable | Unavailable |
| JSP-001021 | [How large a transitive subtournament must every tournament of prescribed order contain?](catalog-1001-1022.md#JSP-001021) | Solved | No | No | Unavailable | Unavailable |
| JSP-001022 | [Must every integer set of positive lower logarithmic density contain an infinite divisibility chain, with controlled growth?](catalog-1001-1022.md#JSP-001022) | Solved | No | No | Unavailable | Unavailable |
