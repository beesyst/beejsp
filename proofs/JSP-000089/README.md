# JSP-000089 — Iteration 5 complete Lean proof

Status: **principal proof complete; independent Iteration 6 verification remains pending.**

`Principal.lean` proves `JSP000089.jsp_000089_complete : JSP000089.jsp_000089_statement`, preserving the exact statement in `Statement.lean`. It combines the completed graph spectrum and sparse-set construction with the short-cycle branch, using `S = sourceLemma43Set ∪ sourceShortCycleLengths`. The explicit `SourceSparsity099` estimate and the conclusion for every finite simple graph of average degree at least ten are both proved.

The source statement, provenance, earlier risks and statement-fidelity evidence are recorded in [STATEMENT.md](STATEMENT.md) and [EVIDENCE.md](EVIDENCE.md). Those inherited documents contain historical progress notes; the completion status and final declaration are recorded here. Build and preliminary axiom checks support proof completion, without claiming independent verification or official acceptance.

## Source reconciliation (Iteration 5)

The authoritative source for the Verstraëte route is the local final Journal
of Graph Theory Version of Record,
`.local-source/verstraete-2005-jgt-version-of-record.pdf` (SHA-256
`bb7e48cc2cfb0c0c5554bf3fc8b394c17ab6df966b521bb844b7d0584762b2e2`).
`.local-source/ucycles.pdf` is an earlier manuscript retained only for
comparison. Its Lemma 3.8 girth/K4 issue and Lemma 4.2 `S(n,k) ⊂ [n]` wording
are not defects of the Version of Record: published Lemma 3.8 has no girth
hypothesis, and published Lemma 4.2 states `S(n,k) ⊂ [2n]`.

The final Section 3 has a separate, genuine proof gap. In Lemma 3.7 the
chosen crossing chords `fᵢ` are not shown to have an endpoint in `Z`. Thus the
claims that `C + {fᵢ}` is a rooted truncation and that `C + {eᵢ, fᵢ}` is a
rooted mesh do not follow from the published rootedness definition. This is a
new BeeJSP source audit finding, not a correction copied from the manuscript.

## Reproduce

From this directory, with network access only if Lake has not already fetched
the pinned dependencies:

```bash
lake build
lake env lean Principal.lean
lake env lean Statement.lean
lake env lean Audit.lean
```

`lean-toolchain` pins Lean `v4.19.0`. `lake-manifest.json` pins Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; the remaining manifest entries
are Mathlib's pinned transitive build dependencies. No local patch or parent
Python state is needed.

## Boundary and non-claim

`Main.lean` proves `hasCycleLengthIn_iff_filter_nonempty` and
`hasCycleLengthIn_sourceShortCycleLengths_of_girth_le`.

| Source step                                                | Lean declaration                                          |
| ---------------------------------------------------------- | --------------------------------------------------------- |
| cycle lengths `C(G)`                                       | `IsCycleLength` and `cycleLengths`                        |
| short-cycle branch after including `[2^120]` in `S`        | `hasCycleLengthIn_sourceShortCycleLengths_of_girth_le`    |
| finite-prefix contribution to the source sparsity estimate | `sourceSparsity099_sourceShortCycleLengths`               |
| collision-free counting step in source Lemma 4.1           | `le_card_additiveSumset_of_pairSumsInjective`              |
| finite collision count implies a valid selected pair       | `sourceLemma41_selection_conclusion_of_colliding_card_lt`  |
| exact fixed-witness and total collision bounds             | `card_sourceLemma41CollidingSelections_le_collision_bound` |
| complete finite-counting source Lemma 4.1                  | `sourceLemma41_complete`                                   |
| reduced finite family in source Lemma 4.2                  | `sourceLemma42ReducedPairs`                                |
| large-pair-to-reduced-pair bridge                          | `sourceLemma42_largePairs_hit_of_hitsReducedPairs`         |
| bounded candidate-counting bridge                          | `sourceLemma42_of_bad_card_lt`                             |

Repaired range-contained source Lemma 4.2 is complete: `sourceLemma42_rangeContained_repaired` formalizes semantic hitting and `sourceLemma42_finalBudget_quantitative_bound` formalizes its quantitative budget with fixed constant `68`. Source Lemma 4.3, including its quantitative `SourceSparsity099 sourceLemma43Set` bound, is complete; the sparse side is complete. In source Lemma 3.6's decreasing Case-B branch, the concrete `C′` and the reindexed source Section-2 `k`-ladder `H` are now certified. The unrooted Lemma-3.7 Branch-I certificate and the five-way Branch-II assembly are now proved; their quantitative Section-2 spectrum conversion and unified longest-cycle-bounded consequence are complete below. The Branch-II shadow analysis is viable: outside-region crossed rungs can use distinct component labels, and the inside-region `1 : 3` case may use an unrooted same-side chord with its K4 label. The earlier nested-K4 example in `EVIDENCE.md` is only a shadow-level obstruction to an unnecessarily strong root-incident lift; it is not a full Lemma-3.9 no-go. The full JSP proof and final sparse hitting-set integration are complete in Principal.lean; independent verification remains pending. There are no exploratory placeholders, `sorry`, `admit`, or custom axioms in this project.

## Direct-net spectrum milestone

`sourceLemma39_direct_net_cycle_spectrum_complete` proves the direct Branch-II shadow/net spectrum alternative for every `k ≥ 1`: two finite sets of positive integers, each of cardinality at least `k`, whose every pair sum is an actual cycle length in `G`. The proof follows Version of Record Section 2 Lemma 2.2, using the existing reduced ambient net with `k² + 1` attachments per hub and `k² − 1` common interior candidates. It constructs both rail/hub route variants, reverses the right attachment indexing, and uses one ambient cycle-replacement proof for all four combinations.

This theorem supplies a cycle spectrum; it does not certify a literal ambient `k²`-net. Literal source Lemma 3.9 remains separate; its quantitative consequence and the principal JSP theorem are complete below. `Audit.lean` checks the axioms of all declarations added for this spectrum milestone.

## Lemma-3.9 branch assembly milestone

`sourceLemma39_direct_crossladder_normalized_complete` converts the existing direct decomposition to `∃ (r' : V) (D : G.Walk r' r'), Nonempty (SourceLemma39AmbientCrossladder G D k)`. The constructed cycle `D` retains the two source rails, the `k` middle physical rung paths and the physical crossing path `Q`. Directed-subpath membership follows from the actual order on `D`; its recorded end arcs contain the required crossing endpoints. This conversion does not identify `D` with the original cycle `C` and does not impose attachment-length inequalities on a crossladder.

`SourceLemma39AmbientOrSpectrum` is a proof-local Prop-valued inductive with four alternatives: a proper ambient `k`-truncation on `C`, an ambient `k`-crossladder on `C`, an ambient `k`-crossladder on a constructed cycle, or positive finite sets `A`, `B` of cardinalities at least `k` with every `a + b` a genuine cycle length in `G`. `sourceLemma39_branchII_ambient_or_spectrum_complete` consumes `shadow.application` and covers all five constructors: both truncations, both crossladders and the direct-net spectrum. It performs only Prop-valued case analysis. The net alternative is not a claim of an exact ambient `k²`-net.

`sourceLemma39_branch_dichotomy_complete` uses `4 * C.length ≤ 9 * zeroOutside.card` or its strict complement. Under the original longest-cycle, connectivity-at-least-four, girth-at-least-five, minimum-degree-at-least-six, length-at-least-`2^6 * 3^4 * (sourceLemma36_c k)^2` and `1 ≤ k` hypotheses, it returns the existing genuine Branch-I included-graph certificate or `SourceLemma39AmbientOrSpectrum G C k`. Literal source Lemma 3.9 remains unproved: the assembled conclusion deliberately retains the Branch-I alternatives and the reduced-net spectrum alternative. The unchanged principal statement contract is proved by `jsp_000089_complete` in Principal.lean.

## Next Section-2 obligations

The ambient proper-truncation, crossladder and genuine chord-based unrooted mesh Section-2 conversions are now complete, as described below. All individual Branch-I and Branch-II certificates now provide positive finite `A`, `B` with cardinalities at least `k / 8` (natural division, the source's `⌊k/8⌋`) and every sum realized by an actual ambient cycle. The direct Branch-II net gives the stronger cardinality bound `k`; the complete Branch-II spectrum theorem below weakens this to `k / 8`. Handle `k < 8` explicitly; a claim of nonempty sets cannot be inferred from the bound `k / 8 = 0`.

| Certificate | Remaining mathematical conversion |
| --- | --- |
| Ambient proper truncation | Complete: `sourceLemma21_ambient_proper_truncation_subsetSums` realizes every subset of all `k` positive normalized increments by a genuine ambient simple cycle. `sourceLemma25_ambient_proper_truncation_spectrum` gives positive sets with both cardinalities at least `k / 8`. |
| Ambient crossladder on `C` or `D` | Complete: `sourceLemma23_ambient_crossladder_subsetSums` realizes every subset of `m` strictly positive increments when `4 * m ≤ k`. `sourceLemma25_ambient_crossladder_spectrum` gives positive sets with both cardinalities at least `k / 8`; both Branch-II lifts use this common theorem. |
| Branch-I `directTruncation` | Complete: `sourceLemma25_direct_truncation_ambient` reconstructs genuine one-edge chords in the included graph, proves the repaired safety contract and applies Section 2; `sourceLemma25_branchI_direct_truncation_spectrum_complete` transports every cycle witness into G. |
| Branch-I `residualTruncation` | Complete: the private certificate retains `attachment_edges_disjoint_cycle` from its genuine chord-family producer; `sourceLemma25_unrooted_truncation_ambient` preserves all physical attachments, and `sourceLemma25_branchI_residual_truncation_spectrum_complete` applies Section 2 and injectively maps every cycle into G. |
| Branch-I `directNet` | Complete: `sourceLemma25_net_cycle_spectrum` uses the genuine x–y path, two-edge closure through w, ordered source attachments and physical Section-2 route cycles in R.graph; `sourceLemma25_branchI_direct_net_spectrum_complete` injectively maps every pair-sum cycle into G. |
| Branch-I `directCrossladder` | Complete: `sourceLemma25_direct_crossladder_ambient` constructs a genuine boundary D from the two extreme matching edges and original-cycle rails inside the included graph, proves all ambient safety fields and strict true-gap placement; `sourceLemma25_branchI_direct_crossladder_spectrum_complete` applies Section 2 on D and injectively transports every pair-sum cycle into G. |
| Branch-I `residualBlock` | Complete: the source Section-2 certificate retains its literal chord Q, off-cycle edge and strict true-gap partition from extreme crossing; `sourceLemma25_section2_crossladder_ambient` normalizes either buffer on R.cycle and `sourceLemma25_branchI_residual_block_spectrum_complete` applies the common spectrum and transports every cycle into G. |
| Branch-I `residualMesh` | Complete for the existing genuine unrooted proper-mesh payload: `sourceLemma24_unrooted_proper_mesh_subsetSums` proves all subset witnesses in the included graph; `sourceLemma25_branchI_residual_mesh_spectrum_complete` maps every cycle witness injectively into G. All-branch quantitative assembly is complete below. |

Cycle-length bounds must survive every conversion. `sourceLemma39_cycle_length_le_longest` proves that every `IsCycleLength G n` satisfies `n ≤ C.length` when `C` is longest, including witnesses on constructed cycles. Apply it to every pair-sum witness; with positive nonempty opposite sets it also bounds each individual set element. For Theorem 3, instantiate the structural parameter at `8 * t`, retain the upper bound on the longest cycle chosen at that step, and prove the final `2^120 * t^24` bound with the existing constants. No bound on an intermediate constructed cycle may be assumed merely from its decomposition.

## Ambient proper-truncation representation repair

`SourceLemma39AmbientProperTruncation.attachment_edges_disjoint_cycle` requires each physical attachment to have no edge in common with its boundary cycle. Internal vertex disjointness and unequal path lengths alone allow a one-edge attachment that reuses a boundary edge; switching that attachment can produce a two-edge closed walk rather than a simple cycle. Genuine one-edge chords remain permitted. This is an intentional strengthening of the proof certificate; direct users constructing the structure must supply the new field.

Both `sourceLemma39_residual_truncation_ambient_complete` and `sourceLemma39_direct_truncation_ambient_complete` retain their existing hypotheses. They transport genuine source off-cycle endpoint edges through `shadow.cycle_edges` and the induced-cycle map, then combine this with the actual replacement path's internal vertex disjointness. `sourceLemma21_path_edges_disjoint_cycle` handles one-edge and longer simple paths separately. The Branch-II assembly and branch dichotomy continue to use the same constructors. `Audit.lean` checks these declarations and contains regression proofs excluding the old triangle attachment while accepting a genuine one-edge chord on a four-vertex boundary cycle.

The repair alone did not prove Lemma 2.1's subset-sum construction or Corollary 2.5's spectrum conversion; the subsequent completion is described below.

## Proper-truncation Section-2 completion

`sourceLemma21_ambient_proper_truncation_subsetSums` proves the full source Lemma 2.1 conclusion for the repaired ambient certificate: a positive baseline cycle length and `k` strictly positive increments whose every subset sum is an actual simple cycle length in the original graph. The theorem also covers `k = 0`. Each attachment is compared independently with its corresponding directed boundary segment, so mixed signs are permitted and no planar embedding or Hamiltonicity of the ambient graph is assumed.

`sourceLemma21_ordered_path_switch` constructs the selected paths in finite endpoint order, retains every complementary segment, and proves path simplicity, exact lengths, and physical-edge provenance. `sourceLemma21_ambient_cycle_family` cuts only the closing boundary edge, applies this construction, and uses `attachment_edges_disjoint_cycle` to prove that the closing edge is absent from the switched path. Closing the path therefore yields a genuine simple cycle, including when a selected attachment is a one-edge chord. The all-shorter configuration supplies the baseline cycle.

`sourceLemma25_ambient_proper_truncation_spectrum` derives positive finite sets `A`, `B` whose cardinalities are at least `k / 8` and whose every pair sum is an actual cycle length. The arithmetic helper `sourceLemma21_subsetSums_spectrum` uses disjoint groups of `m = k / 8` indices and all `m + 1` prefix sums of their positive increments, translated by `1` and `base - 1`. Both shifts are positive because the baseline simple cycle has length at least three. For `k < 8`, the empty groups produce valid singleton sets rather than a vacuous cardinality argument.

`sourceLemma25_residual_truncation_spectrum_complete` and `sourceLemma25_direct_truncation_spectrum_complete` compose the existing Branch-II lifts with this same spectrum theorem, preserving their original hypotheses. `Audit.lean` inspects every added theorem. The quantitative all-branch Lemma 3.9 assembly is complete below; Theorem 3 is complete below; the principal JSP theorem is complete in Principal.lean.

## Ambient crossladder switching-safety repair

`SourceLemma39AmbientCrossladder` now requires `rung_edges_disjoint_cycle`, `q_edges_disjoint_cycle`, `q_edges_disjoint_rungs` and `q_end_gap_partition`. Internal-vertex disjointness and exact carrier intersection alone permit one-edge boundary or rung reuse, including with four rungs. The three edge fields exclude these collisions without restricting genuine one-edge paths. The gap field places Q's endpoints strictly in the two true complementary end gaps, `secondVertex 0 → firstVertex 0` and `firstVertex (k-1) → secondVertex (k-1)`, in either orientation. The earlier broad end-arc fields remain available; they include the second rail and must not be used alone to justify Lemma 2.3's paired-rung switches. Explicit structure constructors must now supply the four safety proofs.

Both existing Branch-II constructors retain their theorem hypotheses. The residual lift uses the source ladder's `rung_off_cycle`, the crossing chord's `not_cycle_edge`, original/shadow edge transport and independent component roots to distinguish endpoint edges. `SourceLemma38LabelledCrossladder.crossing_crosses_selected` now retains the producer's existing proof that the crossing chord crosses every selected rung. Both left-buffer and right-buffer producers supply that evidence from their original crossing hypotheses. `sourceLemma36Section2Ladder_extreme_strict_localization` preserves the strict true-gap positions of the crossing endpoints, including `k = 1`, and the residual lift transports them to the actual ambient boundary.

The direct normalized lift proves edge exclusion and strict gap placement against its constructed cycle `D`. The retained rails have disjoint supports, each middle replacement is separated from both boundary replacements, and the actual positions of Q's endpoints lie strictly in the two true end gaps of `D`. Q can consist of original-`C` edges; those edges are proved absent from `D`, rather than assumed absent from `C`. Neither constructor adds a mathematical premise or discards a rung.

`sourceLemma23_splice_cycle_of_edge_disjoint` closes two simple paths with separated supports and disjoint edges without a blanket length-at-least-two premise. `sourceLemma23_crossladder_baseline_cycles` supplies both physical unswitched cycles. Pairwise rung-edge exclusion follows from the existing rung support separation. `Audit.lean` reproduces all three collisions in the frozen pre-repair geometry on an eight-cycle with four rungs, proves that one baseline then has length two and cannot be a simple cycle, and checks that each edge field excludes its corresponding collision. A genuine one-rung configuration on a four-cycle retains both a one-edge rung and a one-edge crossing chord, satisfies the strict gap field, and has two simple baseline cycles.

The audit also preserves an intermediate edge-only counterexample on the twelve-cycle: first endpoints `1,2,3,4`, second endpoints `10,9,8,7` and crossing chord `8–10`. All three edge exclusions hold, but neither orientation separates the two entire rails into the `u–v` boundary arcs. This fixture is explicitly a frozen weaker geometry, not a current ambient certificate. `CrossladderLocalizationRegression.misplaced_crossing_excluded` proves that the repaired strict-gap certificate cannot retain this configuration. This additional regression prevents treating edge exclusion alone as the complete switching contract.

The switching-safety representation repair is complete for the existing Branch-II lifts. The subsequent Lemma 2.3 completion below uses these safety fields without changing the certificate or producer assumptions. The quantitative all-branch Lemma 3.9 assembly is complete below; the principal JSP theorem is complete in Principal.lean.

## Crossladder Section-2 completion

`sourceLemma23_first_detour` and `sourceLemma23_second_detour` implement both physical adjacent-rung replacements from Verstraëte's source Lemma 2.3. Each uses two genuine rungs and the opposite directed rail segment. Their endpoint, simple-path, support, edge and length proofs retain one-edge paths. The strict complementary gaps normalize either orientation of Q to two baseline cycles on the original boundary, each containing its entire ordered rail.

`sourceLemma23_ambient_crossladder_signed_families` proves actual simple-cycle witnesses for every subset of separated pairs on each fixed side. The existing ordered path-switch construction supplies the physical walks; carrier and edge exclusions justify closing them with Q. The signed increments are `s + c - f` and `f + c - s`, with sum `2 * c > 0`, where c is the sum of the two positive rung lengths. Among `2 * m` pairs one fixed side has at least m positive increments; an injective reindexing selects exactly m of them. No independent mixing of sides on one baseline is used.

`sourceLemma23_ambient_crossladder_subsetSums` gives a positive baseline and `delta : Fin m → ℕ`, with every delta positive and every subset sum realized by a simple cycle in G, whenever `4 * m ≤ k`. Selecting the first `4 * m` rungs inside the original certificate preserves its ordered supports and crossing geometry directly; no weaker replacement certificate is introduced. `Audit.lean` checks the literal `k = 4 * m` source instance and the existing genuine one-edge fixture.

`sourceLemma25_ambient_crossladder_spectrum` takes `m = k / 4`, reuses the proper-truncation subset-sum spectrum helper, and proves `(k / 4) / 2 = k / 8`. For `k < 8` it explicitly uses one physical baseline cycle to choose positive singleton sets `{1}` and `{length - 1}`. `sourceLemma25_residual_crossladder_spectrum_complete` applies the same result on C; `sourceLemma25_direct_crossladder_spectrum_complete` applies it on the genuinely constructed D. Both yield all pair-sum cycle witnesses in the original G while preserving producer assumptions.

The completed source result and its Lean formalization remain attributed separately: the mathematics is Verstraëte's published Lemma 2.3 and Corollary 2.5; BeeJSP provides the machine-checked construction. The principal JSP theorem is complete in Principal.lean. Statement constants, pinned Lean/Mathlib dependencies and package version are unchanged.

## Proper mesh Section-2 completion

`sourceLemma24_unrooted_proper_mesh_subsetSums` formalizes Verstraëte's Lemma 2.4 for the genuine chord-based `SourceLemma37UnrootedProperMesh` produced by repaired Lemma 3.7. The original Hamiltonian boundary, all four attachment coordinates, nested order, actual chords and properness are retained. Both chords in a cell have length one; the two positive original arcs have total length strictly greater than two by `proper`. Thus restoring a cell contributes the positive increment `span i - 2`.

The physical construction recurses from an outer cell to the inner cells. Keeping the original arcs concatenates the two boundary arcs and the inner path. Choosing the two chords reverses the entire inner path between them. Support-coordinate bounds prove every splice intersection and vertex uniqueness, and induction proves that every edge comes from the original boundary or one of the retained chords. The result is one simple path for every simultaneous selection. Closing it with the complementary one-edge boundary arc gives one simple cycle; the constructed path has length at least two, excluding a length-two backtrack. This construction does not apply the ordered proper-truncation switch theorem to nested intervals.

The all-chord configuration is a proved physical simple cycle and supplies the baseline. An exact length equation for every configuration yields `base + ∑ i ∈ I, delta i` when precisely the cells in I restore their two original arcs. `sourceLemma25_unrooted_proper_mesh_spectrum` reuses `sourceLemma21_subsetSums_spectrum` to give positive A+B sets of cardinalities at least `k / 8`, including its explicit singleton-prefix construction below eight and the zero-cell case.

`sourceLemma24_map_cycle_length` preserves a simple-cycle witness and its exact length through an injective graph homomorphism. `sourceLemma25_branchI_residual_mesh_spectrum_complete` applies the mesh spectrum in the existing included graph and maps all pair-sum witnesses into ambient G. Its mesh argument is the payload supplied by the residualMesh alternative; it does not integrate the other Branch-I alternatives. Mathematical attribution remains Verstraëte's Lemma 2.4 and Corollary 2.5. The principal JSP statement, source constants, completed Lemma 2.1/2.3 contracts, toolchain, dependencies and package version are unchanged.

## Complete Branch-II spectrum integration

`sourceLemma39_ambient_or_spectrum_spectrum_complete` consumes every constructor of `SourceLemma39AmbientOrSpectrum`: proper truncation uses `sourceLemma25_ambient_proper_truncation_spectrum`; both crossladder constructors use `sourceLemma25_ambient_crossladder_spectrum`; the direct-net spectrum retains its positive sets and actual ambient witnesses while weakening its cardinality bound from k to `k / 8`. A constructed crossladder uses its actual boundary D; no identification of D with the original longest cycle C is assumed.

`sourceLemma39_branchII_spectrum_complete` composes this conversion with `sourceLemma39_branchII_ambient_or_spectrum_complete`, retaining the existing cycle, shadow-application and `1 ≤ k` hypotheses. It covers all five geometric Branch-II outcomes (direct and residual truncation, direct and residual crossladder, direct net) and returns positive finite A and B, each of cardinality at least `k / 8`, with every pair sum realized by an actual simple cycle in the original ambient G. No new graph hypotheses, certificate fields or proof dependencies are introduced.

All six individual Branch-I spectrum integrations and their all-branch assembly are complete. The directTruncation integration is complete as described below. The completed residualMesh conversion is preserved. Lemma 3.9's common quantitative conclusion is complete below; Theorem 3 is complete below; the principal `jsp_000089_statement` is proved in Principal.lean; independent verification remains pending.

## Branch-I direct proper-truncation integration

`sourceLemma25_direct_truncation_ambient` normalizes the Case-A payload inside its actual graph and Hamiltonian cycle. `SourceLemma36ProperTruncation.attachment_off_cycle` provides a genuine adjacent endpoint pair whose edge is absent from the boundary cycle. The normalizer reconstructs that single-edge chord path between the unchanged ordered endpoints; it does not assume that every edge of an arbitrary stored attachment is off the cycle. Original attachment-support disjointness proves endpoint separation for these new paths, and a single edge has no internal vertices.

The same off-cycle exclusion proves `attachment_edges_disjoint_cycle` and properness. If the directed original arc had length one, it would contain the same endpoint edge, contradicting its absence from C. Thus every reconstructed chord differs in length from its boundary arc, independently of any stored attachment's length. No new certificate field, graph hypothesis or mathematical constant is needed.

`sourceLemma25_branchI_direct_truncation_spectrum_complete` takes the direct payload in `R.graph`, applies `sourceLemma25_ambient_proper_truncation_spectrum` to this normalized certificate, and maps every resulting simple-cycle witness into G through `R.inclusion G` and `R.inclusion_injective G` using `sourceLemma24_map_cycle_length`. Both sets are positive with cardinalities at least `k / 8`, including the existing Section-2 treatment below eight. The inherited residualMesh and complete Branch-II spectrum remain unchanged. The quantitative all-branch Lemma 3.9 assembly is complete below; the principal JSP theorem is completed in Principal.lean.

## Branch-I residual proper-truncation integration

The private `SourceLemma37UnrootedProperTruncation` now retains `attachment_edges_disjoint_cycle`. Its existing chord-family constructor proves this field from `SourceLemma34Chord.not_cycle_edge`: the actual copied one-edge attachment has exactly the certified chord edge, which is absent from the cycle. Internal-vertex disjointness is retained independently and is not used to infer physical edge exclusion. This private certificate repair requires explicit record constructors to supply the field; the existing SameSide producer, labelled chord producer and six-way structural result keep their mathematical hypotheses and source bodies.

`sourceLemma25_unrooted_truncation_ambient` passes the original cycle, anchor, ordered positions, actual paths, disjointness and properness directly to `SourceLemma39AmbientProperTruncation`. It uses the retained edge field for general attachments, with no assumption that every supplied path has length one. `sourceLemma25_branchI_residual_truncation_spectrum_complete` applies the completed proper-truncation spectrum in `R.graph` and transports all simple cycles into G through the injective inclusion. It yields positive finite A and B with both cardinalities at least `k / 8`; the completed Branch-II, directTruncation and residualMesh proofs remain in place. Common Lemma 3.9 spectrum assembly is complete below; Theorem 3 is complete below; the principal JSP theorem is complete in Principal.lean.

## Branch-I direct crossladder integration

`sourceLemma25_direct_crossladder_ambient` consumes the original decreasing matching certificate in its actual Hamiltonian graph. The common-position geometry supplies decreasing f and s with every second-side position strictly before every first-side position. I runs from the last first-side endpoint to the first; O runs from the first second-side endpoint to the last. Literal one-edge matching paths P₀ and P_last close `D = I.append (P₀.append (O.append P_last.reverse))`; `sourceLemma39_boundary_splice_cycle` proves D is a genuine simple cycle. The omitted original-cycle arc Q runs from I.start to O.start. D is a constructed cycle, with no identification with the input cycle.

The reversed middle matching index gives increasing first-side visits and decreasing second-side visits on D. `sourceLemma39_position_rails_gap` proves rail separation and the exact intersections with Q. One-edge rungs have empty internal vertices and pairwise disjoint endpoints. Physical edge exclusion is proved separately for rungs against D, Q against D and Q against every rung, using the existing endpoint-edge exclusion lemmas and matching endpoint inequalities. Cycle indices place Q.start strictly in the outer true gap and Q.end strictly in the inner true gap, including k = 1. These facts populate every field of `SourceLemma39AmbientCrossladder` without a shadow application or stronger graph hypotheses.

`sourceLemma25_branchI_direct_crossladder_spectrum_complete` applies `sourceLemma25_ambient_crossladder_spectrum` to this actual D inside `R.graph`, then uses `sourceLemma24_map_cycle_length` with `R.inclusion G` and its injectivity proof. It produces positive finite A and B, each with cardinality at least `k / 8`, with every pair sum realized by an actual simple cycle in G. `Audit.lean` inspects both new declarations. Branch II remains complete; all six individual Branch-I spectrum integrations are complete. The principal JSP theorem is completed in Principal.lean. Attribution remains Verstraëte’s source construction and Section-2 spectrum argument.

## Branch-I residual buffer integration

The private `SourceLemma36Section2Crossladder` now retains `q_length_one`, `q_off_cycle` and `q_end_gap_partition`. The chord producer constructs Q from the actual SourceLemma34Chord adjacency and retains its `not_cycle_edge`. The private broad chord/oriented constructors now require the strict partition explicitly; broad end-arc membership alone cannot establish it. Their sole extreme-crossing caller supplies the existing `sourceLemma36Section2Ladder_extreme_strict_localization` proof from its genuine first/last crossing evidence. Both source Lemma 3.7 buffer producers and the labelled Lemma 3.8 buffer producers reuse that repaired caller, including reversed endpoint orientation. No six-way dichotomy body or graph hypothesis is changed.

`sourceLemma25_section2_crossladder_ambient` retains the same physical C, rung paths and Q. The existing Section-2 rail interval/separation proofs supply all ambient ordering fields. Rung off-cycle provenance establishes rung edge exclusion; Q’s retained chord edge exclusion establishes Q/cycle edge exclusion. The literal Q has no internal vertices. Cut-cycle coordinates prove that a strict outer-gap endpoint cannot equal either endpoint of any rung, so Q cannot reuse any rung edge. The original exact carrier intersection and strict partition pass to the ambient contract without weakening any field.

`sourceLemma25_branchI_residual_block_spectrum_complete` destructs the actual left/right buffer witness in R.graph, normalizes the corresponding buffer on R.cycle, applies `sourceLemma25_ambient_crossladder_spectrum`, and transports every genuine simple-cycle witness through R.inclusion G and its injectivity proof. Both finite sets are positive and have cardinality at least k / 8. Audit.lean inspects the helper and final theorem; the private certificate/producer audit checks the repair’s existing production routes. Branch II remains complete; all six individual Branch-I spectrum integrations are complete. Common quantitative Lemma 3.9 is complete below; Theorem 3 is complete below; the principal JSP theorem is completed in Principal.lean.

## Branch-I direct-net integration

`sourceLemma25_net_ordered_selection` extracts positions for both k²+2 attachment blocks from `net.source_path_order`. It shares the existing source-only indexing argument with the unchanged-signature Branch-II `sourceLemma39_direct_net_ordered_selection`; no shadow-dependent normalization is used for Branch I. Selection `sel i = i + 1` drops the first left entry and the first reverse-indexed right entry. Strict monotonicity on the left, strict antitonicity on the original right indices, block separation and the simple path's start/terminal indices prove that all selected entries avoid x and y. Reversing the selected right indices gives two strictly increasing, separated families of k²+1 vertices on the actual path I.

`sourceLemma25_net_cycle_spectrum` works entirely in the supplied net's graph. It sets I to `net.blocks.common.geometry.x_y_path.val`, S to the literal y–w–x walk from `hub_to_y.symm` and `hub_to_x`, and D to `I.append S`. It proves D equals the rotation of the certified C′ to x, so D is a genuine simple cycle. Rotation preserves the exclusion of u and v. The selected attachment walks are reversals of the payload's actual one-edge paths; their internal vertices are empty, and their complete left/right supports are disjoint by the net's endpoint inequalities and distinct hubs. For k ≥ 2, `sourceLemma39_net_ordered_ambient_spectrum` constructs separated rails and all four physical simple-cycle route families, giving positive sets of cardinality at least k. For k = 1, `{1}` and `{D.length - 1}` are explicitly positive singleton sets because D has length at least three.

`sourceLemma25_branchI_direct_net_spectrum_complete` retains the directNet payload parameters data, iP, matching, T, u, w, v, x, y and net in R.graph. It weakens the stronger cardinality bound k to k / 8 and maps every actual cycle witness into G with `sourceLemma24_map_cycle_length`, `R.inclusion G` and `R.inclusion_injective G`. D is not identified with R.cycle or the original ambient cycle. No external component path, shadow application, certificate repair, stronger graph hypothesis, source constant or dependency change is introduced. The new declarations have `#check`, `#print` and `#print axioms` inspections in GraphFoundations.lean; the central Audit.lean also inspects them in the unified-spectrum milestone below.

All six individual Branch-I cases and all five Branch-II cases now have spectrum results. The all-branch quantitative Lemma 3.9 assembly and its longest-cycle bounds are complete below; Theorem 3 is complete below; the high-girth/sparse-set integration and principal JSP statement are complete in Principal.lean. Mathematical attribution remains Jacques Verstraëte's source Lemma 2.2 and Corollary 2.5; this pass's Lean formalization was authored with Codex. The principal proof is complete; independent verification remains pending.

## Unified quantitative Lemma-3.9 spectrum

`sourceLemma39_branchI_spectrum_complete` eliminates all six `SourceLemma37UnrootedResult` constructors into the spectrum proposition and passes their exact dependent payloads to the completed directTruncation, directNet, directCrossladder, residualBlock, residualTruncation and residualMesh spectrum theorems. No geometrical witness is reconstructed.

`sourceLemma39_spectrum_complete` calls `sourceLemma39_branch_dichotomy_complete` under precisely its original longest-cycle, `1 ≤ k`, vertex-connectivity-at-least-four, girth-at-least-five, minimum-degree-at-least-six and `2^6 * 3^4 * (sourceLemma36_c k)^2 ≤ C.length` hypotheses. Branch I uses the six-case assembly; Branch II uses `sourceLemma39_ambient_or_spectrum_spectrum_complete`. The result consists of positive finite A and B, each with cardinality at least `k / 8`, with every pair sum realized by a genuine simple cycle in the original graph G.

`sourceLemma39_bounded_spectrum_complete` retains those same sets and cycle witnesses and adds `a + b ≤ C.length` for every pair, solely by applying `sourceLemma39_cycle_length_le_longest` to each actual witness. The interface adds no assumptions or constants and supplies the bounded quantitative consequence needed by the subsequent Theorem 3 proof. `Audit.lean` checks signatures, proof terms and transitive axioms for these three declarations and the preceding direct-net milestone, including its two private helpers.

This completes the quantitative spectrum consequence of source Lemma 3.9, rather than its literal structural k-subgraph statement. Theorem 3 is complete below; the principal JSP statement is completed in the subsequent Principal.lean assembly. Mathematical attribution remains Jacques Verstraëte; this Lean assembly was authored with Codex. Toolchain, dependency pins, source constants, statement contract and package version are unchanged.

## Source Theorem-3 prerequisite bridge

The authoritative Version of Record (printed page 164) assumes girth at least `2^120` and average degree at least ten. Its proof chooses a positive parameter from the actual longest-cycle length, between successive `2^6 * 3^4 * c(8*t)^2` thresholds. It does not assume girth at least `2^120 * t^24` for an arbitrary parameter. The printed conclusion requires k ≥ 2, whereas the proof explicitly selects k ≥ 1; the completed theorem below proves the selected parameter is at least two using the exact second threshold.

`sourceTheorem3_numerical_threshold` proves `2^6 * 3^4 * (sourceLemma36_c (8*t))^2 ≤ 2^120 * t^24` for `1 ≤ t`. The private arithmetic helper bounds the exact unchanged c(k) by `10380 * k^12`, using the explicit identity `3! * choose(n,3) = n.descFactorial 3`, the bound `n.descFactorial 3 ≤ n^3`, and sound Nat inequalities. This enabling threshold is not a universal upper bound on the longest cycle.

`sourceTheorem3_card_lower_bound` derives the seven-vertex premise of Proposition 3.10 from average degree ten by the simple-graph degree upper bound and the degree-sum identity. `sourceTheorem3_mader_extraction` returns the actual induced witness W from `sourceProposition310_k4`, retaining vertex connectivity at least four and minimum degree at least six. Its canonical `Embedding.induce (↑W : Set V)` maps into the original G; no abstract replacement graph is introduced.

`sourceTheorem3_longest_cycle` excludes the acyclic case using connectivity, the tree edge-count formula and minimum degree six. It selects the maximum of the existing finite `cycleLengths` set and returns an actual walk C with `SourceLongestCycle`. `sourceTheorem3_induced_girth` maps an actual shortest induced cycle into G and proves the girth comparison under the explicit cyclicity condition; it does not apply Nat-girth monotonicity to an acyclic induced graph, whose girth is zero.

`sourceTheorem3_parameter_selection` chooses the greatest positive parameter whose exact threshold is at most the actual cycle length, in a proved finite search bound. Its successor threshold is strictly larger. `sourceTheorem3_lemma39_inputs` combines these facts under precisely the source's average-degree and fixed-girth hypotheses, returning W, the actual induced longest cycle C, the selected positive t, the girth comparison, and both threshold inequalities. In particular, `1 ≤ 8*t` and the exact lower threshold are available for `sourceLemma39_bounded_spectrum_complete`; no additional longest-cycle assumption is needed. The upper bound depends on the selected parameter and is proved from maximality, rather than assumed as a universal cap.

The central Audit inspects every new public declaration and its private arithmetic/cycle producers. The shifted-threshold numerical estimate, exact set-size selection, transport of the bounded spectra into G and reconciliation of the printed k ≥ 2 conclusion are complete below. No final sparse hitting-set integration or principal theorem was started. Mathematical attribution remains Jacques Verstraëte (with the source's Mader attribution for Proposition 3.10); this Lean bridge was authored with Codex. Statement, source constants, toolchain, dependencies and package version are unchanged.

## Complete source Theorem 3

`sourceTheorem3_complete` proves the exact Version-of-Record Theorem 3 (printed page 164) for any finite simple graph G of average degree at least ten and girth at least `2^120`: there is k ≥ 2 and positive finite sets A and B, each of cardinality exactly k, such that every pair sum is the length of a genuine simple cycle in G and is at most `2^120 * k^24`. The public theorem requires only the finite-vertex instance; equality decisions are chosen classically inside the proof. No stronger graph hypothesis or source-constant change is introduced.

The private `sourceTheorem3_choose_three_scaled` proves `6 * Nat.choose n 3 ≤ n^3` using the exact factorial/descending-factorial identity. For k ≥ 16, `sourceTheorem3_c_sharp_bound` scales `k+2` and `k²+2` by eight, proves `2*n ≤ 9*k³` for `n = 4*k²*(k+2)`, and obtains `48 * Nat.choose n 3 ≤ 729*k^9`. The first summand of c(k) is at most `5*k^12`; multiplying the two scaled inequalities bounds the second by `35*k^12`. Thus the unchanged c(k) is at most `40*k^12`, with every estimate proved in Nat arithmetic.

`sourceTheorem3_successor_threshold` applies this sharp estimate at `8*t+8`, using `16 ≤ 8*t+8 ≤ 16*t` for t ≥ 1. The coefficient inequality `2^6 * 3^4 * 40^2 ≤ 2^24` and `16^24 = 2^96` give the original `2^120 * t^24` upper threshold. `sourceTheorem3_second_threshold` specializes it at t = 1. `sourceTheorem3_selected_parameter_ge_two` excludes t = 1 because the actual cycle length is at least `2^120` and strictly below its selected successor threshold, which at t = 1 is at most `2^120`. This closes the printed k ≥ 2 requirement without strengthening assumptions.

The final theorem consumes the existing actual induced graph, longest-cycle and selected-parameter witnesses from `sourceTheorem3_lemma39_inputs`. It invokes `sourceLemma39_bounded_spectrum_complete` at `8*t`, selects subsets of exactly t elements from the returned sets, and preserves positivity. Each pair sum is bounded first by the actual C.length, then by the selected successor threshold, and finally by `2^120 * t^24`. Every actual induced-graph simple-cycle witness maps into original G through the canonical induced embedding and `sourceLemma24_map_cycle_length`, preserving its exact length. The lower enabling threshold and the upper successor threshold have distinct proof roles; no universal longest-cycle cap is assumed.

Audit.lean inspects the complete theorem, sharp estimate, successor threshold, second-threshold specialization, parameter-size proof and private choose helper; the inherited Lemma-3.9 inspections remain intact. Source Theorem 3 and the subsequent sparse hitting-set integration and principal proof in Principal.lean are complete. Mathematical attribution remains Jacques Verstraëte, with the source's Mader attribution for Proposition 3.10; this Lean completion was authored with Codex. Source constants, original statement, pins and package version are unchanged.

## Complete principal theorem

`sourceLemma43_theorem3_threshold` converts `2^(j-1) ≤ 2^120*k^24` into `j * sourceLemma43BlockThreshold j ≤ k` for k ≥ 2 and j ≥ 1, without changing the real-valued floor definition. The real root has twenty-fourth power `2^(j-1)`, so it is at most `32*k`. If the floor argument is nonpositive, its natural floor is zero. Otherwise the proved nonnegativity permits `Nat.floor_le`; multiplying by positive j and cancelling its inverse gives the required integer inequality.

The final printed proof on page 166 writes `cn^(-η)` once, although Lemma 4.3 requires `cn^η`. For `N = 2^120*k^24`, the exact positive-exponent quantity with c = 1/32 and η = 1/24 is k. The numerical bridge proves the actual floor-threshold requirement directly, resolving that typographical inconsistency without changing assumptions.

`sourceTheorem3_high_girth_unavoidable` consumes Theorem 3's positive sets of exact cardinality k and its actual cycles in G. Nonempty opposite sets and the pair-sum bound place each summand in `sourceLemma42Universe (2^120*k^24)`. Dyadic membership and the numerical bridge verify every premise of `sourceLemma43_global_hitting`. Destructing its actual image₂ witness supplies a pair a ∈ A, b ∈ B, preserving the original simple-cycle witness for a+b.

`source_averageDegree10_cycle` extracts the actual induced Mader graph, selects its certified longest simple cycle and maps that cycle into G through the canonical injective induced embedding. `source_averageDegree10_girth_pos` excludes acyclic Nat girth zero. `source_short_girth_unavoidable` then applies the existing short-cycle theorem when G.girth < `2^120`.

`jsp_000089_complete` uses the already proved `sourceSparsity099_finalSet` and the two girth branches to prove the literal original Prop-valued statement, with no additional assumptions or change in quantifier order or density exponent. Audit.lean imports Principal, checks every new declaration and its proof term and transitive axioms, and checks an explicit proof of the statement contract. Lake’s explicit library root list includes Principal, so the existing default target builds the new module and Audit’s import succeeds. This single root addition was required because importing Principal alone did not register it with Lake. Mathematical attribution remains Jacques Verstraëte; this Lean assembly was authored with Codex. Source constants, statement, dependency pins, inherited graph and construction proofs, and package version are unchanged.

The remaining work is independent Iteration 6 verification and final read-only review, including isolated reproduction and any applicable kernel replay or external checking. No principal mathematical obligation remains; no submission or award action is claimed.
