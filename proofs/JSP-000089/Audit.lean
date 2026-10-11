import Main
import Statement
import Construction
import GraphFoundations
import Principal

#check JSP000089.card_additiveSumset_eq_of_pairSumsInjective
#print JSP000089.card_additiveSumset_eq_of_pairSumsInjective
#print axioms JSP000089.isCycleLength_le_card
#print axioms JSP000089.hasCycleLengthIn_iff_filter_nonempty
#print axioms JSP000089.hasCycleLengthIn_sourceShortCycleLengths_of_girth_le
#print axioms JSP000089.card_subsetSelectionPairs
#print axioms JSP000089.card_fixedSizeSelectionPairs
#print axioms JSP000089.card_additiveSumset_eq_of_pairSumsInjective
#check JSP000089.le_card_additiveSumset_of_pairSumsInjective
#print JSP000089.le_card_additiveSumset_of_pairSumsInjective
#print axioms JSP000089.le_card_additiveSumset_of_pairSumsInjective
#print axioms JSP000089.sourceLemma41_selection_conclusion_of_nonempty
#print axioms JSP000089.sourceLemma41_collisionFreeSelections_nonempty_of_colliding_card_lt
#check JSP000089.sourceLemma41_selection_conclusion_of_colliding_card_lt
#print JSP000089.sourceLemma41_selection_conclusion_of_colliding_card_lt
#print axioms JSP000089.sourceLemma41_selection_conclusion_of_colliding_card_lt
#check JSP000089.sourceLemma41_selectedSize_quantitative_bounds
#print JSP000089.sourceLemma41_selectedSize_quantitative_bounds
#print axioms JSP000089.sourceLemma41_selectedSize_quantitative_bounds
#print axioms JSP000089.sourceLemma41_selectedSize_le
#print axioms JSP000089.sourceLemma41_fixedSizeSelectionPairs_nonempty
#check JSP000089.sourceLemma41_selectedSize_pow_four_le
#print axioms JSP000089.sourceLemma41_selectedSize_le_fourthRoot
#print axioms JSP000089.sourceLemma41_selectedSize_pow_four_le
#check JSP000089.mem_sourceLemma41CollidingSelections_iff_exists_witness
#print axioms JSP000089.mem_sourceLemma41CollidingSelections_iff_exists_witness
#check JSP000089.sourceLemma41CollisionWitnesses_distinct_coordinates
#print axioms JSP000089.sourceLemma41CollisionWitnesses_distinct_coordinates
#check JSP000089.card_sourceLemma41CollisionWitnesses_le
#print axioms JSP000089.card_sourceLemma41CollisionWitnesses_le
#check JSP000089.sourceLemma41_two_le_selectedSize
#print axioms JSP000089.sourceLemma41_two_le_selectedSize
#check JSP000089.card_sourceLemma41CollidingSelections_le_sum_witnessSelections
#print axioms JSP000089.card_sourceLemma41CollidingSelections_le_sum_witnessSelections
#check JSP000089.sourceLemma41_card_remainingA_of_witness
#print axioms JSP000089.sourceLemma41_card_remainingA_of_witness
#print axioms JSP000089.sourceLemma41_card_remainingB_of_witness
#check JSP000089.sourceLemma41_insert_erase_A_of_witness_coordinates
#print axioms JSP000089.sourceLemma41_insert_erase_A_of_witness_coordinates
#print axioms JSP000089.sourceLemma41_erase_insert_A_of_witness_coordinates
#check JSP000089.sourceLemma41_erase_markedA_mem_residualPowersetCard
#print axioms JSP000089.sourceLemma41_erase_markedA_mem_residualPowersetCard
#check JSP000089.sourceLemma41_insert_residualA_mem_powersetCard
#print axioms JSP000089.sourceLemma41_insert_residualA_mem_powersetCard
#check JSP000089.sourceLemma41MarkedAEquiv
#print axioms JSP000089.sourceLemma41MarkedAEquiv
#check JSP000089.card_sourceLemma41_markedASelections
#print axioms JSP000089.card_sourceLemma41_markedASelections
#print axioms JSP000089.sourceSparsity099_sourceShortCycleLengths

#check JSP000089.card_sourceLemma41SelectionsContainingWitness
#print axioms JSP000089.card_sourceLemma41SelectionsContainingWitness
#check JSP000089.card_sourceLemma41SelectionsContainingWitness_eq_square
#print axioms JSP000089.card_sourceLemma41SelectionsContainingWitness_eq_square
#check JSP000089.card_sourceLemma41CollidingSelections_le_collision_bound
#print axioms JSP000089.card_sourceLemma41CollidingSelections_le_collision_bound
#check JSP000089.sourceLemma41_collision_bound_lt_fixedSize_count
#print axioms JSP000089.sourceLemma41_collision_bound_lt_fixedSize_count
#check JSP000089.sourceLemma41_colliding_card_lt_fixedSizeSelectionPairs
#print axioms JSP000089.sourceLemma41_colliding_card_lt_fixedSizeSelectionPairs
#check JSP000089.sourceLemma41_complete
#print JSP000089.sourceLemma41_complete
#print axioms JSP000089.sourceLemma41_complete

#check JSP000089.sourceLemma42_exists_reducedPair_of_largePair
#print JSP000089.sourceLemma42_exists_reducedPair_of_largePair
#print axioms JSP000089.sourceLemma42_exists_reducedPair_of_largePair
#check JSP000089.sourceLemma42_largePairs_hit_of_hitsReducedPairs
#print JSP000089.sourceLemma42_largePairs_hit_of_hitsReducedPairs
#print axioms JSP000089.sourceLemma42_largePairs_hit_of_hitsReducedPairs
#check JSP000089.sourceLemma42_goodCandidates_nonempty_of_bad_card_lt
#print axioms JSP000089.sourceLemma42_goodCandidates_nonempty_of_bad_card_lt
#check JSP000089.sourceLemma42_of_bad_card_lt
#print JSP000089.sourceLemma42_of_bad_card_lt
#print axioms JSP000089.sourceLemma42_of_bad_card_lt

#check JSP000089.sourceLemma42_rangeContained_of_universe_budget
#print JSP000089.sourceLemma42_rangeContained_of_universe_budget
#print axioms JSP000089.sourceLemma42_rangeContained_of_universe_budget

#check JSP000089.card_sourceLemma42Colourings
#print JSP000089.card_sourceLemma42Colourings
#print axioms JSP000089.card_sourceLemma42Colourings
#check JSP000089.mem_sourceLemma42ColouringsMissing_iff_disjoint
#print JSP000089.mem_sourceLemma42ColouringsMissing_iff_disjoint
#print axioms JSP000089.mem_sourceLemma42ColouringsMissing_iff_disjoint
#check JSP000089.card_sourceLemma42ColouringsMissing
#print JSP000089.card_sourceLemma42ColouringsMissing
#print axioms JSP000089.card_sourceLemma42ColouringsMissing

#check JSP000089.card_sourceLemma42ReducedPairs_le
#print axioms JSP000089.card_sourceLemma42ReducedPairs_le
#check JSP000089.card_sourceLemma42BadColourings_le_reducedPairs_mul
#print JSP000089.card_sourceLemma42BadColourings_le_reducedPairs_mul
#print axioms JSP000089.card_sourceLemma42BadColourings_le_reducedPairs_mul
#check JSP000089.card_sourceLemma42BadColourings_le
#print JSP000089.card_sourceLemma42BadColourings_le
#print axioms JSP000089.card_sourceLemma42BadColourings_le

#check JSP000089.sourceLemma42ColourCount
#check JSP000089.sourceLemma42_reducedPair_factor_lt_decay
#print axioms JSP000089.sourceLemma42_reducedPair_factor_lt_decay
#check JSP000089.two_mul_card_sourceLemma42BadColourings_lt
#print JSP000089.two_mul_card_sourceLemma42BadColourings_lt
#print axioms JSP000089.two_mul_card_sourceLemma42BadColourings_lt

#check JSP000089.card_sourceLemma42ColouringsSelectingAt
#check JSP000089.card_sourceLemma42SelectedColourIncidences
#print JSP000089.card_sourceLemma42SelectedColourIncidences
#check JSP000089.sum_card_sourceLemma42SelectedColourClass
#print axioms JSP000089.sum_card_sourceLemma42SelectedColourClass
#check JSP000089.two_mul_card_sourceLemma42Universe_le_colourCount_mul_budget
#print axioms JSP000089.two_mul_card_sourceLemma42Universe_le_colourCount_mul_budget
#check JSP000089.mem_sourceLemma42OversizedColourings_iff
#print axioms JSP000089.mem_sourceLemma42OversizedColourings_iff
#check JSP000089.budget_mul_card_sourceLemma42OversizedColourings_le
#print JSP000089.budget_mul_card_sourceLemma42OversizedColourings_le
#print axioms JSP000089.budget_mul_card_sourceLemma42OversizedColourings_le


#check JSP000089.sourceLemma42_exists_goodSmallSelectedSet
#print JSP000089.sourceLemma42_exists_goodSmallSelectedSet
#print axioms JSP000089.sourceLemma42_exists_goodSmallSelectedSet
#check JSP000089.sourceLemma42_rangeContained_repaired
#print JSP000089.sourceLemma42_rangeContained_repaired
#print axioms JSP000089.sourceLemma42_rangeContained_repaired
#check JSP000089.sourceLemma42_selectedClassBudget_quantitative_noncoarse
#print JSP000089.sourceLemma42_selectedClassBudget_quantitative_noncoarse
#print axioms JSP000089.sourceLemma42_selectedClassBudget_quantitative_noncoarse
#check JSP000089.sourceLemma42_finalBudget_quantitative_bound
#print JSP000089.sourceLemma42_finalBudget_quantitative_bound
#print axioms JSP000089.sourceLemma42_finalBudget_quantitative_bound


#check JSP000089.sourceLemma43_additiveSumset_subset_dyadicUnion
#print JSP000089.sourceLemma43_additiveSumset_subset_dyadicUnion
#print axioms JSP000089.sourceLemma43_additiveSumset_subset_dyadicUnion
#check JSP000089.sourceLemma43_exists_blockLocalisedHittingSet
#print JSP000089.sourceLemma43_exists_blockLocalisedHittingSet
#print axioms JSP000089.sourceLemma43_exists_blockLocalisedHittingSet


#check JSP000089.sourceLemma43Set
#print JSP000089.sourceLemma43Set
#check JSP000089.sourceLemma43LocalSet_hits_dyadicPair
#print JSP000089.sourceLemma43LocalSet_hits_dyadicPair
#print axioms JSP000089.sourceLemma43LocalSet_hits_dyadicPair
#check JSP000089.sourceLemma43Set_hits_of_dyadicPair
#print JSP000089.sourceLemma43Set_hits_of_dyadicPair
#print axioms JSP000089.sourceLemma43Set_hits_of_dyadicPair


#check JSP000089.sourceLemma43BlockThreshold_eventually_admissible
#print JSP000089.sourceLemma43BlockThreshold_eventually_admissible
#print axioms JSP000089.sourceLemma43BlockThreshold_eventually_admissible
#check JSP000089.sourceLemma43ExceptionalSupport
#print JSP000089.sourceLemma43ExceptionalSupport
#print axioms JSP000089.sourceLemma43ExceptionalSupport


#check JSP000089.sourceLemma43BlockThreshold
#print JSP000089.sourceLemma43BlockThreshold
#print axioms JSP000089.sourceLemma43BlockThreshold
#check JSP000089.sourceLemma43BlockThreshold_real_tendsto
#print JSP000089.sourceLemma43BlockThreshold_real_tendsto
#print axioms JSP000089.sourceLemma43BlockThreshold_real_tendsto
#check JSP000089.sourceLemma43BlockThreshold_eventually_admissible
#print JSP000089.sourceLemma43BlockThreshold_eventually_admissible
#print axioms JSP000089.sourceLemma43BlockThreshold_eventually_admissible
#check JSP000089.sourceLemma43LocalSet_hits_dyadicPair
#print JSP000089.sourceLemma43LocalSet_hits_dyadicPair
#print axioms JSP000089.sourceLemma43LocalSet_hits_dyadicPair

#check JSP000089.sourceLemma43BlockThreshold_mono
#print JSP000089.sourceLemma43BlockThreshold_mono
#print axioms JSP000089.sourceLemma43BlockThreshold_mono

#check JSP000089.sourceLemma43_exists_large_dyadicFiber
#print JSP000089.sourceLemma43_exists_large_dyadicFiber
#print axioms JSP000089.sourceLemma43_exists_large_dyadicFiber

#check JSP000089.sourceLemma43_exists_two_dyadicFibers
#print JSP000089.sourceLemma43_exists_two_dyadicFibers
#print axioms JSP000089.sourceLemma43_exists_two_dyadicFibers
#check JSP000089.sourceLemma43_global_hitting
#print JSP000089.sourceLemma43_global_hitting
#print axioms JSP000089.sourceLemma43_global_hitting

#check JSP000089.sourceLemma43LocalSet_card_le_finalBudget_of_admissible
#print JSP000089.sourceLemma43LocalSet_card_le_finalBudget_of_admissible
#print axioms JSP000089.sourceLemma43LocalSet_card_le_finalBudget_of_admissible
#check JSP000089.sourceLemma43ExceptionalContribution_bound
#print JSP000089.sourceLemma43ExceptionalContribution_bound
#print axioms JSP000089.sourceLemma43ExceptionalContribution_bound

#check JSP000089.sourceLemma43_regular_selectedSize_mul_card_le
#print JSP000089.sourceLemma43_regular_selectedSize_mul_card_le
#print axioms JSP000089.sourceLemma43_regular_selectedSize_mul_card_le

#check JSP000089.sourceLemma43_regular_quartic_local_estimate
#print JSP000089.sourceLemma43_regular_quartic_local_estimate
#print axioms JSP000089.sourceLemma43_regular_quartic_local_estimate

#check JSP000089.sourceLemma43_threshold_exponential_le
#print JSP000089.sourceLemma43_threshold_exponential_le
#print axioms JSP000089.sourceLemma43_threshold_exponential_le
#check JSP000089.sourceLemma43_regular_exponential_quartic_estimate
#print JSP000089.sourceLemma43_regular_exponential_quartic_estimate
#print axioms JSP000089.sourceLemma43_regular_exponential_quartic_estimate

#check JSP000089.sourceLemma43_regular_exponential_power100_estimate
#print JSP000089.sourceLemma43_regular_exponential_power100_estimate
#print axioms JSP000089.sourceLemma43_regular_exponential_power100_estimate


#check JSP000089.sourceLemma43_polynomial_absorbed_with_slack
#print JSP000089.sourceLemma43_polynomial_absorbed_with_slack
#print axioms JSP000089.sourceLemma43_polynomial_absorbed_with_slack


#check JSP000089.sourceLemma43_regular_local_power100_with_slack
#print JSP000089.sourceLemma43_regular_local_power100_with_slack
#print axioms JSP000089.sourceLemma43_regular_local_power100_with_slack

#check JSP000089.sourceSparsity099_sourceLemma43Set
#print JSP000089.sourceSparsity099_sourceLemma43Set
#print axioms JSP000089.sourceSparsity099_sourceLemma43Set

#check JSP000089.finiteMenger_one
#print JSP000089.finiteMenger_one
#print axioms JSP000089.finiteMenger_one
#check JSP000089.sourceLemma33_fourAttachment_bridge
#print JSP000089.sourceLemma33_fourAttachment_bridge
#check JSP000089.sourceLemma32_atMostOneDegreeTwo
#print JSP000089.sourceLemma32_atMostOneDegreeTwo
#print axioms JSP000089.sourceLemma32_atMostOneDegreeTwo

#check JSP000089.sourceLemma31_complete
#print JSP000089.sourceLemma31_complete
#print axioms JSP000089.sourceLemma31_complete

#print axioms JSP000089.sourceLemma33_fourAttachment_bridge

#check JSP000089.sourceLemma39_distinct_component_attachments_complete
#print JSP000089.sourceLemma39_distinct_component_attachments_complete
#print axioms JSP000089.sourceLemma39_distinct_component_attachments_complete

#check JSP000089.sourceLemma39_good_quadruples_complete
#print axioms JSP000089.sourceLemma39_good_quadruples_complete
#check JSP000089.sourceLemma39_branchII_shadow_application_complete
#print axioms JSP000089.sourceLemma39_branchII_shadow_application_complete

#check JSP000089.sourceLemma39_selected_root_edge_replacement
#print axioms JSP000089.sourceLemma39_selected_root_edge_replacement

#check JSP000089.sourceLemma39_shadow_root_edge_replacement
#print axioms JSP000089.sourceLemma39_shadow_root_edge_replacement

#check JSP000089.sourceLemma39_selected_replacements_internal_disjoint
#print axioms JSP000089.sourceLemma39_selected_replacements_internal_disjoint

#check JSP000089.sourceLemma39_selected_root_edge_paths
#print axioms JSP000089.sourceLemma39_selected_root_edge_paths

#check JSP000089.sourceLemma39_residual_truncation_paths
#print axioms JSP000089.sourceLemma39_residual_truncation_paths

#check JSP000089.sourceLemma39_residual_truncation_vertex_disjoint
#print axioms JSP000089.sourceLemma39_residual_truncation_vertex_disjoint

#check JSP000089.sourceLemma33_good_path_forget
#print axioms JSP000089.sourceLemma33_good_path_forget

#check JSP000089.sourceLemma33_good_path_root
#print axioms JSP000089.sourceLemma33_good_path_root

#check JSP000089.sourceLemma33_complete_good_path_low_cycle_degree
#print axioms JSP000089.sourceLemma33_complete_good_path_low_cycle_degree

#check JSP000089.sourceLemma33_high_cycle_degree_two_routes_good_path
#print axioms JSP000089.sourceLemma33_high_cycle_degree_two_routes_good_path

#check JSP000089.sourceLemma39_residual_truncation_proper_paths_of_good_path
#print axioms JSP000089.sourceLemma39_residual_truncation_proper_paths_of_good_path

#check JSP000089.sourceLemma39_direct_crossladder_paths
#print axioms JSP000089.sourceLemma39_direct_crossladder_paths
#check JSP000089.sourceLemma39_direct_net_attachment_paths
#print axioms JSP000089.sourceLemma39_direct_net_attachment_paths

#check JSP000089.sourceLemma39_direct_crossladder_boundary_cycle
#print axioms JSP000089.sourceLemma39_direct_crossladder_boundary_cycle

#check JSP000089.sourceLemma39_direct_crossladder_ambient_complete
#print axioms JSP000089.sourceLemma39_direct_crossladder_ambient_complete

#check JSP000089.sourceLemma39_residual_crossladder_ambient_complete
#print axioms JSP000089.sourceLemma39_residual_crossladder_ambient_complete

#check JSP000089.sourceLemma39_direct_net_ordered_selection
#print JSP000089.sourceLemma39_direct_net_ordered_selection
#print axioms JSP000089.sourceLemma39_direct_net_ordered_selection

#check JSP000089.sourceLemma39_direct_net_boundary_cycle
#print JSP000089.sourceLemma39_direct_net_boundary_cycle
#print axioms JSP000089.sourceLemma39_direct_net_boundary_cycle

#check JSP000089.sourceLemma39_direct_net_reduced_ambient
#print JSP000089.sourceLemma39_direct_net_reduced_ambient
#print axioms JSP000089.sourceLemma39_direct_net_reduced_ambient

#check JSP000089.sourceLemma39_reduced_net_route_length_cardinality
#print JSP000089.sourceLemma39_reduced_net_route_length_cardinality
#print axioms JSP000089.sourceLemma39_reduced_net_route_length_cardinality

#check JSP000089.sourceLemma39_direct_net_cycle_spectrum_one
#print JSP000089.sourceLemma39_direct_net_cycle_spectrum_one
#print axioms JSP000089.sourceLemma39_direct_net_cycle_spectrum_one

-- Direct-net reduced ambient spectrum: audit every new declaration.
#check JSP000089.sourceLemma39_net_attachment_intersection
#print axioms JSP000089.sourceLemma39_net_attachment_intersection
#check JSP000089.sourceLemma39_net_route_prefix
#print axioms JSP000089.sourceLemma39_net_route_prefix
#check JSP000089.sourceLemma39_net_route_suffix
#print axioms JSP000089.sourceLemma39_net_route_suffix
#check JSP000089.sourceLemma39_net_cycle_replacement
#print axioms JSP000089.sourceLemma39_net_cycle_replacement
#check JSP000089.sourceLemma39_net_spectrum_of_four_route_families
#print axioms JSP000089.sourceLemma39_net_spectrum_of_four_route_families
#check JSP000089.sourceLemma39_net_prefix_mem_iff
#print axioms JSP000089.sourceLemma39_net_prefix_mem_iff
#check JSP000089.sourceLemma39_net_suffix_mem_iff
#print axioms JSP000089.sourceLemma39_net_suffix_mem_iff
#check JSP000089.sourceLemma39_net_prefix_length
#print axioms JSP000089.sourceLemma39_net_prefix_length
#check JSP000089.sourceLemma39_net_route_family
#print axioms JSP000089.sourceLemma39_net_route_family
#check JSP000089.sourceLemma39_net_routes_ambient_realization
#print axioms JSP000089.sourceLemma39_net_routes_ambient_realization
#check JSP000089.sourceLemma39_net_prefix_idx
#print axioms JSP000089.sourceLemma39_net_prefix_idx
#check JSP000089.sourceLemma39_net_rail_segment
#print axioms JSP000089.sourceLemma39_net_rail_segment
#check JSP000089.sourceLemma39_net_cycle_arc_intersection
#print axioms JSP000089.sourceLemma39_net_cycle_arc_intersection
#check JSP000089.sourceLemma39_net_ambient_rail_decomposition
#print axioms JSP000089.sourceLemma39_net_ambient_rail_decomposition
#check JSP000089.sourceLemma39_net_ordered_ambient_spectrum
#print axioms JSP000089.sourceLemma39_net_ordered_ambient_spectrum
#check JSP000089.sourceLemma39_direct_net_cycle_spectrum_complete
#print axioms JSP000089.sourceLemma39_direct_net_cycle_spectrum_complete
#print JSP000089.sourceLemma39_direct_net_cycle_spectrum_complete

-- Lemma-3.9 assembly milestone; these are partial structural/spectrum results.
#check JSP000089.sourceLemma39_cycle_oriented_index
#print axioms JSP000089.sourceLemma39_cycle_oriented_index
#check JSP000089.sourceLemma39_path_reverse_index
#print axioms JSP000089.sourceLemma39_path_reverse_index
#check JSP000089.sourceLemma39_append_right_index
#print axioms JSP000089.sourceLemma39_append_right_index
#check JSP000089.sourceLemma39_direct_crossladder_normalized_complete
#print axioms JSP000089.sourceLemma39_direct_crossladder_normalized_complete
#check JSP000089.sourceLemma39_branchII_ambient_or_spectrum_complete
#print axioms JSP000089.sourceLemma39_branchII_ambient_or_spectrum_complete
#check JSP000089.sourceLemma39_branch_dichotomy_complete
#print axioms JSP000089.sourceLemma39_branch_dichotomy_complete
#check JSP000089.sourceLemma39_cycle_length_le_longest
#print axioms JSP000089.sourceLemma39_cycle_length_le_longest
#print JSP000089.sourceLemma39_direct_crossladder_normalized_complete
#print JSP000089.sourceLemma39_branchII_ambient_or_spectrum_complete
#print JSP000089.sourceLemma39_branch_dichotomy_complete
#print JSP000089.sourceLemma39_cycle_length_le_longest
#print JSP000089.SourceLemma39AmbientOrSpectrum

-- Proper-truncation edge-disjointness repair and source-constructor audits.
#check JSP000089.sourceLemma21_path_endpoint_edge_length_one
#print axioms JSP000089.sourceLemma21_path_endpoint_edge_length_one
#check JSP000089.sourceLemma21_common_edge_eq_endpoint_edge
#print axioms JSP000089.sourceLemma21_common_edge_eq_endpoint_edge
#check JSP000089.sourceLemma21_path_edges_disjoint_cycle
#print axioms JSP000089.sourceLemma21_path_edges_disjoint_cycle
#check JSP000089.sourceLemma39_original_edge_mem_shadow_cycle_iff
#print axioms JSP000089.sourceLemma39_original_edge_mem_shadow_cycle_iff
#check JSP000089.sourceLemma39_residual_truncation_ambient_complete
#print axioms JSP000089.sourceLemma39_residual_truncation_ambient_complete
#check JSP000089.sourceLemma39_direct_truncation_ambient_complete
#print axioms JSP000089.sourceLemma39_direct_truncation_ambient_complete

namespace JSP000089.TruncationRegression
open SimpleGraph
abbrev triangle : SimpleGraph (Fin 3) := ⊤
def triangleCycle : triangle.Walk 0 0 :=
  .cons (by decide : triangle.Adj 0 1)
    (.cons (by decide : triangle.Adj 1 2)
      (.cons (by decide : triangle.Adj 2 0) .nil))
theorem triangleCycle_isCycle : triangleCycle.IsCycle := by
  rw [triangleCycle, Walk.cons_isCycle_iff]
  constructor
  · simp [Walk.cons_isPath_iff]
  · decide
/-- The previously admitted attachment is a physical boundary-cycle edge. -/
theorem triangle_attachment_reuses_cycle_edge :
    s((0 : Fin 3), 2) ∈ triangleCycle.edges := by decide
/-- No repaired certificate can carry the old triangle attachment. -/
theorem triangle_no_repaired_configuration :
    ¬ ∃ T : SourceLemma39AmbientProperTruncation triangle triangleCycle 1,
      (T.attachment 0).edges = [s((0 : Fin 3), 2)] := by
  rintro ⟨T, he⟩
  have hp : s((0 : Fin 3), 2) ∈ (T.attachment 0).edges.toFinset := by
    rw [he]
    simp
  exact Finset.disjoint_left.mp (T.attachment_edges_disjoint_cycle 0) hp
    (List.mem_toFinset.mpr triangle_attachment_reuses_cycle_edge)

abbrev chordGraph : SimpleGraph (Fin 4) := ⊤
def chordCycle : chordGraph.Walk 0 0 :=
  .cons (by decide : chordGraph.Adj 0 1)
    (.cons (by decide : chordGraph.Adj 1 2)
      (.cons (by decide : chordGraph.Adj 2 3)
        (.cons (by decide : chordGraph.Adj 3 0) .nil)))
theorem chordCycle_isCycle : chordCycle.IsCycle := by
  rw [chordCycle, Walk.cons_isCycle_iff]
  constructor
  · simp [Walk.cons_isPath_iff]
  · decide
/-- A genuine one-edge chord still inhabits the repaired ambient structure. -/
noncomputable def oneEdgeChordTruncation :
    SourceLemma39AmbientProperTruncation chordGraph chordCycle 1 where
  isCycle := chordCycle_isCycle
  anchor := 0
  anchor_mem := by simp [chordCycle]
  leftPosition := fun _ => ⟨0, by decide⟩
  rightPosition := fun _ => ⟨2, by decide⟩
  left_lt_right := by intro i; decide
  endpoint_order := by
    intro i j h
    have hi : i = j := Subsingleton.elim _ _
    subst j
    exact False.elim (lt_irrefl _ h)
  left_mem := by intro i; change (0 : Fin 4) ∈ chordCycle.support; simp [chordCycle]
  right_mem := by intro i; change (2 : Fin 4) ∈ chordCycle.support; simp [chordCycle]
  attachment := fun _ => .cons (by decide : chordGraph.Adj 0 2) .nil
  attachment_isPath := by
    intro i
    change (Walk.cons (by decide : chordGraph.Adj 0 2) Walk.nil).IsPath
    simp [Walk.cons_isPath_iff]
  attachment_vertex_disjoint := by
    intro i j h
    exact False.elim (h (Subsingleton.elim _ _))
  attachment_internal_disjoint_cycle := by
    intro i
    apply Set.disjoint_left.mpr
    intro v hv _
    rcases hv with ⟨hv, h0, h2⟩
    change v ≠ 0 at h0
    change v ≠ 2 at h2
    change v ∈ [0, 2] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    exact hv.elim h0 h2
  attachment_edges_disjoint_cycle := by intro i; decide
  proper := by intro i; change 1 ≠ 2; decide

theorem genuine_one_edge_chord_permitted :
    ∃ T : SourceLemma39AmbientProperTruncation chordGraph chordCycle 1,
      (T.attachment 0).length = 1 := ⟨oneEdgeChordTruncation, rfl⟩
#print axioms triangleCycle_isCycle
#print axioms triangle_attachment_reuses_cycle_edge
#print axioms triangle_no_repaired_configuration
#print axioms chordCycle_isCycle
#print axioms oneEdgeChordTruncation
#print axioms genuine_one_edge_chord_permitted
end JSP000089.TruncationRegression

#print axioms JSP000089.TruncationRegression.triangleCycle
#print axioms JSP000089.TruncationRegression.chordCycle

-- Source Lemma 2.1 and proper-truncation Corollary 2.5 milestone.
#check JSP000089.sourceLemma21_eq_of_index_eq
#print axioms JSP000089.sourceLemma21_eq_of_index_eq
#check JSP000089.sourceLemma21_suffix_index
#print axioms JSP000089.sourceLemma21_suffix_index
#check JSP000089.sourceLemma21_ordered_path_switch
#print axioms JSP000089.sourceLemma21_ordered_path_switch
#check JSP000089.sourceLemma21_order_nodup
#print axioms JSP000089.sourceLemma21_order_nodup
#check JSP000089.sourceLemma21_order_reanchor
#print axioms JSP000089.sourceLemma21_order_reanchor
#check JSP000089.sourceLemma21_oriented_interval
#print axioms JSP000089.sourceLemma21_oriented_interval
#check JSP000089.sourceLemma21_cut_cycle
#print axioms JSP000089.sourceLemma21_cut_cycle
#check JSP000089.sourceLemma21_arc_coordinates
#print axioms JSP000089.sourceLemma21_arc_coordinates
#check JSP000089.sourceLemma21_linear_segment
#print axioms JSP000089.sourceLemma21_linear_segment
#check JSP000089.sourceLemma21_ambient_cycle_family
#print axioms JSP000089.sourceLemma21_ambient_cycle_family
#check JSP000089.sourceLemma21_normalized_lengths
#print axioms JSP000089.sourceLemma21_normalized_lengths
#check JSP000089.sourceLemma21_ambient_proper_truncation_subsetSums
#print axioms JSP000089.sourceLemma21_ambient_proper_truncation_subsetSums
#check JSP000089.sourceLemma21_subsetSums_spectrum
#print axioms JSP000089.sourceLemma21_subsetSums_spectrum
#check JSP000089.sourceLemma25_ambient_proper_truncation_spectrum
#print axioms JSP000089.sourceLemma25_ambient_proper_truncation_spectrum
#check JSP000089.sourceLemma25_residual_truncation_spectrum_complete
#print axioms JSP000089.sourceLemma25_residual_truncation_spectrum_complete
#check JSP000089.sourceLemma25_direct_truncation_spectrum_complete
#print axioms JSP000089.sourceLemma25_direct_truncation_spectrum_complete

-- Ambient crossladder physical-edge safety and source-proof geometry audit.
#check JSP000089.sourceLemma23_path_edges_disjoint_cycle_iff
#print axioms JSP000089.sourceLemma23_path_edges_disjoint_cycle_iff
#check JSP000089.sourceLemma23_edges_disjoint_of_support_disjoint
#print axioms JSP000089.sourceLemma23_edges_disjoint_of_support_disjoint
#check JSP000089.sourceLemma23_path_edges_disjoint_of_endpoint_edges_ne
#print axioms JSP000089.sourceLemma23_path_edges_disjoint_of_endpoint_edges_ne
#check JSP000089.sourceLemma23_crossladder_q_edges_disjoint_rung_iff
#print axioms JSP000089.sourceLemma23_crossladder_q_edges_disjoint_rung_iff
#check JSP000089.sourceLemma23_splice_cycle_of_edge_disjoint
#print axioms JSP000089.sourceLemma23_splice_cycle_of_edge_disjoint
#check JSP000089.sourceLemma23_crossladder_baseline_cycles
#print axioms JSP000089.sourceLemma23_crossladder_baseline_cycles
#check JSP000089.sourceLemma23_crossladder_rung_edges_disjoint
#print axioms JSP000089.sourceLemma23_crossladder_rung_edges_disjoint
#print axioms JSP000089.SourceLemma39AmbientCrossladder

namespace JSP000089.CrossladderRegression
open SimpleGraph
private structure GeometryBeforeRepair {V : Type*} [Fintype V] [DecidableEq V]
    {r : V} (G : SimpleGraph V) (C : G.Walk r r) (k : ℕ) where
  isCycle : C.IsCycle
  positive : 1 ≤ k
  firstVertex : Fin k → V
  secondVertex : Fin k → V
  first_on_cycle : ∀ i, firstVertex i ∈ C.support
  second_on_cycle : ∀ i, secondVertex i ∈ C.support
  first_between : ∀ i j t, i ≤ j → (firstVertex t ∈
    (sourceOrientedCycleSubpath G C (first_on_cycle i) (first_on_cycle j)).support ↔ i ≤ t ∧ t ≤ j)
  second_between : ∀ i j t, i ≤ j → (secondVertex t ∈
    (sourceOrientedCycleSubpath G C (second_on_cycle j) (second_on_cycle i)).support ↔ i ≤ t ∧ t ≤ j)
  second_not_on_first_rail : ∀ i j t, i ≤ j → secondVertex t ∉
    (sourceOrientedCycleSubpath G C (first_on_cycle i) (first_on_cycle j)).support
  first_not_on_second_rail : ∀ i j t, i ≤ j → firstVertex t ∉
    (sourceOrientedCycleSubpath G C (second_on_cycle j) (second_on_cycle i)).support
  rung : ∀ i, G.Walk (firstVertex i) (secondVertex i)
  rung_isPath : ∀ i, (rung i).IsPath
  rung_internal_disjoint_cycle : ∀ i, Disjoint (internalVertices G (rung i)) {v | v ∈ C.support}
  rung_vertex_disjoint : ∀ i j, i ≠ j → Disjoint {v | v ∈ (rung i).support} {v | v ∈ (rung j).support}
  u : V
  v : V
  u_on_cycle : u ∈ C.support
  v_on_cycle : v ∈ C.support
  u_ne_v : u ≠ v
  u_on_first_end_arc : u ∈ (sourceOrientedCycleSubpath G C
    (second_on_cycle (⟨k-1, by omega⟩ : Fin k))
    (first_on_cycle (⟨0, by omega⟩ : Fin k))).support
  v_on_second_end_arc : v ∈ (sourceOrientedCycleSubpath G C
    (first_on_cycle (⟨k-1, by omega⟩ : Fin k))
    (second_on_cycle (⟨0, by omega⟩ : Fin k))).support
  q : G.Walk u v
  q_isPath : q.IsPath
  q_internal_disjoint_cycle : Disjoint (internalVertices G q) {v | v ∈ C.support}
  q_internal_disjoint_rungs : ∀ i, Disjoint (internalVertices G q) (internalVertices G (rung i))
  q_inter_ladder : q.support.toFinset ∩
    (C.support.toFinset ∪ Finset.univ.biUnion fun i => (rung i).support.toFinset) = {u, v}

abbrev graph : SimpleGraph (Fin 8) := ⊤
def boundary : graph.Walk 0 0 := .cons (by decide : graph.Adj 0 1) (.cons (by decide : graph.Adj 1 2) (.cons (by decide : graph.Adj 2 3) (.cons (by decide : graph.Adj 3 4) (.cons (by decide : graph.Adj 4 5) (.cons (by decide : graph.Adj 5 6) (.cons (by decide : graph.Adj 6 7) (.cons (by decide : graph.Adj 7 0) (.nil))))))))
theorem boundary_isCycle : boundary.IsCycle := by
  rw [boundary, Walk.cons_isCycle_iff]
  constructor
  · simp [Walk.cons_isPath_iff]
  · decide
abbrev first (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
abbrev second (i : Fin 4) : Fin 8 := ⟨7-i.val, by omega⟩
def rung (i : Fin 4) : graph.Walk (first i) (second i) :=
  .cons (by change first i ≠ second i; intro h; have hv := congrArg Fin.val h; change i.val = 7-i.val at hv; omega) .nil
theorem all_on_boundary (z : Fin 8) : z ∈ boundary.support := by fin_cases z <;> decide
theorem index_first (i : Fin 4) : boundary.support.idxOf (first i) = i.val := by
  fin_cases i <;> decide
theorem index_second (i : Fin 4) : boundary.support.idxOf (second i) = 7-i.val := by
  fin_cases i <;> decide
noncomputable def degenerate : GeometryBeforeRepair graph boundary 4 where
  isCycle := boundary_isCycle
  positive := by decide
  firstVertex := first
  secondVertex := second
  first_on_cycle := by intro i; fin_cases i <;> decide
  second_on_cycle := by intro i; fin_cases i <;> decide
  first_between := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_first, index_first]; exact hij)]
    rw [index_first, index_first, index_first]
    rfl
  second_between := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_second, index_second]; exact Nat.sub_le_sub_left hij 7)]
    rw [index_second, index_second, index_second]
    change (7-j.val ≤ 7-t.val ∧ 7-t.val ≤ 7-i.val) ↔ (i.val ≤ t.val ∧ t.val ≤ j.val)
    omega
  second_not_on_first_rail := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_first, index_first]; exact hij)]
    rw [index_first, index_first, index_second]
    omega
  first_not_on_second_rail := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_second, index_second]; exact Nat.sub_le_sub_left hij 7)]
    rw [index_second, index_second, index_first]
    omega
  rung := rung
  rung_isPath := by intro i; fin_cases i <;> norm_num [rung, first, second, Walk.cons_isPath_iff, Fin.val_last]
  rung_internal_disjoint_cycle := by
    intro i; apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    simp only [rung, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  rung_vertex_disjoint := by
    intro i j hij; apply Set.disjoint_left.mpr; intro z hzi hzj
    change z ∈ (rung i).support at hzi
    change z ∈ (rung j).support at hzj
    simp only [rung, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hzi hzj
    rcases hzi with hzi | hzi <;> rcases hzj with hzj | hzj
    · apply hij; apply Fin.ext
      have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change i.val = j.val at hv; exact hv
    · have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change i.val = 7-j.val at hv; omega
    · have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change 7-i.val = j.val at hv; omega
    · apply hij; apply Fin.ext
      have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change 7-i.val = 7-j.val at hv; omega
  u := 0
  v := 7
  u_on_cycle := by decide
  v_on_cycle := by decide
  u_ne_v := by decide
  u_on_first_end_arc := by
    apply (sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).2
    · change boundary.support.idxOf (0 : Fin 8) < boundary.support.idxOf (4 : Fin 8); decide
    · change boundary.support.idxOf (0 : Fin 8) ≤ boundary.support.idxOf (0 : Fin 8); decide
  v_on_second_end_arc := by
    apply ((sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by change boundary.support.idxOf (3 : Fin 8) ≤ boundary.support.idxOf (7 : Fin 8); decide)).mpr
    change boundary.support.idxOf (3 : Fin 8) ≤ boundary.support.idxOf (7 : Fin 8) ∧
      boundary.support.idxOf (7 : Fin 8) ≤ boundary.support.idxOf (7 : Fin 8)
    decide
  q := .cons (by decide : graph.Adj 0 7) .nil
  q_isPath := by simp [Walk.cons_isPath_iff]
  q_internal_disjoint_cycle := by
    apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    change z ∈ [0,7] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  q_internal_disjoint_rungs := by
    intro i; apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    change z ∈ [0,7] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  q_inter_ladder := by decide

theorem all_three_collisions :
    s((0 : Fin 8),7) ∈ (degenerate.rung 0).edges ∧
    s((0 : Fin 8),7) ∈ degenerate.q.edges ∧
    s((0 : Fin 8),7) ∈ boundary.edges := by
  change s((0 : Fin 8),7) ∈ (rung 0).edges ∧
    s((0 : Fin 8),7) ∈ (Walk.cons (by decide : graph.Adj 0 7) Walk.nil).edges ∧
    s((0 : Fin 8),7) ∈ boundary.edges
  decide

/-- Reusing the boundary edge really breaks the source's unswitched baseline. -/
theorem degenerate_baseline_is_not_cycle :
    ¬ ((sourceOrientedCycleSubpath graph boundary degenerate.v_on_cycle
      degenerate.u_on_cycle).append degenerate.q).IsCycle := by
  intro h
  have hl := h.three_le_length
  have he : ((sourceOrientedCycleSubpath graph boundary degenerate.v_on_cycle
      degenerate.u_on_cycle).append degenerate.q).length = 2 := by
    unfold sourceOrientedCycleSubpath
    decide
  omega
/-- The repaired certificate cannot retain this Q on the eight-cycle. -/
theorem boundary_crossing_excluded :
    ¬ ∃ L : SourceLemma39AmbientCrossladder graph boundary 4,
      L.q.edges = [s((0 : Fin 8),7)] := by
  rintro ⟨L, he⟩
  have hq : s((0 : Fin 8),7) ∈ L.q.edges.toFinset := by rw [he]; simp
  exact Finset.disjoint_left.mp L.q_edges_disjoint_cycle hq
    (List.mem_toFinset.mpr (by decide))
/-- The repaired certificate also excludes the boundary-edge rung independently. -/
theorem boundary_rung_excluded :
    ¬ ∃ L : SourceLemma39AmbientCrossladder graph boundary 4,
      (L.rung 0).edges = [s((0 : Fin 8),7)] := by
  rintro ⟨L, he⟩
  have hr : s((0 : Fin 8),7) ∈ (L.rung 0).edges.toFinset := by rw [he]; simp
  exact Finset.disjoint_left.mp (L.rung_edges_disjoint_cycle 0) hr
    (List.mem_toFinset.mpr (by decide))
/-- The third field independently rules out reuse of the same rung by Q. -/
theorem reused_rung_excluded :
    ¬ ∃ L : SourceLemma39AmbientCrossladder graph boundary 4,
      L.q.edges = [s((0 : Fin 8),7)] ∧ (L.rung 0).edges = [s((0 : Fin 8),7)] := by
  rintro ⟨L, hq, hr⟩
  exact Finset.disjoint_left.mp (L.q_edges_disjoint_rungs 0)
    (show s((0 : Fin 8),7) ∈ L.q.edges.toFinset by rw [hq]; simp)
    (show s((0 : Fin 8),7) ∈ (L.rung 0).edges.toFinset by rw [hr]; simp)
end JSP000089.CrossladderRegression

namespace JSP000089.CrossladderOneEdgeRegression
open SimpleGraph
abbrev graph : SimpleGraph (Fin 4) := ⊤
def boundary : graph.Walk 0 0 :=
  .cons (by decide : graph.Adj 0 1)
    (.cons (by decide : graph.Adj 1 2)
      (.cons (by decide : graph.Adj 2 3)
        (.cons (by decide : graph.Adj 3 0) .nil)))
theorem boundary_isCycle : boundary.IsCycle := by
  rw [boundary, Walk.cons_isCycle_iff]
  constructor
  · simp [Walk.cons_isPath_iff]
  · decide
theorem all_on_boundary (z : Fin 4) : z ∈ boundary.support := by fin_cases z <;> decide
noncomputable def genuine : SourceLemma39AmbientCrossladder graph boundary 1 where
  isCycle := boundary_isCycle
  positive := by decide
  firstVertex := fun _ => 0
  secondVertex := fun _ => 2
  first_on_cycle := fun _ => all_on_boundary _
  second_on_cycle := fun _ => all_on_boundary _
  first_between := by
    intro i j t _
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1 (le_refl _)]
    constructor
    · intro _; exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
    · intro _; exact ⟨le_refl _, le_refl _⟩
  second_between := by
    intro i j t _
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1 (le_refl _)]
    constructor
    · intro _; exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
    · intro _; exact ⟨le_refl _, le_refl _⟩
  second_not_on_first_rail := by
    intro i j t _
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1 (le_refl _)]
    change ¬ (0 ≤ 2 ∧ 2 ≤ (0 : ℕ))
    decide
  first_not_on_second_rail := by
    intro i j t _
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1 (le_refl _)]
    change ¬ (2 ≤ 0 ∧ 0 ≤ (2 : ℕ))
    decide
  rung := fun _ => .cons (by decide : graph.Adj 0 2) .nil
  rung_isPath := by intro i; simp [Walk.cons_isPath_iff]
  rung_internal_disjoint_cycle := by
    intro i; apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    change z ∈ [0,2] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  rung_vertex_disjoint := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  u := 3
  v := 1
  u_on_cycle := all_on_boundary _
  v_on_cycle := all_on_boundary _
  u_ne_v := by decide
  u_on_first_end_arc := by unfold sourceOrientedCycleSubpath; decide
  v_on_second_end_arc := by unfold sourceOrientedCycleSubpath; decide
  q := .cons (by decide : graph.Adj 3 1) .nil
  q_isPath := by simp [Walk.cons_isPath_iff]
  q_internal_disjoint_cycle := by
    apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    change z ∈ [3,1] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  q_internal_disjoint_rungs := by
    intro i; apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    change z ∈ [3,1] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  q_inter_ladder := by decide
  rung_edges_disjoint_cycle := by intro i; decide
  q_edges_disjoint_cycle := by decide
  q_edges_disjoint_rungs := by intro i; decide
  q_end_gap_partition := by
    left
    constructor <;> unfold internalVertices sourceOrientedCycleSubpath <;> decide

theorem genuine_one_edge_paths_permitted :
    (genuine.rung 0).length = 1 ∧ genuine.q.length = 1 := ⟨rfl, rfl⟩

theorem genuine_baseline_cycles :
    ((sourceOrientedCycleSubpath graph boundary genuine.u_on_cycle genuine.v_on_cycle).append
      genuine.q.reverse).IsCycle ∧
    ((sourceOrientedCycleSubpath graph boundary genuine.v_on_cycle genuine.u_on_cycle).append
      genuine.q).IsCycle := sourceLemma23_crossladder_baseline_cycles graph genuine
end JSP000089.CrossladderOneEdgeRegression

namespace JSP000089.CrossladderLocalizationRegression
open SimpleGraph
abbrev graph : SimpleGraph (Fin 12) := ⊤
def boundary : graph.Walk 0 0 := .cons (by decide : graph.Adj 0 1) (.cons (by decide : graph.Adj 1 2) (.cons (by decide : graph.Adj 2 3) (.cons (by decide : graph.Adj 3 4) (.cons (by decide : graph.Adj 4 5) (.cons (by decide : graph.Adj 5 6) (.cons (by decide : graph.Adj 6 7) (.cons (by decide : graph.Adj 7 8) (.cons (by decide : graph.Adj 8 9) (.cons (by decide : graph.Adj 9 10) (.cons (by decide : graph.Adj 10 11) (.cons (by decide : graph.Adj 11 0) (.nil))))))))))))
theorem boundary_isCycle : boundary.IsCycle := by
  rw [boundary, Walk.cons_isCycle_iff]
  constructor
  · simp [Walk.cons_isPath_iff]
  · decide
abbrev first (i : Fin 4) : Fin 12 := ⟨1+i.val, by omega⟩
abbrev second (i : Fin 4) : Fin 12 := ⟨10-i.val, by omega⟩
def rung (i : Fin 4) : graph.Walk (first i) (second i) :=
  .cons (by change first i ≠ second i; intro h; have hv := congrArg Fin.val h; change 1+i.val = 10-i.val at hv; omega) .nil
theorem all_on_boundary (z : Fin 12) : z ∈ boundary.support := by fin_cases z <;> decide
theorem index_first (i : Fin 4) : boundary.support.idxOf (first i) = 1+i.val := by
  fin_cases i <;> decide
theorem index_second (i : Fin 4) : boundary.support.idxOf (second i) = 10-i.val := by
  fin_cases i <;> decide
/-- Frozen edge-only geometry, before retaining the strict true end gaps. -/
private structure GeometryWithEdgeExclusion extends
    JSP000089.CrossladderRegression.GeometryBeforeRepair graph boundary 4 where
  rung_edges_disjoint_cycle : ∀ i, Disjoint (rung i).edges.toFinset boundary.edges.toFinset
  q_edges_disjoint_cycle : Disjoint q.edges.toFinset boundary.edges.toFinset
  q_edges_disjoint_rungs : ∀ i, Disjoint q.edges.toFinset (rung i).edges.toFinset

noncomputable def separatedEdges : GeometryWithEdgeExclusion where
  isCycle := boundary_isCycle
  positive := by decide
  firstVertex := first
  secondVertex := second
  first_on_cycle := by intro i; fin_cases i <;> decide
  second_on_cycle := by intro i; fin_cases i <;> decide
  first_between := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_first, index_first]; exact Nat.add_le_add_left hij 1)]
    rw [index_first, index_first, index_first]
    change (1+i.val ≤ 1+t.val ∧ 1+t.val ≤ 1+j.val) ↔ (i.val ≤ t.val ∧ t.val ≤ j.val)
    omega
  second_between := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_second, index_second]; exact Nat.sub_le_sub_left hij 10)]
    rw [index_second, index_second, index_second]
    change (10-j.val ≤ 10-t.val ∧ 10-t.val ≤ 10-i.val) ↔ (i.val ≤ t.val ∧ t.val ≤ j.val)
    omega
  second_not_on_first_rail := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_first, index_first]; exact Nat.add_le_add_left hij 1)]
    rw [index_first, index_first, index_second]
    omega
  first_not_on_second_rail := by
    intro i j t hij
    rw [(sourceLemma39_cycle_oriented_index graph boundary boundary_isCycle
      (all_on_boundary _) (all_on_boundary _) (all_on_boundary _)).1
      (by rw [index_second, index_second]; exact Nat.sub_le_sub_left hij 10)]
    rw [index_second, index_second, index_first]
    omega
  rung := rung
  rung_isPath := by intro i; fin_cases i <;> norm_num [rung, first, second, Walk.cons_isPath_iff, Fin.val_last]
  rung_internal_disjoint_cycle := by
    intro i; apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    simp only [rung, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  rung_vertex_disjoint := by
    intro i j hij; apply Set.disjoint_left.mpr; intro z hzi hzj
    change z ∈ (rung i).support at hzi
    change z ∈ (rung j).support at hzj
    simp only [rung, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hzi hzj
    rcases hzi with hzi | hzi <;> rcases hzj with hzj | hzj
    · apply hij; apply Fin.ext
      have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change 1+i.val = 1+j.val at hv; omega
    · have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change 1+i.val = 10-j.val at hv; omega
    · have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change 10-i.val = 1+j.val at hv; omega
    · apply hij; apply Fin.ext
      have hv := congrArg Fin.val (hzi.symm.trans hzj)
      change 10-i.val = 10-j.val at hv; omega
  u := 8
  v := 10
  u_on_cycle := by decide
  v_on_cycle := by decide
  u_ne_v := by decide
  u_on_first_end_arc := by
    unfold sourceOrientedCycleSubpath
    decide
  v_on_second_end_arc := by
    unfold sourceOrientedCycleSubpath
    decide
  q := .cons (by decide : graph.Adj 8 10) .nil
  q_isPath := by simp [Walk.cons_isPath_iff]
  q_internal_disjoint_cycle := by
    apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    change z ∈ [8,10] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  q_internal_disjoint_rungs := by
    intro i; apply Set.disjoint_left.mpr; intro z hz _
    rcases hz with ⟨hz, ha, hb⟩
    change z ∈ [8,10] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz.elim ha hb
  q_inter_ladder := by decide
  rung_edges_disjoint_cycle := by intro i; fin_cases i <;> decide
  q_edges_disjoint_cycle := by decide
  q_edges_disjoint_rungs := by intro i; fin_cases i <;> decide


/-- Edge exclusion does not establish the source proof's separated rail placement. -/
theorem separated_rail_localization_fails :
    (∃ i, first i ∉ (sourceOrientedCycleSubpath graph boundary
      separatedEdges.u_on_cycle separatedEdges.v_on_cycle).support) ∧
    (∃ i, second i ∉ (sourceOrientedCycleSubpath graph boundary
      separatedEdges.v_on_cycle separatedEdges.u_on_cycle).support) := by
  constructor
  · refine ⟨0, ?_⟩
    unfold sourceOrientedCycleSubpath
    decide
  · refine ⟨1, ?_⟩
    unfold sourceOrientedCycleSubpath
    decide
/-- Exchanging u and v still cannot put the entire second rail on one boundary arc. -/
theorem swapping_crossing_orientation_does_not_repair :
    ∃ i, second i ∉ (sourceOrientedCycleSubpath graph boundary
      separatedEdges.u_on_cycle separatedEdges.v_on_cycle).support := by
  refine ⟨3, ?_⟩
  unfold sourceOrientedCycleSubpath
  decide
/-- The exact rail-placement disjunction needed by the source proof is false. -/
theorem no_separated_rail_orientation :
    ¬ (( (∀ i, first i ∈ (sourceOrientedCycleSubpath graph boundary
          separatedEdges.u_on_cycle separatedEdges.v_on_cycle).support) ∧
        (∀ i, second i ∈ (sourceOrientedCycleSubpath graph boundary
          separatedEdges.v_on_cycle separatedEdges.u_on_cycle).support)) ∨
       ((∀ i, first i ∈ (sourceOrientedCycleSubpath graph boundary
          separatedEdges.v_on_cycle separatedEdges.u_on_cycle).support) ∧
        (∀ i, second i ∈ (sourceOrientedCycleSubpath graph boundary
          separatedEdges.u_on_cycle separatedEdges.v_on_cycle).support))) := by
  intro h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := separated_rail_localization_fails.1
    exact hi (h.1 i)
  · obtain ⟨i, hi⟩ := swapping_crossing_orientation_does_not_repair
    exact hi (h.2 i)
/-- All four rungs and Q are genuine one-edge paths in this repaired certificate. -/
theorem one_edge_paths_retained :
    (∀ i, (separatedEdges.rung i).length = 1) ∧ separatedEdges.q.length = 1 := by
  constructor
  · intro i; rfl
  · rfl
/-- Retaining the strict true gaps excludes the edge-safe misplaced crossing. -/
theorem misplaced_crossing_excluded :
    ¬ ∃ L : SourceLemma39AmbientCrossladder graph boundary 4,
      L.firstVertex = first ∧ L.secondVertex = second ∧ L.u = 8 ∧ L.v = 10 := by
  rintro ⟨L, hf, hs, hu, hv⟩
  rcases L.q_end_gap_partition with h | h
  · have ho := h.1.1
    change L.u ∈ (sourceOrientedCycleSubpath graph boundary
      (L.second_on_cycle 0) (L.first_on_cycle 0)).support at ho
    have bad : (8 : Fin 12) ∉ (sourceOrientedCycleSubpath graph boundary
        (all_on_boundary 10) (all_on_boundary 1)).support := by
      unfold sourceOrientedCycleSubpath
      decide
    have congruent {a b a' b' : Fin 12} (ha : a ∈ boundary.support)
        (hb : b ∈ boundary.support) (ha' : a' ∈ boundary.support)
        (hb' : b' ∈ boundary.support) (hea : a = a') (heb : b = b') :
        (sourceOrientedCycleSubpath graph boundary ha hb).support =
          (sourceOrientedCycleSubpath graph boundary ha' hb').support := by
      subst a'; subst b'; rfl
    have he := congruent (L.second_on_cycle 0) (L.first_on_cycle 0)
      (all_on_boundary 10) (all_on_boundary 1)
      (show L.secondVertex 0 = 10 by rw [hs]; rfl)
      (show L.firstVertex 0 = 1 by rw [hf]; rfl)
    rw [he, hu] at ho
    exact bad ho
  · have hn := h.1.2.1
    change L.v ≠ L.secondVertex 0 at hn
    rw [hv, hs] at hn
    exact hn rfl

end JSP000089.CrossladderLocalizationRegression
#print axioms JSP000089.CrossladderRegression.boundary
#print axioms JSP000089.CrossladderRegression.boundary_isCycle
#print axioms JSP000089.CrossladderRegression.rung
#print axioms JSP000089.CrossladderRegression.degenerate
#print axioms JSP000089.CrossladderRegression.all_three_collisions
#print axioms JSP000089.CrossladderRegression.boundary_crossing_excluded
#print axioms JSP000089.CrossladderRegression.boundary_rung_excluded
#print axioms JSP000089.CrossladderRegression.reused_rung_excluded
#print axioms JSP000089.CrossladderRegression.all_on_boundary
#print axioms JSP000089.CrossladderRegression.index_first
#print axioms JSP000089.CrossladderRegression.index_second
#print axioms JSP000089.CrossladderOneEdgeRegression.boundary
#print axioms JSP000089.CrossladderOneEdgeRegression.boundary_isCycle
#print axioms JSP000089.CrossladderOneEdgeRegression.all_on_boundary
#print axioms JSP000089.CrossladderOneEdgeRegression.genuine
#print axioms JSP000089.CrossladderOneEdgeRegression.genuine_one_edge_paths_permitted
#print axioms JSP000089.CrossladderOneEdgeRegression.genuine_baseline_cycles
#print axioms JSP000089.CrossladderLocalizationRegression.boundary
#print axioms JSP000089.CrossladderLocalizationRegression.boundary_isCycle
#print axioms JSP000089.CrossladderLocalizationRegression.rung
#print axioms JSP000089.CrossladderLocalizationRegression.separatedEdges
#print axioms JSP000089.CrossladderLocalizationRegression.separated_rail_localization_fails
#print axioms JSP000089.CrossladderLocalizationRegression.swapping_crossing_orientation_does_not_repair
#print axioms JSP000089.CrossladderLocalizationRegression.one_edge_paths_retained
#print axioms JSP000089.CrossladderLocalizationRegression.all_on_boundary
#print axioms JSP000089.CrossladderLocalizationRegression.index_first
#print axioms JSP000089.CrossladderLocalizationRegression.index_second

#print axioms JSP000089.CrossladderRegression.degenerate_baseline_is_not_cycle

#print axioms JSP000089.CrossladderRegression.graph
#print axioms JSP000089.CrossladderRegression.first
#print axioms JSP000089.CrossladderRegression.second
#print axioms JSP000089.CrossladderOneEdgeRegression.graph
#print axioms JSP000089.CrossladderLocalizationRegression.graph
#print axioms JSP000089.CrossladderLocalizationRegression.first
#print axioms JSP000089.CrossladderLocalizationRegression.second
#print axioms JSP000089.CrossladderRegression.GeometryBeforeRepair

#print axioms JSP000089.CrossladderLocalizationRegression.no_separated_rail_orientation

#print axioms JSP000089.CrossladderLocalizationRegression.GeometryWithEdgeExclusion
#print axioms JSP000089.CrossladderLocalizationRegression.misplaced_crossing_excluded

namespace JSP000089.CrossladderSubsetSumRegression
/-- Literal source 4m instance: the ambient theorem retains all m independent choices. -/
theorem exact_source_instance {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] {r : V} {C : G.Walk r r} {m : ℕ}
    (L : SourceLemma39AmbientCrossladder G C (4 * m)) :
    ∃ (base : ℕ) (delta : Fin m → ℕ), 0 < base ∧ (∀ i, 0 < delta i) ∧
      ∀ I : Finset (Fin m), IsCycleLength G (base + ∑ i ∈ I, delta i) :=
  sourceLemma23_ambient_crossladder_subsetSums G L (le_refl _)
/-- The genuine one-edge fixture gives positive sets even when k/8 is zero. -/
theorem genuine_one_edge_positive_spectrum :
    ∃ A B : Finset ℕ, (∀ a ∈ A, 0 < a) ∧ (∀ b ∈ B, 0 < b) ∧
      ∀ a ∈ A, ∀ b ∈ B, IsCycleLength CrossladderOneEdgeRegression.graph (a + b) := by
  obtain ⟨A, B, _, _, hA, hB, hAB⟩ := sourceLemma25_ambient_crossladder_spectrum
    CrossladderOneEdgeRegression.graph CrossladderOneEdgeRegression.genuine
  exact ⟨A, B, hA, hB, hAB⟩
end JSP000089.CrossladderSubsetSumRegression
#print axioms JSP000089.sourceLemma23_first_detour
#print axioms JSP000089.sourceLemma23_second_detour
#print axioms JSP000089.sourceLemma23_crossladder_endpoint_ne
#print axioms JSP000089.sourceLemma23_crossladder_rung_boundary
#print axioms JSP000089.sourceLemma23_crossladder_detours_isPath
#print axioms JSP000089.sourceLemma23_crossladder_detour_lengths
#print axioms JSP000089.sourceLemma23_order_mem
#print axioms JSP000089.sourceLemma23_oriented_interval_wrap
#print axioms JSP000089.sourceLemma23_arc_mem_iff
#print axioms JSP000089.sourceLemma23_anchor_index
#print axioms JSP000089.sourceLemma23_opposite_rails_disjoint
#print axioms JSP000089.sourceLemma23_crossladder_detour_intersections
#print axioms JSP000089.sourceLemma23_crossladder_rail_order
#print axioms JSP000089.sourceLemma23_crossladder_detour_edges
#print axioms JSP000089.sourceLemma23_crossladder_cell_cycles
#print axioms JSP000089.sourceLemma23_crossladder_signed_increments
#print axioms JSP000089.sourceLemma23_strict_arc_mem_iff
#print axioms JSP000089.sourceLemma23_crossladder_gap_coordinates
#print axioms JSP000089.sourceLemma23_arc_index
#print axioms JSP000089.sourceLemma23_arc_length
#print axioms JSP000089.sourceLemma23_arc_preserves_order
#print axioms JSP000089.sourceLemma23_arc_segment_length
#print axioms JSP000089.sourceLemma23_crossladder_normalized_rails
#print axioms JSP000089.sourceLemma23_separated_rail_segments
#print axioms JSP000089.sourceLemma23_detour_carriers
#print axioms JSP000089.sourceLemma23_separated_detours
#print axioms JSP000089.sourceLemma23_q_inter_carrier
#print axioms JSP000089.sourceLemma23_detour_ambient_carriers
#print axioms JSP000089.sourceLemma23_ambient_crossladder_signed_families
#print axioms JSP000089.sourceLemma23_ambient_crossladder_subsetSums
#print axioms JSP000089.sourceLemma25_crossladder_division
#print axioms JSP000089.sourceLemma25_ambient_crossladder_spectrum
#print axioms JSP000089.sourceLemma25_residual_crossladder_spectrum_complete
#print axioms JSP000089.sourceLemma25_direct_crossladder_spectrum_complete

#print axioms JSP000089.CrossladderSubsetSumRegression.exact_source_instance
#print axioms JSP000089.CrossladderSubsetSumRegression.genuine_one_edge_positive_spectrum

#check JSP000089.sourceLemma23_ambient_crossladder_subsetSums
#print JSP000089.sourceLemma23_ambient_crossladder_subsetSums
#check JSP000089.sourceLemma25_ambient_crossladder_spectrum
#print JSP000089.sourceLemma25_ambient_crossladder_spectrum
#check JSP000089.sourceLemma25_residual_crossladder_spectrum_complete
#check JSP000089.sourceLemma25_direct_crossladder_spectrum_complete

-- Source Lemma 2.4 and the scoped Branch-I mesh transport.
#print axioms JSP000089.sourceLemma24_mesh_cell_span
#print axioms JSP000089.sourceLemma24_mesh_cell_span_positive
#print axioms JSP000089.sourceLemma24_unrooted_proper_mesh_subsetSums
#print axioms JSP000089.sourceLemma25_unrooted_proper_mesh_spectrum
#print axioms JSP000089.sourceLemma24_map_cycle_length
#print axioms JSP000089.sourceLemma25_branchI_residual_mesh_spectrum_complete
#check JSP000089.sourceLemma24_unrooted_proper_mesh_subsetSums
#print JSP000089.sourceLemma24_unrooted_proper_mesh_subsetSums
#check JSP000089.sourceLemma25_unrooted_proper_mesh_spectrum
#print JSP000089.sourceLemma25_unrooted_proper_mesh_spectrum
#check JSP000089.sourceLemma25_branchI_residual_mesh_spectrum_complete
#print JSP000089.sourceLemma25_branchI_residual_mesh_spectrum_complete

#check JSP000089.sourceLemma39_ambient_or_spectrum_spectrum_complete
#print JSP000089.sourceLemma39_ambient_or_spectrum_spectrum_complete
#print axioms JSP000089.sourceLemma39_ambient_or_spectrum_spectrum_complete
#check JSP000089.sourceLemma39_branchII_spectrum_complete
#print JSP000089.sourceLemma39_branchII_spectrum_complete
#print axioms JSP000089.sourceLemma39_branchII_spectrum_complete

#check JSP000089.sourceLemma25_direct_truncation_ambient
#print JSP000089.sourceLemma25_direct_truncation_ambient
#print axioms JSP000089.sourceLemma25_direct_truncation_ambient

#check JSP000089.sourceLemma25_branchI_direct_truncation_spectrum_complete
#print JSP000089.sourceLemma25_branchI_direct_truncation_spectrum_complete
#print axioms JSP000089.sourceLemma25_branchI_direct_truncation_spectrum_complete

#check JSP000089.sourceLemma25_unrooted_truncation_ambient
#print JSP000089.sourceLemma25_unrooted_truncation_ambient
#print axioms JSP000089.sourceLemma25_unrooted_truncation_ambient

#check JSP000089.sourceLemma25_branchI_residual_truncation_spectrum_complete
#print JSP000089.sourceLemma25_branchI_residual_truncation_spectrum_complete
#print axioms JSP000089.sourceLemma25_branchI_residual_truncation_spectrum_complete

#check JSP000089.sourceLemma25_direct_crossladder_ambient
#print JSP000089.sourceLemma25_direct_crossladder_ambient
#print axioms JSP000089.sourceLemma25_direct_crossladder_ambient

#check JSP000089.sourceLemma25_branchI_direct_crossladder_spectrum_complete
#print JSP000089.sourceLemma25_branchI_direct_crossladder_spectrum_complete
#print axioms JSP000089.sourceLemma25_branchI_direct_crossladder_spectrum_complete

#check JSP000089.sourceLemma25_section2_crossladder_ambient
#print JSP000089.sourceLemma25_section2_crossladder_ambient
#print axioms JSP000089.sourceLemma25_section2_crossladder_ambient

#check JSP000089.sourceLemma25_branchI_residual_block_spectrum_complete
#print JSP000089.sourceLemma25_branchI_residual_block_spectrum_complete
#print axioms JSP000089.sourceLemma25_branchI_residual_block_spectrum_complete

/- Unified Lemma-3.9 spectrum and the preceding direct-net milestone. -/
namespace JSP000089
open private sourceLemma25_net_ordered_selection sourceLemma25_net_cycle_spectrum from GraphFoundations

#check sourceLemma39_branchI_spectrum_complete
#print sourceLemma39_branchI_spectrum_complete
#print axioms sourceLemma39_branchI_spectrum_complete

#check sourceLemma39_spectrum_complete
#print sourceLemma39_spectrum_complete
#print axioms sourceLemma39_spectrum_complete

#check sourceLemma39_bounded_spectrum_complete
#print sourceLemma39_bounded_spectrum_complete
#print axioms sourceLemma39_bounded_spectrum_complete

#check sourceLemma25_branchI_direct_net_spectrum_complete
#print sourceLemma25_branchI_direct_net_spectrum_complete
#print axioms sourceLemma25_branchI_direct_net_spectrum_complete

#check sourceLemma25_net_ordered_selection
#print sourceLemma25_net_ordered_selection
#print axioms sourceLemma25_net_ordered_selection

#check sourceLemma25_net_cycle_spectrum
#print sourceLemma25_net_cycle_spectrum
#print axioms sourceLemma25_net_cycle_spectrum

end JSP000089

/- Source Theorem 3 prerequisites, including private arithmetic and cycle producers. -/
namespace JSP000089
open private sourceTheorem3_c_bound sourceTheorem3_not_acyclic sourceTheorem3_parameter_le_threshold from GraphFoundations

#check sourceTheorem3_c_bound
#print sourceTheorem3_c_bound
#print axioms sourceTheorem3_c_bound

#check sourceTheorem3_numerical_threshold
#print sourceTheorem3_numerical_threshold
#print axioms sourceTheorem3_numerical_threshold

#check sourceTheorem3_card_lower_bound
#print sourceTheorem3_card_lower_bound
#print axioms sourceTheorem3_card_lower_bound

#check sourceTheorem3_mader_extraction
#print sourceTheorem3_mader_extraction
#print axioms sourceTheorem3_mader_extraction

#check sourceTheorem3_not_acyclic
#print sourceTheorem3_not_acyclic
#print axioms sourceTheorem3_not_acyclic

#check sourceTheorem3_longest_cycle
#print sourceTheorem3_longest_cycle
#print axioms sourceTheorem3_longest_cycle

#check sourceTheorem3_induced_girth
#print sourceTheorem3_induced_girth
#print axioms sourceTheorem3_induced_girth

#check sourceTheorem3_parameter_le_threshold
#print sourceTheorem3_parameter_le_threshold
#print axioms sourceTheorem3_parameter_le_threshold

#check sourceTheorem3_parameter_selection
#print sourceTheorem3_parameter_selection
#print axioms sourceTheorem3_parameter_selection

#check sourceTheorem3_lemma39_inputs
#print sourceTheorem3_lemma39_inputs
#print axioms sourceTheorem3_lemma39_inputs

end JSP000089

/- Complete source Theorem 3, including the scaled choose estimate. -/
namespace JSP000089
open private sourceTheorem3_choose_three_scaled from GraphFoundations

#check sourceTheorem3_choose_three_scaled
#print sourceTheorem3_choose_three_scaled
#print axioms sourceTheorem3_choose_three_scaled

#check sourceTheorem3_c_sharp_bound
#print sourceTheorem3_c_sharp_bound
#print axioms sourceTheorem3_c_sharp_bound

#check sourceTheorem3_successor_threshold
#print sourceTheorem3_successor_threshold
#print axioms sourceTheorem3_successor_threshold

#check sourceTheorem3_second_threshold
#print sourceTheorem3_second_threshold
#print axioms sourceTheorem3_second_threshold

#check sourceTheorem3_selected_parameter_ge_two
#print sourceTheorem3_selected_parameter_ge_two
#print axioms sourceTheorem3_selected_parameter_ge_two

#check sourceTheorem3_complete
#print sourceTheorem3_complete
#print axioms sourceTheorem3_complete

end JSP000089

-- Principal Theorem 1 assembly, preserving the original statement contract.
#check JSP000089.jsp_000089_statement
#print JSP000089.jsp_000089_statement

#check JSP000089.sourceLemma43_theorem3_threshold
#print JSP000089.sourceLemma43_theorem3_threshold
#print axioms JSP000089.sourceLemma43_theorem3_threshold

#check JSP000089.sourceTheorem3_high_girth_unavoidable
#print JSP000089.sourceTheorem3_high_girth_unavoidable
#print axioms JSP000089.sourceTheorem3_high_girth_unavoidable

#check JSP000089.source_averageDegree10_cycle
#print JSP000089.source_averageDegree10_cycle
#print axioms JSP000089.source_averageDegree10_cycle

#check JSP000089.source_averageDegree10_girth_pos
#print JSP000089.source_averageDegree10_girth_pos
#print axioms JSP000089.source_averageDegree10_girth_pos

#check JSP000089.source_short_girth_unavoidable
#print JSP000089.source_short_girth_unavoidable
#print axioms JSP000089.source_short_girth_unavoidable

#check JSP000089.jsp_000089_complete
#print JSP000089.jsp_000089_complete
#print axioms JSP000089.jsp_000089_complete

#check JSP000089.sourceSparsity099_finalSet
#print JSP000089.sourceSparsity099_finalSet
#print axioms JSP000089.sourceSparsity099_finalSet

example : JSP000089.jsp_000089_statement := JSP000089.jsp_000089_complete
