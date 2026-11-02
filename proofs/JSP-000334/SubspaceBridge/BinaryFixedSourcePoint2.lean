import SubspaceBridge.BinaryWeightedSourcePoint2
import SubspaceBridge.BinaryFiniteWeights2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_weighted_fixed_source_point (B C : ℚ) (d : ℕ) (hd : 0<d) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) :
    ∃ cut : ℝ,1≤cut ∧ ∀ z : Fin 2 → ℤ,PrimitivePair z →
    z 0 ≠ 0 → z 1 ≠ 0 → B*(z 0 : ℚ)+C*(z 1 : ℚ) ≠ 0 →
    cut<(archPairHeight z : ℝ) →
    (weightedNormalizedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ)<
      Real.rpow (archPairHeight z : ℝ) (-(5 : ℝ)/2) →
    ∃ k : Fin 3 → Fin 2,∃ v ∈ binaryWeightCandidates,
    let Q := (archPairHeight z : ℝ)^4
    1<Q ∧ (∑ tau : Fin 3,∑ i : Fin 2,v tau i)=0 ∧ (∀ tau i,|v tau i|≤1) ∧
    (∀ tau i,binaryPatternNorms d b c k z tau i≤Real.rpow Q (v tau i-if tau=0 then (1 : ℝ)/384 else 0)) := by
  obtain ⟨cut,hcut,hpoint⟩ := binary_weighted_source_point B C d hd b c hb hc
  refine ⟨cut,hcut,?_⟩
  intro z hz h0 h1 hs htail hp
  obtain ⟨k,hQ,ha,hbal,hbound,hdelta,hnorm⟩ := hpoint z hz h0 h1 hs htail hp
  let v := binaryLogWeights (binaryPatternNorms d b c k z) ((archPairHeight z : ℝ)^4)
  have hm := binary_weight_approx_mem v hbal hbound
  have hr := binary_weight_round_bounds v hbal hbound
  refine ⟨k,binaryWeightApprox v,hm,hQ,(hm.2).1,(hm.2).2,?_⟩
  intro tau i
  apply (hnorm tau i).trans
  apply Real.rpow_le_rpow_of_exponent_le hQ.le
  by_cases ht : tau=0
  · subst tau
    have hh := hr.2.1 i
    simp only [ite_true]
    linarith
  · have hh := hr.2.2 tau ht i
    simp only [if_neg ht,sub_zero]
    exact hh

end JSP000334
