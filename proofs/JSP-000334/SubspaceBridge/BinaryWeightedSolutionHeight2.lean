import SubspaceBridge.BinarySourceFamilyBounded2
open scoped BigOperators Classical
namespace JSP000334

def BinaryWeightedNonexceptional (B C : ℚ) (z : Fin 2 → ℤ) : Prop :=
  PrimitivePair z ∧ z 0 ≠ 0 ∧ z 1 ≠ 0 ∧ B*(z 0 : ℚ)+C*(z 1 : ℚ) ≠ 0 ∧
  (weightedNormalizedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ)<
    Real.rpow (archPairHeight z : ℝ) (-(5 : ℝ)/2)

theorem binary_weighted_solution_height_bound (B C : ℚ) (hB : B ≠ 0) (hC : C ≠ 0) :
    ∃ M : ℝ,∀ z : Fin 2 → ℤ,BinaryWeightedNonexceptional B C z → (archPairHeight z : ℝ)≤M := by
  obtain ⟨d,hd,b,c,hb,hc⟩ := binary_common_denominator B C
  obtain ⟨cut,hcut,hbounded⟩ := binary_weighted_source_family_bounded B C hB hC d hd b c hb hc
  let U : Set ℝ := {Q | ∃ z : Fin 2 → ℤ,BinaryWeightedNonexceptional B C z ∧
    cut<(archPairHeight z : ℝ) ∧ Q=(archPairHeight z : ℝ)^4}
  have hp (q : U) : ∃ z : Fin 2 → ℤ,BinaryWeightedNonexceptional B C z ∧
      cut<(archPairHeight z : ℝ) ∧ q.val=(archPairHeight z : ℝ)^4 := q.property
  choose z hz htail hparam using hp
  have hU : BddAbove U := hbounded U z (fun q => (hz q).1)
    (fun q => ⟨(hz q).2.1,(hz q).2.2.1,(hz q).2.2.2.1⟩) htail
    (fun q => (hz q).2.2.2.2) hparam
  obtain ⟨M,hM⟩ := hU
  refine ⟨max cut (max 1 M),?_⟩
  intro z hz
  by_contra! hlarge
  have hc : cut<(archPairHeight z : ℝ) := lt_of_le_of_lt (le_max_left _ _) hlarge
  have hH : 1<(archPairHeight z : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlarge
  have hm : M<(archPairHeight z : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlarge
  have hh := hM (show (archPairHeight z : ℝ)^4 ∈ U from ⟨z,hz,hc,rfl⟩)
  have hpow : (archPairHeight z : ℝ)≤(archPairHeight z : ℝ)^4 := by
    simpa using (pow_le_pow_right₀ hH.le (by decide : 1≤4))
  linarith

end JSP000334
