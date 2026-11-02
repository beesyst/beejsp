import SubspaceBridge.BinarySourceNorms2
import SubspaceBridge.BinaryLogTailBounds2
open scoped BigOperators Classical Matrix
namespace JSP000334

noncomputable def binaryPatternNorms (d : ℕ) (b c : ℤ) (k : Fin 3 → Fin 2)
    (z : Fin 2 → ℤ) (tau : Fin 3) (i : Fin 2) : ℝ :=
  rothLocalAbs tau (binaryLocalVectorValue (binaryIntegerRetained2 d b c (k tau)) z i)

theorem binary_weighted_source_point (B C : ℚ) (d : ℕ) (hd : 0<d) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) :
    ∃ cut : ℝ,1≤cut ∧ ∀ z : Fin 2 → ℤ,PrimitivePair z →
    z 0 ≠ 0 → z 1 ≠ 0 → B*(z 0 : ℚ)+C*(z 1 : ℚ) ≠ 0 →
    cut<(archPairHeight z : ℝ) →
    (weightedNormalizedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ)<
      Real.rpow (archPairHeight z : ℝ) (-(5 : ℝ)/2) →
    ∃ k : Fin 3 → Fin 2,
    let a := binaryPatternNorms d b c k z
    let Q := (archPairHeight z : ℝ)^4
    1<Q ∧ (∀ tau i,0<a tau i) ∧
    (∑ tau : Fin 3,∑ i : Fin 2,binaryLogWeights a Q tau i)=0 ∧
    (∀ tau i,|binaryLogWeights a Q tau i|≤15/32) ∧
    (1 : ℝ)/192≤binaryLogAlpha a Q ∧
    (∀ tau i,a tau i≤Real.rpow Q (binaryLogWeights a Q tau i-if tau=0 then (1 : ℝ)/192 else 0)) := by
  let M := binaryIntegerFormConstant d b c
  let K := (threePlaceProduct (d : ℚ) : ℝ)^2
  have hM : 1≤M := by
    dsimp [M,binaryIntegerFormConstant]
    have hd0 : (0 : ℝ)≤d := Nat.cast_nonneg d
    have hb0 : (0 : ℝ)≤b.natAbs := Nat.cast_nonneg b.natAbs
    have hc0 : (0 : ℝ)≤c.natAbs := Nat.cast_nonneg c.natAbs
    linarith
  have hK : 0<K := by
    dsimp [K]
    have hh : 0<(threePlaceProduct (d : ℚ) : ℝ) := by
      exact_mod_cast weighted_constant_pos2 (d : ℚ) (by exact_mod_cast (ne_of_gt hd))
    positivity
  let cut := max 1 (max (K^4) (M^8))
  refine ⟨cut,le_max_left _ _,?_⟩
  intro z hz h0 h1 hs htail hproduct
  have hH : 1<(archPairHeight z : ℝ) := lt_of_le_of_lt (le_max_left _ _) htail
  have hKcut : K^4<(archPairHeight z : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) htail
  have hMcut : M^8<(archPairHeight z : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) htail
  obtain ⟨k,hk⟩ := binary_integer_pattern_product B C d b c hb hc z
  let a := binaryPatternNorms d b c k z
  let Q := (archPairHeight z : ℝ)^4
  have hQ : 1<Q := one_lt_pow₀ hH (by decide)
  have ha (tau i) : 0<a tau i :=
    (binary_pattern_local_bounds B C d hd b c hb hc (k tau) z h0 h1 hs tau i).1
  have hp : (∏ tau : Fin 3,∏ i : Fin 2,a tau i)<Real.rpow Q (-(1 : ℝ)/16) := by
    calc
      _ = K*(weightedRetainedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ) := hk
      _ < K*Real.rpow (archPairHeight z : ℝ) (-(1 : ℝ)/2) :=
        mul_lt_mul_of_pos_left (binary_primitive_retained_bound B C z hz hH hproduct) hK
      _ < _ := binary_denominator_tail_bound K _ hK hH hKcut
  have halpha := binary_log_positive_margin a Q hQ ha hp
  have hlocal (tau i) := binary_pattern_local_bounds B C d hd b c hb hc (k tau) z h0 h1 hs tau i
  have hbounds := binary_log_tail_bounds M (archPairHeight z : ℝ) hM hH hMcut a ha
    (fun tau i => (hlocal tau i).2.1)
    (fun i => (hlocal 0 i).2.2.2 rfl)
    (fun tau ht i => (hlocal tau i).2.2.1 ht)
  have hdelta : (1 : ℝ)/192≤binaryLogAlpha a Q := by linarith
  exact ⟨k,hQ,ha,binary_log_balance a Q hQ,
    binary_log_uniform_bound a Q (by linarith) hbounds.1 hbounds.2,hdelta,
    binary_log_source_bounds a Q hQ ha hdelta⟩

end JSP000334
