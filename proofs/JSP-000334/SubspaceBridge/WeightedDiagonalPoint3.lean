import SubspaceBridge.WeightedDiagonalWeights3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_integer_source_point3 (y : IntegerTriple) (choice : Fin 3 → Fin 3)
    (C K : ℝ) (hC3 : 3≤C) (hK : 0<K)
    (hH : 3≤(archTripleHeight y : ℝ)) (hC : C≤(archTripleHeight y : ℝ))
    (hKi : K⁻¹≤(archTripleHeight y : ℝ)) (hK4 : K^4≤(archTripleHeight y : ℝ))
    (ha : ∀ tau i,0<(rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))) : ℝ))
    (hinv : ∀ tau i,((rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))) : ℝ))⁻¹≤C*(archTripleHeight y : ℝ))
    (hprod : (tripleChoiceFormsProduct choice (fun j => (y j : ℚ)) : ℝ)*(archTripleHeight y : ℝ)=K) :
    let Q := (archTripleHeight y : ℝ)^4
    ∃ d∈finiteWeightCandidates3 336,∃ hQ : 1<Q,sourceWeightConditions3 d ∧
      y∈qSourceLattice3 (choice 1) (choice 2) Q (d 1) (d 2) ∧
      coordinateGauge3 (qSourceCoordinates3 (choice 0) Q (d 0) hQ) (integerTripleReal3 y)≤Q^(-(1 : ℝ)/24) := by
  intro Q
  let a (tau i : Fin 3) : ℝ := rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ)))
  have hf : ∀ tau,tau≠0 → ∀ i,a tau i≤1 := by
    intro tau ht i
    have hm := retainedIntegerMatrix3_apply (choice tau) i y
    change (rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (y j : ℚ))) : ℝ)≤1
    rw [← hm]
    fin_cases tau
    · exact (ht rfl).elim
    · exact_mod_cast padicNorm.of_int (p:=2) ((retainedIntegerMatrix3 (choice 1) *ᵥ y) i)
    · exact_mod_cast padicNorm.of_int (p:=3) ((retainedIntegerMatrix3 (choice 2) *ᵥ y) i)
  have hp : (∏ tau,∏ i,a tau i)*(archTripleHeight y : ℝ)=K := by
    dsimp [a]
    unfold tripleChoiceFormsProduct at hprod
    exact_mod_cast hprod
  have hrb : ∀ i,a 0 i≤C*(archTripleHeight y : ℝ) := by
    intro i
    have hh := allpoint_form_arch_bound3 y (choice 0) i
    have hcast : a 0 i≤3*(archTripleHeight y : ℝ) := by
      change ((|threeCoordinateSumForms (choice 0) i (fun j => (y j : ℚ))| : ℚ) : ℝ)≤3*(archTripleHeight y : ℝ)
      exact_mod_cast hh
    have hheight : 0≤(archTripleHeight y : ℝ) := by linarith
    exact hcast.trans (mul_le_mul_of_nonneg_right hC3 hheight)
  obtain ⟨hQ,hc,heq,hr,hfinite⟩ := weighted_balanced_weights3
    (archTripleHeight y : ℝ) K C hH hK hC hKi hK4 a ha hrb hf hinv hp
  let c := sourceLogWeights3 Q (weightedBalancedValues3 (archTripleHeight y : ℝ) K a)
  let d := finiteWeightApprox3 336 c
  obtain ⟨hd,hdreal,hdfin⟩ := finiteWeightApprox3_bounds 336 (by norm_num) c hc
  have hQ0 := zero_lt_one.trans hQ
  refine ⟨d,finiteWeightApprox3_mem 336 (by norm_num) c hc,hQ,hd,?_,?_⟩
  · apply ((qSourceLattice3_spec (choice 1) (choice 2) Q (d 1) (d 2) hQ
      (fun i => (hd.2.1 1 (by decide) i).2) (fun i => (hd.2.1 2 (by decide) i).2)).1 y).mpr
    constructor
    · intro i
      change a 1 i≤Q^(d 1 i)
      rw [hfinite 1 (by decide) i]
      exact Real.rpow_le_rpow_of_exponent_le hQ.le (hdfin 1 (by decide) i)
    · intro i
      change a 2 i≤Q^(d 2 i)
      rw [hfinite 2 (by decide) i]
      exact Real.rpow_le_rpow_of_exponent_le hQ.le (hdfin 2 (by decide) i)
  · apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    change |retainedRealCoordinates3 (choice 0) (integerTripleReal3 y) i / Q^(d 0 i)|≤_
    rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos hQ0 _),div_le_iff₀ (Real.rpow_pos_of_pos hQ0 _),← finiteWeight_real_local_value3,finiteWeight_rational_local_value3]
    have hnorm : rothLocalAbs 0 (threeCoordinateSumForms (choice 0) i (fun j => (y j : ℚ)))=a 0 i := by
      simp [a,rothLocalAbs,rationalPlaceNorm]
    rw [hnorm]
    have hexp : c 0 i-(1 : ℝ)/16≤d 0 i-(1 : ℝ)/24 := by
      have hh := hdreal i
      norm_num at hh
      linarith
    have hh := (hr i).trans (Real.rpow_le_rpow_of_exponent_le hQ.le hexp)
    have he : Q^(d 0 i-(1 : ℝ)/24)=Q^(-(1 : ℝ)/24)*Q^(d 0 i) := by
      rw [← Real.rpow_add hQ0]
      congr 1
      ring
    rwa [he] at hh

end JSP000334
