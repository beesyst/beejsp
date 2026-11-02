import SubspaceBridge.SourceSampleSchmidtContradiction10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtContradiction10
open SchmidtNormal10 OriginalDual10 SourceSampling10 SourceSelectedSet10 SourceHeightEnvelope10
open SchmidtCoordinate10 SchmidtPolynomial10 SchmidtRationalNormalization6 SchmidtScalar10 SourceSchmidtBudget10

theorem original_sample_schmidt_exclusion10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hc0 : ∀ i, |c 0 i| ≤ 1) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ alpha_growth C_upper T C_sch beta : ℝ,
      0 < alpha_growth ∧ 0 < C_upper ∧ 1 < T ∧
      C_sch = min (1/2 : ℝ) (alpha_growth/180) ∧ 0 < C_sch ∧ C_sch ≤ 1 ∧ 0 < beta ∧
      ∀ (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
        (eta D E : ℝ), 0 < eta → 1 ≤ D → ∀ (m : ℕ) (hm : 0 < m),
        (∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
          Nonempty (OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)) →
        let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
        let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
        let w := JSP000334.omega65 m theta
        ∃ B0 : ℝ,
          B0 = max T (max 2 (max ((2 : ℝ)^(27*(m : ℝ)/(beta*w*C_sch)))
            (D^(9*((m : ℝ)*(1+eta))/(beta*w*C_sch))))) ∧
          1 < B0 ∧ 0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧
          0 < rho ∧ rho ≤ 1/2 ∧ rho ≤ w ∧ 0 < w ∧
          0 < (2 : ℝ)^(27*(m : ℝ)/(beta*w*C_sch)) ∧
          0 < D^(9*((m : ℝ)*(1+eta))/(beta*w*C_sch)) ∧
          (∀ B : ℝ, Nonempty
            (OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)) ∧
          ∀ (B : ℝ), B0 ≤ B →
          ∀ (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm),
      (¬ ∃ s : Fin m → MixedIndex10,
            (∀ h, s h ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2)
              (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2)) ∧
            (∀ h, (L⁻¹.transpose *ᵥ integerReal (S.data.M h)) (s h 0) ≠ 0) ∧
            (∀ h, ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
              (fun k => (S.data.M h k : ℚ_[2]))) (s h 1) ≠ 0) ∧
            (∀ h, ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
              (fun k => (S.data.M h k : ℚ_[3]))) (s h 2) ≠ 0)) ∧
      ∃ h : Fin m, ∀ t : MixedIndex10, ¬ (t ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2) (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2) ∧ (L⁻¹.transpose *ᵥ integerReal (S.data.M h)) (t 0) ≠ 0 ∧ ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (S.data.M h k : ℚ_[2]))) (t 1) ≠ 0 ∧ ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (S.data.M h k : ℚ_[3]))) (t 2) ≠ 0) := by
  obtain ⟨a,Cu,T,Cs,beta,ha,hCu,hT,hCs,hCspos,hCsone,hbeta,hcontradiction⟩ :=
    original_sample_schmidt_contradiction10 A2 A3 L h2 h3 hL hAlg c2 c3 hc2 hc3
      c hc0 hb hc epsilon he
  refine ⟨a,Cu,T,Cs,beta,ha,hCu,hT,hCs,hCspos,hCsone,hbeta,?_⟩
  intro V v eta D E heta hD m hm hfamily
  obtain ⟨B0,hB0,hBpos,ht,htu,hte,hr,hrhalf,hrw,hw,hdpos,hppos,hfamily',hfalse⟩ :=
    hcontradiction V v eta D E heta hD m hm hfamily
  refine ⟨B0,hB0,hBpos,ht,htu,hte,hr,hrhalf,hrw,hw,hdpos,hppos,hfamily',?_⟩
  intro B hB S
  let P : Fin m → MixedIndex10 → Prop := fun h t => (t ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2) (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2) ∧ (L⁻¹.transpose *ᵥ integerReal (S.data.M h)) (t 0) ≠ 0 ∧ ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (S.data.M h k : ℚ_[2]))) (t 1) ≠ 0 ∧ ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (S.data.M h k : ℚ_[3]))) (t 2) ≠ 0)
  have hnone : ¬ ∃ s : Fin m → MixedIndex10, ∀ h, P h (s h) := by
    rintro ⟨s,hs⟩
    exact hfalse B hB S s (fun h => (hs h).1) (fun h => (hs h).2.1)
      (fun h => (hs h).2.2.1) (fun h => (hs h).2.2.2)
  constructor
  · rintro ⟨s,hs,hn0,hn2,hn3⟩
    exact hnone ⟨s,fun h => ⟨hs h,hn0 h,hn2 h,hn3 h⟩⟩
  · change ∃ h, ∀ t, ¬ P h t
    by_contra! hall
    exact hnone ⟨fun h => Classical.choose (hall h),fun h => Classical.choose_spec (hall h)⟩

end CompoundFeasibility.SourceSchmidtContradiction10
