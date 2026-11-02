import SubspaceBridge.SourceSchmidtBudgetBounds10
import SubspaceBridge.SourceSchmidtBudgetParameters10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtBudget10
open SchmidtNormal10 OriginalDual10 SourceSampling10 SourceSelectedSet10 SourceHeightEnvelope10
open SchmidtCoordinate10 SchmidtPolynomial10 SchmidtRationalNormalization6 SchmidtScalar10 SourceSchmidtGrowth10

theorem original_sample_schmidt_budgets10
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
          ∀ (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
            (s : Fin m → MixedIndex10),
            (∀ h, s h ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2)
              (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2)) →
            (∀ h, (L⁻¹.transpose *ᵥ integerReal (S.data.M h)) (s h 0) ≠ 0) →
            (∀ h, ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
              (fun k => (S.data.M h k : ℚ_[2]))) (s h 1) ≠ 0) →
            (∀ h, ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
              (fun k => (S.data.M h k : ℚ_[3]))) (s h 2) ≠ 0) →
            ∃ (C : (h : Fin m) → NormalCoordinateChoice10 (S.data.M h))
              (G : MvPolynomial (Fin m) ℤ),
              G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height10 S.data.P ∧
              (∀ h, G.degreeOf h ≤ S.data.r h) ∧
              G.map (Int.castRingHom ℝ) ∈ monicIdeal6
                (binaryLift6 (permutedNormals10 S.data.M (fun h => (C h).e))) S.data.r ((m : ℝ)*eta) ∧
              (∀ h, 0 < S.data.r h) ∧
              (∀ (h : Fin m) (hh : h.val+1 < m),
                (S.data.r ⟨h.val+1,hh⟩ : ℝ) ≤ w*(S.data.r h : ℝ)) ∧
              let N := permutedNormals10 S.data.M (fun g => (C g).e)
              let b := fun h => rootDenominator6 (N h 0) (N h 1)
              let p := fun h => rootNumerator6 (N h 0) (N h 1)
              (JSP000334.rothIntegerHeight G : ℝ) ≤
                |(b ⟨0,hm⟩ : ℝ)|^(w*(S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ∧
              ∀ h, B0 < (S.data.t h).val^5 ∧
                ((S.data.t h).val^5)^beta ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                N h 0 ≠ 0 ∧ Int.gcd (N h 0) (N h 1)^9 ≤ (N h 0).natAbs^8 ∧
                b h ≠ 0 ∧ Int.gcd (p h) (b h) = 1 ∧
                (normalHeight10 (S.data.M h) : ℝ)^(1/9 : ℝ) ≤ |(b h : ℝ)| ∧
                |(b h : ℝ)| ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                ((S.data.t h).val^5)^(beta/9) ≤ |(b h : ℝ)| ∧
                |(b ⟨0,hm⟩ : ℝ)|^((S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ≤
                  |(b h : ℝ)|^(S.data.r h : ℝ) ∧
                (2 : ℝ)^(3*m) ≤ |(b h : ℝ)|^(w*C_sch) := by
  obtain ⟨alpha_growth,C_upper,Tg,C_sch,hag,hCg,hTg,hCs,hCspos,hCsone,hgrowth⟩ :=
    original_sample_schmidt_growth10 A2 A3 L h2 h3 hL hAlg c2 c3 hc2 hc3
      c hc0 hb hc epsilon he
  obtain ⟨beta,_C_height,Th,hbeta,_hCh,hTh,hheight⟩ := original_sample_height_envelope10
    A2 A3 L h2 h3 hL hAlg c2 c3 hc2 hc3 c hc0 hb hc epsilon he
  refine ⟨alpha_growth,C_upper,max Tg Th,C_sch,beta,hag,hCg,
    hTg.trans_le (le_max_left _ _),hCs,hCspos,hCsone,hbeta,?_⟩
  intro V v eta D E heta hD m hm hfamily
  let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
  let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
  let w := JSP000334.omega65 m theta
  obtain ⟨ht,htu,hte,hr,hrhalf,hrw⟩ := explicit_schmidt_parameters10 m hm eta heta
  have hw : 0 < w := JSP000334.omega65_pos m theta ht
  let Tden := (2 : ℝ)^(27*(m : ℝ)/(beta*w*C_sch))
  let Tpoly := D^(9*((m : ℝ)*(1+eta))/(beta*w*C_sch))
  let B0 := max (max Tg Th) (max 2 (max Tden Tpoly))
  have hB0 : 1 < B0 := hTg.trans_le ((le_max_left Tg Th).trans (le_max_left _ _))
  have hTden : 0 < Tden := Real.rpow_pos_of_pos (by norm_num) _
  have hTpoly : 0 < Tpoly := Real.rpow_pos_of_pos (zero_lt_one.trans_le hD) _
  refine ⟨B0,rfl,hB0,ht,htu,hte,hr,hrhalf,hrw,hw,hTden,hTpoly,hfamily rho hr,?_⟩
  intro B hB S s hs hn0 hn2 hn3
  have hcut (h : Fin m) : B0 < (S.data.t h).val^5 := original_sample_power_cutoff10 S B0 hB h
  have hBTg : Tg ≤ B := (le_max_left Tg Th).trans ((le_max_left _ _).trans hB)
  have hheight_lower (h : Fin m) :
      ((S.data.t h).val^5)^beta ≤ (normalHeight10 (S.data.M h) : ℝ) :=
    (hheight V v eta D E B rho m hm S h
      (((le_max_right Tg Th).trans (le_max_left _ _)).trans_lt (hcut h))
      (s h) (hs h) (hn0 h) (hn2 h) (hn3 h)).1
  obtain ⟨C,G,hGn,hGH,hdeg,hmonic,hdata⟩ := hgrowth V v eta D E B rho m hm hBTg S s hs hn0 hn2 hn3
  let N := permutedNormals10 S.data.M (fun g => (C g).e)
  let b := fun h => rootDenominator6 (N h 0) (N h 1)
  have hden_lower (h : Fin m) : ((S.data.t h).val^5)^(beta/9) ≤ |(b h : ℝ)| :=
    height_denominator_power_lower10 _ beta _ _
      (zero_lt_one.trans (S.conditions.large h).2.2.1) (hheight_lower h) (hdata h).2.2.2.2.1
  have hden_cut (h : Fin m) : Tden ≤ (S.data.t h).val^5 :=
    ((le_max_left Tden Tpoly).trans ((le_max_right 2 _).trans (le_max_right _ _))).trans (hcut h).le
  have hpoly_cut : Tpoly ≤ (S.data.t ⟨0,hm⟩).val^5 :=
    ((le_max_right Tden Tpoly).trans ((le_max_right 2 _).trans (le_max_right _ _))).trans (hcut ⟨0,hm⟩).le
  have hGheight := original_sample_reduced_height10 heta hD S G hGH
  have hpoly := polynomial_budget_threshold beta w C_sch D ((m : ℝ)*(1+eta))
    ((S.data.t ⟨0,hm⟩).val^5) |(b ⟨0,hm⟩ : ℝ)|
    (S.data.r ⟨0,hm⟩) (JSP000334.rothIntegerHeight G)
    hbeta hw hCspos (zero_lt_one.trans_le hD)
    (zero_lt_one.trans (S.conditions.large ⟨0,hm⟩).2.2.1) (Nat.cast_nonneg _)
    (hden_lower ⟨0,hm⟩) hGheight hpoly_cut
  refine ⟨C,G,hGn,hGH,hdeg,hmonic,S.conditions.positive_degrees,?_,hpoly,?_⟩
  · intro h hh
    exact (S.conditions.degree_separation h hh).trans
      (mul_le_mul_of_nonneg_right hrw (Nat.cast_nonneg _))
  · intro h
    obtain ⟨hN,hgcd,hbn,hcop,hroot,hupper,hgrow⟩ := hdata h
    refine ⟨hcut h,hheight_lower h,hN,hgcd,hbn,hcop,hroot,hupper,hden_lower h,hgrow,?_⟩
    exact denominator_budget_threshold m beta w C_sch ((S.data.t h).val^5) |(b h : ℝ)|
      hbeta hw hCspos (zero_lt_one.trans (S.conditions.large h).2.2.1)
      (hden_lower h) (hden_cut h)

end CompoundFeasibility.SourceSchmidtBudget10
