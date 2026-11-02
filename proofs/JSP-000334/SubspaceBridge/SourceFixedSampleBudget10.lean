import SubspaceBridge.SourceFixedBudgetNumeric10
import SubspaceBridge.SourceSchmidtBudgetParameters10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedBudget10
open SchmidtNormal10 OriginalDual10 SourceSampling10 SourceSelectedSet10 SourceHeightEnvelope10
open SchmidtCoordinate10 SchmidtPolynomial10 SchmidtRationalNormalization6 SchmidtScalar10 SourceSchmidtGrowth10 SourceSchmidtBudget10

theorem fixed_sample_schmidt_budgets10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (c2 c3 : Fin 10 → ℝ) (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
    (c : Fin 3 → Fin 10 → ℝ) (epsilon eta D E alpha C_upper T : ℝ)
    (heta : 0 < eta) (hD : 1 ≤ D) (ha : 0 < alpha) (hC : 0 < C_upper) (hT : 1 < T)
    (m : ℕ) (hm : 0 < m) :
    let C_sch := min (1/2 : ℝ) (alpha/180)
    let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
    let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
    let w := JSP000334.omega65 m theta
    ∃ B0 : ℝ,
      B0 = max T (max C_upper (max 2 (max ((2 : ℝ)^(27*(m : ℝ)/(alpha*w*C_sch)))
        (D^(9*((m : ℝ)*(1+eta))/(alpha*w*C_sch)))))) ∧
      1 < B0 ∧ 0 < C_sch ∧ C_sch ≤ 1 ∧
      0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧
      0 < rho ∧ rho ≤ 1/2 ∧ rho ≤ w ∧ 0 < w ∧
      0 < (2 : ℝ)^(27*(m : ℝ)/(alpha*w*C_sch)) ∧
      0 < D^(9*((m : ℝ)*(1+eta))/(alpha*w*C_sch)) ∧
      ∀ (B : ℝ), B0 ≤ B →
      ∀ (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm),
        (∀ h, ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9) →
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
              (JSP000334.rothIntegerHeight G : ℝ) ≤ D^((m : ℝ)*(1+eta)*(S.data.r ⟨0,hm⟩ : ℝ)) ∧
              (JSP000334.rothIntegerHeight G : ℝ) ≤
                |(b ⟨0,hm⟩ : ℝ)|^(w*(S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ∧
              ∀ h, B0 < (S.data.t h).val^5 ∧
                ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                N h 0 ≠ 0 ∧ Int.gcd (N h 0) (N h 1)^9 ≤ (N h 0).natAbs^8 ∧
                b h ≠ 0 ∧ Int.gcd (p h) (b h) = 1 ∧
                (normalHeight10 (S.data.M h) : ℝ)^(1/9 : ℝ) ≤ |(b h : ℝ)| ∧
                |(b h : ℝ)| ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                ((S.data.t h).val^5)^(alpha/9) ≤ |(b h : ℝ)| ∧
                |(b ⟨0,hm⟩ : ℝ)|^((S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ≤
                  |(b h : ℝ)|^(S.data.r h : ℝ) ∧
                (2 : ℝ)^(3*m) ≤ |(b h : ℝ)|^(w*C_sch) := by
  let C_sch := min (1/2 : ℝ) (alpha/180)
  let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
  let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
  let w := JSP000334.omega65 m theta
  obtain ⟨hCs,hCs1,_hcmp⟩ := schmidt_constant_range10 alpha ha
  obtain ⟨ht,htu,hte,hr,hrhalf,hrw⟩ := explicit_schmidt_parameters10 m hm eta heta
  have hw : 0 < w := JSP000334.omega65_pos m theta ht
  let Tden := (2 : ℝ)^(27*(m : ℝ)/(alpha*w*C_sch))
  let Tpoly := D^(9*((m : ℝ)*(1+eta))/(alpha*w*C_sch))
  let B0 := max T (max C_upper (max 2 (max Tden Tpoly)))
  have hB0 : 1 < B0 := hT.trans_le (le_max_left _ _)
  refine ⟨B0,rfl,hB0,hCs,hCs1,ht,htu,hte,hr,hrhalf,hrw,hw,
    Real.rpow_pos_of_pos (by norm_num) _,Real.rpow_pos_of_pos (zero_lt_one.trans_le hD) _,?_⟩
  intro B hB S hheight
  have hcut (h : Fin m) : B0 < (S.data.t h).val^5 := original_sample_power_cutoff10 S B0 hB h
  obtain ⟨C,G,hGn,hGH,hdeg,hdata,hclosed,_hstrict⟩ := primitive_scalar_denominator_bounds10
    S.data.M S.conditions.primitive S.data.r S.data.P
    S.conditions.homogeneous S.conditions.polynomial_nonzero
  let N := permutedNormals10 S.data.M (fun g => (C g).e)
  let b := fun h => rootDenominator6 (N h 0) (N h 1)
  have hbn (h : Fin m) : b h ≠ 0 :=
    (integer_normalization6 (N h 0) (N h 1) (hdata h).1).2.2.2.2.2.1
  have hgrowth (h : Fin m) :
      ((S.data.t h).val^5)^(alpha/9) ≤ |(b h : ℝ)| ∧
      |(b ⟨0,hm⟩ : ℝ)|^((S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ≤ |(b h : ℝ)|^(S.data.r h : ℝ) := by
    have hb0R : (b ⟨0,hm⟩ : ℝ) ≠ 0 := by exact_mod_cast hbn ⟨0,hm⟩
    exact height_envelope_growth10 alpha C_upper
      ((S.data.t ⟨0,hm⟩).val^5) ((S.data.t h).val^5)
      (normalHeight10 (S.data.M ⟨0,hm⟩)) (normalHeight10 (S.data.M h))
      |(b ⟨0,hm⟩ : ℝ)| |(b h : ℝ)| (S.data.r ⟨0,hm⟩) (S.data.r h)
      ha (S.conditions.large ⟨0,hm⟩).2.2.1 (S.conditions.large h).2.2.1
      (by exact_mod_cast S.conditions.positive_degrees ⟨0,hm⟩)
      (by exact_mod_cast S.conditions.positive_degrees h)
      (((le_max_left C_upper _).trans (le_max_right T _)).trans (hcut ⟨0,hm⟩).le)
      (hheight ⟨0,hm⟩).2 (hdata ⟨0,hm⟩).2.2.2 (abs_pos.mpr hb0R)
      (hheight h).1 (hdata h).2.2.1
      (nonzero_normal_height_one10 _ (S.conditions.normal_nonzero h))
      (S.conditions.logarithmic_balance h).1
  have hden_cut (h : Fin m) : Tden ≤ (S.data.t h).val^5 :=
    ((le_max_left Tden Tpoly).trans ((le_max_right 2 _).trans
      ((le_max_right C_upper _).trans (le_max_right T _)))).trans (hcut h).le
  have hpoly_cut : Tpoly ≤ (S.data.t ⟨0,hm⟩).val^5 :=
    ((le_max_right Tden Tpoly).trans ((le_max_right 2 _).trans
      ((le_max_right C_upper _).trans (le_max_right T _)))).trans (hcut ⟨0,hm⟩).le
  have hGheight := original_sample_reduced_height10 heta hD S G hGH
  have hpoly := polynomial_budget_threshold alpha w C_sch D ((m : ℝ)*(1+eta))
    ((S.data.t ⟨0,hm⟩).val^5) |(b ⟨0,hm⟩ : ℝ)|
    (S.data.r ⟨0,hm⟩) (JSP000334.rothIntegerHeight G)
    ha hw hCs (zero_lt_one.trans_le hD)
    (zero_lt_one.trans (S.conditions.large ⟨0,hm⟩).2.2.1) (Nat.cast_nonneg _)
    (hgrowth ⟨0,hm⟩).1 hGheight hpoly_cut
  refine ⟨C,G,hGn,hGH,hdeg,hclosed _ S.conditions.normal_ideal,
    S.conditions.positive_degrees,?_,hGheight,hpoly,?_⟩
  · intro h hh
    exact (S.conditions.degree_separation h hh).trans
      (mul_le_mul_of_nonneg_right hrw (Nat.cast_nonneg _))
  · intro h
    obtain ⟨hN,hgcd,hroot,hupper⟩ := hdata h
    have hcop := (integer_normalization6 (N h 0) (N h 1) hN).2.2.2.2.2.2
    refine ⟨hcut h,(hheight h).1,hN,hgcd,hbn h,hcop,hroot,hupper,(hgrowth h).1,(hgrowth h).2,?_⟩
    exact denominator_budget_threshold m alpha w C_sch ((S.data.t h).val^5) |(b h : ℝ)|
      ha hw hCs (zero_lt_one.trans (S.conditions.large h).2.2.1) (hgrowth h).1 (hden_cut h)

end CompoundFeasibility.SourceFixedBudget10
