import SubspaceBridge.SourceSampleHeightEnvelope10
import SubspaceBridge.SourceSchmidtNumeric10
import SubspaceBridge.SourceSchmidtReduction10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtGrowth10
open SchmidtNormal10 OriginalDual10 SourceSampling10 SourceSelectedSet10 SourceHeightEnvelope10
open SchmidtCoordinate10 SchmidtPolynomial10 SchmidtRationalNormalization6 SchmidtScalar10

theorem original_sample_schmidt_growth10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hc0 : ∀ i, |c 0 i| ≤ 1) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ alpha C_upper T C_sch : ℝ,
      0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      C_sch = min (1/2 : ℝ) (alpha/180) ∧ 0 < C_sch ∧ C_sch ≤ 1 ∧
      ∀ (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
        (eta D E B rho : ℝ) (m : ℕ) (hm : 0 < m), T ≤ B →
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
            ∀ h, let N := permutedNormals10 S.data.M (fun g => (C g).e)
              let b := fun g => rootDenominator6 (N g 0) (N g 1)
              N h 0 ≠ 0 ∧ Int.gcd (N h 0) (N h 1)^9 ≤ (N h 0).natAbs^8 ∧
              b h ≠ 0 ∧ Int.gcd (rootNumerator6 (N h 0) (N h 1)) (b h) = 1 ∧
              (normalHeight10 (S.data.M h) : ℝ)^(1/9 : ℝ) ≤ |(b h : ℝ)| ∧
              |(b h : ℝ)| ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
              |(b ⟨0,hm⟩ : ℝ)|^((S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ≤
                |(b h : ℝ)|^(S.data.r h : ℝ) := by
  obtain ⟨alpha,C_upper,T,ha,hC,hT,henvelope⟩ := original_sample_height_envelope10
    A2 A3 L h2 h3 hL hAlg c2 c3 hc2 hc3 c hc0 hb hc epsilon he
  obtain ⟨hCs,hCs1,_hcmp⟩ := schmidt_constant_range10 alpha ha
  refine ⟨alpha,C_upper,max T C_upper,min (1/2 : ℝ) (alpha/180),ha,hC,
    hT.trans_le (le_max_left _ _),rfl,hCs,hCs1,?_⟩
  intro V v eta D E B rho m hm hB S s hs hn0 hn2 hn3
  have hlarge (h : Fin m) : max T C_upper < (S.data.t h).val^5 := by
    exact (hB.trans_lt (S.conditions.large h).1).trans_le
      (le_self_pow₀ (S.conditions.large h).2.1.le (by norm_num))
  have hheight (h : Fin m) := henvelope V v eta D E B rho m hm S h
    ((le_max_left _ _).trans_lt (hlarge h)) (s h) (hs h) (hn0 h) (hn2 h) (hn3 h)
  obtain ⟨C,G,hGn,hGH,hdeg,hden,hclosed,_hstrict⟩ := primitive_scalar_denominator_bounds10
    S.data.M S.conditions.primitive S.data.r S.data.P
    S.conditions.homogeneous S.conditions.polynomial_nonzero
  refine ⟨C,G,hGn,hGH,hdeg,hclosed _ S.conditions.normal_ideal,?_⟩
  intro h
  let N := permutedNormals10 S.data.M (fun g => (C g).e)
  let b := fun g => rootDenominator6 (N g 0) (N g 1)
  obtain ⟨hfirst,hgcd,hl,hu⟩ := hden h
  obtain ⟨_hg,_hdiv0,_hdiv1,_heq0,_heq1,hbn,hcop⟩ := integer_normalization6 _ _ hfirst
  refine ⟨hfirst,hgcd,hbn,hcop,hl,hu,?_⟩
  have hb0n := (integer_normalization6 (N ⟨0,hm⟩ 0) (N ⟨0,hm⟩ 1)
    (hden ⟨0,hm⟩).1).2.2.2.2.2.1
  have hb0R : (b ⟨0,hm⟩ : ℝ) ≠ 0 := by exact_mod_cast hb0n
  exact denominator_growth_numeric10 alpha C_upper
    ((S.data.t ⟨0,hm⟩).val^5) ((S.data.t h).val^5)
    (normalHeight10 (S.data.M ⟨0,hm⟩)) (normalHeight10 (S.data.M h))
    |(b ⟨0,hm⟩ : ℝ)| |(b h : ℝ)| (S.data.r ⟨0,hm⟩) (S.data.r h)
    ha (S.conditions.large ⟨0,hm⟩).2.2.1 (S.conditions.large h).2.2.1
    (by exact_mod_cast S.conditions.positive_degrees ⟨0,hm⟩)
    (by exact_mod_cast S.conditions.positive_degrees h)
    ((le_max_right _ _).trans (hlarge ⟨0,hm⟩).le)
    (hheight ⟨0,hm⟩).2 (hden ⟨0,hm⟩).2.2.2 (abs_pos.mpr hb0R)
    (hheight h).1 hl (nonzero_normal_height_one10 _ (S.conditions.normal_nonzero h))
    (S.conditions.logarithmic_balance h).1

end CompoundFeasibility.SourceSchmidtGrowth10
