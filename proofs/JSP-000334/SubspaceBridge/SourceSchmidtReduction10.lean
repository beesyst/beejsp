import SubspaceBridge.SchmidtApplication10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtGrowth10
open SchmidtNormal10 SchmidtPolynomial10 SourceNormalHighIndex10 SchmidtCoordinate10 SchmidtScalar10
open SchmidtRationalNormalization6 SchmidtApplication10

theorem primitive_scalar_denominator_bounds10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, Ideal.span (Set.range (M h)) = ⊤) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) (hn : P ≠ 0) :
    ∃ (C : (h : Fin m) → NormalCoordinateChoice10 (M h)) (G : MvPolynomial (Fin m) ℤ),
      G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height10 P ∧ (∀ h, G.degreeOf h ≤ r h) ∧
      (∀ h, let N := permutedNormals10 M (fun g => (C g).e) h
        N 0 ≠ 0 ∧ Int.gcd (N 0) (N 1)^9 ≤ (N 0).natAbs^8 ∧
        (normalHeight10 (M h) : ℝ)^(1/9 : ℝ) ≤ |(rootDenominator6 (N 0) (N 1) : ℝ)| ∧
        |(rootDenominator6 (N 0) (N 1) : ℝ)| ≤ (normalHeight10 (M h) : ℝ)) ∧
      (∀ c, P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c →
        G.map (Int.castRingHom ℝ) ∈ monicIdeal6 (binaryLift6 (permutedNormals10 M (fun h => (C h).e))) r c) ∧
      (∀ c, P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c →
        G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 (binaryLift6 (permutedNormals10 M (fun h => (C h).e))) r c) := by
  obtain ⟨C,G,hGn,hGH,hGdeg,hdata,hclosed,hstrict⟩ :=
    primitive_scalar_reduction10 M hM r P hP hn
  refine ⟨C,G,hGn,hGH,hGdeg,?_,hclosed,hstrict⟩
  intro h
  obtain ⟨hfirst,hgcd,hroot⟩ := hdata h
  obtain ⟨_hc,_hprim,hheight,_hfirst,hatt,_hmax,_hgcd,_hinv⟩ := choice_normal_data10 M C h
  have hha : (normalHeight10 (M h) : ℝ) =
      |(permutedNormals10 M (fun g => (C g).e) h 0 : ℝ)| := by
    rw [← hheight,hatt,Int.cast_natAbs,Int.cast_abs]
  refine ⟨hfirst,hgcd,hroot,?_⟩
  rw [hha]
  exact (denominator_real_bounds10 _ _ hfirst hgcd).2

end CompoundFeasibility.SourceSchmidtGrowth10
