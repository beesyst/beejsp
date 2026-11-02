import SubspaceBridge.SchmidtCoordinate10
import SubspaceBridge.SchmidtScalar10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SchmidtApplication10
open SchmidtNormal10 SchmidtPolynomial10 SourceNormalHighIndex10 SchmidtCoordinate10 SchmidtScalar10
open SchmidtRationalNormalization6
noncomputable section

theorem primitive_scalar_reduction10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, Ideal.span (Set.range (M h)) = ⊤) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) (hn : P ≠ 0) :
    ∃ (C : (h : Fin m) → NormalCoordinateChoice10 (M h)) (G : MvPolynomial (Fin m) ℤ),
      G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height10 P ∧ (∀ h, G.degreeOf h ≤ r h) ∧
      (∀ h, let N := permutedNormals10 M (fun g => (C g).e) h
        N 0 ≠ 0 ∧ Int.gcd (N 0) (N 1)^9 ≤ (N 0).natAbs^8 ∧
        (normalHeight10 (M h) : ℝ)^(1/9 : ℝ) ≤ |(rootDenominator6 (N 0) (N 1) : ℝ)|) ∧
      (∀ c, P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c →
        G.map (Int.castRingHom ℝ) ∈ monicIdeal6 (binaryLift6 (permutedNormals10 M (fun h => (C h).e))) r c) ∧
      (∀ c, P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c →
        G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 (binaryLift6 (permutedNormals10 M (fun h => (C h).e))) r c) := by
  have hex (h) := normal_coordinate_choice10 (M h) (hM h)
  let C := fun h => Classical.choice (hex h)
  let e := fun h => (C h).e
  let N := permutedNormals10 M e
  let P' := transport10 ℤ e P
  have hn' : P' ≠ 0 := (transport10_nonzero e P).mpr hn
  have hh' : homogeneous10 r P' := (transport10_homogeneous e r P).mpr hP
  have hN (h) : N h 0 ≠ 0 := (choice_normal_data10 M C h).2.2.2.1
  obtain ⟨G,hGn,hGH,hGdeg,hclosed,hstrict⟩ := scalar_reduction10 N hN r P' hh' hn'
  have hH : JSP000334.rothIntegerHeight G ≤ height10 P :=
    hGH.trans_eq (transport10_height e P)
  refine ⟨C,G,hGn,hH,hGdeg,?_,?_,?_⟩
  · intro h
    obtain ⟨hc,hprim,hheight,hfirst,hatt,hmax,hgcd,hinv⟩ := choice_normal_data10 M C h
    have hgcd' : Int.gcd (N h 0) (N h 1)^9 ≤ (N h 0).natAbs^8 := by
      simpa only [hatt] using hgcd
    have hroot := (denominator_real_bounds10 (N h 0) (N h 1) hfirst hgcd').1
    have hha : (normalHeight10 (M h) : ℝ) = |(N h 0 : ℝ)| := by
      rw [← hheight,hatt,Int.cast_natAbs,Int.cast_abs]
    exact ⟨hfirst,hgcd',by rw [hha]; exact hroot⟩
  · intro c hPc
    apply hclosed c
    rw [transport10_map]
    exact (transport10_normalIdeal_iff e M r c (P.map (Int.castRingHom ℝ))).mp hPc
  · intro c hPc
    apply hstrict c
    rw [transport10_map]
    exact (transport10_strictIdeal_iff e M r c (P.map (Int.castRingHom ℝ))).mp hPc

end
end CompoundFeasibility.SchmidtApplication10
