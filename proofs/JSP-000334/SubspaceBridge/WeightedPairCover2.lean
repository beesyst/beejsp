import SubspaceBridge.WeightedPairTransport2
import SubspaceBridge.BinaryAllPointFiniteCover2
open scoped Classical
namespace JSP000334

theorem weighted_pair_descale_mem (P : Submodule ℚ (Fin 2 → ℚ))
    (u v s : fixedSUnitGroup) (z : Fin 2 → ℤ)
    (h0 : (z 0 : ℚ)=((s : ℚˣ) : ℚ)*((u : ℚˣ) : ℚ))
    (h1 : (z 1 : ℚ)=((s : ℚˣ) : ℚ)*((v : ℚˣ) : ℚ))
    (hz : (fun i => (z i : ℚ)) ∈ P) :
    ![((u : ℚˣ) : ℚ),((v : ℚˣ) : ℚ)] ∈ P := by
  have hm := P.smul_mem (((s : ℚˣ) : ℚ)⁻¹) hz
  have he : (((s : ℚˣ) : ℚ)⁻¹) • (fun i => (z i : ℚ)) =
      ![((u : ℚˣ) : ℚ),((v : ℚˣ) : ℚ)] := by
    ext i
    fin_cases i <;> simp [h0,h1,Units.ne_zero]
  rw [he] at hm
  exact hm

theorem weighted_pair_high_product (A B C : ℚ) (hA : A≠0) (u v s : fixedSUnitGroup)
    (z : Fin 2 → ℤ)
    (he : A+B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ)=0)
    (h0 : (z 0 : ℚ)=((s : ℚˣ) : ℚ)*((u : ℚˣ) : ℚ))
    (h1 : (z 1 : ℚ)=((s : ℚˣ) : ℚ)*((v : ℚˣ) : ℚ))
    (hheight : pairHeight ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ)=archPairHeight z)
    (hH : max 1 ((threePlaceProduct A : ℝ)^2)<(archPairHeight z : ℝ)) :
    (weightedNormalizedProduct2 B C (z 0 : ℚ) (z 1 : ℚ) : ℝ)<
      Real.rpow (archPairHeight z : ℝ) (-(5 : ℝ)/2) := by
  have hp := weighted_strict_product2 A B C hA u v he (by simpa only [hheight] using hH)
  rw [hheight] at hp
  rw [h0,h1,weighted_normalized_sunit_scale2]
  exact hp

theorem weighted_pair_finite_proper_cover (A B C : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0) :
    ∃ F : Set (Submodule ℚ (Fin 2 → ℚ)), F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ p ∈ weightedFixedSUnitPairs A B C,
        ∃ P∈F, ![((p.1 : ℚˣ) : ℚ),((p.2 : ℚˣ) : ℚ)] ∈ P := by
  obtain ⟨F,hF,hproper,hcover⟩ := binary_weighted_allpoint_finite_cover B C hB hC
  let M : ℝ := max 1 ((threePlaceProduct A : ℝ)^2)
  let T : Set (Fin 2 → ℤ) := {z | z 1≠0 ∧ (archPairHeight z : ℝ)≤M}
  have hT : T.Finite := binary_integer_height_ball_finite T M (fun _ hz => hz.2)
  refine ⟨F ∪ (binaryRationalSpan '' T),hF.union (hT.image _),?_,?_⟩
  · intro P hP
    rcases hP with hP | ⟨z,hz,rfl⟩
    · exact hproper P hP
    · exact binary_rational_span_proper z hz.1
  · intro p hp
    obtain ⟨z,s,_,hz,_,hz1,h0,h1,hh⟩ := weighted_pair_primitive_transport p.1 p.2
    by_cases hH : M<(archPairHeight z : ℝ)
    · have hprod := weighted_pair_high_product A B C hA p.1 p.2 s z hp h0 h1 hh hH
      obtain ⟨P,hPF,hzP⟩ := hcover z hz hprod
      exact ⟨P,Or.inl hPF,weighted_pair_descale_mem P p.1 p.2 s z h0 h1 hzP⟩
    · have hzT : z ∈ T := ⟨hz1,le_of_not_gt hH⟩
      exact ⟨binaryRationalSpan z,Or.inr ⟨z,hzT,rfl⟩,
        weighted_pair_descale_mem _ p.1 p.2 s z h0 h1 (binary_rational_span_mem z)⟩

end JSP000334
