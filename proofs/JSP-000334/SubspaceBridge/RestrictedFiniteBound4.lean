import SubspaceBridge.RestrictedCoordinateCovolume4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedFiniteBound4
open RestrictedGeometry4 RestrictedRelaxed4 RestrictedIntegerCoordinates4 RestrictedRows4
open RestrictedWeightOrder4 SelectedRestriction4 RestrictedSelectedBasis4 RestrictedFiniteCoordinates4
open RestrictedCoordinateCovolume4 RestrictedSelectedIndex4
noncomputable section

def finiteSelection4 (P : Submodule ℚ (Fin 4 → ℚ)) (A : Matrix (Fin 4) (Fin 4) ℚ)
    (hA : A.det = 1) (c : Fin 4 → ℝ) : Fin (Module.finrank ℚ P) → Fin 4 :=
  fun k => weightOrder4 c (selectedIndex4 (rationalRowCoordinates4 P A) c (rationalRowCoordinates4_span P A hA) k)

theorem selected_prime_powers_lower4 {d : ℕ} (p : ℕ) (hp : 1 < p)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin d → ℝ) :
    Q^(-(∑ k, c k)) ≤ (p : ℝ)^(∑ k, Nat.ceil (JSP000334.qThreshold p Q (c k))) := by
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  calc
    _ = ∏ k, Q^(-c k) := by
      rw [← Real.rpow_sum_of_pos hQpos]
      simp
    _ ≤ ∏ k, (p : ℝ)^Nat.ceil (JSP000334.qThreshold p Q (c k)) := by
      apply Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hQpos _).le)
      intro k hk
      rw [← JSP000334.qThreshold_rpow p hp Q (c k) hQ,← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem source_finite_inverse_covolume4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (c₂ c₃ : Fin 4 → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q →
      1 / ZLattice.covolume
        (relaxedLattice4 P A₂ A₃ Q c₂ c₃ (finiteSelection4 P A₂ h₂ c₂) (finiteSelection4 P A₃ h₃ c₃))
        (restrictedMeasure4 P) ≤
      K * Q^((∑ k, c₂ (finiteSelection4 P A₂ h₂ c₂ k)) + (∑ k, c₃ (finiteSelection4 P A₃ h₃ c₃ k))) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let s₂ := finiteSelection4 P A₂ h₂ c₂
  let s₃ := finiteSelection4 P A₃ h₃ c₃
  let B₂ := finiteSelectedMatrix4 P hP A₂ h₂ c₂
  let B₃ := finiteSelectedMatrix4 P hP A₃ h₃ c₃
  let D : ℝ := (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ)
  let C₀ := ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P)
  have hD₂ : 0 < (padicNorm 2 B₂.det : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg B₂.det)
      (Ne.symm (padicNorm.nonzero (finiteSelectedMatrix4_det_ne_zero P hP A₂ h₂ c₂)))
  have hD₃ : 0 < (padicNorm 3 B₃.det : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg B₃.det)
      (Ne.symm (padicNorm.nonzero (finiteSelectedMatrix4_det_ne_zero P hP A₃ h₃ c₃)))
  have hD : 0 < D := mul_pos hD₂ hD₃
  have hC₀ : 0 < C₀ := ZLattice.covolume_pos _ _
  refine ⟨1/(D*C₀),div_pos zero_lt_one (mul_pos hD hC₀),?_⟩
  intro Q hQ
  let F := (∑ k, c₂ (s₂ k)) + ∑ k, c₃ (s₃ k)
  let e₂ := fun k => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ (s₂ k)))
  let e₃ := fun k => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ (s₃ k)))
  let H := relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  let E := relaxedIntegerEquiv4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  letI : Module.Free ℤ H := Module.Free.of_equiv E.symm
  letI : Module.Finite ℤ H := Module.Finite.equiv E.symm
  let bH : Basis (Fin (Module.finrank ℚ P)) ℤ H :=
    Module.finBasisOfFinrankEq ℤ H (relaxedIntegerGroup4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)
  have hnorm₂ (z : H) : ∀ k, padicNorm 2 ((B₂ *ᵥ (fun i => ((z : Fin (Module.finrank ℚ P) → ℤ) i : ℚ))) k) ≤
      (2 : ℚ)^(-(e₂ k : ℤ)) := by
    apply selected_local_coordinates4 P hP 2 A₂ Q c₂ s₂ z
    obtain ⟨w,hw,hval⟩ := z.property
    exact ⟨w,hw.1,hval⟩
  have hnorm₃ (z : H) : ∀ k, padicNorm 3 ((B₃ *ᵥ (fun i => ((z : Fin (Module.finrank ℚ P) → ℤ) i : ℚ))) k) ≤
      (3 : ℚ)^(-(e₃ k : ℤ)) := by
    apply selected_local_coordinates4 P hP 3 A₃ Q c₃ s₃ z
    obtain ⟨w,hw,hval⟩ := z.property
    exact ⟨w,hw.2,hval⟩
  have hindex := selected_rational_index_lower4 ⟨Module.finrank ℚ P,by omega⟩
    B₂ B₃ H bH e₂ e₃ hnorm₂ hnorm₃
  have hlow₂ := selected_prime_powers_lower4 2 (by decide) Q hQ (fun k => c₂ (s₂ k))
  have hlow₃ := selected_prime_powers_lower4 3 (by decide) Q hQ (fun k => c₃ (s₃ k))
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hQlow : Q^(-F) ≤ (2 : ℝ)^(∑ k, e₂ k) * (3 : ℝ)^(∑ k, e₃ k) := by
    calc
      _ = Q^(-(∑ k, c₂ (s₂ k))) * Q^(-(∑ k, c₃ (s₃ k))) := by
        rw [← Real.rpow_add hQpos]
        congr 1
        dsimp [F]
        ring
      _ ≤ _ := mul_le_mul hlow₂ hlow₃ (by positivity) (by positivity)
  have hidxlo : D*Q^(-F) ≤ (H.index : ℝ) := by
    calc
      _ ≤ D * ((2 : ℝ)^(∑ k, e₂ k) * (3 : ℝ)^(∑ k, e₃ k)) :=
        mul_le_mul_of_nonneg_left hQlow hD.le
      _ ≤ _ := by convert hindex using 1 <;> ring
  have hcvlo : D*C₀*Q^(-F) ≤
      ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) := by
    rw [relaxedLattice4_covolume_index P hP]
    convert mul_le_mul_of_nonneg_right hidxlo hC₀.le using 1 <;> ring
  have hcancel : Q^(-F)*Q^F = 1 := by rw [← Real.rpow_add hQpos];simp
  have hbound : D*C₀ ≤ ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃)
      (restrictedMeasure4 P) * Q^F := by
    calc
      _ = (D*C₀*Q^(-F))*Q^F := by
        calc
          D*C₀ = D*C₀*(Q^(-F)*Q^F) := by rw [hcancel,mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcvlo (Real.rpow_pos_of_pos hQpos _).le
  change 1 / ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) ≤
    (1/(D*C₀))*Q^F
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_div_iff₀ (relaxedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃ s₂ s₃) (mul_pos hD hC₀)).mpr
  simpa only [one_mul,mul_comm] using hbound

end
end CompoundFeasibility.RestrictedFiniteBound4
