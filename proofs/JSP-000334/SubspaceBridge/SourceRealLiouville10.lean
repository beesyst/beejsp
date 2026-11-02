import SubspaceBridge.SourceFieldAdjugate10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10
open SchmidtNormal10

theorem normalHeight10_coord (M : Fin 10 → ℤ) (i : Fin 10) :
    |(M i : ℝ)| ≤ (normalHeight10 M : ℝ) := by
  have hn : (M i).natAbs ≤ normalHeight10 M :=
    Finset.le_sup (f := fun k : Fin 10 => (M k).natAbs) (Finset.mem_univ i)
  have hr : ((M i).natAbs : ℝ) ≤ (normalHeight10 M : ℝ) := by exact_mod_cast hn
  simpa only [Int.cast_natAbs,Int.cast_abs] using hr

theorem normal_pi_norm_le_height10 (M : Fin 10 → ℤ) :
    ‖integerReal M‖ ≤ (normalHeight10 M : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  simpa only [integerReal,Real.norm_eq_abs] using normalHeight10_coord M i

theorem field_row_real_dual10 (K : IntermediateField ℚ ℝ)
    (T : Matrix (Fin 10) (Fin 10) K) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hT : T.map K.val.toRingHom = L⁻¹.transpose) (z : Fin 10 → ℤ) (s : Fin 10) :
    (∑ i, (T s i : ℝ)*(z i : ℝ)) = (L⁻¹.transpose *ᵥ integerReal z) s := by
  change (∑ i, (T s i : ℝ)*(z i : ℝ)) = ∑ i, L⁻¹.transpose s i*(z i : ℝ)
  apply Finset.sum_congr rfl
  intro i _
  have hh : (T s i : ℝ) = L⁻¹.transpose s i :=
    congrArg (fun A : Matrix (Fin 10) (Fin 10) ℝ => A s i) hT
  rw [hh]

theorem actual_real_dual_liouville10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (M : Fin 10 → ℤ) i,
      (L⁻¹.transpose *ᵥ integerReal M) i ≠ 0 →
      C ≤ |(L⁻¹.transpose *ᵥ integerReal M) i| * (max 1 (normalHeight10 M : ℝ))^D := by
  obtain ⟨K,hK,hmem⟩ := liouville10_common_field L hAlg
  letI : FiniteDimensional ℚ K := hK
  let B : Matrix (Fin 10) (Fin 10) K := fun i j => ⟨L i j,hmem i j⟩
  let T : Matrix (Fin 10) (Fin 10) K := B.adjugate.transpose
  have hmap : B.map K.val.toRingHom = L := rfl
  have hT : T.map K.val.toRingHom = L⁻¹.transpose := number_field_adjugate_dual10 K B L hmap hL
  obtain ⟨C,hC,D,h⟩ := liouville10_field_liouville K T
  refine ⟨C,hC,D,?_⟩
  intro M i hn
  have he := field_row_real_dual10 K T L hT M i
  have hn' : (∑ k, (T i k : ℝ)*(M k : ℝ)) ≠ 0 := by rw [he]; exact hn
  have hh := h i M hn'
  rw [he] at hh
  change C ≤ |(L⁻¹.transpose *ᵥ integerReal M) i| * (max 1 ‖integerReal M‖)^D at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (le_trans zero_le_one (le_max_left _ _))
    (max_le_max_left 1 (normal_pi_norm_le_height10 M)) D) (abs_nonneg _))

end CompoundFeasibility.SourceHeightEnvelope10
