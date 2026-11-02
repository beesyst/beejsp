import SubspaceBridge.RestrictedGreedyRows5
open scoped BigOperators Matrix
namespace CompoundFeasibility.SelectedRestriction5
open RestrictedGeometry5 RestrictedWeightOrder5 RestrictedRows5 RestrictedGreedyRows5
noncomputable section

def sortedRows5 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ) : Fin 5 → Fin d → K :=
  fun i => M (weightOrder5 c i)

theorem sortedRows5_span {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    Submodule.span K (Set.range (sortedRows5 M c)) = ⊤ := by
  have hrange : Set.range (sortedRows5 M c) = Set.range M.row := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨weightOrder5 c i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨(weightOrder5 c).symm i,by simp [sortedRows5,Matrix.row_def]⟩
  rw [hrange,hfull]

def selectedIndex5 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) : Fin d ↪o Fin 5 :=
  greedyIndex5 (sortedRows5 M c) (sortedRows5_span M c hfull) d (by simp)

def selectedMatrix5 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) : Matrix (Fin d) (Fin d) K :=
  fun k => M (weightOrder5 c (selectedIndex5 M c hfull k))

theorem selectedMatrix5_independent {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    LinearIndependent K (selectedMatrix5 M c hfull).row :=
  greedyIndex5_independent (sortedRows5 M c) (sortedRows5_span M c hfull) d (by simp)

theorem selectedMatrix5_det_ne_zero {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    (selectedMatrix5 M c hfull).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp (selectedMatrix5_independent M c hfull)))

def realRestrictionBasis5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan5 P) :=
  (Module.finBasis ℝ (rationalRealSpan5 P)).reindex (finCongr (rationalRealSpan5_finrank P hP))

def realRestrictionCoordinates5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 5) (Fin (Module.finrank ℚ P)) ℝ :=
  rowCoordinates5 (rationalRealSpan5 P) (realRestrictionBasis5 P hP) L

theorem realRestrictionCoordinates5_span (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) :
    Submodule.span ℝ (Set.range (realRestrictionCoordinates5 P hP L).row) = ⊤ :=
  rowCoordinates5_span _ _ L ((Matrix.isUnit_iff_isUnit_det L).mpr (hL ▸ isUnit_one))

def sourceSelectedExponent5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 5 → ℝ) : ℝ :=
    (∑ k : Fin (Module.finrank ℚ P), c₀ (weightOrder5 c₀
      (selectedIndex5 (realRestrictionCoordinates5 P hP L) c₀ (realRestrictionCoordinates5_span P hP L hL) k))) +
    (∑ k : Fin (Module.finrank ℚ P), c₂ (weightOrder5 c₂
      (selectedIndex5 (rationalRowCoordinates5 P A₂) c₂ (rationalRowCoordinates5_span P A₂ h₂) k))) +
    (∑ k : Fin (Module.finrank ℚ P), c₃ (weightOrder5 c₃
      (selectedIndex5 (rationalRowCoordinates5 P A₃) c₃ (rationalRowCoordinates5_span P A₃ h₃) k)))

end
end CompoundFeasibility.SelectedRestriction5
