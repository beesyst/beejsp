import SubspaceBridge.RestrictedGreedyRows4
open scoped BigOperators Matrix
namespace CompoundFeasibility.SelectedRestriction4
open RestrictedGeometry4 RestrictedWeightOrder4 RestrictedRows4 RestrictedGreedyRows4
noncomputable section

def sortedRows4 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ) : Fin 4 → Fin d → K :=
  fun i => M (weightOrder4 c i)

theorem sortedRows4_span {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    Submodule.span K (Set.range (sortedRows4 M c)) = ⊤ := by
  have hrange : Set.range (sortedRows4 M c) = Set.range M.row := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨weightOrder4 c i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨(weightOrder4 c).symm i,by simp [sortedRows4,Matrix.row_def]⟩
  rw [hrange,hfull]

def selectedIndex4 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) : Fin d ↪o Fin 4 :=
  greedyIndex4 (sortedRows4 M c) (sortedRows4_span M c hfull) d (by simp)

def selectedMatrix4 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) : Matrix (Fin d) (Fin d) K :=
  fun k => M (weightOrder4 c (selectedIndex4 M c hfull k))

theorem selectedMatrix4_independent {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    LinearIndependent K (selectedMatrix4 M c hfull).row :=
  greedyIndex4_independent (sortedRows4 M c) (sortedRows4_span M c hfull) d (by simp)

theorem selectedMatrix4_det_ne_zero {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    (selectedMatrix4 M c hfull).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp (selectedMatrix4_independent M c hfull)))

def realRestrictionBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan4 P) :=
  (Module.finBasis ℝ (rationalRealSpan4 P)).reindex (finCongr (rationalRealSpan4_finrank P hP))

def realRestrictionCoordinates4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin (Module.finrank ℚ P)) ℝ :=
  rowCoordinates4 (rationalRealSpan4 P) (realRestrictionBasis4 P hP) L

theorem realRestrictionCoordinates4_span (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) :
    Submodule.span ℝ (Set.range (realRestrictionCoordinates4 P hP L).row) = ⊤ :=
  rowCoordinates4_span _ _ L ((Matrix.isUnit_iff_isUnit_det L).mpr (hL ▸ isUnit_one))

def sourceSelectedExponent4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ) : ℝ :=
    (∑ k : Fin (Module.finrank ℚ P), c₀ (weightOrder4 c₀
      (selectedIndex4 (realRestrictionCoordinates4 P hP L) c₀ (realRestrictionCoordinates4_span P hP L hL) k))) +
    (∑ k : Fin (Module.finrank ℚ P), c₂ (weightOrder4 c₂
      (selectedIndex4 (rationalRowCoordinates4 P A₂) c₂ (rationalRowCoordinates4_span P A₂ h₂) k))) +
    (∑ k : Fin (Module.finrank ℚ P), c₃ (weightOrder4 c₃
      (selectedIndex4 (rationalRowCoordinates4 P A₃) c₃ (rationalRowCoordinates4_span P A₃ h₃) k)))

end
end CompoundFeasibility.SelectedRestriction4
