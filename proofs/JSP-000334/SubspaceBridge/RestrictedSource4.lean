import SubspaceBridge.RestrictedUpper4
import SubspaceBridge.RestrictedLower4
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry4

theorem source_restricted_minkowski4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hPlo : 1 ≤ Module.finrank ℚ P) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    Module.finrank ℝ (rationalRealSpan4 P) = Module.finrank ℚ P ∧
    Module.finrank ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃) = Module.finrank ℚ P ∧
    0 < (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) ∧
    (restrictedMeasure4 P) (restrictedBody4 P L Q c₀) < ⊤ ∧
    0 < ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
    ∃ v : Fin (Module.finrank ℚ P) → rationalRealSpan4 P,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) ∧
      (∀ i, 0 < restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      Monotone (restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ i, restrictedGauge4 P L hL Q hQ c₀ (v i) =
        restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      (∀ i, ∀ y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix4 v i →
        restrictedGauge4 P L hL Q hQ c₀ (v i) ≤ restrictedGauge4 P L hL Q hQ c₀ y) ∧
      (2 : ℝ)^(Module.finrank ℚ P) / (Nat.factorial (Module.finrank ℚ P) : ℝ) ≤
        (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
          (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
            ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
      (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
            (4 : ℝ)^(Module.finrank ℚ P) := by
  obtain ⟨v,hv,hvL,hpos,hmono,hatt,hshort⟩ :=
    exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hvol := restrictedBody4_volume_pos_finite P L hL Q hQ c₀
  exact ⟨rationalRealSpan4_finrank P hP,restrictedLattice4_rank P hP A₂ A₃ Q c₂ c₃,
    hvol.1,hvol.2,restrictedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃,
    v,hv,hvL,hpos,hmono,hatt,hshort,
    source_restricted_minkowski_lower4 P hPlo hP A₂ A₃ L hL Q hQ c₀ c₂ c₃,
    source_restricted_minkowski_upper4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃⟩

end CompoundFeasibility.RestrictedGeometry4
