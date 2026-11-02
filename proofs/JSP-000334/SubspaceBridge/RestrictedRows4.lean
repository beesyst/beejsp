import SubspaceBridge.RestrictedWeightOrder4
import Mathlib.Data.Matrix.Rank
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedRows4
open RestrictedGeometry4
noncomputable section

def rowCoordinates4 {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin d) K :=
  fun i k => (A *ᵥ (b k : Fin 4 → K)) i

theorem rowCoordinates4_span {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A) :
    Submodule.span K (Set.range (rowCoordinates4 P b A).row) = ⊤ := by
  let e := LinearEquiv.ofBijective (Matrix.toLin' A)
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hA,Matrix.mulVec_surjective_iff_isUnit.mpr hA⟩
  have hli : LinearIndependent K (fun k => (A *ᵥ (b k : Fin 4 → K))) :=
    (b.linearIndependent.map' P.subtype P.ker_subtype).map' e.toLinearMap e.ker
  have hcol : LinearIndependent K (rowCoordinates4 P b A).transpose.row := hli
  have hrank : (rowCoordinates4 P b A).rank = d := by
    rw [← Matrix.rank_transpose]
    simpa only [Fintype.card_fin] using hcol.rank_matrix
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank_eq_finrank_span_row,hrank,Module.finrank_pi]
  simp

def rationalRowCoordinates4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 4) (Fin (Module.finrank ℚ P)) ℚ :=
  rowCoordinates4 P (Module.finBasis ℚ P) A

def realRowCoordinates4 (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin (Module.finrank ℝ (rationalRealSpan4 P))) ℝ :=
  rowCoordinates4 (rationalRealSpan4 P) (Module.finBasis ℝ (rationalRealSpan4 P)) L

theorem rationalRowCoordinates4_span (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
    Submodule.span ℚ (Set.range (rationalRowCoordinates4 P A).row) = ⊤ := by
  exact rowCoordinates4_span P _ A ((Matrix.isUnit_iff_isUnit_det A).mpr (hA ▸ isUnit_one))

theorem realRowCoordinates4_span (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) :
    Submodule.span ℝ (Set.range (realRowCoordinates4 P L).row) = ⊤ := by
  exact rowCoordinates4_span _ _ L ((Matrix.isUnit_iff_isUnit_det L).mpr (hL ▸ isUnit_one))

end
end CompoundFeasibility.RestrictedRows4
