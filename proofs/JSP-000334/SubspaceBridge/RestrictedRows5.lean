import SubspaceBridge.RestrictedWeightOrder5
import Mathlib.Data.Matrix.Rank
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedRows5
open RestrictedGeometry5
noncomputable section

def rowCoordinates5 {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 5 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 5) (Fin 5) K) : Matrix (Fin 5) (Fin d) K :=
  fun i k => (A *ᵥ (b k : Fin 5 → K)) i

theorem rowCoordinates5_span {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 5 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 5) (Fin 5) K) (hA : IsUnit A) :
    Submodule.span K (Set.range (rowCoordinates5 P b A).row) = ⊤ := by
  let e := LinearEquiv.ofBijective (Matrix.toLin' A)
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hA,Matrix.mulVec_surjective_iff_isUnit.mpr hA⟩
  have hli : LinearIndependent K (fun k => (A *ᵥ (b k : Fin 5 → K))) :=
    (b.linearIndependent.map' P.subtype P.ker_subtype).map' e.toLinearMap e.ker
  have hcol : LinearIndependent K (rowCoordinates5 P b A).transpose.row := hli
  have hrank : (rowCoordinates5 P b A).rank = d := by
    rw [← Matrix.rank_transpose]
    simpa only [Fintype.card_fin] using hcol.rank_matrix
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank_eq_finrank_span_row,hrank,Module.finrank_pi]
  simp

def rationalRowCoordinates5 (P : Submodule ℚ (Fin 5 → ℚ))
    (A : Matrix (Fin 5) (Fin 5) ℚ) : Matrix (Fin 5) (Fin (Module.finrank ℚ P)) ℚ :=
  rowCoordinates5 P (Module.finBasis ℚ P) A

def realRowCoordinates5 (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix (Fin 5) (Fin (Module.finrank ℝ (rationalRealSpan5 P))) ℝ :=
  rowCoordinates5 (rationalRealSpan5 P) (Module.finBasis ℝ (rationalRealSpan5 P)) L

theorem rationalRowCoordinates5_span (P : Submodule ℚ (Fin 5 → ℚ))
    (A : Matrix (Fin 5) (Fin 5) ℚ) (hA : A.det = 1) :
    Submodule.span ℚ (Set.range (rationalRowCoordinates5 P A).row) = ⊤ := by
  exact rowCoordinates5_span P _ A ((Matrix.isUnit_iff_isUnit_det A).mpr (hA ▸ isUnit_one))

theorem realRowCoordinates5_span (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) :
    Submodule.span ℝ (Set.range (realRowCoordinates5 P L).row) = ⊤ := by
  exact rowCoordinates5_span _ _ L ((Matrix.isUnit_iff_isUnit_det L).mpr (hL ▸ isUnit_one))

end
end CompoundFeasibility.RestrictedRows5
