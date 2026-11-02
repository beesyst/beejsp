import SubspaceBridge.SourceOriginalRank4Flag245U
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

def compound4246 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    Matrix (Fin 5) (Fin 5) R := A.adjugate.transpose

def wedge4246 {R : Type*} [CommRing R] (x : Fin 4 → Fin 5 → R) : Fin 5 → R :=
  fun i => (Matrix.of (Fin.snoc x 0)).adjugate i 4

theorem compound_minor4246 {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) (i j : Fin 5) :
    compound4246 A i j = (-1)^(i.val+j.val)*
      (A.submatrix i.succAbove j.succAbove).det := by
  change A.adjugate j i = _
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]

theorem compound_mul4246 {R : Type*} [CommRing R]
    (A B : Matrix (Fin 5) (Fin 5) R) :
    compound4246 (A*B) = compound4246 A*compound4246 B := by
  simp only [compound4246, Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

theorem wedge_transform4246 {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) (x : Fin 4 → Fin 5 → R) :
    compound4246 A *ᵥ wedge4246 x = wedge4246 (fun j => A *ᵥ x j) := by
  have he : Matrix.of (Fin.snoc (fun j => A *ᵥ x j) 0) =
      Matrix.of (Fin.snoc x 0)*A.transpose := by
    ext i k
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change (0 : Fin 5 → R) k = ∑ j, (0 : Fin 5 → R) j * A k j
      simp
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  funext i
  simp only [wedge4246,he,Matrix.adjugate_mul_distrib, ← Matrix.adjugate_transpose,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, compound4246, Matrix.transpose_apply]

end CompoundFeasibility.Exterior54_246
