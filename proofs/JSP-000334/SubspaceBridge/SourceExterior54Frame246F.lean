import SubspaceBridge.SourceExterior54Packet246F
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

def signedQuad246 {R : Type*} [CommRing R] (u : Fin 5 → Fin 5 → R) (j : Fin 5) : Fin 5 → R :=
  (-1 : R)^j.val • wedge4246 (fun k : Fin 4 => u (j.succAbove k))

theorem signedQuad_adjugate246 {R : Type*} [CommRing R]
    (u : Matrix (Fin 5) (Fin 5) R) (j i : Fin 5) :
    signedQuad246 u j i = u.adjugate i j := by
  let M : Matrix (Fin 5) (Fin 5) R :=
    Matrix.of (Fin.snoc (fun k : Fin 4 => u (j.succAbove k)) (0 : Fin 5 → R))
  have he : M.submatrix (Fin.last 4).succAbove i.succAbove =
      u.submatrix j.succAbove i.succAbove := by
    ext k l
    simp only [Matrix.submatrix_apply, M, Matrix.of_apply, Fin.succAbove_last, Fin.snoc_castSucc]
  change (-1 : R)^j.val * M.adjugate i (Fin.last 4) = _
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, he,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hs : (-1 : R)^j.val * (-1)^(i.val+4) = (-1)^(i.val+j.val) := by
    simp only [pow_add, show (-1 : R)^4 = 1 by ring, mul_one]
    ring
  rw [← mul_assoc]
  simpa only [Fin.val_last, add_comm] using
    congrArg (fun z : R => z * (u.submatrix j.succAbove i.succAbove).det) hs

theorem signedQuad_independent246 (u : Fin 5 → Fin 5 → ℝ)
    (hu : LinearIndependent ℝ u) : LinearIndependent ℝ (signedQuad246 u) := by
  have he : signedQuad246 u = Matrix.transpose (Matrix.adjugate (u : Matrix (Fin 5) (Fin 5) ℝ)) := by
    funext j i
    exact signedQuad_adjugate246 u j i
  rw [he]
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr
    (compound_unit4246 u (Matrix.linearIndependent_rows_iff_isUnit.mp hu))

theorem signedQuad_cast246 (u : Fin 5 → Fin 5 → ℤ) (j : Fin 5) :
    integerReal (signedQuad246 u j) = signedQuad246 (fun k => integerReal (u k)) j := by
  funext i
  change ((signedQuad246 u j i : ℤ) : ℝ) = _
  rw [signedQuad_adjugate246, signedQuad_adjugate246]
  have h := (Int.castRingHom ℝ).map_adjugate (u : Matrix (Fin 5) (Fin 5) ℤ)
  exact congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M i j) h

theorem integer_signedQuad_independent246 (u : Fin 5 → Fin 5 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) :
    LinearIndependent ℝ (fun j => integerReal (signedQuad246 u j)) := by
  simp_rw [signedQuad_cast246]
  exact signedQuad_independent246 _ hu

theorem signedQuad_source_group246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c2 c3 : Fin 5 → ℝ)
    (u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3) (j : Fin 5) :
    signedQuad246 (fun k => (u k : Fin 5 → ℤ)) j ∈
      originalSourceGroup5 (compound4246 A2) (compound4246 A3) (Q^4)
        (normalizedWeights4246 c2) (normalizedWeights4246 c3) := by
  exact AddSubgroup.zsmul_mem _ (wedge_source_group4246 A2 A3 Q c2 c3
    (fun k => u (j.succAbove k))) ((-1 : ℤ)^j.val)

end CompoundFeasibility.Exterior54_246
