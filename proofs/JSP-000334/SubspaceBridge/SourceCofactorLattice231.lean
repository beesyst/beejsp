import SubspaceBridge.SourceSecondMinimum230
import SubspaceBridge.SourceRelativeIndex6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceLastDual231
open OriginalDual10 SourceDualGeometry219 SourceRelativeIndex6

theorem lattice_frame_det_dvd231 {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    (c : Basis (Fin n) ℤ G) (w : Fin n → G) :
    (G.index : ℤ) ∣ (Matrix.of (fun j => (w j : Fin n → ℤ))).det := by
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => (c j : Fin n → ℤ) i
  have hm : B * c.toMatrix w = (Matrix.of (fun j => (w j : Fin n → ℤ))).transpose := by
    ext i j
    have he := congrArg (fun x : G => (x : Fin n → ℤ) i) (c.sum_repr (w j))
    simpa [B, Matrix.mul_apply, Basis.toMatrix_apply, Finset.sum_apply, mul_comm] using he
  have hB : B.det.natAbs = G.index := by
    rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin n)) G c,
      integer_basis_det_eq_matrix_det]
    rfl
  rw [← hB, Int.natAbs_dvd]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_transpose] at hd
  exact hd ▸ dvd_mul_right B.det (c.toMatrix w).det

theorem last_row_det_pairing231 {n : ℕ} (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (x : Fin (n+1) → ℤ) :
    (u.updateRow (Fin.last n) x).det = ∑ i, x i * integerLastDual10 u i := by
  have h := congrFun (Matrix.cramer_eq_adjugate_mulVec u.transpose x) (Fin.last n)
  rw [Matrix.cramer_transpose_apply] at h
  rw [← Matrix.adjugate_transpose] at h
  simpa only [Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, integerLastDual10, mul_comm] using h

theorem cofactor_pairing_dvd231 {n : ℕ} (G : AddSubgroup (Fin (n+1) → ℤ))
    (c : Basis (Fin (n+1)) ℤ G) (u : Fin (n+1) → G) (x : G) :
    (G.index : ℤ) ∣ ∑ i, (x : Fin (n+1) → ℤ) i *
      integerLastDual10 (fun j => (u j : Fin (n+1) → ℤ)) i := by
  let w : Fin (n+1) → G := Function.update u (Fin.last n) x
  have he : Matrix.of (fun j => (w j : Fin (n+1) → ℤ)) =
      (Matrix.of (fun j => (u j : Fin (n+1) → ℤ))).updateRow (Fin.last n) x := by
    ext j i
    by_cases hj : j = Fin.last n <;> simp [w, Matrix.updateRow, hj]
  have hd := lattice_frame_det_dvd231 G c w
  rw [he, last_row_det_pairing231] at hd
  exact hd

theorem cofactor_scaled_dual231 (G : AddSubgroup (Fin 10 → ℤ))
    (c : Basis (Fin 10) ℤ G) (hG : G.index ≠ 0) (u : Fin 10 → G) :
    (fun i => (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) i : ℚ)) ∈ scaledDual219 G := by
  apply (scaledDual_pairing219 G hG _).mpr
  intro x
  obtain ⟨a, ha⟩ := cofactor_pairing_dvd231 G c u x
  refine ⟨a, ?_⟩
  change (∑ i, ((x : Fin 10 → ℤ) i : ℚ) *
    (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) i : ℚ)) = _
  exact_mod_cast ha

open SourceSatz51Entry218
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}

theorem source_cofactor_dual231 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    (fun i => (integerLastDual10 D.u i : ℚ)) ∈
      scaledDual219 (originalSourceGroup10 A2 A3 q c2 c3) := by
  obtain ⟨c⟩ := sourceLattice10_has_basis A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))
  exact cofactor_scaled_dual231 (originalSourceGroup10 A2 A3 q c2 c3) c
    (Nat.ne_of_gt (sourceLattice10_index_pos A2 A3 _ _)) (fun j => ⟨D.u j, D.member j⟩)

end CompoundFeasibility.SourceLastDual231
