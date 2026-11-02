import SubspaceBridge.SourceCofactorLattice231
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceLastDual231
open OriginalDual10 SourceOriginalDual10 SourceSatz51Entry218 SourceRelativeIndex6

theorem signed_cofactor231 {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (r : ℚ)
    (hr : r = |((Matrix.det u : ℤ) : ℚ)|) :
    (fun i => (integerLastDual10 u i : ℚ)) = r • lastDual10 (fun j i => (u j i : ℚ)) hu ∨
    (fun i => (integerLastDual10 u i : ℚ)) = -(r • lastDual10 (fun j i => (u j i : ℚ)) hu) := by
  rw [integerLastDual10_eq u hu, hr]
  by_cases h : 0 ≤ ((Matrix.det u : ℤ) : ℚ)
  · left
    rw [abs_of_nonneg h]
  · right
    rw [abs_of_neg (lt_of_not_ge h), neg_smul, neg_neg]

theorem frame_normalization_eq231 {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    [IsZLattice ℝ (integerRealImage G)] (c : Basis (Fin n) ℤ G)
    (u : Fin n → G) (hu : LinearIndependent ℤ u) (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : Matrix.of (fun j => (u j : Fin n → ℤ)) = U) :
    frameRelativeIndex G u * G.index = U.det.natAbs ∧
      |(U.det : ℝ)| = (frameRelativeIndex G u : ℝ) * ZLattice.covolume (integerRealImage G) := by
  have h := And.intro (frameRelativeIndex_mul_index G c u hu) (frame_abs_det_covolume G c u hu)
  exact Eq.mp (congrArg (fun V : Matrix (Fin n) (Fin n) ℤ =>
    frameRelativeIndex G u * G.index = V.det.natAbs ∧
      |(V.det : ℝ)| = (frameRelativeIndex G u : ℝ) * ZLattice.covolume (integerRealImage G)) hU) h

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}

def sourceFrame231 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    Fin 10 → originalSourceGroup10 A2 A3 q c2 c3 := fun j => ⟨D.u j, D.member j⟩

def sourceFrameIndex231 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) : ℕ :=
  frameRelativeIndex (originalSourceGroup10 A2 A3 q c2 c3) (sourceFrame231 D)

def sourceScaledLast231 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) : Fin 10 → ℚ :=
  ((sourceFrameIndex231 D * (originalSourceGroup10 A2 A3 q c2 c3).index : ℕ) : ℚ) •
    lastDual10 (fun j i => (D.u j i : ℚ)) (integer_frame_rational_independent10 D.u D.independent)

theorem source_cofactor_nonzero231 (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    integerLastDual10 D.u ≠ 0 := by
  have hu := integer_frame_rational_independent10 D.u D.independent
  exact integerLastDual10_nonzero D.u hu

end CompoundFeasibility.SourceLastDual231
