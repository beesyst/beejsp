import SubspaceBridge.SourceDualBasis220
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceDualGeometry219

theorem original_basis_independent220
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ)
    (c : Basis (Fin 10) ℤ (originalSourceGroup10 A2 A3 q c2 c3)) :
    LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) := by
  exact SourceOriginalDual10.integer_frame_rational_independent10 _
    (integerRealImage_basis_independent _ c)

theorem original_scaledDual_eq_basis220
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    let G := originalSourceGroup10 A2 A3 q c2 c3
    let c : Basis (Fin 10) ℤ G := (sourceLattice10_has_basis A2 A3
      (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))).some
    scaledDual219 G = (basisDualSpan219 G c : Set (Fin 10 → ℚ)) := by
  let G := originalSourceGroup10 A2 A3 q c2 c3
  let c : Basis (Fin 10) ℤ G := (sourceLattice10_has_basis A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))).some
  exact scaledDual_eq_basis219 G (Nat.ne_of_gt (sourceLattice10_index_pos A2 A3 _ _)) c
    (original_basis_independent220 A2 A3 q c2 c3 c)

end CompoundFeasibility.SourceDualGeometry219
