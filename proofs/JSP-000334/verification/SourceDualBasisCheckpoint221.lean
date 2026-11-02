import SubspaceBridge.SourceOriginalDualBasis220
import verification.DualSetRepresentation221
import verification.DualSpanRepresentation221
open scoped BigOperators Classical Matrix
noncomputable section
namespace M220SourceChallenge
open CompoundFeasibility SourceDualGeometry219
open M221SetRepresentation M221SpanRepresentation

theorem expanded_basis_equality220 (G : AddSubgroup (Fin 10 → ℤ)) (hD : G.index ≠ 0)
    (c : Basis (Fin 10) ℤ G)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))) :
    (fun v : Fin 10 → ℚ => (G.index : ℚ) • v) ''
      {v | ∀ x : G, ∃ a : ℤ, (∑ i, ((x : Fin 10 → ℤ) i : ℚ)*v i) = (a : ℚ)} =
    (Submodule.span ℤ (Set.range (fun j : Fin 10 => (G.index : ℚ) •
      (fun i => (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ i j))) : Set (Fin 10 → ℚ)) := by
  exact (raw_scaled221 G).trans
    ((scaledDual_eq_basis219 G hD c hc).trans (raw_span_set221 G c).symm)

theorem actual_original_equality220
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    let G := originalSourceGroup10 A2 A3 q c2 c3
    let c : Basis (Fin 10) ℤ G := (sourceLattice10_has_basis A2 A3
      (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))).some
    (fun v : Fin 10 → ℚ => (G.index : ℚ) • v) ''
      {v | ∀ x : G, ∃ a : ℤ, (∑ i, ((x : Fin 10 → ℤ) i : ℚ)*v i) = (a : ℚ)} =
    (Submodule.span ℤ (Set.range (fun j : Fin 10 => (G.index : ℚ) •
      (fun i => (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ i j))) : Set (Fin 10 → ℚ)) := by
  exact (raw_scaled221 _).trans
    ((original_scaledDual_eq_basis220 A2 A3 q c2 c3).trans (raw_span_set221 _ _).symm)

theorem expanded_matrix_pairing220 (W : Matrix (Fin 10) (Fin 10) ℚ) (hW : IsUnit W)
    (i j : Fin 10) : (∑ k, W i k*W⁻¹ k j) = if i=j then 1 else 0 := by
  exact dualVector_pairing219 W hW i j

theorem actual_old_basis_pairing220
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    let G := originalSourceGroup10 A2 A3 q c2 c3
    let c : Basis (Fin 10) ℤ G := (sourceLattice10_has_basis A2 A3
      (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))).some
    ∀ i j : Fin 10, (∑ k, ((c i : Fin 10 → ℤ) k : ℚ)*
      (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ k j) = if i=j then 1 else 0 := by
  intro G c i j
  exact raw_kronecker221 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))
    (original_basis_independent220 A2 A3 q c2 c3 c) i j


theorem actual_original_both_inclusions220
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ)
    (c : Basis (Fin 10) ℤ (originalSourceGroup10 A2 A3 q c2 c3)) (z : Fin 10 → ℚ) :
    (z ∈ scaledDual219 (originalSourceGroup10 A2 A3 q c2 c3) →
      z ∈ basisDualSpan219 (originalSourceGroup10 A2 A3 q c2 c3) c) ∧
    (z ∈ basisDualSpan219 (originalSourceGroup10 A2 A3 q c2 c3) c →
      z ∈ scaledDual219 (originalSourceGroup10 A2 A3 q c2 c3)) := by
  have hc := SourceOriginalDual10.integer_frame_rational_independent10
    (fun j => (c j : Fin 10 → ℤ)) (integerRealImage_basis_independent _ c)
  exact ⟨scaledDual_subset_basis219 _ c hc z,basisDual_subset_scaled219 _
    (Nat.ne_of_gt (sourceLattice10_index_pos A2 A3 _ _)) c hc z⟩

end M220SourceChallenge
#check M220SourceChallenge.expanded_basis_equality220
#print M220SourceChallenge.expanded_basis_equality220
#print axioms M220SourceChallenge.expanded_basis_equality220
#check M220SourceChallenge.actual_original_equality220
#print M220SourceChallenge.actual_original_equality220
#print axioms M220SourceChallenge.actual_original_equality220
#check M220SourceChallenge.expanded_matrix_pairing220
#print M220SourceChallenge.expanded_matrix_pairing220
#print axioms M220SourceChallenge.expanded_matrix_pairing220
#check M220SourceChallenge.actual_old_basis_pairing220
#print M220SourceChallenge.actual_old_basis_pairing220
#print axioms M220SourceChallenge.actual_old_basis_pairing220
#check M220SourceChallenge.actual_original_both_inclusions220
#print M220SourceChallenge.actual_original_both_inclusions220
#print axioms M220SourceChallenge.actual_original_both_inclusions220
