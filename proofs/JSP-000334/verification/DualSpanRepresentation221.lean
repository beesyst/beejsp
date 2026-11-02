import verification.DualMatrixRepresentation221
open scoped BigOperators Matrix
namespace M221SpanRepresentation
open CompoundFeasibility.SourceDualGeometry219 M221MatrixRepresentation

theorem raw_generator221 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G)
    (j : Fin 10) :
    (G.index : ℚ) • (fun i => (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ i j) =
      (G.index : ℚ) • dualVector219 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) j := by
  exact congrArg (fun v : Fin 10 → ℚ => (G.index : ℚ) • v)
    (raw_column221 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) j)

theorem raw_generators221 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G) :
    (fun j : Fin 10 => (G.index : ℚ) •
      (fun i => (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ i j)) =
    (fun j : Fin 10 => (G.index : ℚ) •
      dualVector219 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) j) := by
  exact funext (raw_generator221 G c)

theorem raw_range221 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G) :
    Set.range (fun j : Fin 10 => (G.index : ℚ) •
      (fun i => (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ i j)) =
    Set.range (fun j : Fin 10 => (G.index : ℚ) •
      dualVector219 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) j) := by
  exact congrArg Set.range (raw_generators221 G c)

theorem raw_span221 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G) :
    Submodule.span ℤ (Set.range (fun j : Fin 10 => (G.index : ℚ) •
      (fun i => (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ i j))) =
      basisDualSpan219 G c := by
  exact congrArg (Submodule.span ℤ) (raw_range221 G c)

theorem raw_span_set221 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G) :
    (Submodule.span ℤ (Set.range (fun j : Fin 10 => (G.index : ℚ) •
      (fun i => (Matrix.of (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))⁻¹ i j))) : Set (Fin 10 → ℚ)) =
      (basisDualSpan219 G c : Set (Fin 10 → ℚ)) := by
  exact congrArg (fun S : Submodule ℤ (Fin 10 → ℚ) => (S : Set (Fin 10 → ℚ))) (raw_span221 G c)


theorem raw_kronecker221 (f : Fin 10 → Fin 10 → ℚ)
    (hf : LinearIndependent ℚ f) (i j : Fin 10) :
    (∑ k, f i k*(Matrix.of f)⁻¹ k j) = if i=j then 1 else 0 := by
  let W : Matrix (Fin 10) (Fin 10) ℚ := f
  have hW : IsUnit W := Matrix.linearIndependent_rows_iff_isUnit.mp hf
  have h := congrArg (fun z : Fin 10 → ℚ => ∑ k, f i k*z k) (raw_column221 f j)
  exact h.trans (dualVector_pairing219 W hW i j)

end M221SpanRepresentation
