import SubspaceBridge.SourceBalance6
open scoped Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10

theorem inverse_map_generic10 {ι F E : Type*} [Fintype ι] [DecidableEq ι]
    [Field F] [Field E] (f : F →+* E) (A : Matrix ι ι F) (hA : A.det ≠ 0) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have hleft : A⁻¹.map f * A.map f = 1 :=
    (Auxiliary6.SourceBalance.mapped_inverse f A hA).1
  exact Matrix.inv_eq_left_inv hleft

theorem inverse_adjugate_generic10 {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Field F] (A : Matrix ι ι F) (hA : A.det = 1) : A⁻¹ = A.adjugate := by
  rw [Matrix.inv_def,hA,Ring.inverse_one,one_smul]

theorem adjugate_dual_map_generic10 {ι F E : Type*} [Fintype ι] [DecidableEq ι]
    [Field F] [Field E] (f : F →+* E) (A : Matrix ι ι F) (hA : A.det = 1) :
    (A.map f)⁻¹.transpose = A.adjugate.transpose.map f := by
  have hn : A.det ≠ 0 := by rw [hA]; exact one_ne_zero
  rw [inverse_map_generic10 f A hn,inverse_adjugate_generic10 A hA]
  rfl

end CompoundFeasibility.SourceHeightEnvelope10
