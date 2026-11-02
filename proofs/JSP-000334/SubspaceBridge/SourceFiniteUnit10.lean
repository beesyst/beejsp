import SubspaceBridge.SourceForms10
open scoped Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceBalance10

theorem source_finite_unit10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.det = 1) :
    IsUnit (SourceForms10.finiteMatrix10 p A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [SourceForms10.finite_det_one10 p A hA]
  exact isUnit_one

end CompoundFeasibility.Auxiliary10.SourceBalance10
