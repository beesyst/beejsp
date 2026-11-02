import SubspaceBridge.SourceRealClaim10
import SubspaceBridge.SourceFiniteUnit10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceBalance10
open SourceMultiblock10 SourceNormalHighIndex10

theorem source_p2_claim10 {m : ℕ} (A : Matrix (Fin 10) (Fin 10) ℚ)
    (hA : A.det = 1) (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (P : MvPolynomial (Vars10 m) ℤ)
    (hhom : homogeneous10 r P) (hi : matrixIndex10 (SourceForms10.finiteMatrix10 2 A) r eta P) :
    Claims r eta (SourceForms10.finiteMatrix10 2 A) P := by
  exact claims_of_unit10 (SourceForms10.finiteMatrix10 2 A)
    (source_finite_unit10 2 A hA) r hr eta heta P hhom hi

end CompoundFeasibility.Auxiliary10.SourceBalance10
