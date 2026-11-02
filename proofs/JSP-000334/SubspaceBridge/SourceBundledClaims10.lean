import SubspaceBridge.SourceP2Claim10
import SubspaceBridge.SourceP3Claim10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceBalance10
open SourceMultiblock10 SourceNormalHighIndex10

theorem source_three_claims10 {m : ℕ} (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (P : MvPolynomial (Vars10 m) ℤ)
    (hhom : homogeneous10 r P) (hi0 : matrixIndex10 L r eta P)
    (hi2 : matrixIndex10 (SourceForms10.finiteMatrix10 2 A2) r eta P)
    (hi3 : matrixIndex10 (SourceForms10.finiteMatrix10 3 A3) r eta P) :
    Claims r eta L P ∧ Claims r eta (SourceForms10.finiteMatrix10 2 A2) P ∧
      Claims r eta (SourceForms10.finiteMatrix10 3 A3) P := by
  exact ⟨source_real_claim10 L hL r hr eta heta P hhom hi0,
    source_p2_claim10 A2 h2 r hr eta heta P hhom hi2,
    source_p3_claim10 A3 h3 r hr eta heta P hhom hi3⟩

end CompoundFeasibility.Auxiliary10.SourceBalance10
