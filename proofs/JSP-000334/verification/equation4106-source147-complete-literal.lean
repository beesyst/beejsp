import SubspaceBridge.SchlickeweiEquation4106
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Equation410147Literal
open SourceReadiness6 SchlickeweiDualVanishing6

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem complete_literal
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (q : V) (i : Fin 6) :
    ‖∑ k : Fin 6,
      (((Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index : ℝ) *
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) *
        algebraMap ℚ ℝ (rationalFrameDual42
          (fun j k => ((R.w q j : Fin 6 → ℤ) k : ℚ)) (sourceFrameIndependent6 R q)
          5 (Pi.single k 1))) * (compound L)⁻¹.transpose i k‖ ≤
      120 * ((q.val ^ (11 : ℕ)) ^ (R.c 0 i))⁻¹ *
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) *
        (q.val ^ (11 : ℕ)) ^ (-5 * R.delta) := by
  have h := SchlickeweiEquation4106.source_equation4106 R h2 h3 hLdet q i
  dsimp only [SourceRelativeIndex6.frameRelativeIndex, dualVector6] at h
  with_reducible exact h

end CompoundFeasibility.Equation410147Literal
#check CompoundFeasibility.Equation410147Literal.complete_literal
#print CompoundFeasibility.Equation410147Literal.complete_literal
#print axioms CompoundFeasibility.Equation410147Literal.complete_literal
