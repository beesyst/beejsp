import SubspaceBridge.SchlickeweiEquation4116
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Equation411150Literal
open SourceReadiness6 SchlickeweiDualVanishing6
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem complete_literal
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q : V) (i : Fin 6) :
    (ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3))) = ((directCompoundGroup42 A2 A3 q.val c2 c3).index : ℝ) ∧
    ((((Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index) * (directCompoundGroup42 A2 A3 q.val c2 c3).index : ℕ) : ℝ) = (((Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index) : ℝ) * (ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3))) ∧
    (∀ k, (-(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 k)) : ℤ)) =
      -(Nat.ceil (JSP000334.qThreshold 2 (q.val ^ (11 : ℕ)) (R.c 1 k)) : ℤ)) ∧
    (∀ k, (-(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 k)) : ℤ)) =
      -(Nat.ceil (JSP000334.qThreshold 3 (q.val ^ (11 : ℕ)) (R.c 2 k)) : ℤ)) ∧
    (‖∑ k, (((((Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index) * (directCompoundGroup42 A2 A3 q.val c2 c3).index : ℕ) : ℚ_[2]) * algebraMap ℚ ℚ_[2] (rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5, (-(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ)))) ∧
    (‖∑ k, (((((Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index) * (directCompoundGroup42 A2 A3 q.val c2 c3).index : ℕ) : ℚ_[3]) * algebraMap ℚ ℚ_[3] (rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5, (-(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ)))) := by
  have h := SchlickeweiEquation4116.source_equation4116 R h2 h3 q i
  dsimp only [SourceRelativeIndex6.frameRelativeIndex, dualVector6,
    Auxiliary6.SourceExpansion.finiteMatrix, SchlickeweiEquation4116.sourceExponent6] at h
  with_reducible exact h
end CompoundFeasibility.Equation411150Literal
#check CompoundFeasibility.Equation411150Literal.complete_literal
#print CompoundFeasibility.Equation411150Literal.complete_literal
#print axioms CompoundFeasibility.Equation411150Literal.complete_literal
