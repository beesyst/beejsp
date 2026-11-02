import SubspaceBridge.SchlickeweiReferenceRescaling6
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.Reference162Bridges
open SchlickeweiDualVanishing6 SchlickeweiReference6 SchlickeweiEquation4116 Auxiliary6.SourceExpansion

theorem coordinate6 {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (D : Fin 6 → ℚ) (i : Fin 6) :
    dualFormValue6 B D i =
      ∑ k : Fin 6, algebraMap ℚ K (D k) * B⁻¹.transpose i k := by
  rfl

end CompoundFeasibility.Reference162Bridges
#check CompoundFeasibility.Reference162Bridges.coordinate6
#print CompoundFeasibility.Reference162Bridges.coordinate6
#print axioms CompoundFeasibility.Reference162Bridges.coordinate6
