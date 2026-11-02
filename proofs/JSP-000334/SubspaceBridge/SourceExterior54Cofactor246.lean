import SubspaceBridge.SourceExterior54_246
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246
open OriginalDual10

def paddedFrame246 (x : Fin 4 → Fin 5 → ℤ) : Fin 5 → Fin 5 → ℤ :=
  Fin.snoc x (0 : Fin 5 → ℤ)

theorem wedge_cofactor246 (x : Fin 4 → Fin 5 → ℤ) :
    wedge4246 x = integerLastDual10 (n := 4) (paddedFrame246 x) := by
  rfl

end CompoundFeasibility.Exterior54_246
