import SubspaceBridge.OriginalExterior3Source4
open scoped BigOperators Matrix
namespace Exterior3Source181RChallenge
open CompoundFeasibility CompoundFeasibility.Exterior3

theorem dimension4 : Module.finrank ℚ (Fin 4 → ℚ) = Nat.choose 4 3 := by
  norm_num [Nat.choose]

theorem ordered_triples4 (s : Fin 4) : StrictMono (tripleIndex4 s) := by
  fin_cases s <;> decide

theorem exact_compound_group4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃ =
      sourceLattice4 (compound3Matrix4 A₂) (compound3Matrix4 A₃)
        (summedExponents3_4 2 Q c₂) (summedExponents3_4 3 Q c₃) := rfl

#print axioms dimension4
#print axioms ordered_triples4
#print axioms exact_compound_group4
end Exterior3Source181RChallenge
