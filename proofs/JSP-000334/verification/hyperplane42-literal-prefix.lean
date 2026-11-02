import SubspaceBridge.CompoundHyperplane42
open scoped BigOperators Matrix
open CompoundFeasibility
namespace Hyperplane42Literal
noncomputable section

def H (v : Fin 6 → Fin 6 → ℤ) : Submodule ℝ (Fin 6 → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : Fin 5 => fun i => (v j.castSucc i : ℝ)))

def rationalH (v : Fin 6 → Fin 6 → ℤ) : Submodule ℚ (Fin 6 → ℚ) :=
  Submodule.span ℚ (Set.range (fun j : Fin 5 => fun i => (v j.castSucc i : ℚ)))

theorem missing_pair (a : Fin 4 → ℝ) :
    lo (pairProductOrder42 a 5) = 2 ∧ hi (pairProductOrder42 a 5) = 3 := by
  rw [pairProductOrder42_last]
  constructor <;> rfl

theorem margin (B x y Q delta : ℝ) (hB : 0 < B) (hy : 0 < y) (hQ : 1 < Q)
    (hcut : B < Q ^ (delta / 2)) (hgap : x < y * Q ^ (-delta / 2)) : B * x < y :=
  gap_margin42 B x y Q delta hB hy hQ hcut hgap

end
#check H
#print axioms H
#check rationalH
#print axioms rationalH
#check missing_pair
#print axioms missing_pair
#check margin
#print axioms margin
end Hyperplane42Literal
