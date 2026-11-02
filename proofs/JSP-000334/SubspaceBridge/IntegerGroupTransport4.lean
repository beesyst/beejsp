import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Int.Defs
namespace CompoundFeasibility.BoundedWeights4

def castGroupMember4 (G H : AddSubgroup (Fin 4 → ℤ)) (h : G = H) (x : G) : H := by
  cases h
  exact x

theorem castGroupMember4_values (G H : AddSubgroup (Fin 4 → ℤ)) (h : G = H) (x : G) :
    (castGroupMember4 G H h x : Fin 4 → ℤ) = (x : Fin 4 → ℤ) := by
  cases h
  rfl

end CompoundFeasibility.BoundedWeights4
