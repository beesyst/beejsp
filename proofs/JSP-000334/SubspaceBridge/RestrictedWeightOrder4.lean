import SubspaceBridge.RestrictedSelectedIndex4
import Mathlib.Data.Fin.Tuple.Sort
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedWeightOrder4
open RestrictedGeometry4
noncomputable section

def weightOrder4 (c : Fin 4 → ℝ) : Equiv.Perm (Fin 4) := Tuple.sort c

def permutedRows4 {K : Type*} (A : Matrix (Fin 4) (Fin 4) K)
    (sigma : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) K := fun i k => A (sigma i) k

theorem weightOrder4_bijective (c : Fin 4 → ℝ) : Function.Bijective (weightOrder4 c) :=
  (weightOrder4 c).bijective

theorem weightOrder4_monotone (c : Fin 4 → ℝ) :
    Monotone (fun i => c (weightOrder4 c i)) := Tuple.monotone_sort c

theorem weightOrder4_adjacent (c : Fin 4 → ℝ) (i : Fin 3) :
    c (weightOrder4 c i.castSucc) ≤ c (weightOrder4 c i.succ) :=
  weightOrder4_monotone c (by exact Fin.le_iff_val_le_val.mpr (by simp))

theorem weightOrder4_forall_pair {α : Type*} (f : Fin 4 → α) (c : Fin 4 → ℝ)
    (R : α → ℝ → Prop) :
    (∀ i, R (f (weightOrder4 c i)) (c (weightOrder4 c i))) ↔ ∀ i, R (f i) (c i) := by
  constructor
  · intro h i
    simpa using h ((weightOrder4 c).symm i)
  · intro h i
    exact h _

theorem weightOrder4_ties (c : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4))
    (h : Monotone (fun i => c (sigma i))) :
    (fun i => c (sigma i)) = (fun i => c (weightOrder4 c i)) := by
  exact (Tuple.comp_sort_eq_comp_iff_monotone).mpr h

theorem permutedRows4_mulVec {K : Type*} [CommRing K]
    (A : Matrix (Fin 4) (Fin 4) K) (sigma : Equiv.Perm (Fin 4)) (x : Fin 4 → K) (i : Fin 4) :
    (permutedRows4 A sigma *ᵥ x) i = (A *ᵥ x) (sigma i) := rfl

theorem originalBody4_weightOrder (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) :
    originalBody4 (permutedRows4 L (weightOrder4 c)) Q (fun i => c (weightOrder4 c i)) =
      originalBody4 L Q c := by
  ext x
  exact weightOrder4_forall_pair (fun i => (L *ᵥ x) i) c (fun y w => |y| ≤ Q^w)

theorem lattice4_weightOrder (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ) :
    lattice4 p (permutedRows4 A (weightOrder4 c))
      (fun i => Nat.ceil (JSP000334.qThreshold p Q (c (weightOrder4 c i)))) =
    lattice4 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))) := by
  ext x
  rw [lattice4_spec,lattice4_spec]
  exact weightOrder4_forall_pair (fun i => (A *ᵥ (fun k => (x k : ℚ))) i) c
    (fun y w => padicNorm p y ≤ (p : ℚ)^(-(Nat.ceil (JSP000334.qThreshold p Q w) : ℤ)))

theorem originalSourceGroup4_weightOrder
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    originalSourceGroup4 (permutedRows4 A₂ (weightOrder4 c₂))
      (permutedRows4 A₃ (weightOrder4 c₃)) Q
      (fun i => c₂ (weightOrder4 c₂ i)) (fun i => c₃ (weightOrder4 c₃ i)) =
    originalSourceGroup4 A₂ A₃ Q c₂ c₃ := by
  unfold originalSourceGroup4 sourceLattice4
  rw [lattice4_weightOrder,lattice4_weightOrder]

theorem restrictedBody4_weightOrder (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) :
    restrictedBody4 P (permutedRows4 L (weightOrder4 c)) Q (fun i => c (weightOrder4 c i)) =
      restrictedBody4 P L Q c := by
  unfold restrictedBody4
  rw [originalBody4_weightOrder]

theorem restrictedLattice4_weightOrder (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    restrictedLattice4 P (permutedRows4 A₂ (weightOrder4 c₂))
      (permutedRows4 A₃ (weightOrder4 c₃)) Q
      (fun i => c₂ (weightOrder4 c₂ i)) (fun i => c₃ (weightOrder4 c₃ i)) =
    restrictedLattice4 P A₂ A₃ Q c₂ c₃ := by
  unfold restrictedLattice4
  rw [originalSourceGroup4_weightOrder]

end
end CompoundFeasibility.RestrictedWeightOrder4
