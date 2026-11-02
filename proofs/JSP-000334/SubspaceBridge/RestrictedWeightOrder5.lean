import SubspaceBridge.RestrictedSelectedIndex5
import Mathlib.Data.Fin.Tuple.Sort
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedWeightOrder5
open RestrictedGeometry5
noncomputable section

def weightOrder5 (c : Fin 5 → ℝ) : Equiv.Perm (Fin 5) := Tuple.sort c

def permutedRows5 {K : Type*} (A : Matrix (Fin 5) (Fin 5) K)
    (sigma : Equiv.Perm (Fin 5)) : Matrix (Fin 5) (Fin 5) K := fun i k => A (sigma i) k

theorem weightOrder5_bijective (c : Fin 5 → ℝ) : Function.Bijective (weightOrder5 c) :=
  (weightOrder5 c).bijective

theorem weightOrder5_monotone (c : Fin 5 → ℝ) :
    Monotone (fun i => c (weightOrder5 c i)) := Tuple.monotone_sort c

theorem weightOrder5_adjacent (c : Fin 5 → ℝ) (i : Fin 4) :
    c (weightOrder5 c i.castSucc) ≤ c (weightOrder5 c i.succ) :=
  weightOrder5_monotone c (by exact Fin.le_iff_val_le_val.mpr (by simp))

theorem weightOrder5_forall_pair {α : Type*} (f : Fin 5 → α) (c : Fin 5 → ℝ)
    (R : α → ℝ → Prop) :
    (∀ i, R (f (weightOrder5 c i)) (c (weightOrder5 c i))) ↔ ∀ i, R (f i) (c i) := by
  constructor
  · intro h i
    simpa using h ((weightOrder5 c).symm i)
  · intro h i
    exact h _

theorem weightOrder5_ties (c : Fin 5 → ℝ) (sigma : Equiv.Perm (Fin 5))
    (h : Monotone (fun i => c (sigma i))) :
    (fun i => c (sigma i)) = (fun i => c (weightOrder5 c i)) := by
  exact (Tuple.comp_sort_eq_comp_iff_monotone).mpr h

theorem permutedRows5_mulVec {K : Type*} [CommRing K]
    (A : Matrix (Fin 5) (Fin 5) K) (sigma : Equiv.Perm (Fin 5)) (x : Fin 5 → K) (i : Fin 5) :
    (permutedRows5 A sigma *ᵥ x) i = (A *ᵥ x) (sigma i) := rfl

theorem originalBody5_weightOrder (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c : Fin 5 → ℝ) :
    originalBody5 (permutedRows5 L (weightOrder5 c)) Q (fun i => c (weightOrder5 c i)) =
      originalBody5 L Q c := by
  ext x
  exact weightOrder5_forall_pair (fun i => (L *ᵥ x) i) c (fun y w => |y| ≤ Q^w)

theorem lattice5_weightOrder (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c : Fin 5 → ℝ) :
    lattice5 p (permutedRows5 A (weightOrder5 c))
      (fun i => Nat.ceil (JSP000334.qThreshold p Q (c (weightOrder5 c i)))) =
    lattice5 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))) := by
  ext x
  rw [lattice5_spec,lattice5_spec]
  exact weightOrder5_forall_pair (fun i => (A *ᵥ (fun k => (x k : ℚ))) i) c
    (fun y w => padicNorm p y ≤ (p : ℚ)^(-(Nat.ceil (JSP000334.qThreshold p Q w) : ℤ)))

theorem originalSourceGroup5_weightOrder
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    originalSourceGroup5 (permutedRows5 A₂ (weightOrder5 c₂))
      (permutedRows5 A₃ (weightOrder5 c₃)) Q
      (fun i => c₂ (weightOrder5 c₂ i)) (fun i => c₃ (weightOrder5 c₃ i)) =
    originalSourceGroup5 A₂ A₃ Q c₂ c₃ := by
  unfold originalSourceGroup5 sourceLattice5
  rw [lattice5_weightOrder,lattice5_weightOrder]

theorem restrictedBody5_weightOrder (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c : Fin 5 → ℝ) :
    restrictedBody5 P (permutedRows5 L (weightOrder5 c)) Q (fun i => c (weightOrder5 c i)) =
      restrictedBody5 P L Q c := by
  unfold restrictedBody5
  rw [originalBody5_weightOrder]

theorem restrictedLattice5_weightOrder (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    restrictedLattice5 P (permutedRows5 A₂ (weightOrder5 c₂))
      (permutedRows5 A₃ (weightOrder5 c₃)) Q
      (fun i => c₂ (weightOrder5 c₂ i)) (fun i => c₃ (weightOrder5 c₃ i)) =
    restrictedLattice5 P A₂ A₃ Q c₂ c₃ := by
  unfold restrictedLattice5
  rw [originalSourceGroup5_weightOrder]

end
end CompoundFeasibility.RestrictedWeightOrder5
