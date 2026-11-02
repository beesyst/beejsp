import SubspaceBridge.AlgebraicLiouville6
open scoped BigOperators Matrix
namespace Liouville6Literal
open CompoundFeasibility
noncomputable section

def first : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def second : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
def entry (L : Matrix (Fin 4) (Fin 4) ℝ) (s t : Fin 6) : ℝ :=
  L (first s) (first t) * L (second s) (second t) -
    L (first s) (second t) * L (second s) (first t)

theorem integer_form_bound (a : Fin 6 → Fin 6 → ℝ)
    (ha : ∀ s i, IsAlgebraic ℚ (a s i)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (s : Fin 6) (z : Fin 6 → ℤ),
      (∑ i, a s i * (z i : ℝ)) ≠ 0 →
      C ≤ |∑ i, a s i * (z i : ℝ)| * (max 1 ‖(fun i => (z i : ℝ))‖)^D := by
  exact algebraic_fin6_liouville_lower a ha

theorem raw_source_bound (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (s : Fin 6) (z : Fin 6 → ℤ),
      (∑ t, (L (first s) (first t) * L (second s) (second t) -
        L (first s) (second t) * L (second s) (first t)) * (z t : ℝ)) ≠ 0 →
      C ≤ |∑ t, (L (first s) (first t) * L (second s) (second t) -
        L (first s) (second t) * L (second s) (first t)) * (z t : ℝ)| *
          (max 1 ‖(fun t => (z t : ℝ))‖)^D := by
  exact integer_form_bound (entry L) (fun s t =>
    ((ha _ _).mul (ha _ _)).sub ((ha _ _).mul (ha _ _)))

theorem raw_coordinate_identity (L : Matrix (Fin 4) (Fin 4) ℝ)
    (s : Fin 6) (z : Fin 6 → ℤ) :
    (compound L *ᵥ integerReal z) s = ∑ t, entry L s t * (z t : ℝ) := rfl

theorem full_source_contract (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (s : Fin 6) (z : Fin 6 → ℤ),
      (compound L *ᵥ integerReal z) s ≠ 0 →
      C ≤ |(compound L *ᵥ integerReal z) s| * (max 1 ‖integerReal z‖)^D := by
  simpa only [raw_coordinate_identity] using raw_source_bound L hL ha

end
end Liouville6Literal
#print axioms Liouville6Literal.first
#print axioms Liouville6Literal.second
#print axioms Liouville6Literal.entry
#print axioms Liouville6Literal.integer_form_bound
#print axioms Liouville6Literal.raw_source_bound
#print axioms Liouville6Literal.raw_coordinate_identity
#print axioms Liouville6Literal.full_source_contract
