import SubspaceBridge.SchlickeweiEquation4106
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiEquation4116
open SourceLocalUpper6 SourceHeightBounds6 Auxiliary6.SourceExpansion SourceWeights
open SchlickeweiDualVanishing6 SourceProper6 SchlickeweiEquation4106

theorem padic_minor_bound6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ_[p]) (f : Fin 5 → ℤ)
    (hA : ∀ j k, ‖A j k‖ ≤ (p : ℝ) ^ f k) :
    ‖A.det‖ ≤ (p : ℝ) ^ (∑ k, f k) := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hprod (s : Finset (Fin 5)) : (∏ k ∈ s, (p : ℝ) ^ f k) =
      (p : ℝ) ^ (∑ k ∈ s, f k) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.prod_insert, Finset.sum_insert, ha, ih, zpow_add₀ hp]
  calc
    _ ≤ ∏ k, (p : ℝ) ^ f k := padic_det5_le p A _ (fun k => zpow_nonneg (by positivity) _) hA
    _ = _ := hprod Finset.univ

def sourceExponent6 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 6) : ℤ :=
  -(Nat.ceil (JSP000334.qThreshold p q (pairWeights42 c i)) : ℤ)

theorem local_integer_exponent6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (q : ℝ) (c : Fin 4 → ℝ) (z : Fin 6 → ℤ) :
    z ∈ directLocal42 p A (fun j => JSP000334.qThreshold p q (c j)) ↔
      ∀ i, ‖(finiteMatrix p A *ᵥ (fun k => (z k : ℚ_[p]))) i‖ ≤
        (p : ℝ) ^ sourceExponent6 p q c i := by
  rw [directLocal42_spec]
  apply forall_congr'
  intro i
  rw [finite_form_norm, ← qThreshold_add42]
  simp only [sourceExponent6, pairWeights42, zpow_neg, zpow_natCast]
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rfl

open SourceReadiness6
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_first_five_integer_bounds6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    (∀ (j : Fin 5) i, ‖(finiteMatrix 2 A2 *ᵥ
      (fun k => ((R.w q j.castSucc : Fin 6 → ℤ) k : ℚ_[2]))) i‖ ≤
        (2 : ℝ) ^ sourceExponent6 2 q.val c2 i) ∧
    (∀ (j : Fin 5) i, ‖(finiteMatrix 3 A3 *ᵥ
      (fun k => ((R.w q j.castSucc : Fin 6 → ℤ) k : ℚ_[3]))) i‖ ≤
        (3 : ℝ) ^ sourceExponent6 3 q.val c3 i) := by
  constructor
  · intro j
    exact (local_integer_exponent6 2 A2 q.val c2 _).mp (R.w q j.castSucc).property.1
  · intro j
    exact (local_integer_exponent6 3 A3 q.val c3 _).mp (R.w q j.castSucc).property.2

theorem source_exponent_rescaling6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (i : Fin 6) :
    sourceExponent6 2 q.val c2 i =
      -(Nat.ceil (JSP000334.qThreshold 2 (q.val ^ (11 : ℕ)) (R.c 1 i)) : ℤ) ∧
    sourceExponent6 3 q.val c3 i =
      -(Nat.ceil (JSP000334.qThreshold 3 (q.val ^ (11 : ℕ)) (R.c 2 i)) : ℤ) := by
  rw [(R.finite_weights i).1, (R.finite_weights i).2]
  simp only [sourceExponent6, finiteWeight, davenport_rescaled_threshold42]
  trivial

theorem source_exponent_nonpos6 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 6) :
    sourceExponent6 p q c i ≤ 0 := neg_nonpos.mpr (Int.natCast_nonneg _)
end CompoundFeasibility.SchlickeweiEquation4116

#check CompoundFeasibility.SchlickeweiEquation4116.padic_minor_bound6
#print CompoundFeasibility.SchlickeweiEquation4116.padic_minor_bound6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.padic_minor_bound6

#check CompoundFeasibility.SchlickeweiEquation4116.local_integer_exponent6
#print CompoundFeasibility.SchlickeweiEquation4116.local_integer_exponent6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.local_integer_exponent6

#check CompoundFeasibility.SchlickeweiEquation4116.source_first_five_integer_bounds6
#print CompoundFeasibility.SchlickeweiEquation4116.source_first_five_integer_bounds6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_first_five_integer_bounds6

#check CompoundFeasibility.SchlickeweiEquation4116.source_exponent_rescaling6
#print CompoundFeasibility.SchlickeweiEquation4116.source_exponent_rescaling6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_exponent_rescaling6

#check CompoundFeasibility.SchlickeweiEquation4116.source_exponent_nonpos6
#print CompoundFeasibility.SchlickeweiEquation4116.source_exponent_nonpos6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_exponent_nonpos6
