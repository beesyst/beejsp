import SubspaceBridge.SchlickeweiRealCompletion6
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.Reference163Bridges
open SchlickeweiDualVanishing6 SchlickeweiReference6 SchlickeweiIntegerPairing6
open SchlickeweiEquation4116 Auxiliary6.SourceExpansion

theorem integer_coordinate6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (b : Fin 6 → ℤ) (i : Fin 6) :
    dualFormValue6 B (fun k => (b k : ℚ)) i =
      ∑ k : Fin 6, algebraMap ℚ ℚ_[p] (b k : ℚ) * B⁻¹.transpose i k := by
  rw [native_dual_coordinates6 p B b i]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_intCast]
  exact mul_comm _ _


theorem finite_matrix6 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) :
    finiteMatrix p A = (compound A).map (algebraMap ℚ ℚ_[p]) := by
  rfl

theorem finite_coordinate6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (b : Fin 6 → ℤ) (i : Fin 6) :
    dualFormValue6 (finiteMatrix p A) (fun k => (b k : ℚ)) i =
      ∑ k : Fin 6, algebraMap ℚ ℚ_[p] (b k : ℚ) *
        ((compound A).map (algebraMap ℚ ℚ_[p]))⁻¹.transpose i k := by
  have h := integer_coordinate6 p (finiteMatrix p A) b i
  rw [finite_matrix6 p A] at h
  exact h

theorem exponent6 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 6) :
    sourceExponent6 p q c i =
      -(Nat.ceil (JSP000334.qThreshold p q (pairWeights42 c i)) : ℤ) := by
  rfl

theorem exponent_sum6 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 6) :
    (∑ k : Fin 5, sourceExponent6 p q c (i.succAbove k)) =
      ∑ k : Fin 5, -(Nat.ceil (JSP000334.qThreshold p q (pairWeights42 c (i.succAbove k))) : ℤ) := by
  apply Finset.sum_congr rfl
  intro k _
  exact exponent6 p q c (i.succAbove k)

theorem finite_bound_representation6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (b : Fin 6 → ℤ) (q : ℝ) (c : Fin 4 → ℝ)
    (h : ∀ i, ‖dualFormValue6 (finiteMatrix p A) (fun k => (b k : ℚ)) i‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, sourceExponent6 p q c (i.succAbove k))) :
    ∀ i, ‖∑ k, algebraMap ℚ ℚ_[p] (b k : ℚ) *
      ((compound A).map (algebraMap ℚ ℚ_[p]))⁻¹.transpose i k‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5,
        -(Nat.ceil (JSP000334.qThreshold p q (pairWeights42 c (i.succAbove k))) : ℤ)) := by
  intro i
  have hv := congrArg (fun z : ℚ_[p] => ‖z‖) (finite_coordinate6 p A b i)
  have he := congrArg (fun n : ℤ => (p : ℝ) ^ n) (exponent_sum6 p q c i)
  exact hv.symm.trans_le ((h i).trans_eq he)

open SourceReadiness6
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem reference_coordinate2_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) (i : Fin 6) :
    dualFormValue6 (finiteMatrix 2 A2) (fun k => (sourceReference6 R q1 k : ℚ)) i =
      ∑ k, algebraMap ℚ ℚ_[2] (sourceReference6 R q1 k : ℚ) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k :=
  finite_coordinate6 2 A2 (sourceReference6 R q1) i

theorem reference_bound2_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) :
    ∀ i, ‖∑ k, algebraMap ℚ ℚ_[2] (sourceReference6 R q1 k : ℚ) *
      ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5,
        -(Nat.ceil (JSP000334.qThreshold 2 q1.val (pairWeights42 c2 (i.succAbove k))) : ℤ)) :=
  finite_bound_representation6 2 A2 (sourceReference6 R q1) q1.val c2 (source_reference_p2_bound6 R h2 h3 q1)

theorem rescaled_coordinate2_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) (i : Fin 6) :
    dualFormValue6 (finiteMatrix 2 A2) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i =
      ∑ k, algebraMap ℚ ℚ_[2] (rescaledReference6 R h2 h3 q1 q k : ℚ) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k :=
  finite_coordinate6 2 A2 (rescaledReference6 R h2 h3 q1 q) i

theorem rescaled_bound2_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) :
    ∀ i, ‖∑ k, algebraMap ℚ ℚ_[2] (rescaledReference6 R h2 h3 q1 q k : ℚ) *
      ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5,
        -(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ)) :=
  finite_bound_representation6 2 A2 (rescaledReference6 R h2 h3 q1 q) q.val c2 (rescaled_reference_p2_6 R h2 h3 hc2 hc3 q1 q)

theorem reference_coordinate3_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) (i : Fin 6) :
    dualFormValue6 (finiteMatrix 3 A3) (fun k => (sourceReference6 R q1 k : ℚ)) i =
      ∑ k, algebraMap ℚ ℚ_[3] (sourceReference6 R q1 k : ℚ) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k :=
  finite_coordinate6 3 A3 (sourceReference6 R q1) i

theorem reference_bound3_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) :
    ∀ i, ‖∑ k, algebraMap ℚ ℚ_[3] (sourceReference6 R q1 k : ℚ) *
      ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5,
        -(Nat.ceil (JSP000334.qThreshold 3 q1.val (pairWeights42 c3 (i.succAbove k))) : ℤ)) :=
  finite_bound_representation6 3 A3 (sourceReference6 R q1) q1.val c3 (source_reference_p3_bound6 R h2 h3 q1)

theorem rescaled_coordinate3_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) (i : Fin 6) :
    dualFormValue6 (finiteMatrix 3 A3) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i =
      ∑ k, algebraMap ℚ ℚ_[3] (rescaledReference6 R h2 h3 q1 q k : ℚ) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k :=
  finite_coordinate6 3 A3 (rescaledReference6 R h2 h3 q1 q) i

theorem rescaled_bound3_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) :
    ∀ i, ‖∑ k, algebraMap ℚ ℚ_[3] (rescaledReference6 R h2 h3 q1 q k : ℚ) *
      ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5,
        -(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ)) :=
  finite_bound_representation6 3 A3 (rescaledReference6 R h2 h3 q1 q) q.val c3 (rescaled_reference_p3_6 R h2 h3 hc2 hc3 q1 q)

end CompoundFeasibility.Reference163Bridges
#check CompoundFeasibility.Reference163Bridges.reference_coordinate3_6
#print axioms CompoundFeasibility.Reference163Bridges.reference_coordinate3_6
#check CompoundFeasibility.Reference163Bridges.reference_bound3_6
#print axioms CompoundFeasibility.Reference163Bridges.reference_bound3_6
#check CompoundFeasibility.Reference163Bridges.rescaled_coordinate3_6
#print axioms CompoundFeasibility.Reference163Bridges.rescaled_coordinate3_6
#check CompoundFeasibility.Reference163Bridges.rescaled_bound3_6
#print axioms CompoundFeasibility.Reference163Bridges.rescaled_bound3_6

#check CompoundFeasibility.Reference163Bridges.reference_coordinate2_6
#print CompoundFeasibility.Reference163Bridges.reference_coordinate2_6
#print axioms CompoundFeasibility.Reference163Bridges.reference_coordinate2_6

#check CompoundFeasibility.Reference163Bridges.reference_bound2_6
#print CompoundFeasibility.Reference163Bridges.reference_bound2_6
#print axioms CompoundFeasibility.Reference163Bridges.reference_bound2_6

#check CompoundFeasibility.Reference163Bridges.rescaled_coordinate2_6
#print CompoundFeasibility.Reference163Bridges.rescaled_coordinate2_6
#print axioms CompoundFeasibility.Reference163Bridges.rescaled_coordinate2_6

#check CompoundFeasibility.Reference163Bridges.rescaled_bound2_6
#print CompoundFeasibility.Reference163Bridges.rescaled_bound2_6
#print axioms CompoundFeasibility.Reference163Bridges.rescaled_bound2_6

#check CompoundFeasibility.Reference163Bridges.reference_coordinate3_6
#print CompoundFeasibility.Reference163Bridges.reference_coordinate3_6
#print axioms CompoundFeasibility.Reference163Bridges.reference_coordinate3_6

#check CompoundFeasibility.Reference163Bridges.reference_bound3_6
#print CompoundFeasibility.Reference163Bridges.reference_bound3_6
#print axioms CompoundFeasibility.Reference163Bridges.reference_bound3_6

#check CompoundFeasibility.Reference163Bridges.rescaled_coordinate3_6
#print CompoundFeasibility.Reference163Bridges.rescaled_coordinate3_6
#print axioms CompoundFeasibility.Reference163Bridges.rescaled_coordinate3_6

#check CompoundFeasibility.Reference163Bridges.rescaled_bound3_6
#print CompoundFeasibility.Reference163Bridges.rescaled_bound3_6
#print axioms CompoundFeasibility.Reference163Bridges.rescaled_bound3_6
