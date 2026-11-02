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

theorem support_member6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (b : Fin 6 → ℤ) (i : Fin 6) :
    i ∈ finiteSupport6 p B b ↔
      (∑ k, algebraMap ℚ ℚ_[p] (b k : ℚ) * B⁻¹.transpose i k) ≠ 0 := by
  simp only [finiteSupport6, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [integer_coordinate6 p B b i]

theorem support_set6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (b : Fin 6 → ℤ) :
    finiteSupport6 p B b = Finset.univ.filter (fun i =>
      (∑ k, algebraMap ℚ ℚ_[p] (b k : ℚ) * B⁻¹.transpose i k) ≠ 0) := by
  apply Finset.ext
  intro i
  rw [support_member6 p B b i]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem finite_support_set6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (b : Fin 6 → ℤ) :
    finiteSupport6 p (finiteMatrix p A) b = Finset.univ.filter (fun i =>
      (∑ k, algebraMap ℚ ℚ_[p] (b k : ℚ) *
        ((compound A).map (algebraMap ℚ ℚ_[p]))⁻¹.transpose i k) ≠ 0) := by
  have h := support_set6 p (finiteMatrix p A) b
  rw [finite_matrix6 p A] at h
  exact h

theorem support_representation6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (b : Fin 6 → ℤ)
    (h : (finiteSupport6 p (finiteMatrix p A) b).Nonempty) :
    (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[p] (b k : ℚ) *
      ((compound A).map (algebraMap ℚ ℚ_[p]))⁻¹.transpose i k) ≠ 0)).Nonempty :=
  (congrArg Finset.Nonempty (finite_support_set6 p A b)).mp h

theorem real_coordinate6 (B : Matrix (Fin 6) (Fin 6) ℝ) (b : Fin 6 → ℤ) (i : Fin 6) :
    dualFormValue6 B (fun k => (b k : ℚ)) i =
      ∑ k : Fin 6, algebraMap ℚ ℝ (b k : ℚ) * B⁻¹.transpose i k := by
  rw [SchlickeweiRealPairing6.real_dual_coordinates6 B b i]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_intCast]
  exact mul_comm _ _

theorem real_bound_representation6 (B : Matrix (Fin 6) (Fin 6) ℝ)
    (b : Fin 6 → ℤ) (d Q : ℝ) (c : Fin 6 → ℝ)
    (h : ∀ i, ‖dualFormValue6 B (fun k => (b k : ℚ)) i‖ ≤ d / Q ^ (c i)) :
    ∀ i, ‖∑ k, algebraMap ℚ ℝ (b k : ℚ) * B⁻¹.transpose i k‖ ≤ d / Q ^ (c i) := by
  intro i
  exact (congrArg (fun z : ℝ => ‖z‖) (real_coordinate6 B b i)).symm.trans_le (h i)

theorem product_representation6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 6 → ℤ) (s : SourceMixed6.MixedIndex6) :
    SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L (fun k => (b k : ℚ)) s =
      ‖∑ k, algebraMap ℚ ℝ (b k : ℚ) * (compound L)⁻¹.transpose (s 0) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[2] (b k : ℚ) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose (s 1) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[3] (b k : ℚ) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose (s 2) k‖ := by
  have hr := congrArg (fun z : ℝ => ‖z‖) (real_coordinate6 (compound L) b (s 0))
  have h2 := congrArg (fun z : ℚ_[2] => ‖z‖) (finite_coordinate6 2 A2 b (s 1))
  have h3 := congrArg (fun z : ℚ_[3] => ‖z‖) (finite_coordinate6 3 A3 b (s 2))
  exact congrArg₂ (fun x y : ℝ => x * y) (congrArg₂ (fun x y : ℝ => x * y) hr h2) h3

theorem product_zero_representation6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 6 → ℤ) (S : Finset SourceMixed6.MixedIndex6)
    (h : ∀ s ∈ S, SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L (fun k => (b k : ℚ)) s = 0) :
    ∀ s ∈ S,
      ‖∑ k, algebraMap ℚ ℝ (b k : ℚ) * (compound L)⁻¹.transpose (s 0) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[2] (b k : ℚ) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose (s 1) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[3] (b k : ℚ) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose (s 2) k‖ = 0 := by
  intro s hs
  exact (product_representation6 A2 A3 L b s).symm.trans (h s hs)

theorem published_floor6 (p : ℕ) (Q : ℝ) (c : Fin 6 → ℝ) (i : Fin 6) :
    publishedFloor6 p Q c i =
      ⌊Real.log Q / Real.log (p : ℝ) * (∑ k : Fin 5, c (i.succAbove k))⌋ := by
  rfl

theorem inf_transport6 (T U : Finset (Fin 6)) (hT : T.Nonempty) (hU : U.Nonempty)
    (hTU : T = U) (f g : Fin 6 → ℤ) (hfg : ∀ i, f i = g i) :
    T.inf' hT f = U.inf' hU g := by
  subst U
  have he : f = g := funext hfg
  subst g
  rfl

theorem floor_representation6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (b : Fin 6 → ℤ) (Q : ℝ) (c : Fin 6 → ℝ)
    (hT : (finiteSupport6 p (finiteMatrix p A) b).Nonempty)
    (hU : (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[p] (b k : ℚ) *
      ((compound A).map (algebraMap ℚ ℚ_[p]))⁻¹.transpose i k) ≠ 0)).Nonempty) :
    supportFloor6 p Q c (finiteSupport6 p (finiteMatrix p A) b) hT =
      (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[p] (b k : ℚ) *
        ((compound A).map (algebraMap ℚ ℚ_[p]))⁻¹.transpose i k) ≠ 0)).inf' hU
        (fun i => ⌊Real.log Q / Real.log (p : ℝ) * (∑ k : Fin 5, c (i.succAbove k))⌋) :=
  inf_transport6 _ _ hT hU (finite_support_set6 p A b) _ _ (published_floor6 p Q c)

theorem integer_rescale_representation6 (g2 g3 : ℤ) (b : Fin 6 → ℤ) :
    integerRescale6 g2 g3 b =
      ((6 : ℤ) ^ (5 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat) • b := by
  rfl

open SourceReadiness6
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_floor2_representation6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V)
    (hU : (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[2] (sourceReference6 R q1 k : ℚ) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)).Nonempty) :
    sourceFloor2 R h2 h3 q1 q =
      (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[2] (sourceReference6 R q1 k : ℚ) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)).inf' hU
        (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (2 : ℝ) *
          (∑ k : Fin 5, R.c 1 (i.succAbove k))⌋) :=
  floor_representation6 2 A2 (sourceReference6 R q1) (q.val ^ (11 : ℕ)) (R.c 1)
    (source_reference_supports6 R h2 h3 q1).1 hU

theorem source_floor3_representation6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V)
    (hU : (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[3] (sourceReference6 R q1 k : ℚ) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)).Nonempty) :
    sourceFloor3 R h2 h3 q1 q =
      (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[3] (sourceReference6 R q1 k : ℚ) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)).inf' hU
        (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (3 : ℝ) *
          (∑ k : Fin 5, R.c 2 (i.succAbove k))⌋) :=
  floor_representation6 3 A3 (sourceReference6 R q1) (q.val ^ (11 : ℕ)) (R.c 2)
    (source_reference_supports6 R h2 h3 q1).2 hU

theorem source_rescale_representation6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V)
    (hU2 : (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[2] (sourceReference6 R q1 k : ℚ) *
      ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)).Nonempty)
    (hU3 : (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[3] (sourceReference6 R q1 k : ℚ) *
      ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)).Nonempty) :
    let g2 : ℤ := (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[2] (sourceReference6 R q1 k : ℚ) *
      ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)).inf' hU2
        (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (2 : ℝ) *
          (∑ k : Fin 5, R.c 1 (i.succAbove k))⌋)
    let g3 : ℤ := (Finset.univ.filter (fun i => (∑ k, algebraMap ℚ ℚ_[3] (sourceReference6 R q1 k : ℚ) *
      ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)).inf' hU3
        (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (3 : ℝ) *
          (∑ k : Fin 5, R.c 2 (i.succAbove k))⌋)
    rescaledReference6 R h2 h3 q1 q =
      ((6 : ℤ) ^ (5 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat) • sourceReference6 R q1 := by
  have he2 := source_floor2_representation6 R h2 h3 q1 q hU2
  have he3 := source_floor3_representation6 R h2 h3 q1 q hU3
  have hv := congrArg₂ (fun g2 g3 : ℤ => integerRescale6 g2 g3 (sourceReference6 R q1)) he2 he3
  exact hv.trans (integer_rescale_representation6 _ _ (sourceReference6 R q1))

end CompoundFeasibility.Reference163Bridges
