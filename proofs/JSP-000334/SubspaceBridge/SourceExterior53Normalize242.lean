import SubspaceBridge.SourceExterior53Lattice242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior53_242

def normalizedWeights3242 (c : Fin 5 → ℝ) : Fin 10 → ℝ := fun s => tripleWeights242 c s/3

theorem tripleWeights_sum242 (c : Fin 5 → ℝ) :
    (∑ s, tripleWeights242 c s) = 6*∑ i, c i := by
  simp [tripleWeights242,lo242,mid242,hi242,Fin.sum_univ_succ]
  ring

theorem powered_gt_one3242 (Q : ℝ) (hQ : 1 < Q) : 1 < Q^3 :=
  one_lt_pow₀ hQ (by decide)

theorem normalized_real_bound3242 (c : Fin 5 → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    ∀ s, |normalizedWeights3242 c s| ≤ 1 := by
  intro s
  change |(c (lo242 s)+c (mid242 s)+c (hi242 s))/3| ≤ 1
  rw [abs_div,abs_of_pos (show (0 : ℝ) < 3 by norm_num)]
  apply (div_le_iff₀ (show (0 : ℝ) < 3 by norm_num)).mpr
  have h := (abs_add (c (lo242 s)+c (mid242 s)) (c (hi242 s))).trans (add_le_add_right (abs_add _ _) _)
  linarith [hc (lo242 s),hc (mid242 s),hc (hi242 s)]

theorem normalized_finite_bounds3242 (c : Fin 5 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    ∀ s, -1 ≤ normalizedWeights3242 c s ∧ normalizedWeights3242 c s ≤ 0 := by
  intro s
  change -1 ≤ (c (lo242 s)+c (mid242 s)+c (hi242 s))/3 ∧ (c (lo242 s)+c (mid242 s)+c (hi242 s))/3 ≤ 0
  constructor <;> linarith [(hc (lo242 s)).1,(hc (lo242 s)).2,(hc (mid242 s)).1,(hc (mid242 s)).2,(hc (hi242 s)).1,(hc (hi242 s)).2]

theorem normalized_balance3242 (c0 c2 c3 : Fin 5 → ℝ)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∑ s, (normalizedWeights3242 c0 s+normalizedWeights3242 c2 s+normalizedWeights3242 c3 s)) = 0 := by
  calc
    _ = (∑ s, tripleWeights242 (fun i => c0 i+c2 i+c3 i) s)/3 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      dsimp [normalizedWeights3242,tripleWeights242]
      ring
    _ = 0 := by rw [tripleWeights_sum242,hb]; norm_num

theorem powered_rpow3242 (Q a b c : ℝ) (hQ : 1 < Q) :
    (Q^3)^((a+b+c)/3) = Q^(a+b+c) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans hQ).le]
  congr 1
  ring

theorem powered_threshold3242 (p : ℕ) (Q a b c : ℝ) :
    JSP000334.qThreshold p (Q^3) ((a+b+c)/3) = JSP000334.qThreshold p Q (a+b+c) := by
  unfold JSP000334.qThreshold
  rw [Real.log_pow]
  ring

theorem powered_group3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ) :
    originalSourceGroup10 (compound3242 A2) (compound3242 A3) (Q^3)
      (normalizedWeights3242 c2) (normalizedWeights3242 c3) = directGroup3242 A2 A3 Q c2 c3 := by
  unfold originalSourceGroup10 directGroup3242 normalizedWeights3242 tripleWeights242
  simp_rw [powered_threshold3242]

theorem powered_body3242 (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 5 → ℝ) (x : Fin 10 → ℝ) (r : ℝ) :
    coordinateGauge10 (originalCoordinates10 (compound3242 L) (compound_real_unit3242 L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0)) x ≤ r ↔
      ∀ s, |(compound3242 L *ᵥ x) s| ≤ r*Q^(tripleWeights242 c0 s) := by
  change ‖originalCoordinates10 (compound3242 L) (compound_real_unit3242 L hL)
    (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0) x‖ ≤ r ↔ _
  rw [originalCoordinates10_bounds]
  simp only [normalizedWeights3242,tripleWeights242,powered_rpow3242 Q _ _ _ hQ]

end CompoundFeasibility.Exterior53_242
