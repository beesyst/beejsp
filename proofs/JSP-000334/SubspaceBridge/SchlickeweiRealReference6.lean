import SubspaceBridge.SchlickeweiReferenceRescaling6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiRealReference6

theorem floor_power_bound6 (p Q u : ℝ) (hp : 1 < p) (hQ : 1 < Q) :
    p ^ (-⌊Real.log Q / Real.log p * u⌋ : ℤ) ≤ p * Q ^ (-u) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hf := Int.lt_floor_add_one (Real.log Q / Real.log p * u)
  have hex : ((-⌊Real.log Q / Real.log p * u⌋ : ℤ) : ℝ) ≤
      1 - Real.log Q / Real.log p * u := by
    push_cast
    linarith
  calc
    _ = p ^ (((-⌊Real.log Q / Real.log p * u⌋ : ℤ) : ℝ)) := (Real.rpow_intCast _ _).symm
    _ ≤ p ^ (1 - Real.log Q / Real.log p * u) := Real.rpow_le_rpow_of_exponent_le hp.le hex
    _ = p * Q ^ (-u) := by
      rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hQ0]
      have he : Real.log p * (1 - Real.log Q / Real.log p * u) =
          Real.log p + Real.log Q * (-u) := by
        field_simp [ne_of_gt (Real.log_pos hp)]
        ring
      rw [he, Real.exp_add, Real.exp_log hp0]

theorem floor_growth6 (Q u v : ℝ) (hQ : 1 < Q) :
    (6 : ℝ) ^ (5 : ℕ) * (2 : ℝ) ^ (-⌊Real.log Q / Real.log 2 * u⌋ : ℤ) *
      (3 : ℝ) ^ (-⌊Real.log Q / Real.log 3 * v⌋ : ℤ) ≤
      (6 : ℝ) ^ (6 : ℕ) * Q ^ (-u-v) := by
  have h2 := floor_power_bound6 2 Q u (by norm_num) hQ
  have h3 := floor_power_bound6 3 Q v (by norm_num) hQ
  calc
    _ ≤ (6 : ℝ) ^ (5 : ℕ) * (2 * Q ^ (-u)) * (3 * Q ^ (-v)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h3 (by positivity) (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add (zero_lt_one.trans hQ)]
      ring


open Auxiliary6.SourceExpansion SourceReadiness6 SourceMixed6 SchlickeweiReference6 SchlickeweiDualVanishing6
open SchlickeweiSatz51Selected6 SchlickeweiEquation4106 SchlickeweiIntegerPairing6

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem real_scalar_norm6 (g2 g3 : ℤ) :
    ‖algebraMap ℚ ℝ ((6 : ℚ) ^ (5 : ℕ) * 2 ^ (-g2) * 3 ^ (-g3))‖ =
      (6 : ℝ) ^ (5 : ℕ) * (2 : ℝ) ^ (-g2) * (3 : ℝ) ^ (-g3) := by
  simp only [map_mul, map_pow, map_ofNat, map_zpow₀, norm_mul, norm_pow, norm_zpow]
  norm_num

theorem source_floor_attained6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 q : V) :
    (∃ j2 ∈ finiteSupport6 2 (finiteMatrix 2 A2) (sourceReference6 R q1),
      sourceFloor2 R h2 h3 q1 q = publishedFloor6 2 (q.val ^ (11 : ℕ)) (R.c 1) j2) ∧
    (∃ j3 ∈ finiteSupport6 3 (finiteMatrix 3 A3) (sourceReference6 R q1),
      sourceFloor3 R h2 h3 q1 q = publishedFloor6 3 (q.val ^ (11 : ℕ)) (R.c 2) j3) :=
  ⟨(support_floor_spec6 _ _ _ _ _).1, (support_floor_spec6 _ _ _ _ _).1⟩

theorem rescaled_reference_real_growth6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (q1 q : V) (i j2 j3 : Fin 6)
    (hmin2 : sourceFloor2 R h2 h3 q1 q = publishedFloor6 2 (q.val ^ (11 : ℕ)) (R.c 1) j2)
    (hmin3 : sourceFloor3 R h2 h3 q1 q = publishedFloor6 3 (q.val ^ (11 : ℕ)) (R.c 2) j3) :
    ‖dualFormValue6 (compound L) (fun k => (rescaledReference6 R h2 h3 q1 q k : ℚ)) i‖ ≤
      ((6 : ℝ) ^ (6 : ℕ) * (q.val ^ (11 : ℕ)) ^
        (-(∑ k : Fin 5, R.c 1 (j2.succAbove k)) - (∑ k : Fin 5, R.c 2 (j3.succAbove k)))) *
        ‖dualFormValue6 (compound L) (fun k => (sourceReference6 R q1 k : ℚ)) i‖ := by
  rw [rescaled_reference_published6 R h2 h3 hc2 hc3 q1 q, dual_scalar_value6, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [real_scalar_norm6, hmin2, hmin3]
  exact floor_growth6 _ _ _ (source_parameter_gt_one6 R q)

end CompoundFeasibility.SchlickeweiRealReference6
