import SubspaceBridge.OriginalMinima4
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

def sortedPairProducts42 (a : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![a 0 * a 1, a 0 * a 2, min (a 0 * a 3) (a 1 * a 2),
    max (a 0 * a 3) (a 1 * a 2), a 1 * a 3, a 2 * a 3]

def pairProductOrder42 (a : Fin 4 → ℝ) : Equiv.Perm (Fin 6) :=
  if a 0 * a 3 ≤ a 1 * a 2 then Equiv.refl _ else Equiv.swap 2 3

theorem sortedPairProducts42_of_middle_le (a : Fin 4 → ℝ)
    (h : a 0 * a 3 ≤ a 1 * a 2) :
    sortedPairProducts42 a = ![a 0 * a 1, a 0 * a 2, a 0 * a 3,
      a 1 * a 2, a 1 * a 3, a 2 * a 3] := by
  simp only [sortedPairProducts42, min_eq_left h, max_eq_right h]

theorem sortedPairProducts42_of_middle_ge (a : Fin 4 → ℝ)
    (h : a 1 * a 2 ≤ a 0 * a 3) :
    sortedPairProducts42 a = ![a 0 * a 1, a 0 * a 2, a 1 * a 2,
      a 0 * a 3, a 1 * a 3, a 2 * a 3] := by
  simp only [sortedPairProducts42, min_eq_right h, max_eq_left h]

theorem sortedPairProducts42_reindex (a : Fin 4 → ℝ) (j : Fin 6) :
    sortedPairProducts42 a j =
      a (lo (pairProductOrder42 a j)) * a (hi (pairProductOrder42 a j)) := by
  by_cases h : a 0 * a 3 ≤ a 1 * a 2
  · rw [sortedPairProducts42_of_middle_le a h]
    fin_cases j <;> simp [pairProductOrder42, h, lo, hi]
  · rw [sortedPairProducts42_of_middle_ge a (le_of_lt (lt_of_not_ge h))]
    fin_cases j <;> simp [pairProductOrder42, h, lo, hi, Equiv.swap_apply_def]

theorem sortedPairProducts42_pos (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ j, 0 < sortedPairProducts42 a j := by
  intro j
  fin_cases j
  · exact mul_pos (ha 0) (ha 1)
  · exact mul_pos (ha 0) (ha 2)
  · exact lt_min (mul_pos (ha 0) (ha 3)) (mul_pos (ha 1) (ha 2))
  · exact (mul_pos (ha 0) (ha 3)).trans_le (le_max_left _ _)
  · exact mul_pos (ha 1) (ha 3)
  · exact mul_pos (ha 2) (ha 3)

theorem sortedPairProducts42_monotone (a : Fin 4 → ℝ)
    (ha : ∀ i, 0 < a i) (hm : Monotone a) : Monotone (sortedPairProducts42 a) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  fin_cases j
  · exact mul_le_mul_of_nonneg_left (hm (show (1 : Fin 4) ≤ 2 by decide)) (ha 0).le
  · exact le_min
      (mul_le_mul_of_nonneg_left (hm (show (2 : Fin 4) ≤ 3 by decide)) (ha 0).le)
      (mul_le_mul_of_nonneg_right (hm (show (0 : Fin 4) ≤ 1 by decide)) (ha 2).le)
  · exact min_le_max
  · exact max_le
      (mul_le_mul_of_nonneg_right (hm (show (0 : Fin 4) ≤ 1 by decide)) (ha 3).le)
      (mul_le_mul_of_nonneg_left (hm (show (2 : Fin 4) ≤ 3 by decide)) (ha 1).le)
  · exact mul_le_mul_of_nonneg_right (hm (show (1 : Fin 4) ≤ 2 by decide)) (ha 3).le

theorem sortedPairProducts42_product (a : Fin 4 → ℝ) :
    (∏ j : Fin 6, sortedPairProducts42 a j) = (∏ i : Fin 4, a i) ^ 3 := by
  calc
    _ = ∏ j : Fin 6, a (lo (pairProductOrder42 a j)) * a (hi (pairProductOrder42 a j)) :=
      Finset.prod_congr rfl (fun j _ => sortedPairProducts42_reindex a j)
    _ = ∏ s : Fin 6, a (lo s) * a (hi s) :=
      Equiv.prod_comp (pairProductOrder42 a) (fun s => a (lo s) * a (hi s))
    _ = _ := compound_width_product a

def sourcePairProducts42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) : Fin 6 → ℝ :=
  sortedPairProducts42 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃)

theorem sourcePairProducts42_pos_mono (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∀ j, 0 < sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨sortedPairProducts42_pos _ hp, sortedPairProducts42_monotone _ hp hm⟩

theorem sourcePairProducts42_reindex (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
        (lo (pairProductOrder42 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) j)) *
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
        (hi (pairProductOrder42 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) j)) :=
  sortedPairProducts42_reindex _ j

theorem sourcePairProducts42_product (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∏ j : Fin 6, sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) =
      (∏ i : Fin 4, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ^ 3 :=
  sortedPairProducts42_product _

theorem source_pair_products42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∀ j, 0 < sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∃ σ : Equiv.Perm (Fin 6), ∀ j,
        sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j =
          sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (lo (σ j)) *
          sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (hi (σ j))) ∧
      (∏ j : Fin 6, sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) =
        (∏ i : Fin 4, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ^ 3 := by
  obtain ⟨hp,hm⟩ := sourcePairProducts42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨hp,hm,⟨pairProductOrder42 _,sourcePairProducts42_reindex A₂ A₃ L hL Q hQ c₀ c₂ c₃⟩,
    sourcePairProducts42_product A₂ A₃ L hL Q hQ c₀ c₂ c₃⟩

end
end CompoundFeasibility
