import SubspaceBridge.SourceCompoundGap53_242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag244
open Exterior53_242

theorem unique_triple_top244 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i)
    (hm : Monotone a) (h12 : a 1 < a 2) (s : Fin 10) (hs : s ≠ 9) :
    a (lo242 s)*a (mid242 s)*a (hi242 s) < a 2*a 3*a 4 := by
  have bounds : ∀ s : Fin 10, s ≠ 9 → lo242 s ≤ (1 : Fin 5) ∧ mid242 s ≤ (3 : Fin 5) ∧ hi242 s ≤ (4 : Fin 5) := by decide
  exact (mul_le_mul (mul_le_mul (hm (bounds s hs).1) (hm (bounds s hs).2.1) (ha _).le (ha _).le)
    (hm (bounds s hs).2.2) (ha _).le (mul_pos (ha _) (ha _)).le).trans_lt
    (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h12 (ha 3)) (ha 4))

theorem tripleOrder_last244 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i)
    (hm : Monotone a) (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (hg : a 1 < a 2*Q^(-delta)) : tripleOrder242 a 9 = 9 := by
  have h12 : a 1 < a 2 := hg.trans_le (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hQ.le (by linarith : -delta ≤ 0)) (ha 2).le)
  by_contra h
  have hs := unique_triple_top244 a ha hm h12 _ h
  have he := (tripleProducts_top242 a ha hm).2
  exact (ne_of_lt hs) he

theorem tripleOrder_first_nine244 (a : Fin 5 → ℝ) (hlast : tripleOrder242 a 9 = 9)
    (s : Fin 10) : (∃ j : Fin 9, tripleOrder242 a j.castSucc = s) ↔ s ≠ 9 := by
  constructor
  · rintro ⟨j,rfl⟩ he
    have hj := (tripleOrder242 a).injective (he.trans hlast.symm)
    have hv : j.val = 9 := congrArg Fin.val hj
    have := j.isLt
    omega
  · intro hs
    let k := (tripleOrder242 a).symm s
    have hk : k ≠ 9 := by
      intro h
      have hh := (tripleOrder242 a).apply_symm_apply s
      change tripleOrder242 a k = s at hh
      rw [h,hlast] at hh
      exact hs hh.symm
    have hlt : k.val < 9 := by
      have := k.isLt
      have hn : k.val ≠ 9 := fun h => hk (Fin.ext h)
      omega
    refine ⟨⟨k.val,hlt⟩,?_⟩
    change tripleOrder242 a k = s
    exact (tripleOrder242 a).apply_symm_apply s

end CompoundFeasibility.SourceFlag244
