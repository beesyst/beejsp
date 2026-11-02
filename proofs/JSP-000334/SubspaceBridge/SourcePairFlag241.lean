import SubspaceBridge.SourceCompoundGap52_239
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open Exterior52_237 Exterior52_238 ExteriorGap52_239

theorem unique_pair_top241 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i)
    (hm : Monotone a) (h23 : a 2 < a 3) (s : Fin 10) (hs : s ≠ 9) :
    a (lo237 s)*a (hi237 s) < a 3*a 4 := by
  have bounds : ∀ s : Fin 10, s ≠ 9 → lo237 s ≤ (2 : Fin 5) ∧ hi237 s ≤ (4 : Fin 5) := by decide
  exact (mul_le_mul (hm (bounds s hs).1) (hm (bounds s hs).2) (ha _).le (ha _).le).trans_lt
    (mul_lt_mul_of_pos_right h23 (ha 4))

theorem pairOrder_last241 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i)
    (hm : Monotone a) (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (hg : a 2 < a 3*Q^(-delta)) : pairOrder239 a 9 = 9 := by
  have h23 : a 2 < a 3 := hg.trans_le (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hQ.le (by linarith : -delta ≤ 0)) (ha 3).le)
  by_contra h
  have hs := unique_pair_top241 a ha hm h23 _ h
  have he := (pairProducts_top239 a ha hm).2
  exact (ne_of_lt hs) he

theorem pairOrder_first_nine241 (a : Fin 5 → ℝ) (hlast : pairOrder239 a 9 = 9)
    (s : Fin 10) : (∃ j : Fin 9, pairOrder239 a j.castSucc = s) ↔ s ≠ 9 := by
  constructor
  · rintro ⟨j,rfl⟩ he
    have hj := (pairOrder239 a).injective (he.trans hlast.symm)
    have hv : j.val = 9 := congrArg Fin.val hj
    have := j.isLt
    omega
  · intro hs
    let k := (pairOrder239 a).symm s
    have hk : k ≠ 9 := by
      intro h
      have hh := (pairOrder239 a).apply_symm_apply s
      change pairOrder239 a k = s at hh
      rw [h,hlast] at hh
      exact hs hh.symm
    have hlt : k.val < 9 := by
      have := k.isLt
      have hn : k.val ≠ 9 := fun h => hk (Fin.ext h)
      omega
    refine ⟨⟨k.val,hlt⟩,?_⟩
    change pairOrder239 a k = s
    exact (pairOrder239 a).apply_symm_apply s

end CompoundFeasibility.SourceFlag241
