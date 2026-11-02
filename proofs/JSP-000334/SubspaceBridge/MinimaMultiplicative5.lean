import SubspaceBridge.MinimaPower5
open scoped BigOperators
noncomputable section
namespace CompoundFeasibility.MinimaPower5

def firstProductIndex5 (j : Fin 4) (a : Fin (j.val+1)) : Fin 5 := ⟨a.val,by omega⟩

def tailProductIndex5 (j : Fin 4) (b : Fin (4-j.val)) : Fin 5 := ⟨j.val+1+b.val,by omega⟩

theorem prefixProduct5_pos (j : Fin 4) (lam : Fin 5 → ℝ) (hp : ∀ i, 0 < lam i) :
    0 < prefixProduct5 j lam := Finset.prod_pos (fun _ _ => hp _)

theorem tailProduct5_pos (j : Fin 4) (lam : Fin 5 → ℝ) (hp : ∀ i, 0 < lam i) :
    0 < tailProduct5 j lam := Finset.prod_pos (fun _ _ => hp _)

theorem prefix_tail_product5 (j : Fin 4) (lam : Fin 5 → ℝ) :
    prefixProduct5 j lam * tailProduct5 j lam = ∏ i, lam i := by
  have hd : (j.val+1)+(4-j.val) = 5 := by omega
  let f : Fin ((j.val+1)+(4-j.val)) → ℝ := fun i => lam ⟨i.val,by omega⟩
  have h : (∏ i : Fin 5, lam i) = ∏ i, f i := by
    apply Fintype.prod_equiv (finCongr hd.symm)
    intro i
    rfl
  rw [Fin.prod_univ_add] at h
  exact h.symm

theorem prefix_tail_power5 (j : Fin 4) (lam : Fin 5 → ℝ) (Q delta : ℝ)
    (hQ : 0 < Q) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta)) :
    (prefixProduct5 j lam)^(4-j.val) ≤ (tailProduct5 j lam)^(j.val+1) *
      Q^(-delta*((j.val+1 : ℕ) : ℝ)*((4-j.val : ℕ) : ℝ)) := by
  let r := Q^(-delta)
  have hr : 0 < r := Real.rpow_pos_of_pos hQ _
  have hpair (a : Fin (j.val+1)) (b : Fin (4-j.val)) :
      lam (firstProductIndex5 j a) ≤ lam (tailProductIndex5 j b) * r := by
    exact ((hm (show (firstProductIndex5 j a : Fin 5) ≤ j.castSucc by change a.val ≤ j.val; omega)).trans_lt hg).le.trans
      (mul_le_mul_of_nonneg_right (hm (show j.succ ≤ (tailProductIndex5 j b : Fin 5) by change j.val+1 ≤ j.val+1+b.val; omega)) hr.le)
  have ha (a : Fin (j.val+1)) :
      (lam (firstProductIndex5 j a))^(4-j.val) ≤ tailProduct5 j lam * r^(4-j.val) := by
    calc
      _ = ∏ _b : Fin (4-j.val), lam (firstProductIndex5 j a) := by simp
      _ ≤ ∏ b : Fin (4-j.val), lam (tailProductIndex5 j b) * r :=
        Finset.prod_le_prod (fun _ _ => (hp _).le) (fun b _ => hpair a b)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp [tailProduct5,tailProductIndex5]
  have h := Finset.prod_le_prod (s := Finset.univ)
    (fun a _ => pow_nonneg (hp (firstProductIndex5 j a : Fin 5)).le (4-j.val)) (fun a _ => ha a)
  have he : (r^(4-j.val))^(j.val+1) = Q^(-delta*((j.val+1 : ℕ) : ℝ)*((4-j.val : ℕ) : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hQ.le,← Real.rpow_mul hQ.le]
    congr 1
    ring
  simpa only [← Finset.prod_pow,prefixProduct5,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,he,firstProductIndex5] using h

theorem prefix_fifth_power5 (j : Fin 4) (lam : Fin 5 → ℝ) (Q delta : ℝ)
    (hQ : 0 < Q) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta)) :
    (prefixProduct5 j lam)^5 ≤ (∏ i, lam i)^(j.val+1) *
      Q^(-delta*((j.val+1 : ℕ) : ℝ)*(5-((j.val+1 : ℕ) : ℝ))) := by
  have ht : ((4-j.val : ℕ) : ℝ) = 5-((j.val+1 : ℕ) : ℝ) := by
    have h : (j.val+1)+(4-j.val) = 5 := by omega
    have hr := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hr ⊢
    linarith
  have h := mul_le_mul_of_nonneg_left (prefix_tail_power5 j lam Q delta hQ hp hm hg)
    (pow_nonneg (prefixProduct5_pos j lam hp).le (j.val+1))
  have hn : (j.val+1)+(4-j.val) = 5 := by omega
  calc
    _ = (prefixProduct5 j lam)^(j.val+1) * (prefixProduct5 j lam)^(4-j.val) := by rw [← pow_add,hn]
    _ ≤ _ := h
    _ = _ := by rw [← mul_assoc,← mul_pow,prefix_tail_product5,ht]

theorem source_prefix_product_decay5 (j : Fin 4) (lam : Fin 5 → ℝ)
    (Q delta C5 : ℝ) (hQ : 0 < Q) (hC : 0 < C5)
    (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta)) (hprod : ∏ i, lam i ≤ C5) :
    prefixProduct5 j lam ≤ C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta) := by
  have h := (prefix_fifth_power5 j lam Q delta hQ hp hm hg).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.prod_pos (fun i _ => hp i)).le hprod _)
      (Real.rpow_pos_of_pos hQ _).le)
  have he : (C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta))^5 =
      C5^(j.val+1) * Q^(-delta*((j.val+1 : ℕ) : ℝ)*(5-((j.val+1 : ℕ) : ℝ))) := by
    rw [mul_pow,← Real.rpow_natCast,← Real.rpow_mul hC.le,
      ← Real.rpow_natCast,← Real.rpow_mul hQ.le]
    have hc : (((j.val+1 : ℕ) : ℝ)/5)*5 = ((j.val+1 : ℕ) : ℝ) := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hc,Real.rpow_natCast]
    congr 1
    congr 1
    unfold decayExponent5
    push_cast
    ring
  exact le_of_pow_le_pow_left₀ (by decide : 5 ≠ 0) (by positivity) (he.symm ▸ h)

theorem source_gap_geometric_mean5 (j : Fin 4) (lam : Fin 5 → ℝ)
    (Q delta : ℝ) (hQ : 0 < Q) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta)) :
    ∀ i : Fin 5, i.val < j.val+1 → lam i <
      (tailProduct5 j lam)^(1/(5-((j.val+1 : ℕ) : ℝ))) * Q^(-delta) := by
  have hn : 0 < 4-j.val := by omega
  have hnR : (0 : ℝ) < ((4-j.val : ℕ) : ℝ) := by exact_mod_cast hn
  have he : ((4-j.val : ℕ) : ℝ) = 5-((j.val+1 : ℕ) : ℝ) := by
    have h : (j.val+1)+(4-j.val) = 5 := by omega
    have hr := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hr ⊢
    linarith
  have ht : (lam j.succ)^(4-j.val) ≤ tailProduct5 j lam := by
    calc
      _ = ∏ _b : Fin (4-j.val), lam j.succ := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => (hp _).le) (fun b _ => hm
        (show j.succ ≤ (tailProductIndex5 j b : Fin 5) by change j.val+1 ≤ j.val+1+b.val; omega))
  have hr := Real.rpow_le_rpow (pow_nonneg (hp _).le _) ht (by positivity : (0 : ℝ) ≤ 1/((4-j.val : ℕ) : ℝ))
  rw [← Real.rpow_natCast,← Real.rpow_mul (hp _).le] at hr
  have hc : ((4-j.val : ℕ) : ℝ) * (1/((4-j.val : ℕ) : ℝ)) = 1 := by exact mul_one_div_cancel hnR.ne'
  rw [hc,Real.rpow_one,he] at hr
  intro i hi
  exact ((hm (show i ≤ j.castSucc by change i.val ≤ j.val; omega)).trans_lt hg).trans_le
    (mul_le_mul_of_nonneg_right hr (Real.rpow_pos_of_pos hQ _).le)

end CompoundFeasibility.MinimaPower5
