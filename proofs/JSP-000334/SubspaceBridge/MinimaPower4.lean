import SubspaceBridge.OriginalMinima4
open scoped BigOperators
namespace CompoundFeasibility.MinimaPower4
noncomputable section

def prefixProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) : ℝ :=
  ∏ i : Fin (j.val+1), lam ⟨i.val, by omega⟩

def tailProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) : ℝ :=
  ∏ i : Fin (3-j.val), lam ⟨j.val+1+i.val, by omega⟩

def decayExponent4 (j : Fin 3) (delta : ℝ) : ℝ :=
  delta * (j.val+1) * (4-(j.val+1)) / 4

theorem selectedDimension4_cases (j : Fin 3) :
    j.val+1 = 1 ∨ j.val+1 = 2 ∨ j.val+1 = 3 := by
  omega

theorem decayExponent4_pos (j : Fin 3) (delta : ℝ) (hd : 0 < delta) :
    0 < decayExponent4 j delta := by
  unfold decayExponent4
  have hj : (j.val : ℝ) < 3 := by exact_mod_cast j.isLt
  have hx : 0 < 4 - ((j.val : ℝ)+1) := by linarith
  exact div_pos (mul_pos (mul_pos hd (by positivity)) hx) (by norm_num)

theorem log_gap_average4 (j : Fin 3) (a : Fin 4 → ℝ) (t : ℝ)
    (hm : Monotone a) (hg : a j.castSucc < a j.succ-t) :
    a j.castSucc < (∑ i : Fin (3-j.val), a ⟨j.val+1+i.val, by omega⟩) /
      (4-((j.val+1 : ℕ) : ℝ)) - t := by
  have h01 := hm (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := hm (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := hm (show (2 : Fin 4) ≤ 3 by decide)
  fin_cases j <;> norm_num at * <;> simp [Fin.sum_univ_succ, Fin.succ_mk] at * <;> norm_num at * <;> linarith

theorem log_prefix_decay4 (j : Fin 3) (a : Fin 4 → ℝ) (t z : ℝ)
    (hm : Monotone a) (hg : a j.castSucc < a j.succ-t)
    (hprod : ∑ i, a i ≤ z) :
    (∑ i : Fin (j.val+1), a ⟨i.val, by omega⟩) ≤
      ((j.val+1 : ℕ) : ℝ)/4*z - t*((j.val+1 : ℕ) : ℝ)*(4-((j.val+1 : ℕ) : ℝ))/4 := by
  have h01 := hm (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := hm (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := hm (show (2 : Fin 4) ≤ 3 by decide)
  fin_cases j <;> norm_num at * <;> simp [Fin.sum_univ_succ, Fin.succ_mk] at * <;> norm_num at * <;> linarith

theorem prefixProduct4_pos (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    0 < prefixProduct4 j lam := by
  exact Finset.prod_pos (fun _ _ => hp _)

theorem tailProduct4_pos (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    0 < tailProduct4 j lam := by
  exact Finset.prod_pos (fun _ _ => hp _)

theorem log_prefixProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    Real.log (prefixProduct4 j lam) =
      ∑ i : Fin (j.val+1), Real.log (lam ⟨i.val, by omega⟩) := by
  exact Real.log_prod _ _ (fun _ _ => ne_of_gt (hp _))

theorem log_tailProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    Real.log (tailProduct4 j lam) =
      ∑ i : Fin (3-j.val), Real.log (lam ⟨j.val+1+i.val, by omega⟩) := by
  exact Real.log_prod _ _ (fun _ _ => ne_of_gt (hp _))

theorem source_gap_geometric_mean4 (j : Fin 3) (lam : Fin 4 → ℝ)
    (Q delta : ℝ) (hQ : 0 < Q) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta)) :
    ∀ i : Fin 4, i.val < j.val+1 →
      lam i < (tailProduct4 j lam)^(1/(4-((j.val+1 : ℕ) : ℝ))) * Q^(-delta) := by
  have hlogmono : Monotone (fun i => Real.log (lam i)) :=
    fun i k hik => Real.log_le_log (hp i) (hm hik)
  have hgap := Real.log_lt_log (hp j.castSucc) hg
  rw [Real.log_mul (ne_of_gt (hp _)) (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow hQ] at hgap
  have havg := log_gap_average4 j (fun i => Real.log (lam i))
    (delta * Real.log Q) hlogmono (by linarith)
  intro i hi
  apply (Real.log_lt_log_iff (hp i)
    (mul_pos (Real.rpow_pos_of_pos (tailProduct4_pos j lam hp) _)
      (Real.rpow_pos_of_pos hQ _))).mp
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (tailProduct4_pos j lam hp) _))
    (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow (tailProduct4_pos j lam hp), Real.log_rpow hQ,
    log_tailProduct4 j lam hp]
  have hle := hlogmono (show i ≤ j.castSucc from Fin.le_iff_val_le_val.mpr (by simpa using Nat.le_of_lt_succ hi))
  convert lt_of_le_of_lt hle havg using 1 <;> ring

theorem source_prefix_product_decay4 (j : Fin 3) (lam : Fin 4 → ℝ)
    (Q delta C4 : ℝ) (hQ : 0 < Q) (hC4 : 0 < C4)
    (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta))
    (hprod : ∏ i, lam i ≤ C4) :
    prefixProduct4 j lam ≤ C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta) := by
  have hlogmono : Monotone (fun i => Real.log (lam i)) :=
    fun i k hik => Real.log_le_log (hp i) (hm hik)
  have hgap := Real.log_lt_log (hp j.castSucc) hg
  rw [Real.log_mul (ne_of_gt (hp _)) (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow hQ] at hgap
  have hall := Real.log_le_log (Finset.prod_pos (fun i _ => hp i)) hprod
  rw [Real.log_prod _ _ (fun i _ => ne_of_gt (hp i))] at hall
  have hdec := log_prefix_decay4 j (fun i => Real.log (lam i)) (delta*Real.log Q)
    (Real.log C4) hlogmono (by linarith) hall
  apply (Real.log_le_log_iff (prefixProduct4_pos j lam hp)
    (mul_pos (Real.rpow_pos_of_pos hC4 _) (Real.rpow_pos_of_pos hQ _))).mp
  rw [log_prefixProduct4 j lam hp,
    Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hC4 _)) (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow hC4, Real.log_rpow hQ]
  convert hdec using 1 <;> push_cast <;> unfold decayExponent4 <;> ring

end
end CompoundFeasibility.MinimaPower4
