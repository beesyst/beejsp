import SubspaceBridge.WeightedFourTermSource3
namespace JSP000334
open scoped BigOperators Matrix
noncomputable section

def weightedBalancedValues3 (H K : ℝ) (a : Fin 3 → Fin 3 → ℝ) (tau i : Fin 3) : ℝ :=
  if tau=0 then a tau i*(H/K)^((1 : ℝ)/3) else a tau i

theorem weighted_balanced_weights3 (H K C : ℝ) (hH : 3≤H) (hK : 0<K)
    (hC : C≤H) (hKi : K⁻¹≤H) (hK4 : K^4≤H)
    (a : Fin 3 → Fin 3 → ℝ) (ha : ∀ tau i,0<a tau i)
    (hreal : ∀ i,a 0 i≤C*H)
    (hfinite : ∀ tau,tau≠0 → ∀ i,a tau i≤1)
    (hinv : ∀ tau i,(a tau i)⁻¹≤C*H)
    (hprod : (∏ tau,∏ i,a tau i)*H=K) :
    let Q := H^4
    let W := weightedBalancedValues3 H K a
    1<Q ∧ sourceWeightConditions3 (sourceLogWeights3 Q W) ∧
      (∀ tau i,Q^(sourceLogWeights3 Q W tau i)=W tau i) ∧
      (∀ i,a 0 i≤Q^(sourceLogWeights3 Q W 0 i-(1 : ℝ)/16)) ∧
      (∀ tau,tau≠0 → ∀ i,a tau i=Q^(sourceLogWeights3 Q W tau i)) := by
  intro Q W
  have hH0 : 0<H := by linarith
  have hH1 : 1≤H := by linarith
  have hQ : 1<Q := by dsimp [Q]; nlinarith [sq_nonneg (H^2-1)]
  have hQ0 := zero_lt_one.trans hQ
  let r := (H/K)^((1 : ℝ)/3)
  let q := H^((1 : ℝ)/4)
  have hr : 0<r := Real.rpow_pos_of_pos (div_pos hH0 hK) _
  have hq : 0<q := Real.rpow_pos_of_pos hH0 _
  have hrpow : r^3=H/K := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (div_pos hH0 hK).le]
    norm_num
  have hqpow : q^4=H := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hH0.le]
    norm_num
  have hq1 : 1≤q := Real.one_le_rpow hH1 (by norm_num)
  have hKq : K≤q := le_of_pow_le_pow_left (by decide : (4 : ℕ)≠0) hq.le (by rw [hqpow];exact hK4)
  have hqr : q≤r := by
    apply le_of_pow_le_pow_left (by decide : (3 : ℕ)≠0) hr.le
    rw [hrpow]
    apply (le_div_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left hKq (pow_nonneg hq.le 3)
    nlinarith [hqpow]
  have hr1 : 1≤r := hq1.trans hqr
  have hrH : r≤H := by
    apply le_of_pow_le_pow_left (by decide : (3 : ℕ)≠0) hH0.le
    rw [hrpow]
    have hh : H/K≤H^2 := by
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left hKi hH0.le]
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hH1 (sq_nonneg H)])
  have hQq : Q^((1 : ℝ)/16)=q := by
    dsimp [Q,q]
    rw [← Real.rpow_natCast,← Real.rpow_mul hH0.le]
    congr 1
    norm_num
  have hW : ∀ tau i,0<W tau i := by
    intro tau i
    dsimp [W,weightedBalancedValues3]
    split_ifs
    · exact mul_pos (ha tau i) hr
    · exact ha tau i
  have hcut : ∀ tau i,(W tau i)⁻¹<Q := by
    intro tau i
    have hb : (a tau i)⁻¹≤H^2 := (hinv tau i).trans (by nlinarith [mul_le_mul_of_nonneg_right hC hH0.le])
    have hpow : H^2<Q := pow_lt_pow_right₀ (by linarith : 1<H) (by decide : (2 : ℕ)<4)
    by_cases ht : tau=0
    · subst tau
      change (a 0 i*r)⁻¹<Q
      rw [mul_inv_rev]
      have hri : r⁻¹≤1 := (inv_le_one₀ hr).mpr hr1
      exact (by nlinarith [mul_le_mul_of_nonneg_right hri (inv_pos.mpr (ha 0 i)).le] : r⁻¹*(a 0 i)⁻¹≤H^2).trans_lt hpow
    · simpa only [W,weightedBalancedValues3,if_neg ht] using hb.trans_lt hpow
  have hcut0 : ∀ i,W 0 i<Q := by
    intro i
    change a 0 i*r<Q
    have hb : a 0 i≤H^2 := (hreal i).trans (by nlinarith [mul_le_mul_of_nonneg_right hC hH0.le])
    have hh := mul_le_mul hb hrH hr.le (sq_nonneg H)
    exact (by nlinarith : a 0 i*r≤H^3).trans_lt (pow_lt_pow_right₀ (by linarith : 1<H) (by decide : (3 : ℕ)<4))
  have hWfin : ∀ tau,tau≠0 → ∀ i,W tau i≤1 := by
    intro tau ht i
    simpa only [W,weightedBalancedValues3,if_neg ht] using hfinite tau ht i
  have hWprod : (∏ tau,∏ i,W tau i)=1 := by
    simp only [W,weightedBalancedValues3,Fin.prod_univ_three,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
    have hp := hprod
    simp only [Fin.prod_univ_three] at hp
    change (a 0 0*r*(a 0 1*r)*(a 0 2*r))*(a 1 0*a 1 1*a 1 2)*(a 2 0*a 2 1*a 2 2)=1
    calc
      _=(a 0 0*a 0 1*a 0 2)*(a 1 0*a 1 1*a 1 2)*(a 2 0*a 2 1*a 2 2)*r^3 := by ring
      _=1 := by rw [hrpow,← mul_div_assoc,hp,div_self hK.ne']
  have heq := sourceLogWeights3_rpow Q hQ W hW
  refine ⟨hQ,sourceLogWeights3_conditions Q hQ W hW hcut hcut0 hWfin hWprod,heq,?_,?_⟩
  · intro i
    rw [Real.rpow_sub hQ0,heq,hQq]
    change a 0 i≤(a 0 i*r)/q
    exact (le_div_iff₀ hq).mpr (mul_le_mul_of_nonneg_left hqr (ha 0 i).le)
  · intro tau ht i
    rw [heq]
    simp only [W,weightedBalancedValues3,if_neg ht]

end
end JSP000334
