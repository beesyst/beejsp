import SubspaceBridge.AllPointProduct4
import SubspaceBridge.AllPointWeights4
import SubspaceBridge.WeightedDiagonalProducts3
namespace JSP000334

def weightedProductConstant4 (k : Fin 4 → ℚ) (a : ℚ) : ℚ :=
  (∏ i,threePlaceProduct (k i))*threePlaceProduct a

theorem weighted_fixed_product_height4 (y : Fin 4 → ℤ) (hy : PrimitiveFour y)
    (k : Fin 4 → ℚ) (a : ℚ)
    (hc : ∀ i,threePlaceProduct (y i : ℚ)=threePlaceProduct (k i))
    (hs : threePlaceProduct (∑ i : Fin 4,(y i : ℚ))=threePlaceProduct a) :
    ∃ choice : Fin 3 → Fin 4,
      fourRetainedProduct choice (fun i => (y i : ℚ))*archFourHeight y=weightedProductConstant4 k a := by
  choose choice hchoice using fun tau => exists_four_maximal_coordinate tau (fun i => (y i : ℚ))
  refine ⟨choice,?_⟩
  have hh := four_retained_product_height choice (fun i => (y i : ℚ)) hchoice
  rw [primitive_four_height y hy] at hh
  simpa only [hc,hs,weightedProductConstant4] using hh

open scoped BigOperators Matrix
noncomputable section

def weightedBalancedValues4 (H K : ℝ) (a : Fin 3 → Fin 4 → ℝ) (tau : Fin 3) (i : Fin 4) : ℝ :=
  if tau=0 then a tau i*(H/K)^((1 : ℝ)/4) else a tau i

theorem weighted_balanced_weights4 (H K C : ℝ) (hH : 4≤H) (hK : 0<K)
    (hC : C≤H) (hKi : K⁻¹≤H) (hK5 : K^5≤H)
    (a : Fin 3 → Fin 4 → ℝ) (ha : ∀ tau i,0<a tau i)
    (hreal : ∀ i,a 0 i≤C*H)
    (hfinite : ∀ tau,tau≠0 → ∀ i,a tau i≤1)
    (hinv : ∀ tau i,(a tau i)⁻¹≤C*H)
    (hprod : (∏ tau,∏ i,a tau i)*H=K) :
    let Q := H^8
    let W := weightedBalancedValues4 H K a
    1<Q ∧ sourceWeightConditions4 (sourceLogWeights4 Q W) ∧
      (∀ tau i,Q^(sourceLogWeights4 Q W tau i)=W tau i) ∧
      (∀ i,a 0 i≤Q^(sourceLogWeights4 Q W 0 i-(1 : ℝ)/40)) ∧
      (∀ tau,tau≠0 → ∀ i,a tau i=Q^(sourceLogWeights4 Q W tau i)) := by
  intro Q W
  have hH0 : 0<H := by linarith
  have hH1 : 1≤H := by linarith
  have hQ : 1<Q := by dsimp [Q]; nlinarith [sq_nonneg (H^2-1)]
  have hQ0 := zero_lt_one.trans hQ
  let r := (H/K)^((1 : ℝ)/4)
  let q := H^((1 : ℝ)/5)
  have hr : 0<r := Real.rpow_pos_of_pos (div_pos hH0 hK) _
  have hq : 0<q := Real.rpow_pos_of_pos hH0 _
  have hrpow : r^4=H/K := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (div_pos hH0 hK).le]
    norm_num
  have hqpow : q^5=H := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hH0.le]
    norm_num
  have hq1 : 1≤q := Real.one_le_rpow hH1 (by norm_num)
  have hKq : K≤q := le_of_pow_le_pow_left (by decide : (5 : ℕ)≠0) hq.le (by rw [hqpow];exact hK5)
  have hqr : q≤r := by
    apply le_of_pow_le_pow_left (by decide : (4 : ℕ)≠0) hr.le
    rw [hrpow]
    apply (le_div_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left hKq (pow_nonneg hq.le 4)
    nlinarith [hqpow]
  have hr1 : 1≤r := hq1.trans hqr
  have hrH : r≤H := by
    apply le_of_pow_le_pow_left (by decide : (4 : ℕ)≠0) hH0.le
    rw [hrpow]
    have hh : H/K≤H^2 := by
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left hKi hH0.le]
    exact hh.trans (by nlinarith [sq_nonneg (H^2-1)])
  have hQq : Q^((1 : ℝ)/40)=q := by
    dsimp [Q,q]
    rw [← Real.rpow_natCast,← Real.rpow_mul hH0.le]
    congr 1
    norm_num
  have hW : ∀ tau i,0<W tau i := by
    intro tau i
    dsimp [W,weightedBalancedValues4]
    split_ifs
    · exact mul_pos (ha tau i) hr
    · exact ha tau i
  have hcut : ∀ tau i,(W tau i)⁻¹<Q := by
    intro tau i
    have hb : (a tau i)⁻¹≤H^2 := (hinv tau i).trans (by nlinarith [mul_le_mul_of_nonneg_right hC hH0.le])
    have hpow : H^2<Q := pow_lt_pow_right₀ (by linarith : 1<H) (by decide : (2 : ℕ)<8)
    by_cases ht : tau=0
    · subst tau
      change (a 0 i*r)⁻¹<Q
      rw [mul_inv_rev]
      have hri : r⁻¹≤1 := (inv_le_one₀ hr).mpr hr1
      exact (by nlinarith [mul_le_mul_of_nonneg_right hri (inv_pos.mpr (ha 0 i)).le] : r⁻¹*(a 0 i)⁻¹≤H^2).trans_lt hpow
    · simpa only [W,weightedBalancedValues4,if_neg ht] using hb.trans_lt hpow
  have hcut0 : ∀ i,W 0 i<Q := by
    intro i
    change a 0 i*r<Q
    have hb : a 0 i≤H^2 := (hreal i).trans (by nlinarith [mul_le_mul_of_nonneg_right hC hH0.le])
    have hh := mul_le_mul hb hrH hr.le (sq_nonneg H)
    exact (by nlinarith : a 0 i*r≤H^3).trans_lt (pow_lt_pow_right₀ (by linarith : 1<H) (by decide : (3 : ℕ)<8))
  have hWfin : ∀ tau,tau≠0 → ∀ i,W tau i≤1 := by
    intro tau ht i
    simpa only [W,weightedBalancedValues4,if_neg ht] using hfinite tau ht i
  have hWprod : (∏ tau,∏ i,W tau i)=1 := by
    have hfactor (tau : Fin 3) : (∏ i : Fin 4,W tau i)=
        if tau=0 then (∏ i : Fin 4,a tau i)*r^4 else ∏ i : Fin 4,a tau i := by
      by_cases ht : tau=0
      · subst tau
        simp only [W,weightedBalancedValues4,if_pos rfl,ite_true]
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        rfl
      · simp only [W,weightedBalancedValues4,if_neg ht]
    simp_rw [hfactor]
    simp only [Fin.prod_univ_three,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
    have hp := hprod
    simp only [Fin.prod_univ_three] at hp
    calc
      _=((∏ i : Fin 4,a 0 i)*(∏ i : Fin 4,a 1 i)*(∏ i : Fin 4,a 2 i))*r^4 := by ring
      _=1 := by rw [hrpow,← mul_div_assoc,hp,div_self hK.ne']
  have heq := sourceLogWeights4_rpow Q hQ W hW
  refine ⟨hQ,sourceLogWeights4_conditions Q hQ W hW hcut hcut0 hWfin hWprod,heq,?_,?_⟩
  · intro i
    rw [Real.rpow_sub hQ0,heq,hQq]
    change a 0 i≤(a 0 i*r)/q
    exact (le_div_iff₀ hq).mpr (mul_le_mul_of_nonneg_left hqr (ha 0 i).le)
  · intro tau ht i
    rw [heq]
    simp only [W,weightedBalancedValues4,if_neg ht]

end
end JSP000334
