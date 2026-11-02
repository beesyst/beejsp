import SubspaceBridge.AuxiliaryMatrix
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators Classical
namespace JSP000334

theorem rothAux_weight_block {m : ℕ} (d : RothBlockVars m →₀ ℕ) (h : Fin m) :
    Finsupp.weight (fun u : RothBlockVars m => if u.1 = h then 1 else 0) d =
      ∑ j : Fin 3, d (h,j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type, nsmul_eq_mul]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero]
  calc
    (∑ x : Fin m, ∑ j : Fin 3,
        if x = h then d (x,j) else 0) =
      ∑ x : Fin m,
        if x = h then (∑ j : Fin 3, d (x,j)) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = h
          · simp [hx]
          · simp [hx]
    _ = ∑ j : Fin 3, d (h,j) := by simp

theorem rothAux_weight_pivot {m : ℕ} (d : RothBlockVars m →₀ ℕ) (k : Fin 3) :
    Finsupp.weight (fun u : RothBlockVars m => if u.2 = k then 1 else 0) d =
      ∑ h : Fin m, d (h,k) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, nsmul_eq_mul]

theorem rothAux_weighted_neg {m : ℕ} (w : RothBlockVars m → ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (n : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous w P n) :
    MvPolynomial.IsWeightedHomogeneous w (-P) n := by
  intro d hd
  apply hP
  simpa using hd

theorem rothAuxScaledChart_block_weight {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3)
    (h : Fin m) (u : RothBlockVars m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars m => if v.1 = h then 1 else 0)
      (rothAuxScaledChart a k u) (if u.1 = h then 1 else 0) := by
  let w := fun v : RothBlockVars m => if v.1 = h then 1 else 0
  have hx (j : Fin 3) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) (if u.1 = h then 1 else 0) := by
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X ℤ w (u.1,j))
  unfold rothAuxScaledChart
  by_cases hu : u.2 = k
  · rw [if_pos hu]
    exact rothAux_weighted_neg w _ _
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun j _ => hx j))
  · rw [if_neg hu]
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X ℤ w u)

theorem rothAuxScaledChart_pivot_weight {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3)
    (u : RothBlockVars m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars m => if v.2 = k then 1 else 0)
      (rothAuxScaledChart a k u) 0 := by
  let w := fun v : RothBlockVars m => if v.2 = k then 1 else 0
  have hx (j : Fin 3) (hj : j ≠ k) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) 0 := by
    simpa only [w, hj, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X ℤ w (u.1,j))
  unfold rothAuxScaledChart
  split_ifs with hu
  · exact rothAux_weighted_neg w _ 0
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ 0 (fun j hj => hx j (Finset.mem_erase.mp hj).1))
  · simpa only [w, hu, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X ℤ w u)

theorem rothAux_scaled_monomial_weighted {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3)
    (J b : RothBlockVars m →₀ ℕ) (w : RothBlockVars m → ℕ) (v : RothBlockVars m → ℕ)
    (hv : ∀ u, MvPolynomial.IsWeightedHomogeneous w (rothAuxScaledChart a k u) (v u)) :
    MvPolynomial.IsWeightedHomogeneous w
      (rothAuxScaledSubstitution a k
        (rothBlockIntegerDividedDerivative J (MvPolynomial.monomial b 1)))
      (∑ u : RothBlockVars m, (b - J) u * v u) := by
  rw [rothAux_scaled_derivative_monomial]
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : RothBlockVars m => rothAuxScaledChart a k u ^ (b - J) u)
    (fun u => (b - J) u * v u) (fun u _ => by simpa only [nsmul_eq_mul] using (hv u).pow ((b - J) u))
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w _).mul hp



theorem rothAux_transformed_polynomial {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (J : RothBlockVars m →₀ ℕ)
    (c : RothAuxCoefficients r → ℤ) :
    rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative J (rothAuxPolynomial c)) =
      ∑ b, MvPolynomial.C (c b) * rothAuxScaledSubstitution a k
        (rothBlockIntegerDividedDerivative J (MvPolynomial.monomial (rothAuxExponent b) 1)) := by
  apply MvPolynomial.ext
  intro d
  rw [rothAuxPolynomial, rothAux_transformed_coeff_sum]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem rothAux_pivot_monomial_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (i : Fin m → ℕ) (b : RothAuxCoefficients r) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : RothBlockVars m => if u.1 = h then 1 else 0)
      (rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative k i) (MvPolynomial.monomial (rothAuxExponent b) 1)))
      (r h - i h) := by
  let J := rothAuxPivotDerivative k i
  let w := fun u : RothBlockVars m => if u.1 = h then 1 else 0
  by_cases hle : J ≤ rothAuxExponent b
  · have hw := rothAux_scaled_monomial_weighted a k J (rothAuxExponent b) w w
      (rothAuxScaledChart_block_weight a k h)
    have heq : (∑ u : RothBlockVars m, (rothAuxExponent b - J) u * w u) =
        ∑ j : Fin 3, (rothAuxExponent b - J) (h,j) := by
      have he := rothAux_weight_block (rothAuxExponent b - J) h
      rw [Finsupp.weight_apply] at he
      rw [Finsupp.sum_fintype (rothAuxExponent b - J)
        (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
      simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
    have hdeg : (∑ j : Fin 3, (rothAuxExponent b - J) (h,j)) = r h - i h := by
      change (∑ j : Fin 3, (rothAuxExponent b (h,j) - J (h,j))) = _
      rw [Finset.sum_tsub_distrib _ (fun j _ => hle (h,j))]
      have hb : (∑ j : Fin 3, rothAuxExponent b (h,j)) = r h := (b h).property
      rw [hb]
      congr 1
      simp [J, rothAuxPivotDerivative]
    rw [heq, hdeg] at hw
    exact hw
  · change ¬ ∀ u, J u ≤ rothAuxExponent b u at hle
    push_neg at hle
    obtain ⟨u, hu⟩ := hle
    have hz : (∏ v : RothBlockVars m, (Nat.choose (rothAuxExponent b v) (J v) : ℤ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [Nat.choose_eq_zero_of_lt hu]
    rw [rothAux_scaled_derivative_monomial, hz, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero ℤ w _

theorem rothAux_transformed_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → ℤ) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : RothBlockVars m => if u.1 = h then 1 else 0)
      (rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative k i) (rothAuxPolynomial c))) (r h - i h) := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul
    (rothAux_pivot_monomial_block_weight a k i b h)

theorem rothAux_transformed_block_homogeneous {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → ℤ) :
    rothBlockHomogeneous (fun h => r h - i h)
      (rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative k i) (rothAuxPolynomial c))) := by
  intro d hd h
  rw [← rothAux_weight_block]
  exact rothAux_transformed_block_weight a k i c h (MvPolynomial.mem_support_iff.mp hd)

theorem rothAux_transformed_pivot_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (J : RothBlockVars m →₀ ℕ)
    (c : RothAuxCoefficients r → ℤ) :
    MvPolynomial.IsWeightedHomogeneous (fun u : RothBlockVars m => if u.2 = k then 1 else 0)
      (rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative J (rothAuxPolynomial c))) 0 := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  have hb := rothAux_scaled_monomial_weighted a k J (rothAuxExponent b)
    (fun u : RothBlockVars m => if u.2 = k then 1 else 0) (fun _ => 0)
    (rothAuxScaledChart_pivot_weight a k)
  simp only [mul_zero, Finset.sum_const_zero] at hb
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul hb

theorem rothAux_transformed_pivot_zero {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (J : RothBlockVars m →₀ ℕ)
    (c : RothAuxCoefficients r → ℤ) (d : RothBlockVars m →₀ ℕ)
    (hd : (rothAuxScaledSubstitution a k
      (rothBlockIntegerDividedDerivative J (rothAuxPolynomial c))).coeff d ≠ 0) (h : Fin m) :
    d (h,k) = 0 := by
  have hw := rothAux_transformed_pivot_weight a k J c hd
  rw [rothAux_weight_pivot] at hw
  have hle : d (h,k) ≤ ∑ g : Fin m, d (g,k) :=
    Finset.single_le_sum (fun g _ => Nat.zero_le (d (g,k))) (Finset.mem_univ h)
  omega


theorem rothAuxFreeExponent_reconstruct {m : ℕ} (s : Fin m → ℕ) (k : Fin 3)
    (d : RothBlockVars m →₀ ℕ) (hs : ∀ h, ∑ t : Fin 3, d (h,t) = s h)
    (hz : ∀ h, d (h,k) = 0) :
    ∃ j : (h : Fin m) → Fin (s h + 1), rothAuxFreeExponent s k j = d := by
  let e := Equiv.swap (0 : Fin 3) k
  have hp (h : Fin m) : d (h,e 0) = 0 := by simpa [e] using hz h
  have hf (h : Fin m) : d (h,e 1) + d (h,e 2) = s h := by
    have he := (Equiv.sum_comp e (fun t => d (h,t))).trans (hs h)
    simp only [Fin.sum_univ_three] at he
    rw [hp h] at he
    omega
  let j : (h : Fin m) → Fin (s h + 1) :=
    fun h => ⟨d (h,e 1), by have hh := hf h; omega⟩
  refine ⟨j, ?_⟩
  apply Finsupp.ext
  rintro ⟨h,t⟩
  obtain ⟨v, rfl⟩ := e.surjective t
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h21 : e 2 ≠ e 1 := e.injective.ne (by decide)
  fin_cases v
  · change (if e 0 = e 1 then (j h).val else if e 0 = e 2 then s h - (j h).val else 0) = d (h,e 0)
    rw [if_neg h01, if_neg h02, hp h]
  · change (if e 1 = e 1 then (j h).val else if e 1 = e 2 then s h - (j h).val else 0) = d (h,e 1)
    rw [if_pos rfl]
  · change (if e 2 = e 1 then (j h).val else if e 2 = e 2 then s h - (j h).val else 0) = d (h,e 2)
    rw [if_neg h21, if_pos rfl]
    change s h - d (h,e 1) = d (h,e 2)
    have hh := hf h
    omega

theorem rothAux_transformed_support {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → ℤ) (d : RothBlockVars m →₀ ℕ)
    (hd : (rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative
      (rothAuxPivotDerivative k i) (rothAuxPolynomial c))).coeff d ≠ 0) :
    (∀ h, ∑ t : Fin 3, d (h,t) = r h - i h) ∧
      (∀ h, d (h,k) = 0) ∧
      ∃ j : (h : Fin m) → Fin (r h - i h + 1),
        rothAuxFreeExponent (fun h => r h - i h) k j = d := by
  have hs : ∀ h, ∑ t : Fin 3, d (h,t) = r h - i h := fun h =>
    rothAux_transformed_block_homogeneous a k i c d (MvPolynomial.mem_support_iff.mpr hd) h
  have hz : ∀ h, d (h,k) = 0 :=
    rothAux_transformed_pivot_zero a k (rothAuxPivotDerivative k i) c d hd
  exact ⟨hs, hz, rothAuxFreeExponent_reconstruct _ k d hs hz⟩

theorem rothAux_transformed_eq_zero_iff {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → ℤ) :
    (∀ j : (h : Fin m) → Fin (r h - i h + 1),
      (rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative k i) (rothAuxPolynomial c))).coeff
          (rothAuxFreeExponent (fun h => r h - i h) k j) = 0) ↔
      rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative k i) (rothAuxPolynomial c)) = 0 := by
  constructor
  · intro hz
    apply MvPolynomial.ext
    intro d
    simp only [MvPolynomial.coeff_zero]
    by_cases hd : (rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative k i) (rothAuxPolynomial c))).coeff d = 0
    · exact hd
    · obtain ⟨_, _, j, hj⟩ := rothAux_transformed_support a k i c d hd
      rw [← hj]
      exact hz j
  · intro hz j
    rw [hz, MvPolynomial.coeff_zero]

theorem rothAuxEquation_all_iff_polynomial_zero {m : ℕ} {r : Fin m → ℕ} {eta : ℝ}
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (f : Fin 9) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
    (c : RothAuxCoefficients r → ℤ) :
    (∀ j : (h : Fin m) → Fin (r h - (i.val h).val + 1),
      rothAuxEquation L hL f i j (rothAuxPolynomial c) = 0) ↔
      rothAuxScaledSubstitution (L (rothAuxFormEquiv f).1 (rothAuxFormEquiv f).2)
        (rothAuxPivot L hL f) (rothBlockIntegerDividedDerivative
          (rothAuxPivotDerivative (rothAuxPivot L hL f) (fun h => (i.val h).val))
          (rothAuxPolynomial c)) = 0 :=
  rothAux_transformed_eq_zero_iff _ _ _ c

theorem rothAuxMatrix_mulVec_zero_iff_polynomials_zero {m : ℕ}
    (r : Fin m → ℕ) (eta : ℝ) (L : Fin 3 → Fin 3 → Fin 3 → ℤ)
    (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) (c : RothAuxCoefficients r → ℤ) :
    (rothAuxMatrix r eta L hL).mulVec c = 0 ↔
      ∀ (f : Fin 9) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}),
        rothAuxScaledSubstitution (L (rothAuxFormEquiv f).1 (rothAuxFormEquiv f).2)
          (rothAuxPivot L hL f) (rothBlockIntegerDividedDerivative
            (rothAuxPivotDerivative (rothAuxPivot L hL f) (fun h => (i.val h).val))
            (rothAuxPolynomial c)) = 0 := by
  rw [rothAuxMatrix_mulVec_zero_iff]
  constructor
  · intro hz f i
    exact (rothAuxEquation_all_iff_polynomial_zero L hL f i c).mp (hz f i)
  · intro hz f i
    exact (rothAuxEquation_all_iff_polynomial_zero L hL f i c).mpr (hz f i)

end JSP000334
