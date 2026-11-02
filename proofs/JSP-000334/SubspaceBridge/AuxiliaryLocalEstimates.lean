import SubspaceBridge.AuxiliaryNormalBasis

open scoped BigOperators Classical
namespace JSP000334

noncomputable def rothNormalLocalValue (L : Matrix (Fin 3) (Fin 3) ℤ)
    (w : Fin 3 → ℤ) (i : Fin 3) : ℚ :=
  ∑ k : Fin 3, (L i k : ℚ) * (w k : ℚ)

noncomputable def rothNormalLocalChart {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (u : RothBlockVars m) :
    MvPolynomial (RothNormalVars m) ℚ :=
  ∑ j : Fin 2, MvPolynomial.C (rothNormalLocalValue L (w u.1 j) u.2) *
    MvPolynomial.X (u.1,j)

theorem rothNormal_local_chart {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (u : RothBlockVars m) :
    rothNormalSubstitution w (rothLocalLinearChart (rothLocalRationalMatrix L) u) =
      rothNormalLocalChart L w u := by
  change MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalVectorChart w)
    (∑ i : Fin 3, MvPolynomial.C (L u.2 i : ℚ) * MvPolynomial.X (u.1,i)) = _
  rw [map_sum]
  simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  unfold rothNormalVectorChart rothNormalLocalChart rothNormalLocalValue
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul, ← map_sum]

theorem rothNormal_local_reconstruct {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalLocalChart L w)
      (rothLocalExpansion L J P) = rothNormalDerivativeRestriction w J P := by
  have he : (rothNormalSubstitution w).comp
      (rothLocalSubstitution (rothLocalRationalMatrix L)) =
      MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalLocalChart L w) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [rothLocalSubstitution, rothNormalSubstitution]
    · intro u
      simp only [RingHom.comp_apply, rothLocalSubstitution, MvPolynomial.eval₂Hom_X']
      exact rothNormal_local_chart L w u
  rw [← he, RingHom.comp_apply, rothLocal_expansion_reconstruct L hL]
  have hm : (rothNormalSubstitution w).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w) := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp [rothNormalSubstitution]
  exact congrArg (fun f => f (rothBlockIntegerDividedDerivative J P)) hm

noncomputable def rothNormalSplitExponent {m : ℕ} (u : RothBlockVars m) (n k : ℕ) :
    RothNormalVars m →₀ ℕ :=
  Finsupp.single (u.1,0) k + Finsupp.single (u.1,1) (n-k)

noncomputable def rothNormalSplitScalar {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (u : RothBlockVars m) (n k : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) * rothNormalLocalValue L (w u.1 0) u.2 ^ k *
    rothNormalLocalValue L (w u.1 1) u.2 ^ (n-k)

theorem rothNormal_local_chart_pow {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (u : RothBlockVars m) (n : ℕ) :
    rothNormalLocalChart L w u ^ n =
      ∑ k ∈ Finset.range (n+1), MvPolynomial.monomial
        (rothNormalSplitExponent u n k) (rothNormalSplitScalar L w u n k) := by
  simp only [rothNormalLocalChart, Fin.sum_univ_two]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_pow, ← map_pow, MvPolynomial.X_pow_eq_monomial,
    rothNormalSplitExponent, rothNormalSplitScalar]
  have hn : (n.choose k : MvPolynomial (RothNormalVars m) ℚ) =
      MvPolynomial.C (n.choose k : ℚ) := by simp
  rw [hn]
  simp only [MvPolynomial.C_apply, MvPolynomial.monomial_mul, zero_add,
    add_zero, one_mul, mul_one]
  congr 1
  ring

noncomputable def rothNormalSplits {m : ℕ} (b : RothBlockVars m →₀ ℕ) :
    Finset (RothBlockVars m → ℕ) :=
  Fintype.piFinset (fun u => Finset.range (b u + 1))

noncomputable def rothNormalConvolutionExponent {m : ℕ}
    (b : RothBlockVars m →₀ ℕ) (k : RothBlockVars m → ℕ) :
    RothNormalVars m →₀ ℕ := ∑ u : RothBlockVars m, rothNormalSplitExponent u (b u) (k u)

theorem rothNormal_monomial_product {m : ℕ} (s : Finset (RothBlockVars m))
    (b : RothBlockVars m →₀ ℕ) (k : RothBlockVars m → ℕ)
    (a : RothBlockVars m → ℚ) :
    (∏ u ∈ s, MvPolynomial.monomial (rothNormalSplitExponent u (b u) (k u)) (a u)) =
      MvPolynomial.monomial (∑ u ∈ s, rothNormalSplitExponent u (b u) (k u))
        (∏ u ∈ s, a u) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert u s hu ih => simp [hu, ih, MvPolynomial.monomial_mul]

theorem rothNormal_local_monomial {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (b : RothBlockVars m →₀ ℕ) :
    (∏ u : RothBlockVars m, rothNormalLocalChart L w u ^ b u) =
      ∑ k ∈ rothNormalSplits b,
        MvPolynomial.monomial (rothNormalConvolutionExponent b k)
          (∏ u : RothBlockVars m, rothNormalSplitScalar L w u (b u) (k u)) := by
  simp_rw [rothNormal_local_chart_pow]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact rothNormal_monomial_product Finset.univ b k _

theorem rothNormal_local_coefficient {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (e : RothNormalVars m →₀ ℕ) :
    (rothNormalDerivativeRestriction w J P).coeff e =
      ∑ b ∈ (rothLocalExpansion L J P).support, ∑ k ∈ rothNormalSplits b,
        if e = rothNormalConvolutionExponent b k then
          (rothLocalExpansion L J P).coeff b *
            ∏ u : RothBlockVars m, rothNormalSplitScalar L w u (b u) (k u)
        else 0 := by
  rw [← rothNormal_local_reconstruct L hL w J P]
  conv_lhs => arg 2; arg 2; rw [MvPolynomial.as_sum (rothLocalExpansion L J P)]
  rw [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), rothNormal_local_monomial,
    Finset.mul_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_ite, eq_comm]

theorem rothNormal_same_integer_coefficient {m : ℕ}
    (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ)
    (hL : ∀ tau, (rothLocalRationalMatrix (L tau)).det ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (e : RothNormalVars m →₀ ℕ) :
    ∀ tau : Fin 3,
      (((rothNormalIntegerRestriction w J P).coeff e : ℤ) : ℚ) =
        ∑ b ∈ (rothLocalExpansion (L tau) J P).support, ∑ k ∈ rothNormalSplits b,
          if e = rothNormalConvolutionExponent b k then
            (rothLocalExpansion (L tau) J P).coeff b *
              ∏ u : RothBlockVars m, rothNormalSplitScalar (L tau) w u (b u) (k u)
          else 0 := by
  intro tau
  rw [← rothNormal_integer_coeff]
  exact rothNormal_local_coefficient (L tau) (hL tau) w J P e
theorem rothNormal_local_order_le {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (J b : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (hb : (rothLocalExpansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ i : Fin 3, J (h,i)) ≤ r h := by
  by_contra! hbad
  have hz := rothSource_derivative_zero_of_block_excess r P hP J h hbad
  apply hb
  simp [rothLocalExpansion, hz]

theorem rothNormal_local_total_weight {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 3) (Fin 3) ℤ)
    (J b : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (hP : rothBlockHomogeneous r P)
    (hb : (rothLocalExpansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 3, rothLocalCoordinateWeight r i b) =
      (m : ℝ) - rothSourceDerivativeWeight r J := by
  unfold rothLocalCoordinateWeight rothSourceDerivativeWeight
  have hm : (m : ℝ) = ∑ _h : Fin m, (1 : ℝ) := by simp
  rw [Finset.sum_comm, hm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_div]
  have hd := rothLocal_expansion_block_degree r L J P hP b hb h
  have hle := rothNormal_local_order_le r L J b P hP hb h
  have hdR : (∑ i : Fin 3, (b (h,i) : ℝ)) = (r h : ℝ) - ∑ i : Fin 3, (J (h,i) : ℝ) := by
    have hh : (∑ i : Fin 3, (b (h,i) : ℝ)) + (∑ i : Fin 3, (J (h,i) : ℝ)) = (r h : ℝ) := by
      exact_mod_cast (show (∑ i : Fin 3, b (h,i)) + (∑ i : Fin 3, J (h,i)) = r h by omega)
    linarith
  rw [hdR]
  have hpos : (0 : ℝ) < r h := by exact_mod_cast hr h
  field_simp [ne_of_gt hpos]

noncomputable def rothNormalLogWeight {m : ℕ} (Q : Fin m → ℝ)
    (b : RothBlockVars m →₀ ℕ) (i : Fin 3) : ℝ :=
  ∑ h : Fin m, (b (h,i) : ℝ) * Real.log (Q h)

theorem rothNormal_log_weight_transport {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (eta A : ℝ)
    (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ) * Real.log (Q h) ∧
      (r h : ℝ) * Real.log (Q h) ≤ (1+eta)*A)
    (b : RothBlockVars m →₀ ℕ)
    (hdegree : ∀ h, (∑ i : Fin 3, b (h,i)) ≤ r h)
    (hbalance : ∀ i : Fin 3,
      |rothLocalCoordinateWeight r i b - (m : ℝ)/3| ≤ 9*m*eta) :
    ∀ i : Fin 3, |rothNormalLogWeight Q b i - A*(m : ℝ)/3| ≤ 10*A*m*eta := by
  intro i
  have hnorm : 0 ≤ rothLocalCoordinateWeight r i b ∧
      rothLocalCoordinateWeight r i b ≤ (m : ℝ) := by
    constructor
    · unfold rothLocalCoordinateWeight
      exact Finset.sum_nonneg (fun h _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · unfold rothLocalCoordinateWeight
      calc
        _ ≤ ∑ h : Fin m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro h hh
          apply (div_le_one (by exact_mod_cast hr h)).mpr
          exact_mod_cast (Finset.single_le_sum (fun j _ => Nat.zero_le (b (h,j)))
            (Finset.mem_univ i)).trans (hdegree h)
        _ = _ := by simp
  have hterm (h : Fin m) :
      (b (h,i) : ℝ) * Real.log (Q h) =
        ((b (h,i) : ℝ) / (r h : ℝ)) * ((r h : ℝ) * Real.log (Q h)) := by
    have hn : (r h : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr h)
    field_simp [hn]
    ring
  have hlo : A * rothLocalCoordinateWeight r i b ≤ rothNormalLogWeight Q b i := by
    unfold rothLocalCoordinateWeight rothNormalLogWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [hterm]
    calc
      A * ((b (h,i) : ℝ) / r h) = ((b (h,i) : ℝ) / r h) * A := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlog h).1
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hhi : rothNormalLogWeight Q b i ≤ (1+eta)*A*rothLocalCoordinateWeight r i b := by
    unfold rothLocalCoordinateWeight rothNormalLogWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [hterm]
    calc
      _ ≤ ((b (h,i) : ℝ) / r h) * ((1+eta)*A) := mul_le_mul_of_nonneg_left (hlog h).2
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = _ := by ring
  have hbal := abs_le.mp (hbalance i)
  have hscale1 := mul_le_mul_of_nonneg_left hbal.1 hA
  have hscale2 := mul_le_mul_of_nonneg_left hbal.2 hA
  have herror := mul_le_mul_of_nonneg_left hnorm.2 (mul_nonneg heta hA)
  apply abs_le.mpr
  constructor <;> nlinarith

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem rothNormalAbs_pow (tau : Fin 3) (x : ℚ) (n : ℕ) :
    rothLocalAbs tau (x^n) = rothLocalAbs tau x ^ n := by
  induction n with
  | zero => simp [rothLocalAbs_one]
  | succ n ih => simp only [pow_succ, rothLocalAbs_mul, ih]

theorem rothNormalAbs_prod {ι : Type*} (tau : Fin 3) (s : Finset ι) (x : ι → ℚ) :
    rothLocalAbs tau (∏ i ∈ s, x i) = ∏ i ∈ s, rothLocalAbs tau (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [rothLocalAbs_one]
  | @insert i s hi ih => simp [hi, rothLocalAbs_mul, ih]

theorem rothNormalAbs_int_finite (tau : Fin 3) (htau : tau ≠ 0) (z : ℤ) :
    rothLocalAbs tau (z : ℚ) ≤ 1 := by
  fin_cases tau
  · exact (htau rfl).elim
  · change (padicNorm 2 (z : ℚ) : ℝ) ≤ 1
    exact_mod_cast (padicNorm.of_int (p := 2) z)
  · change (padicNorm 3 (z : ℚ) : ℝ) ≤ 1
    exact_mod_cast (padicNorm.of_int (p := 3) z)

theorem rothNormalAbs_add_finite (tau : Fin 3) (htau : tau ≠ 0) (x y : ℚ) :
    rothLocalAbs tau (x+y) ≤ max (rothLocalAbs tau x) (rothLocalAbs tau y) := by
  fin_cases tau
  · exact (htau rfl).elim
  · change (padicNorm 2 (x+y) : ℝ) ≤ max (padicNorm 2 x : ℝ) (padicNorm 2 y : ℝ)
    exact_mod_cast (padicNorm.nonarchimedean (p := 2) (q := x) (r := y))
  · change (padicNorm 3 (x+y) : ℝ) ≤ max (padicNorm 3 x : ℝ) (padicNorm 3 y : ℝ)
    exact_mod_cast (padicNorm.nonarchimedean (p := 3) (q := x) (r := y))

theorem rothNormalAbs_sum_finite {ι : Type*} (tau : Fin 3) (htau : tau ≠ 0)
    (s : Finset ι) (x : ι → ℚ) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ i ∈ s, rothLocalAbs tau (x i) ≤ C) :
    rothLocalAbs tau (∑ i ∈ s, x i) ≤ C := by
  induction s using Finset.induction_on with
  | empty => simpa [rothLocalAbs_zero] using hC
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (rothNormalAbs_add_finite tau htau _ _).trans
      (max_le (hx i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))))

noncomputable def rothNormalBinomialBudget (tau : Fin 3) (n k : ℕ) : ℝ :=
  if tau = 0 then (Nat.choose n k : ℝ) else 1

theorem rothNormal_split_bound {m : ℕ} (tau : Fin 3)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (u : RothBlockVars m) (n k : ℕ) (hk : k ≤ n) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ j : Fin 2, rothLocalAbs tau (rothNormalLocalValue L (w u.1 j) u.2) ≤ B) :
    rothLocalAbs tau (rothNormalSplitScalar L w u n k) ≤
      rothNormalBinomialBudget tau n k * B^n := by
  have hc : rothLocalAbs tau (n.choose k : ℚ) ≤ rothNormalBinomialBudget tau n k := by
    by_cases htau : tau = 0
    · subst tau
      simp [rothLocalAbs, rothNormalBinomialBudget]
    · simpa [rothNormalBinomialBudget, htau] using
        rothNormalAbs_int_finite tau htau (n.choose k : ℤ)
  have h0 := pow_le_pow_left₀ (rothLocalAbs_nonneg tau _) (hw 0) k
  have h1 := pow_le_pow_left₀ (rothLocalAbs_nonneg tau _) (hw 1) (n-k)
  unfold rothNormalSplitScalar
  rw [rothLocalAbs_mul, rothLocalAbs_mul, rothNormalAbs_pow, rothNormalAbs_pow]
  calc
    _ ≤ (rothNormalBinomialBudget tau n k * B^k) * B^(n-k) := by
      apply mul_le_mul
      · exact mul_le_mul hc h0 (pow_nonneg (rothLocalAbs_nonneg tau _) _)
          (by unfold rothNormalBinomialBudget; split_ifs <;> positivity)
      · exact h1
      · exact pow_nonneg (rothLocalAbs_nonneg tau _) _
      · exact mul_nonneg (by unfold rothNormalBinomialBudget; split_ifs <;> positivity)
          (pow_nonneg hB _)
    _ = _ := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk]

noncomputable def rothNormalLocalExponent {m : ℕ} (tau : Fin 3)
    (Q : Fin m → ℝ) (c : Fin 3 → Fin 3 → ℝ) (delta : ℝ)
    (b : RothBlockVars m →₀ ℕ) : ℝ :=
  ∑ i : Fin 3, (c tau i - if tau = 0 then delta else 0) * rothNormalLogWeight Q b i

theorem rothNormal_log_total_lower {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ) * Real.log (Q h))
    (L : Matrix (Fin 3) (Fin 3) ℤ) (J b : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (hb : (rothLocalExpansion L J P).coeff b ≠ 0)
    (eta : ℝ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m) :
    A*(m : ℝ)*(1-2*eta) ≤ ∑ i : Fin 3, rothNormalLogWeight Q b i := by
  have hw := rothNormal_local_total_weight r hr L J b P hP hb
  have hlo : A * (∑ i : Fin 3, rothLocalCoordinateWeight r i b) ≤
      ∑ i : Fin 3, rothNormalLogWeight Q b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    unfold rothLocalCoordinateWeight rothNormalLogWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hratio : 0 ≤ (b (h,i) : ℝ) / r h := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have ht := mul_le_mul_of_nonneg_left (hlog h) hratio
    have hn : (r h : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr h)
    convert ht using 1 <;> field_simp [hn] <;> ring
  rw [hw] at hlo
  have hmul := mul_le_mul_of_nonneg_left hJ hA
  nlinarith

theorem rothNormal_source_exponent {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (eta delta A : ℝ)
    (heta : 0 < eta) (hdelta : 432*eta < delta) (hdeltalt : delta < 1)
    (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (c : Fin 3 → Fin 3 → ℝ) (hc : ∀ tau i, |c tau i| ≤ 1)
    (tau : Fin 3) (L : Matrix (Fin 3) (Fin 3) ℤ)
    (J b : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (hP : rothBlockHomogeneous r P)
    (hb : (rothLocalExpansion L J P).coeff b ≠ 0)
    (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hbalance : ∀ i : Fin 3,
      |rothLocalCoordinateWeight r i b - (m : ℝ)/3| ≤ 9*m*eta) :
    rothNormalLocalExponent tau Q c delta b ≤
      A*m*((∑ i : Fin 3, c tau i)/3 + if tau = 0 then -279*eta else 126*eta) := by
  have hdeg (h : Fin m) : (∑ i : Fin 3, b (h,i)) ≤ r h := by
    have hd := rothLocal_expansion_block_degree r L J P hP b hb h
    omega
  have ht := rothNormal_log_weight_transport r hr Q eta A heta.le hA hlog b hdeg hbalance
  have hnn : 0 ≤ 10*A*m*eta := by positivity
  have hterm (i : Fin 3) :
      c tau i * rothNormalLogWeight Q b i ≤ c tau i * (A*m/3) + 10*A*m*eta := by
    have hmul : |c tau i * (rothNormalLogWeight Q b i - A*m/3)| ≤ 10*A*m*eta := by
      calc
        _ = |c tau i| * |rothNormalLogWeight Q b i - A*m/3| := abs_mul _ _
        _ ≤ 1 * (10*A*m*eta) := mul_le_mul (hc tau i) (ht i) (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have ha := (le_abs_self (c tau i * (rothNormalLogWeight Q b i - A*m/3))).trans hmul
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hterm i)
  have hsimp : (∑ i : Fin 3, c tau i * rothNormalLogWeight Q b i) ≤
      (A*m/3)*(∑ i : Fin 3, c tau i) + 30*A*m*eta := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith [hs]
  by_cases htau : tau = 0
  · have hlower := rothNormal_log_total_lower r hr Q A hA (fun h => (hlog h).1)
      L J b P hP hb eta hJ
    have hetaSmall : eta < 1/432 := by linarith
    have hdeltaPos : 0 < delta := by linarith
    have hbudget : 405*eta ≤ delta*(1-2*eta) := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hA (Nat.cast_nonneg m))
    have hnegative := mul_le_mul_of_nonneg_left hlower hdeltaPos.le
    rw [htau] at hsimp
    simp only [rothNormalLocalExponent, htau, if_pos rfl, sub_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ite_true]
    nlinarith
  · simp only [rothNormalLocalExponent, if_neg htau, sub_zero]
    nlinarith

theorem rothNormal_local_support_card {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P) :
    (rothLocalExpansion L J P).support.card ≤ 3 ^ (∑ h, r h) := by
  let s : Fin m → ℕ := fun h => r h - ∑ i : Fin 3, J (h,i)
  have hs : (rothLocalExpansion L J P).support ⊆ Finset.univ.image (@rothAuxExponent m s) := by
    intro b hb
    have hdeg (h : Fin m) : (∑ i : Fin 3, b (h,i)) = s h :=
      rothLocal_expansion_block_degree r L J P hP b (MvPolynomial.mem_support_iff.mp hb) h
    have hle (h : Fin m) (i : Fin 3) : b (h,i) ≤ s h := by
      rw [← hdeg h]
      exact Finset.single_le_sum (f := fun j : Fin 3 => b (h,j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    let a : RothAuxCoefficients s := fun h =>
      ⟨fun i => ⟨b (h,i), by have hh := hle h i; omega⟩, hdeg h⟩
    refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
    ext u
    rfl
  calc
    _ ≤ (Finset.univ.image (@rothAuxExponent m s)).card := Finset.card_le_card hs
    _ ≤ Fintype.card (RothAuxCoefficients s) := Finset.card_image_le
    _ ≤ 3 ^ (∑ h, s h) := rothAuxDimension_le_three_pow s
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Finset.sum_le_sum (fun h _ => Nat.sub_le _ _))

theorem rothNormal_binomial_sum {m : ℕ} (b : RothBlockVars m →₀ ℕ) :
    (∑ k ∈ rothNormalSplits b, ∏ u : RothBlockVars m, (Nat.choose (b u) (k u) : ℝ)) =
      (2 : ℝ) ^ (∑ u : RothBlockVars m, b u) := by
  unfold rothNormalSplits
  rw [← Finset.prod_univ_sum (fun u : RothBlockVars m => Finset.range (b u + 1))
    (fun u k => (Nat.choose (b u) k : ℝ))]
  have hsum (u : RothBlockVars m) :
      (∑ k ∈ Finset.range (b u+1), (Nat.choose (b u) k : ℝ)) = (2 : ℝ) ^ b u := by
    exact_mod_cast Nat.sum_range_choose (b u)
  simp_rw [hsum]
  rw [Finset.prod_pow_eq_pow_sum]

theorem rothNormal_split_product_bound {m : ℕ} (tau : Fin 3)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 3 → Fin 3 → ℝ) (delta : ℝ)
    (hw : ∀ h j i, rothLocalAbs tau (rothNormalLocalValue L (w h j) i) ≤
      Real.rpow (Q h) (c tau i - if tau = 0 then delta else 0))
    (b : RothBlockVars m →₀ ℕ) (k : RothBlockVars m → ℕ)
    (hk : k ∈ rothNormalSplits b) :
    rothLocalAbs tau (∏ u : RothBlockVars m, rothNormalSplitScalar L w u (b u) (k u)) ≤
      (∏ u : RothBlockVars m, rothNormalBinomialBudget tau (b u) (k u)) *
        Real.exp (rothNormalLocalExponent tau Q c delta b) := by
  have hk' (u : RothBlockVars m) : k u ≤ b u := by
    have hh := (Fintype.mem_piFinset.mp hk) u
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  rw [rothNormalAbs_prod]
  calc
    _ ≤ ∏ u : RothBlockVars m, rothNormalBinomialBudget tau (b u) (k u) *
        (Real.rpow (Q u.1) (c tau u.2 - if tau = 0 then delta else 0)) ^ b u := by
      apply Finset.prod_le_prod
      · intro u hu
        exact rothLocalAbs_nonneg _ _
      · intro u hu
        exact rothNormal_split_bound tau L w u (b u) (k u) (hk' u) _
          (Real.rpow_nonneg (hQ u.1).le _) (fun j => hw u.1 j u.2)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      congr 1
      have hexp (u : RothBlockVars m) :
          (Real.rpow (Q u.1) (c tau u.2 - if tau = 0 then delta else 0)) ^ b u =
            Real.exp ((b u : ℝ) * (Real.log (Q u.1) * (c tau u.2 - if tau = 0 then delta else 0))) := by
        rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (hQ u.1), ← Real.exp_nat_mul]
      simp_rw [hexp]
      rw [← Real.exp_sum]
      congr 1
      unfold rothNormalLocalExponent rothNormalLogWeight
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring

theorem rothNormalAbs_sum {ι : Type*} (s : Finset ι) (x : ι → ℚ) :
    rothLocalAbs 0 (∑ i ∈ s, x i) ≤ ∑ i ∈ s, rothLocalAbs 0 (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [rothLocalAbs_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rothLocalAbs_add 0 _ _).trans (add_le_add_left ih _)

theorem rothNormal_coefficient_uniform_bound {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (hL : (rothLocalRationalMatrix L).det ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (tau : Fin 3) (E : ℝ) (hE : 0 ≤ E) (T : ℝ)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 3 → Fin 3 → ℝ) (delta : ℝ)
    (hw : ∀ h j i, rothLocalAbs tau (rothNormalLocalValue L (w h j) i) ≤
      Real.rpow (Q h) (c tau i - if tau = 0 then delta else 0))
    (hcoeff : ∀ b, rothLocalAbs tau ((rothLocalExpansion L J P).coeff b) ≤ E ^ (∑ h, r h))
    (hexponent : ∀ b ∈ (rothLocalExpansion L J P).support,
      rothNormalLocalExponent tau Q c delta b ≤ T)
    (e : RothNormalVars m →₀ ℕ) :
    rothLocalAbs tau ((rothNormalDerivativeRestriction w J P).coeff e) ≤
      (if tau = 0 then (8*E) ^ (∑ h, r h) else E ^ (∑ h, r h)) * Real.exp T := by
  let R := ∑ h, r h
  let D := rothLocalExpansion L J P
  let f := fun (b : RothBlockVars m →₀ ℕ) (k : RothBlockVars m → ℕ) =>
    if e = rothNormalConvolutionExponent b k then
      D.coeff b * ∏ u : RothBlockVars m, rothNormalSplitScalar L w u (b u) (k u)
    else 0
  have hterm (b : RothBlockVars m →₀ ℕ) (hb : b ∈ D.support)
      (k : RothBlockVars m → ℕ) (hk : k ∈ rothNormalSplits b) :
      rothLocalAbs tau (f b k) ≤ E^R *
        (∏ u : RothBlockVars m, rothNormalBinomialBudget tau (b u) (k u)) * Real.exp T := by
    have hbudget : 0 ≤ ∏ u : RothBlockVars m, rothNormalBinomialBudget tau (b u) (k u) :=
      Finset.prod_nonneg (fun u _ => by unfold rothNormalBinomialBudget; split_ifs <;> positivity)
    dsimp only [f]
    split_ifs with he
    · rw [rothLocalAbs_mul]
      calc
        _ ≤ E^R * ((∏ u : RothBlockVars m, rothNormalBinomialBudget tau (b u) (k u)) *
            Real.exp (rothNormalLocalExponent tau Q c delta b)) :=
          mul_le_mul (hcoeff b) (rothNormal_split_product_bound tau L w Q hQ c delta hw b k hk)
            (rothLocalAbs_nonneg _ _) (pow_nonneg hE _)
        _ ≤ E^R * ((∏ u : RothBlockVars m, rothNormalBinomialBudget tau (b u) (k u)) * Real.exp T) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexponent b hb)) hbudget) (pow_nonneg hE _)
        _ = _ := by ring
    · rw [rothLocalAbs_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg hE _) hbudget) (Real.exp_pos T).le
  rw [rothNormal_local_coefficient L hL w J P e]
  change rothLocalAbs tau (∑ b ∈ D.support, ∑ k ∈ rothNormalSplits b, f b k) ≤ _
  by_cases htau : tau = 0
  · subst tau
    have hinner (b : RothBlockVars m →₀ ℕ) (hb : b ∈ D.support) :
        rothLocalAbs 0 (∑ k ∈ rothNormalSplits b, f b k) ≤ E^R * (2:ℝ)^R * Real.exp T := by
      have htotal : (∑ u : RothBlockVars m, b u) ≤ R := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_le_sum
        intro h hh
        have hd := rothLocal_expansion_block_degree r L J P hP b (MvPolynomial.mem_support_iff.mp hb) h
        omega
      calc
        _ ≤ ∑ k ∈ rothNormalSplits b, rothLocalAbs 0 (f b k) := rothNormalAbs_sum _ _
        _ ≤ ∑ k ∈ rothNormalSplits b, E^R *
            (∏ u : RothBlockVars m, (Nat.choose (b u) (k u) : ℝ)) * Real.exp T := by
          apply Finset.sum_le_sum
          intro k hk
          simpa only [rothNormalBinomialBudget, if_pos rfl] using hterm b hb k hk
        _ = E^R * (2:ℝ)^(∑ u : RothBlockVars m, b u) * Real.exp T := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, rothNormal_binomial_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) htotal)
            (pow_nonneg hE _)) (Real.exp_pos T).le
    calc
      _ ≤ ∑ b ∈ D.support, rothLocalAbs 0 (∑ k ∈ rothNormalSplits b, f b k) := rothNormalAbs_sum _ _
      _ ≤ ∑ _b ∈ D.support, E^R * (2:ℝ)^R * Real.exp T := Finset.sum_le_sum hinner
      _ = (D.support.card : ℝ) * (E^R * (2:ℝ)^R * Real.exp T) := by simp
      _ ≤ (3:ℝ)^R * (E^R * (2:ℝ)^R * Real.exp T) := by
        have hcard : (D.support.card : ℝ) ≤ (3:ℝ)^R := by exact_mod_cast rothNormal_local_support_card r L J P hP
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (6*E)^R * Real.exp T := by
        rw [← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow]
        congr 1
        ring
      _ ≤ _ := by
        simp only [if_pos rfl]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by nlinarith) _) (Real.exp_pos T).le
  · simp only [if_neg htau]
    apply rothNormalAbs_sum_finite tau htau _ _ _ (mul_nonneg (pow_nonneg hE _) (Real.exp_pos T).le)
    intro b hb
    apply rothNormalAbs_sum_finite tau htau _ _ _ (mul_nonneg (pow_nonneg hE _) (Real.exp_pos T).le)
    intro k hk
    simpa only [rothNormalBinomialBudget, if_neg htau, Finset.prod_const_one, mul_one] using hterm b hb k hk

noncomputable def rothNormalSourceBound {m : ℕ} (tau : Fin 3) (E eta : ℝ)
    (r : Fin m → ℕ) (Q : Fin m → ℝ) (h0 : Fin m) (c : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (if tau = 0 then (8*E) ^ (∑ h, r h) else E ^ (∑ h, r h)) *
    Real.exp (((r h0 : ℝ)*Real.log (Q h0))*m*
      ((∑ i : Fin 3, c tau i)/3 + if tau = 0 then -279*eta else 126*eta))

theorem rothNormal_three_place_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ)
    (hL : ∀ tau, (rothLocalRationalMatrix (L tau)).det ≠ 0)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (eta E : ℝ) (heta : 0 < eta) (hE : 1 ≤ E)
    (hindex : ∀ tau i, rothSourceHighIndex r (fun _ => L tau i) ((1/3-eta)*m) P)
    (hlocal : ∀ (tau : Fin 3) (J b : RothBlockVars m →₀ ℕ),
      rothLocalAbs tau ((rothLocalExpansion (L tau) J P).coeff b) ≤ E^(∑ h, r h))
    (delta : ℝ) (c : Fin 3 → Fin 3 → ℝ) (Q : Fin m → ℝ) (h0 : Fin m)
    (_hcsum : (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0)
    (hc : ∀ tau i, |c tau i| ≤ 1) (hdelta : 432*eta < delta) (hdeltalt : delta < 1)
    (hQ : ∀ h, 1 < Q h)
    (_hEthreshold : ∀ h, 8*E < Real.rpow (Q h) eta)
    (_hgrid : ∀ h, 3*(eta⁻¹+1) < Real.rpow (Q h) eta)
    (hlog : ∀ h, (r h0 : ℝ)*Real.log (Q h0) ≤ (r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r h0 : ℝ)*Real.log (Q h0))
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (hw0 : ∀ h j i, rothLocalAbs 0 (rothNormalLocalValue (L 0) (w h j) i) ≤
      Real.rpow (Q h) (c 0 i-delta))
    (hw1 : ∀ h j i, rothLocalAbs 1 (rothNormalLocalValue (L 1) (w h j) i) ≤ Real.rpow (Q h) (c 1 i))
    (hw2 : ∀ h j i, rothLocalAbs 2 (rothNormalLocalValue (L 2) (w h j) i) ≤ Real.rpow (Q h) (c 2 i))
    (J : RothBlockVars m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (e : RothNormalVars m →₀ ℕ) (z : ℤ)
    (hz : (rothNormalDerivativeRestriction w J P).coeff e = (z : ℚ)) :
    ∀ tau : Fin 3, rothLocalAbs tau (z : ℚ) ≤ rothNormalSourceBound tau E eta r Q h0 c := by
  intro tau
  rw [← hz]
  have hA : 0 ≤ (r h0 : ℝ)*Real.log (Q h0) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (hQ h0)).le
  apply rothNormal_coefficient_uniform_bound r (L tau) (hL tau) w J P hP tau E
    (by linarith) _ Q (fun h => lt_trans zero_lt_one (hQ h)) c delta
  · fin_cases tau
    · simpa only [if_pos rfl] using hw0
    · simpa using hw1
    · simpa using hw2
  · exact hlocal tau J
  · intro b hb
    exact rothNormal_source_exponent r hr Q eta delta _ heta hdelta hdeltalt hA
      (fun h => by simpa only [mul_assoc] using hlog h) c hc tau
      (L tau) J b P hP (MvPolynomial.mem_support_iff.mp hb) hJ
      (rothLocal_coefficient_balance r hr eta heta (L tau) (hL tau) P hP (hindex tau)
        J b hJ (MvPolynomial.mem_support_iff.mp hb))

theorem roth_auxiliary_integer_satz34_coefficients
    (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ)
    (hL : ∀ tau, (rothLocalRationalMatrix (L tau)).det ≠ 0) :
    ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log 18 ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (RothBlockVars m) ℤ,
        P ≠ 0 ∧ rothBlockHomogeneous r P ∧
        (rothKernelBlockHeight P : ℝ) ≤ D^(∑ h, r h) ∧
        (∀ tau i, rothSourceHighIndex r (fun _ => L tau i) ((1/3-eta)*m) P) ∧
        ∀ (delta : ℝ) (c : Fin 3 → Fin 3 → ℝ) (Q : Fin m → ℝ) (h0 : Fin m),
          (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0 →
          (∀ tau i, |c tau i| ≤ 1) → 432*eta < delta → delta < 1 →
          (∀ h, 1 < Q h) →
          (∀ h, 8*E < Real.rpow (Q h) eta) →
          (∀ h, 3*(eta⁻¹+1) < Real.rpow (Q h) eta) →
          (∀ h, (r h0 : ℝ)*Real.log (Q h0) ≤ (r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r h0 : ℝ)*Real.log (Q h0)) →
          ∀ w : Fin m → Fin 2 → Fin 3 → ℤ,
            (∀ h j i, rothLocalAbs 0 (rothNormalLocalValue (L 0) (w h j) i) ≤
              Real.rpow (Q h) (c 0 i-delta)) →
            (∀ h j i, rothLocalAbs 1 (rothNormalLocalValue (L 1) (w h j) i) ≤ Real.rpow (Q h) (c 1 i)) →
            (∀ h j i, rothLocalAbs 2 (rothNormalLocalValue (L 2) (w h j) i) ≤ Real.rpow (Q h) (c 2 i)) →
            ∀ J : RothBlockVars m →₀ ℕ, rothSourceDerivativeWeight r J ≤ 2*eta*m →
              ∀ (e : RothNormalVars m →₀ ℕ) (z : ℤ),
                (rothNormalDerivativeRestriction w J P).coeff e = (z : ℚ) →
                ∀ tau : Fin 3, rothLocalAbs tau (z : ℚ) ≤ rothNormalSourceBound tau E eta r Q h0 c := by
  obtain ⟨D,E,hD,hE,hconstruction⟩ := roth_auxiliary_integer_satz33 L hL
  refine ⟨D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hP,hheight,hindex,hlocal,_hbalance⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hP,hheight,hindex,?_⟩
  intro delta c Q h0 hcsum hc hdelta hdeltalt hQ hEth hgrid hlog w hw0 hw1 hw2 J hJ e z hz
  exact rothNormal_three_place_bound r hr L hL P hP eta E heta hE hindex hlocal
    delta c Q h0 hcsum hc hdelta hdeltalt hQ hEth hgrid hlog w hw0 hw1 hw2 J hJ e z hz

theorem roth_auxiliary_integer_satz34_normal_coefficients
    (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ)
    (hL : ∀ tau, (rothLocalRationalMatrix (L tau)).det ≠ 0) :
    ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log 18 ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (RothBlockVars m) ℤ,
        P ≠ 0 ∧ rothBlockHomogeneous r P ∧
        (rothKernelBlockHeight P : ℝ) ≤ D^(∑ h, r h) ∧
        (∀ tau i, rothSourceHighIndex r (fun _ => L tau i) ((1/3-eta)*m) P) ∧
        ∀ (delta : ℝ) (c : Fin 3 → Fin 3 → ℝ) (Q : Fin m → ℝ) (h0 : Fin m),
          (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0 →
          (∀ tau i, |c tau i| ≤ 1) → 432*eta < delta → delta < 1 →
          (∀ h, 1 < Q h) →
          (∀ h, 8*E < Real.rpow (Q h) eta) →
          (∀ h, 3*(eta⁻¹+1) < Real.rpow (Q h) eta) →
          (∀ h, (r h0 : ℝ)*Real.log (Q h0) ≤ (r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r h0 : ℝ)*Real.log (Q h0)) →
          ∀ w : Fin m → Fin 2 → Fin 3 → ℤ,
            (∀ h j i, rothLocalAbs 0 (rothNormalLocalValue (L 0) (w h j) i) ≤
              Real.rpow (Q h) (c 0 i-delta)) →
            (∀ h j i, rothLocalAbs 1 (rothNormalLocalValue (L 1) (w h j) i) ≤ Real.rpow (Q h) (c 1 i)) →
            (∀ h j i, rothLocalAbs 2 (rothNormalLocalValue (L 2) (w h j) i) ≤ Real.rpow (Q h) (c 2 i)) →
            ∀ V : Fin m → Fin 3 → ℤ,
              (∀ h, (∃ i, V h i ≠ 0) ∧ Ideal.span (Set.range (V h)) = ⊤) →
              (∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ))) →
              (∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0) →
              ∀ J : RothBlockVars m →₀ ℕ, rothSourceDerivativeWeight r J ≤ 2*eta*m →
                ∀ k : Fin m → Fin 3, (∀ h, V h (k h) ≠ 0) →
                  rothKernelRestriction V k (rothBlockIntegerDividedDerivative J P) ≠ 0 →
                  ∃ (e : RothNormalVars m → ℕ) (z : ℤ),
                    e ∈ rothNormalFiniteExponents w J P ∧ z ≠ 0 ∧
                    (rothNormalDerivativeRestriction w J P).coeff (Finsupp.equivFunOnFinite.symm e) = (z : ℚ) ∧
                    ∀ tau : Fin 3, rothLocalAbs tau (z : ℚ) ≤ rothNormalSourceBound tau E eta r Q h0 c := by
  obtain ⟨D,E,hD,hE,hconstruction⟩ := roth_auxiliary_integer_satz34_coefficients L hL
  refine ⟨D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hP,hheight,hindex,hbounds⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hP,hheight,hindex,?_⟩
  intro delta c Q h0 hcsum hc hdelta hdeltalt hQ hEth hgrid hlog w hw0 hw1 hw2
  intro V hrow hli horth J hJ k hk hnonzero
  obtain ⟨e,z,he,hnz,hz⟩ :=
    ((rothNormal_kernel_basis_bridge V hrow w hli horth J P).2 k hk).mp hnonzero
  refine ⟨e,z,he,hnz,hz,?_⟩
  exact hbounds delta c Q h0 hcsum hc hdelta hdeltalt hQ hEth hgrid hlog w hw0 hw1 hw2
    J hJ (Finsupp.equivFunOnFinite.symm e) z hz


end JSP000334
