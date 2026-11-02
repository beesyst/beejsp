import SubspaceBridge.BinaryIntegerBridge2
open scoped BigOperators Classical
namespace JSP000334
theorem binaryNormal_local_order_le {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 2) (Fin 2) ℤ) (J b : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (hb : (binaryLocalExpansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ i : Fin 2, J (h,i)) ≤ r h := by
  by_contra! hbad
  have hz := binary_source_derivative_zero_of_block_excess r P hP J h hbad
  apply hb
  simp [binaryLocalExpansion, hz]

theorem binaryNormal_local_total_weight {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 2) (Fin 2) ℤ)
    (J b : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hP : binaryBlockHomogeneous r P)
    (hb : (binaryLocalExpansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 2, binaryLocalCoordinateWeight r i b) =
      (m : ℝ) - binarySourceDerivativeWeight r J := by
  unfold binaryLocalCoordinateWeight binarySourceDerivativeWeight
  have hm : (m : ℝ) = ∑ _h : Fin m, (1 : ℝ) := by simp
  rw [Finset.sum_comm, hm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_div]
  have hd := binaryLocal_expansion_block_degree r L J P hP b hb h
  have hle := binaryNormal_local_order_le r L J b P hP hb h
  have hdR : (∑ i : Fin 2, (b (h,i) : ℝ)) = (r h : ℝ) - ∑ i : Fin 2, (J (h,i) : ℝ) := by
    have hh : (∑ i : Fin 2, (b (h,i) : ℝ)) + (∑ i : Fin 2, (J (h,i) : ℝ)) = (r h : ℝ) := by
      exact_mod_cast (show (∑ i : Fin 2, b (h,i)) + (∑ i : Fin 2, J (h,i)) = r h by omega)
    linarith
  rw [hdR]
  have hpos : (0 : ℝ) < r h := by exact_mod_cast hr h
  field_simp [ne_of_gt hpos]

noncomputable def binaryNormalLogWeight {m : ℕ} (Q : Fin m → ℝ)
    (b : RothBlockVars2 m →₀ ℕ) (i : Fin 2) : ℝ :=
  ∑ h : Fin m, (b (h,i) : ℝ) * Real.log (Q h)

theorem binaryNormal_log_weight_transport {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (eta A : ℝ)
    (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ) * Real.log (Q h) ∧
      (r h : ℝ) * Real.log (Q h) ≤ (1+eta)*A)
    (b : RothBlockVars2 m →₀ ℕ)
    (hdegree : ∀ h, (∑ i : Fin 2, b (h,i)) ≤ r h)
    (hbalance : ∀ i : Fin 2,
      |binaryLocalCoordinateWeight r i b - (m : ℝ)/2| ≤ 3*m*eta) :
    ∀ i : Fin 2, |binaryNormalLogWeight Q b i - A*(m : ℝ)/2| ≤ 4*A*m*eta := by
  intro i
  have hnorm : 0 ≤ binaryLocalCoordinateWeight r i b ∧
      binaryLocalCoordinateWeight r i b ≤ (m : ℝ) := by
    constructor
    · unfold binaryLocalCoordinateWeight
      exact Finset.sum_nonneg (fun h _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · unfold binaryLocalCoordinateWeight
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
  have hlo : A * binaryLocalCoordinateWeight r i b ≤ binaryNormalLogWeight Q b i := by
    unfold binaryLocalCoordinateWeight binaryNormalLogWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [hterm]
    calc
      A * ((b (h,i) : ℝ) / r h) = ((b (h,i) : ℝ) / r h) * A := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlog h).1
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hhi : binaryNormalLogWeight Q b i ≤ (1+eta)*A*binaryLocalCoordinateWeight r i b := by
    unfold binaryLocalCoordinateWeight binaryNormalLogWeight
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

noncomputable def binaryNormalLocalExponent {m : ℕ} (tau : Fin 3)
    (Q : Fin m → ℝ) (c : Fin 3 → Fin 2 → ℝ) (delta : ℝ)
    (b : RothBlockVars2 m →₀ ℕ) : ℝ :=
  ∑ i : Fin 2, (c tau i - if tau = 0 then delta else 0) * binaryNormalLogWeight Q b i

theorem binaryNormal_log_total_lower {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ) * Real.log (Q h))
    (L : Matrix (Fin 2) (Fin 2) ℤ) (J b : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (hb : (binaryLocalExpansion L J P).coeff b ≠ 0)
    (eta : ℝ) (hJ : binarySourceDerivativeWeight r J ≤ 2*eta*m) :
    A*(m : ℝ)*(1-2*eta) ≤ ∑ i : Fin 2, binaryNormalLogWeight Q b i := by
  have hw := binaryNormal_local_total_weight r hr L J b P hP hb
  have hlo : A * (∑ i : Fin 2, binaryLocalCoordinateWeight r i b) ≤
      ∑ i : Fin 2, binaryNormalLogWeight Q b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    unfold binaryLocalCoordinateWeight binaryNormalLogWeight
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

theorem binaryNormal_source_exponent {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (eta delta A : ℝ)
    (heta : 0 < eta) (hdelta : 40*eta < delta) (hdeltalt : delta < 1)
    (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (c : Fin 3 → Fin 2 → ℝ) (hc : ∀ tau i, |c tau i| ≤ 1)
    (tau : Fin 3) (L : Matrix (Fin 2) (Fin 2) ℤ)
    (J b : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hP : binaryBlockHomogeneous r P)
    (hb : (binaryLocalExpansion L J P).coeff b ≠ 0)
    (hJ : binarySourceDerivativeWeight r J ≤ 2*eta*m)
    (hbalance : ∀ i : Fin 2,
      |binaryLocalCoordinateWeight r i b - (m : ℝ)/2| ≤ 3*m*eta) :
    binaryNormalLocalExponent tau Q c delta b ≤
      A*m*((∑ i : Fin 2, c tau i)/2 + if tau = 0 then -30*eta else 8*eta) := by
  have hdeg (h : Fin m) : (∑ i : Fin 2, b (h,i)) ≤ r h := by
    have hd := binaryLocal_expansion_block_degree r L J P hP b hb h
    omega
  have ht := binaryNormal_log_weight_transport r hr Q eta A heta.le hA hlog b hdeg hbalance
  have hnn : 0 ≤ 4*A*m*eta := by positivity
  have hterm (i : Fin 2) :
      c tau i * binaryNormalLogWeight Q b i ≤ c tau i * (A*m/2) + 4*A*m*eta := by
    have hmul : |c tau i * (binaryNormalLogWeight Q b i - A*m/2)| ≤ 4*A*m*eta := by
      calc
        _ = |c tau i| * |binaryNormalLogWeight Q b i - A*m/2| := abs_mul _ _
        _ ≤ 1 * (4*A*m*eta) := mul_le_mul (hc tau i) (ht i) (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have ha := (le_abs_self (c tau i * (binaryNormalLogWeight Q b i - A*m/2))).trans hmul
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hterm i)
  have hsimp : (∑ i : Fin 2, c tau i * binaryNormalLogWeight Q b i) ≤
      (A*m/2)*(∑ i : Fin 2, c tau i) + 8*A*m*eta := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith [hs]
  by_cases htau : tau = 0
  · have hlower := binaryNormal_log_total_lower r hr Q A hA (fun h => (hlog h).1)
      L J b P hP hb eta hJ
    have hetaSmall : eta < 1/40 := by linarith
    have hdeltaPos : 0 < delta := by linarith
    have hbudget : 38*eta ≤ delta*(1-2*eta) := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hA (Nat.cast_nonneg m))
    have hnegative := mul_le_mul_of_nonneg_left hlower hdeltaPos.le
    rw [htau] at hsimp
    simp only [binaryNormalLocalExponent, htau, if_pos rfl, sub_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ite_true]
    nlinarith
  · simp only [binaryNormalLocalExponent, if_neg htau, sub_zero]
    nlinarith

end JSP000334
