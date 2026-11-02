import SubspaceBridge.BinaryAuxMatrix2
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators Classical
namespace JSP000334
theorem binary_derivative_coeff {m : ℕ} (J e : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    (binaryDividedDerivative J P).coeff e =
      P.coeff (e+J)*∏ u : RothBlockVars2 m, (Nat.choose ((e+J) u) (J u) : ℤ) := by
  rw [binaryDividedDerivative,MvPolynomial.sum_def,MvPolynomial.coeff_sum]
  calc
    _ = (MvPolynomial.monomial ((e+J)-J)
        (P.coeff (e+J)*∏ u : RothBlockVars2 m, (Nat.choose ((e+J) u) (J u) : ℤ))).coeff e := by
      apply Finset.sum_eq_single (e+J)
      · intro b hb hne
        by_cases hle : J ≤ b
        · have he : b-J ≠ e := by
            intro heq
            apply hne
            calc
              b = (b-J)+J := (tsub_add_cancel_of_le hle).symm
              _ = _ := by rw [heq]
          simp [MvPolynomial.coeff_monomial,he]
        · change ¬ ∀ u, J u ≤ b u at hle
          push_neg at hle
          obtain ⟨u,hu⟩ := hle
          have hz : (∏ u : RothBlockVars2 m, (Nat.choose (b u) (J u) : ℤ)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ u)
            simp [Nat.choose_eq_zero_of_lt hu]
          simp [hz]
      · intro hn
        have hz := MvPolynomial.not_mem_support_iff.mp hn
        simp [hz]
    _ = _ := by simp

theorem binary_transformed_coeff_sum {m : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → RothBlockVars2 m →₀ ℕ) (c : ι → ℤ) (J d : RothBlockVars2 m →₀ ℕ)
    (S : MvPolynomial (RothBlockVars2 m) ℤ →+* MvPolynomial (RothBlockVars2 m) ℤ) :
    (S (binaryDividedDerivative J (∑ b, MvPolynomial.monomial (e b) (c b)))).coeff d =
      ∑ b, c b*(S (binaryDividedDerivative J (MvPolynomial.monomial (e b) 1))).coeff d := by
  have hadd : binaryDividedDerivative J (∑ b, MvPolynomial.monomial (e b) (c b)) =
      ∑ b, binaryDividedDerivative J (MvPolynomial.monomial (e b) (c b)) := by
    apply MvPolynomial.ext
    intro f
    simp only [binary_derivative_coeff,MvPolynomial.coeff_sum,Finset.sum_mul]
  rw [hadd,map_sum,MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [binary_derivative_monomial,binary_derivative_monomial]
  simp only [one_mul]
  have hc : MvPolynomial.monomial (e b-J)
      (c b*∏ u : RothBlockVars2 m, (Nat.choose (e b u) (J u) : ℤ)) =
      MvPolynomial.C (c b)*MvPolynomial.monomial (e b-J)
        (∏ u : RothBlockVars2 m, (Nat.choose (e b u) (J u) : ℤ)) := by
    rw [MvPolynomial.C_mul_monomial]
  rw [hc,map_mul]
  have hC : S (MvPolynomial.C (c b)) = MvPolynomial.C (c b) := map_intCast S (c b)
  rw [hC,MvPolynomial.coeff_C_mul]

theorem binary_transformed_polynomial {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 2 → ℤ) (k : Fin 2) (J : RothBlockVars2 m →₀ ℕ)
    (c : BinaryAuxCoefficients r → ℤ) :
    binaryScaledSubstitution a k (binaryDividedDerivative J (binaryAuxPolynomial c)) =
      ∑ b, MvPolynomial.C (c b)*binaryScaledSubstitution a k
        (binaryDividedDerivative J (MvPolynomial.monomial (binaryAuxExponent b) 1)) := by
  apply MvPolynomial.ext
  intro d
  rw [binaryAuxPolynomial,binary_transformed_coeff_sum]
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul]

theorem binary_matrix_mulVec {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (c : BinaryAuxCoefficients r → ℤ) (q : BinaryAuxEquations r eta) :
    (binaryAuxMatrix r eta L hL).mulVec c q =
      (binaryScaledSubstitution (L q.1.1 q.1.2) (binaryAuxPivot L hL q.1)
        (binaryDividedDerivative (binaryPivotDerivative (binaryAuxPivot L hL q.1) (fun h => (q.2.val h).val))
          (binaryAuxPolynomial c))).coeff
            (binaryFreeExponent (binaryAuxPivot L hL q.1) (fun h => r h-(q.2.val h).val)) := by
  rw [binary_transformed_polynomial,MvPolynomial.coeff_sum]
  simp only [Matrix.mulVec,dotProduct,binaryAuxMatrix,MvPolynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem binary_weight_block {m : ℕ} (e : RothBlockVars2 m →₀ ℕ) (h : Fin m) :
    Finsupp.weight (fun u : RothBlockVars2 m => if u.1=h then 1 else 0) e =
      ∑ j : Fin 2, e (h,j) := by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type,nsmul_eq_mul,mul_ite,ite_mul,one_mul,zero_mul,mul_one,mul_zero]
  calc
    _ = ∑ g : Fin m, if g=h then (∑ j : Fin 2, e (g,j)) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : g=h <;> simp [hg]
    _ = _ := by simp

theorem binary_weight_pivot {m : ℕ} (e : RothBlockVars2 m →₀ ℕ) (k : Fin 2) :
    Finsupp.weight (fun u : RothBlockVars2 m => if u.2=k then 1 else 0) e = ∑ h, e (h,k) := by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type,nsmul_eq_mul]

theorem binary_chart_block_weight {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2)
    (h : Fin m) (u : RothBlockVars2 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars2 m => if v.1=h then 1 else 0)
      (binaryScaledChart a k u) (if u.1=h then 1 else 0) := by
  let w := fun v : RothBlockVars2 m => if v.1=h then 1 else 0
  have hx (c : ℤ) (j : Fin 2) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C c*MvPolynomial.X (u.1,j)) (if u.1=h then 1 else 0) := by
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w c).mul (MvPolynomial.isWeightedHomogeneous_X ℤ w (u.1,j))
  unfold binaryScaledChart
  by_cases hu : u.2=k
  · rw [if_pos hu]
    exact hx _ _
  · rw [if_neg hu]
    exact hx _ _

theorem binary_chart_pivot_weight {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2)
    (u : RothBlockVars2 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars2 m => if v.2=k then 1 else 0)
      (binaryScaledChart a k u) 0 := by
  let w := fun v : RothBlockVars2 m => if v.2=k then 1 else 0
  have hx (c : ℤ) (j : Fin 2) (hj : j ≠ k) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C c*MvPolynomial.X (u.1,j)) 0 := by
    simpa only [w,hj,if_false,zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w c).mul (MvPolynomial.isWeightedHomogeneous_X ℤ w (u.1,j))
  unfold binaryScaledChart
  split_ifs with hu
  · apply hx
    fin_cases k <;> decide
  · exact hx _ _ hu

theorem binary_scaled_monomial_weighted {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2)
    (J e : RothBlockVars2 m →₀ ℕ) (w v : RothBlockVars2 m → ℕ)
    (hv : ∀ u, MvPolynomial.IsWeightedHomogeneous w (binaryScaledChart a k u) (v u)) :
    MvPolynomial.IsWeightedHomogeneous w
      (binaryScaledSubstitution a k (binaryDividedDerivative J (MvPolynomial.monomial e 1)))
      (∑ u : RothBlockVars2 m, (e-J) u*v u) := by
  rw [binary_scaled_derivative_monomial]
  have hh := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : RothBlockVars2 m => binaryScaledChart a k u ^ (e-J) u)
    (fun u => (e-J) u*v u)
    (fun u _ => by simpa only [nsmul_eq_mul] using (hv u).pow ((e-J) u))
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w _).mul hh

theorem binary_pivot_monomial_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 2 → ℤ) (k : Fin 2) (i : Fin m → ℕ) (b : BinaryAuxCoefficients r) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : RothBlockVars2 m => if u.1=h then 1 else 0)
      (binaryScaledSubstitution a k (binaryDividedDerivative (binaryPivotDerivative k i)
        (MvPolynomial.monomial (binaryAuxExponent b) 1))) (r h-i h) := by
  let J := binaryPivotDerivative k i
  let w := fun u : RothBlockVars2 m => if u.1=h then 1 else 0
  by_cases hle : J ≤ binaryAuxExponent b
  · have hh := binary_scaled_monomial_weighted a k J (binaryAuxExponent b) w w (binary_chart_block_weight a k h)
    have he : (∑ u : RothBlockVars2 m, (binaryAuxExponent b-J) u*w u) =
        ∑ j : Fin 2, (binaryAuxExponent b-J) (h,j) := by
      have he := binary_weight_block (binaryAuxExponent b-J) h
      rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)] at he
      simpa only [nsmul_eq_mul,w] using he
    have hd : (∑ j : Fin 2, (binaryAuxExponent b-J) (h,j)) = r h-i h := by
      change (∑ j : Fin 2, (binaryAuxExponent b (h,j)-J (h,j))) = _
      rw [Finset.sum_tsub_distrib _ (fun j _ => hle (h,j)),binary_exponent_block]
      congr 1
      simp [J,binaryPivotDerivative,Finset.sum_ite_eq,Finset.sum_ite_eq']
    rw [he,hd] at hh
    exact hh
  · change ¬ ∀ u, J u ≤ binaryAuxExponent b u at hle
    push_neg at hle
    obtain ⟨u,hu⟩ := hle
    have hz : (∏ v : RothBlockVars2 m, (Nat.choose (binaryAuxExponent b v) (J v) : ℤ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [Nat.choose_eq_zero_of_lt hu]
    rw [binary_scaled_derivative_monomial,hz,map_zero,zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero ℤ w _

theorem binary_transformed_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 2 → ℤ) (k : Fin 2) (i : Fin m → ℕ) (c : BinaryAuxCoefficients r → ℤ) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : RothBlockVars2 m => if u.1=h then 1 else 0)
      (binaryScaledSubstitution a k (binaryDividedDerivative (binaryPivotDerivative k i)
        (binaryAuxPolynomial c))) (r h-i h) := by
  rw [binary_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul
    (binary_pivot_monomial_block_weight a k i b h)

theorem binary_transformed_pivot_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 2 → ℤ) (k : Fin 2) (J : RothBlockVars2 m →₀ ℕ) (c : BinaryAuxCoefficients r → ℤ) :
    MvPolynomial.IsWeightedHomogeneous (fun u : RothBlockVars2 m => if u.2=k then 1 else 0)
      (binaryScaledSubstitution a k (binaryDividedDerivative J (binaryAuxPolynomial c))) 0 := by
  rw [binary_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  have hh := binary_scaled_monomial_weighted a k J (binaryAuxExponent b)
    (fun u : RothBlockVars2 m => if u.2=k then 1 else 0) (fun _ => 0) (binary_chart_pivot_weight a k)
  simp only [mul_zero,Finset.sum_const_zero] at hh
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul hh

theorem binary_transformed_support {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 2 → ℤ) (k : Fin 2) (i : Fin m → ℕ) (c : BinaryAuxCoefficients r → ℤ)
    (e : RothBlockVars2 m →₀ ℕ)
    (he : (binaryScaledSubstitution a k (binaryDividedDerivative (binaryPivotDerivative k i)
      (binaryAuxPolynomial c))).coeff e ≠ 0) :
    e = binaryFreeExponent k (fun h => r h-i h) := by
  have hb (h : Fin m) := binary_transformed_block_weight a k i c h he
  simp_rw [binary_weight_block] at hb
  have hp := binary_transformed_pivot_weight a k (binaryPivotDerivative k i) c he
  rw [binary_weight_pivot] at hp
  have hz (h : Fin m) : e (h,k) = 0 := by
    have hh := Finset.single_le_sum (fun g _ => Nat.zero_le (e (g,k))) (Finset.mem_univ h)
    omega
  apply Finsupp.ext
  rintro ⟨h,j⟩
  have hs := hb h
  have hh := hz h
  fin_cases k <;> fin_cases j <;> simp [binaryFreeExponent,Fin.sum_univ_two] at * <;> omega

theorem binary_pivot_coefficient_zero_iff {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 2 → ℤ) (k : Fin 2) (i : Fin m → ℕ) (c : BinaryAuxCoefficients r → ℤ) :
    (binaryScaledSubstitution a k (binaryDividedDerivative (binaryPivotDerivative k i)
      (binaryAuxPolynomial c))).coeff (binaryFreeExponent k (fun h => r h-i h)) = 0 ↔
    binaryScaledSubstitution a k (binaryDividedDerivative (binaryPivotDerivative k i)
      (binaryAuxPolynomial c)) = 0 := by
  constructor
  · intro hz
    apply MvPolynomial.ext
    intro e
    simp only [MvPolynomial.coeff_zero]
    by_cases he : (binaryScaledSubstitution a k (binaryDividedDerivative (binaryPivotDerivative k i)
        (binaryAuxPolynomial c))).coeff e = 0
    · exact he
    · rw [binary_transformed_support a k i c e he]
      exact hz
  · intro hz
    rw [hz,MvPolynomial.coeff_zero]

theorem binary_matrix_kernel_iff {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (c : BinaryAuxCoefficients r → ℤ) :
    (binaryAuxMatrix r eta L hL).mulVec c = 0 ↔
      ∀ f : Fin 3 × Fin 2, ∀ i : BinaryAuxCoefficients r,
        (∑ h, ((i h).val : ℝ)/(r h : ℝ)) < (1/2-eta)*m →
        binaryScaledSubstitution (L f.1 f.2) (binaryAuxPivot L hL f)
          (binaryDividedDerivative (binaryPivotDerivative (binaryAuxPivot L hL f) (fun h => (i h).val))
            (binaryAuxPolynomial c)) = 0 := by
  constructor
  · intro hk f i hi
    apply (binary_pivot_coefficient_zero_iff _ _ _ _).mp
    let q : BinaryAuxEquations r eta := ⟨f,⟨i,(binary_aux_bad_iff r eta i).mpr hi⟩⟩
    have hh := congrFun hk q
    rw [binary_matrix_mulVec] at hh
    exact hh
  · intro hz
    funext q
    rw [binary_matrix_mulVec]
    exact (binary_pivot_coefficient_zero_iff _ _ _ _).mpr
      (hz q.1 q.2.val ((binary_aux_bad_iff r eta q.2.val).mp q.2.property))

end JSP000334
