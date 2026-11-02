import SubspaceBridge.SourceEvaluation6
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary6.SourceGrid
open SourceExpansion SourceSupport SourceBalance SourceEvaluation

theorem evaluation_upper {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (hA : A.det ≠ 0)
    (r : Fin m → ℕ) (J : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) ℤ)
    (hP : homogeneous6 r P) (v : Fin m → Fin 6 → ℤ)
    (E T : ℝ) (hE : 0 ≤ E) (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 6 → ℝ)
    (hv : ∀ h i, ‖(A *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i))
    (hc : ∀ b, ‖(expansion A J P).coeff b‖ ≤ E^(∑ h, r h))
    (ht : ∀ b ∈ (expansion A J P).support, (∑ i, c i * logWeight Q b i) ≤ T) :
    ‖(integerValue J P v : K)‖ ≤ (64*E)^(∑ h, r h)*Real.exp T := by
  rw [evaluation_identity A hA J P v]
  calc
    _ ≤ ∑ b ∈ (expansion A J P).support, ‖(expansion A J P).coeff b *
        ∏ u : Vars6 m, ((A *ᵥ (fun i => (v u.1 i : K))) u.2)^b u‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ (expansion A J P).support, E^(∑ h, r h)*Real.exp T := by
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul]
      exact (mul_le_mul (hc b) (monomial_bound A v Q hQ c hv b)
        (norm_nonneg _) (pow_nonneg hE _)).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (ht b hb)) (pow_nonneg hE _))
    _ = ((expansion A J P).support.card : ℝ)*(E^(∑ h, r h)*Real.exp T) := by simp
    _ ≤ (64 : ℝ)^(∑ h, r h)*(E^(∑ h, r h)*Real.exp T) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast expansion_support_card r A J P hP
    _ = _ := by rw [← mul_assoc, ← mul_pow]

def gridPoint {m : ℕ} (w : Fin m → Fin 5 → Fin 6 → ℤ)
    (a : Fin m → Fin 5 → ℕ) : Fin m → Fin 6 → ℤ :=
  fun h i => ∑ j, (a h j : ℤ)*w h j i

theorem matrix_grid {K : Type*} [CommRing K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (w : Fin m → Fin 5 → Fin 6 → ℤ)
    (a : Fin m → Fin 5 → ℕ) (h : Fin m) (i : Fin 6) :
    (A *ᵥ (fun k => (gridPoint w a h k : K))) i =
      ∑ j : Fin 5, (a h j : K)*(A *ᵥ (fun k => (w h j k : K))) i := by
  simp only [gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast,
    Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem grid_form_norm {K : Type*} [NormedField K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (w : Fin m → Fin 5 → Fin 6 → ℤ)
    (a : Fin m → Fin 5 → ℕ) (h : Fin m) (i : Fin 6) (U B : ℝ)
    (hU : 0 ≤ U) (ha : ∀ j, ‖(a h j : K)‖ ≤ U)
    (hw : ∀ j, ‖(A *ᵥ (fun k => (w h j k : K))) i‖ ≤ B) :
    ‖(A *ᵥ (fun k => (gridPoint w a h k : K))) i‖ ≤ 5*U*B := by
  rw [matrix_grid]
  calc
    _ ≤ ∑ j : Fin 5, ‖(a h j : K)*(A *ᵥ (fun k => (w h j k : K))) i‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 5, U*B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (ha j) (hw j) (norm_nonneg _) hU
    _ = _ := by simp; ring

theorem real_multiplier {m : ℕ} (a : Fin m → Fin 5 → ℕ) (eta : ℝ) (heta : 0 < eta)
    (ha : ∀ h j, a h j ≤ Nat.floor eta⁻¹+1) (h : Fin m) (j : Fin 5) :
    ‖(a h j : ℝ)‖ ≤ eta⁻¹+1 := by
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hh : (a h j : ℝ) ≤ (Nat.floor eta⁻¹ : ℝ)+1 := by exact_mod_cast ha h j
  exact hh.trans (add_le_add_right (Nat.floor_le (inv_nonneg.mpr heta.le)) 1)

theorem padic_multiplier (p : ℕ) [Fact p.Prime] (a : ℕ) : ‖(a : ℚ_[p])‖ ≤ 1 := by
  have hh : (padicNorm p (a : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast padicNorm.of_int (p := p) (a : ℤ)
  simpa only [← finite_norm p,map_natCast] using hh

theorem grid_form_rpow {K : Type*} [NormedField K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (w : Fin m → Fin 5 → Fin 6 → ℤ)
    (a : Fin m → Fin 5 → ℕ) (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 6 → ℝ) (eta U : ℝ) (hU : 0 ≤ U)
    (ha : ∀ h j, ‖(a h j : K)‖ ≤ U) (hg : ∀ h, 5*U ≤ (Q h)^eta)
    (hw : ∀ h j i, ‖(A *ᵥ (fun k => (w h j k : K))) i‖ ≤ (Q h)^(c i)) :
    ∀ h i, ‖(A *ᵥ (fun k => (gridPoint w a h k : K))) i‖ ≤ (Q h)^(c i+eta) := by
  intro h i
  calc
    _ ≤ 5*U*(Q h)^(c i) := grid_form_norm A w a h i U _ hU (ha h) (fun j => hw h j i)
    _ ≤ (Q h)^eta*(Q h)^(c i) := mul_le_mul_of_nonneg_right (hg h) (Real.rpow_pos_of_pos (hQ h) _).le
    _ = _ := by rw [← Real.rpow_add (hQ h)]; congr 1; ring

theorem log_total_bounds {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (eta A : ℝ) (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (J b : Vars6 m →₀ ℕ)
    (hdegree : ∀ h, (∑ i : Fin 6, b (h,i)) = r h - ∑ i : Fin 6, J (h,i))
    (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m) :
    A*m*(1-2*eta) ≤ ∑ i : Fin 6, logWeight Q b i ∧
      (∑ i : Fin 6, logWeight Q b i) ≤ (1+eta)*A*m := by
  have hdeg (h : Fin m) : (∑ i : Fin 6, b (h,i)) ≤ r h := by rw [hdegree h]; exact Nat.sub_le _ _
  have hweights : (m : ℝ) ≤ (∑ i : Fin 6, coordinateWeight r i b) + rothSourceDerivativeWeight r J := by
    unfold coordinateWeight rothSourceDerivativeWeight
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _h : Fin m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro h hh
        rw [← Finset.sum_div, ← add_div]
        apply (le_div_iff₀ (by exact_mod_cast hr h)).mpr
        simp only [one_mul]
        have hn : r h ≤ (∑ i : Fin 6, b (h,i)) + ∑ i : Fin 6, J (h,i) := by
          rw [hdegree h]
          omega
        exact_mod_cast hn
  have hlo : A*(∑ i : Fin 6, coordinateWeight r i b) ≤ ∑ i : Fin 6, logWeight Q b i := by
    unfold coordinateWeight logWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have ht := mul_le_mul_of_nonneg_left (hlog h).1
      (show 0 ≤ (b (h,i) : ℝ)/(r h : ℝ) from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hn : (r h : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr h)
    convert ht using 1 <;> field_simp [hn] <;> ring
  constructor
  · have hs := mul_le_mul_of_nonneg_left (show (m : ℝ)-2*eta*m ≤ ∑ i : Fin 6, coordinateWeight r i b by linarith) hA
    nlinarith
  · unfold logWeight
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ h : Fin m, (1+eta)*A := by
        apply Finset.sum_le_sum
        intro h hh
        rw [← Finset.sum_mul]
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg h) (Real.log_pos (hQ h)).le).trans (hlog h).2
      _ = _ := by simp; ring

theorem weighted_log_upper {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (eta A : ℝ) (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (b : Vars6 m →₀ ℕ) (hdegree : ∀ h, (∑ i : Fin 6, b (h,i)) ≤ r h)
    (hbalance : ∀ i, |coordinateWeight r i b - (m : ℝ)/6| ≤ 18*eta*m)
    (c : Fin 6 → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    (∑ i : Fin 6, c i * logWeight Q b i) ≤ A*m/6*(∑ i, c i)+114*A*m*eta := by
  have ht := log_weight_transport r hr Q eta A heta hA hlog b hdegree hbalance
  have hterm (i : Fin 6) : c i*logWeight Q b i ≤ c i*(A*m/6)+19*A*m*eta := by
    have hh : |c i*(logWeight Q b i-A*m/6)| ≤ 19*A*m*eta := by
      rw [abs_mul]
      exact (mul_le_mul (hc i) (ht i) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have hh' := (le_abs_self _).trans hh
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hterm i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  nlinarith

theorem source_exponents {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (eta delta A : ℝ)
    (heta : 0 < eta) (hd : 1728*eta < delta) (hd1 : delta < 1) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (J b : Vars6 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hdegree : ∀ h, (∑ i : Fin 6, b (h,i)) = r h - ∑ i : Fin 6, J (h,i))
    (hbalance : ∀ i, |coordinateWeight r i b - (m : ℝ)/6| ≤ 18*eta*m)
    (c : Fin 6 → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    (∑ i : Fin 6, (c i-delta+eta)*logWeight Q b i) ≤ A*m*((∑ i,c i)/6-1116*eta) ∧
    (∑ i : Fin 6, (c i+eta)*logWeight Q b i) ≤ A*m*((∑ i,c i)/6+504*eta) := by
  have hdeg (h : Fin m) : (∑ i : Fin 6, b (h,i)) ≤ r h := by rw [hdegree h]; exact Nat.sub_le _ _
  have hw := weighted_log_upper r hr Q eta A heta.le hA hlog b hdeg hbalance c hc
  have ht := log_total_bounds r hr Q hQ eta A heta.le hA hlog J b hdegree hJ
  have heta1 : eta < 1 := by linarith
  have hdeta : 0 ≤ delta-eta := by linarith
  have he : delta*eta < eta := by nlinarith
  have hbudget : 1230*eta ≤ (delta-eta)*(1-2*eta) := by nlinarith [sq_nonneg eta]
  have hs := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ A*(m : ℝ) by positivity)
  have hn := mul_le_mul_of_nonneg_left ht.1 hdeta
  have hp := mul_le_mul_of_nonneg_left ht.2 heta.le
  have he2 : eta*(1+eta) ≤ 2*eta := by nlinarith
  have hs2 := mul_le_mul_of_nonneg_left he2 (show 0 ≤ A*(m : ℝ) by positivity)
  constructor
  · simp only [sub_add,sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith
  · simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
    nlinarith

theorem local_upper {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (B : Matrix (Fin 6) (Fin 6) K) (hB : B.det ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (eta delta A E : ℝ) (heta : 0 < eta) (hd : 1728*eta < delta) (hd1 : delta < 1)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) (hclaims : Claims r eta B P)
    (hcfs : ∀ J b, ‖(expansion B J P).coeff b‖ ≤ E^(∑ h, r h))
    (c : Fin 6 → ℝ) (hc : ∀ i, |c i| ≤ 1) (arch : Bool)
    (v : Fin m → Fin 6 → ℤ)
    (hv : ∀ h i, ‖(B *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i-(if arch then delta else 0)+eta))
    (J : Vars6 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m) :
    ‖(integerValue J P v : K)‖ ≤ (64*E)^(∑ h, r h)*
      Real.exp (A*m*((∑ i,c i)/6+(if arch then -1116*eta else 504*eta))) := by
  apply evaluation_upper B hB r J P hP v E _ hE Q (fun h => lt_trans zero_lt_one (hQ h))
    (fun i => c i-(if arch then delta else 0)+eta) hv (hcfs J)
  intro b hb
  have hn := MvPolynomial.mem_support_iff.mp hb
  have he := source_exponents r hr Q hQ eta delta A heta hd hd1 hA hlog J b hJ
    (hclaims.2.2.1 J b hn) (hclaims.2.2.2.2 J b hJ hn) c hc
  cases arch
  · simpa using he.2
  · simpa using he.1

theorem strict_product_bound {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (h0 : Fin m) (eta E : ℝ)
    (heta : 0 < eta) (heta1 : eta < 1) (hE : 1 ≤ E)
    (hg : ∀ h, 64*E < (Q h)^eta)
    (hlog : ∀ h, (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*((r h0 : ℝ)*Real.log (Q h0))) :
    (64*E)^(3*(∑ h,r h))*Real.exp (-108*((r h0 : ℝ)*Real.log (Q h0))*m*eta) < 1 := by
  let A := (r h0 : ℝ)*Real.log (Q h0)
  let R := ∑ h,r h
  have hA : 0 < A := mul_pos (by exact_mod_cast hr h0) (Real.log_pos (hQ h0))
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by have := h0.isLt; omega)
  have hbase : 0 < 64*E := by positivity
  have ht (h : Fin m) : (r h : ℝ)*Real.log (64*E) < (r h : ℝ)*(eta*Real.log (Q h)) := by
    apply mul_lt_mul_of_pos_left _ (by exact_mod_cast hr h)
    have hh := Real.log_lt_log hbase (hg h)
    simpa only [Real.rpow_eq_pow,Real.log_rpow (lt_trans zero_lt_one (hQ h))] using hh
  have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (⟨h0,Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin m)).Nonempty) (fun h _ => ht h)
  have hs' : (R : ℝ)*Real.log (64*E) < eta*(∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) := by
    simpa only [← Finset.sum_mul,mul_left_comm,← Finset.mul_sum,← Nat.cast_sum,R] using hs
  have hb : (∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) ≤ (1+eta)*A*m := by
    have hh := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin m))) => hlog h)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,A,
      mul_assoc,mul_comm,mul_left_comm] using hh
  have hs3 := mul_lt_mul_of_pos_left hs' (by norm_num : (0 : ℝ) < 3)
  have hb3 := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3*eta by positivity)
  have hgap := mul_lt_mul_of_pos_right (show 3*(1+eta) < (108 : ℝ) by linarith)
    (show 0 < A*m*eta by positivity)
  have hexp : (3*(R : ℝ))*Real.log (64*E)-108*A*m*eta < 0 := by nlinarith
  calc
    _ = Real.exp ((3*(R : ℝ))*Real.log (64*E)-108*A*m*eta) := by
      rw [Real.exp_sub,show 3*(R : ℝ) = (3*R : ℕ) by push_cast; rfl,
        Real.exp_nat_mul,Real.exp_log hbase]
      change (64*E)^(3*R)*Real.exp (-108*A*m*eta) = (64*E)^(3*R)/Real.exp (108*A*m*eta)
      rw [div_eq_mul_inv,← Real.exp_neg]
      congr 2
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hexp

theorem real_grid_bounds {m : ℕ} (B : Matrix (Fin 6) (Fin 6) ℝ)
    (w : Fin m → Fin 5 → Fin 6 → ℤ) (a : Fin m → Fin 5 → ℕ)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h) (c : Fin 6 → ℝ) (eta delta : ℝ)
    (heta : 0 < eta) (ha : ∀ h j, a h j ≤ Nat.floor eta⁻¹+1)
    (hg : ∀ h, 6*(eta⁻¹+1) < (Q h)^eta)
    (hw : ∀ h j i, ‖(B *ᵥ (fun k => (w h j k : ℝ))) i‖ ≤ (Q h)^(c i-delta)) :
    ∀ h i, ‖(B *ᵥ (fun k => (gridPoint w a h k : ℝ))) i‖ ≤ (Q h)^(c i-delta+eta) := by
  apply grid_form_rpow B w a Q hQ (fun i => c i-delta) eta (eta⁻¹+1)
  · positivity
  · exact real_multiplier a eta heta ha
  · intro h
    exact (by have hh : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le; linarith : 5*(eta⁻¹+1) ≤ 6*(eta⁻¹+1)).trans (hg h).le
  · exact hw

theorem padic_grid_bounds (p : ℕ) [Fact p.Prime] {m : ℕ} (B : Matrix (Fin 6) (Fin 6) ℚ_[p])
    (w : Fin m → Fin 5 → Fin 6 → ℤ) (a : Fin m → Fin 5 → ℕ)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h) (c : Fin 6 → ℝ) (eta : ℝ) (heta : 0 < eta)
    (hg : ∀ h, 6*(eta⁻¹+1) < (Q h)^eta)
    (hw : ∀ h j i, ‖(B *ᵥ (fun k => (w h j k : ℚ_[p]))) i‖ ≤ (Q h)^(c i)) :
    ∀ h i, ‖(B *ᵥ (fun k => (gridPoint w a h k : ℚ_[p]))) i‖ ≤ (Q h)^(c i+eta) := by
  apply grid_form_rpow B w a Q hQ c eta 1 (by norm_num)
  · intro h j; exact padic_multiplier p (a h j)
  · intro h
    have hh : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
    have ht := hg h
    linarith
  · exact hw

def sourceBound {m : ℕ} (r : Fin m → ℕ) (E eta : ℝ) (Q : Fin m → ℝ)
    (h0 : Fin m) (c : Fin 3 → Fin 6 → ℝ) (tau : Fin 3) : ℝ :=
  (64*E)^(∑ h,r h)*Real.exp (((r h0 : ℝ)*Real.log (Q h0))*m*
    ((∑ i,c tau i)/6+(if tau=0 then -1116*eta else 504*eta)))

end CompoundFeasibility.Auxiliary6.SourceGrid
