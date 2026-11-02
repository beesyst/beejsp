import SubspaceBridge.BinaryLocalCore2
open scoped BigOperators Classical
namespace JSP000334
noncomputable def binaryLocalZeroCoordinate {m : ℕ} (i : Fin 2) :
    MvPolynomial (RothBlockVars2 m) ℚ →+* MvPolynomial (RothBlockVars2 m) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = i then 0 else MvPolynomial.X u)

noncomputable def binaryLocalKernelImage {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (i : Fin 2) (u : RothBlockVars2 m) : MvPolynomial (RothBlockVars2 m) ℚ :=
  binaryLocalZeroCoordinate i (binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹ u)

theorem binaryLocal_kernel_image_form {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (i : Fin 2) (h : Fin m) :
    (∑ j : Fin 2, MvPolynomial.C (L i j : ℚ) * binaryLocalKernelImage L i (h,j)) = 0 := by
  have he := binaryLocal_chart_comp (binaryLocalRationalMatrix L)⁻¹ (binaryLocalRationalMatrix L) (h,i)
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL), binaryLocal_chart_one] at he
  change binaryLocalSubstitution (binaryLocalRationalMatrix L)⁻¹
    (∑ j : Fin 2, MvPolynomial.C (binaryLocalRationalMatrix L i j) * MvPolynomial.X (h,j)) =
      MvPolynomial.X (h,i) at he
  simp only [map_sum, map_mul, binaryLocalSubstitution,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at he
  have hz := congrArg (binaryLocalZeroCoordinate i) he
  have hC (q : ℚ) : binaryLocalZeroCoordinate (m := m) i (MvPolynomial.C q) = MvPolynomial.C q := by
    simp [binaryLocalZeroCoordinate]
  simp only [map_sum, map_mul, hC] at hz
  rw [show binaryLocalZeroCoordinate i (MvPolynomial.X (h,i)) = 0 by
    simp [binaryLocalZeroCoordinate]] at hz
  exact hz

theorem binaryLocal_kernel_factor_variable {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (i p : Fin 2) (hp : L i p ≠ 0)
    (u : RothBlockVars2 m) :
    MvPolynomial.eval₂Hom MvPolynomial.C (binaryLocalKernelImage L i)
      (binaryKernelChart (fun _ : Fin m => L i) (fun _ => p) u) =
      binaryLocalKernelImage L i u := by
  classical
  have ha : (L i p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hcancel : (MvPolynomial.C ((L i p : ℚ)⁻¹) : MvPolynomial (RothBlockVars2 m) ℚ) *
      MvPolynomial.C (L i p : ℚ) = 1 := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, map_one]
  by_cases hu : u.2 = p
  · have hs := binaryLocal_kernel_image_form L hL i u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hs
    have hr : -(∑ j ∈ Finset.univ.erase p,
        MvPolynomial.C (L i j : ℚ) * binaryLocalKernelImage L i (u.1,j)) =
        MvPolynomial.C (L i p : ℚ) * binaryLocalKernelImage L i (u.1,p) := by
      linear_combination -hs
    simp only [binaryKernelChart, hu, if_pos rfl, ite_true, map_neg, map_sum, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((L i p : ℚ)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p,
            MvPolynomial.C (L i j : ℚ) * binaryLocalKernelImage L i (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv, MvPolynomial.C_mul]
        ring
      _ = _ := by rw [hr, ← mul_assoc, hcancel, one_mul]; simp [← hu]
  · simp [binaryKernelChart, hu]

theorem binaryLocal_kernel_factor {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (i p : Fin 2) (hp : L i p ≠ 0)
    (J : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (binaryLocalKernelImage L i)
      (binaryKernelRestriction (fun _ : Fin m => L i) (fun _ => p)
        (binaryDividedDerivative J P)) =
      binaryLocalZeroCoordinate i (binaryLocalExpansion L J P) := by
  have he : (MvPolynomial.eval₂Hom MvPolynomial.C (binaryLocalKernelImage (m := m) L i)).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom _)
        (binaryKernelChart (fun _ : Fin m => L i) (fun _ => p))) =
      (binaryLocalZeroCoordinate i).comp (MvPolynomial.eval₂Hom (Int.castRingHom _)
        (binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [binaryLocalZeroCoordinate]
    · intro u
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact binaryLocal_kernel_factor_variable L hL i p hp u
  exact congrArg (fun f => f (binaryDividedDerivative J P)) he

theorem binaryLocal_index_zero_slice {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 2) (Fin 2) ℤ) (hL : (binaryLocalRationalMatrix L).det ≠ 0)
    (i p : Fin 2) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hindex : binarySourceHighIndex r (fun _ : Fin m => L i) T P)
    (J : RothBlockVars2 m →₀ ℕ) (hJ : binarySourceDerivativeWeight r J < T) :
    binaryLocalZeroCoordinate i (binaryLocalExpansion L J P) = 0 := by
  rw [← binaryLocal_kernel_factor L hL i p hp]
  rw [hindex J hJ (fun _ => p) (fun _ => hp), map_zero]

theorem binaryLocal_zero_monomial {m : ℕ} (i : Fin 2)
    (b : RothBlockVars2 m →₀ ℕ) (c : ℚ) :
    binaryLocalZeroCoordinate i (MvPolynomial.monomial b c) =
      if (∀ h, b (h,i) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [binaryLocalZeroCoordinate, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  by_cases hb : ∀ h, b (h,i) = 0
  · rw [if_pos hb, MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    apply Finset.prod_congr rfl
    intro u _
    by_cases hu : u.2 = i
    · have he : u = (u.1,i) := Prod.ext rfl hu
      have hz : b u = 0 := (congrArg b he).trans (hb u.1)
      simp [hu, hz]
    · simp [hu]
  · rw [if_neg hb]
    push_neg at hb
    obtain ⟨h, hh⟩ := hb
    have hz : (∏ u : RothBlockVars2 m, (if u.2 = i then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (RothBlockVars2 m) ℚ) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,i))
      simp [hh]
    rw [hz, mul_zero]

theorem binaryLocal_zero_coeff {m : ℕ} (i : Fin 2)
    (Q : MvPolynomial (RothBlockVars2 m) ℚ) (b : RothBlockVars2 m →₀ ℕ) :
    (binaryLocalZeroCoordinate i Q).coeff b = if (∀ h, b (h,i) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [binaryLocal_zero_monomial]
    by_cases ha : ∀ h, a (h,i) = 0
    · rw [if_pos ha]
      by_cases hb : ∀ h, b (h,i) = 0
      · simp [hb]
      · have hab : a ≠ b := by intro he; subst a; exact hb ha
        simp [hb, hab]
    · rw [if_neg ha]
      by_cases hb : ∀ h, b (h,i) = 0
      · have hab : a ≠ b := by intro he; subst a; exact ha hb
        simp [hb, hab]
      · simp [hb]
  | add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, hP, hQ, MvPolynomial.coeff_add]
    split_ifs <;> simp

theorem binaryLocal_pderiv_coeff {m : ℕ} (u : RothBlockVars2 m)
    (Q : MvPolynomial (RothBlockVars2 m) ℚ) (b : RothBlockVars2 m →₀ ℕ) :
    (MvPolynomial.pderiv u Q).coeff b =
      (b u + 1 : ℕ) * Q.coeff (b + Finsupp.single u 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]; ring
  | monomial a c =>
    by_cases ha : a u = 0
    · have hab : a ≠ b + Finsupp.single u 1 := by
        intro he
        have h := congrArg (fun d : RothBlockVars2 m →₀ ℕ => d u) he
        simp [ha, Finsupp.add_apply, Finsupp.single_apply] at h
      simp [MvPolynomial.pderiv_monomial, ha, MvPolynomial.coeff_monomial, hab]
    · have hle : Finsupp.single u 1 ≤ a := by rw [Finsupp.single_le_iff]; omega
      have heq : a - Finsupp.single u 1 = b ↔ a = b + Finsupp.single u 1 := by
        constructor
        · intro he
          rw [← he]
          exact (tsub_add_cancel_of_le hle).symm
        · intro he
          rw [he, add_tsub_cancel_right]
      simp only [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, heq]
      split_ifs with he
      · subst a
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
        ring
      · simp

theorem binaryLocal_substitution_map {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ)
    (Q : MvPolynomial (RothBlockVars2 m) ℤ) :
    binaryLocalSubstitution B (MvPolynomial.map (Int.castRingHom ℚ) Q) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (binaryLocalLinearChart B) Q := by
  have hc : (MvPolynomial.C : ℚ →+* MvPolynomial (RothBlockVars2 m) ℚ).comp
      (Int.castRingHom ℚ) = Int.castRingHom _ := by
    ext z
    simp
  simp only [binaryLocalSubstitution, MvPolynomial.eval₂Hom_map_hom, hc]

theorem binaryLocal_expansion_chain {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (h : Fin m) (i : Fin 2) (J : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial.pderiv (h,i) (binaryLocalExpansion L J P) =
      ∑ j : Fin 2, MvPolynomial.C ((binaryLocalRationalMatrix L)⁻¹ j i) *
        (J (h,j) + 1) • binaryLocalExpansion L (J + Finsupp.single (h,j) 1) P := by
  change MvPolynomial.pderiv (h,i)
    (MvPolynomial.eval₂Hom (Int.castRingHom _)
      (binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹)
      (binaryDividedDerivative J P)) = _
  rw [← binaryLocal_substitution_map, binaryLocal_substitution_chain]
  simp only [MvPolynomial.pderiv_map, binary_source_pderiv_hasse, map_nsmul]
  simp only [binaryLocal_substitution_map, binaryLocalExpansion]

noncomputable def binaryLocalCoordinateWeight {m : ℕ} (r : Fin m → ℕ) (i : Fin 2)
    (b : RothBlockVars2 m →₀ ℕ) : ℝ := ∑ h, (b (h,i) : ℝ) / r h

theorem binaryLocal_coordinate_weight_add {m : ℕ} (r : Fin m → ℕ) (i : Fin 2)
    (b c : RothBlockVars2 m →₀ ℕ) :
    binaryLocalCoordinateWeight r i (b + c) =
      binaryLocalCoordinateWeight r i b + binaryLocalCoordinateWeight r i c := by
  simp [binaryLocalCoordinateWeight, Finsupp.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]

theorem binaryLocal_coordinate_weight_single {m : ℕ} (r : Fin m → ℕ)
    (i : Fin 2) (h : Fin m) :
    binaryLocalCoordinateWeight r i (Finsupp.single (h,i) 1) = 1 / (r h : ℝ) := by
  simp [binaryLocalCoordinateWeight, Finsupp.single_apply, Prod.mk.injEq,
    ite_div, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem binaryLocal_coeff_zero_below_index {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 2) (Fin 2) ℤ) (hL : (binaryLocalRationalMatrix L).det ≠ 0)
    (i p : Fin 2) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hindex : binarySourceHighIndex r (fun _ : Fin m => L i) T P)
    (J b : RothBlockVars2 m →₀ ℕ)
    (hbad : binarySourceDerivativeWeight r J + binaryLocalCoordinateWeight r i b < T) :
    (binaryLocalExpansion L J P).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : RothBlockVars2 m →₀ ℕ,
      (∑ h : Fin m, b (h,i)) = n →
      binarySourceDerivativeWeight r J + binaryLocalCoordinateWeight r i b < T →
      (binaryLocalExpansion L J P).coeff b = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J b hn hw
      by_cases hnzero : n = 0
      · have hbzero : ∀ h, b (h,i) = 0 := by
          intro h
          have hle : b (h,i) ≤ ∑ g : Fin m, b (g,i) :=
            Finset.single_le_sum (f := fun g : Fin m => b (g,i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
          omega
        have hnonneg : 0 ≤ binaryLocalCoordinateWeight r i b := by
          unfold binaryLocalCoordinateWeight
          positivity
        have hJ : binarySourceDerivativeWeight r J < T := by linarith
        have hz := binaryLocal_index_zero_slice r L hL i p hp T P hindex J hJ
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [binaryLocal_zero_coeff, if_pos hbzero, MvPolynomial.coeff_zero] at he
        exact he
      · have hex : ∃ h : Fin m, b (h,i) ≠ 0 := by
          by_contra hzero
          push_neg at hzero
          have hs : (∑ h : Fin m, b (h,i)) = 0 := Finset.sum_eq_zero (fun h _ => hzero h)
          omega
        obtain ⟨h, hh⟩ := hex
        let c := b - Finsupp.single (h,i) 1
        have hle : Finsupp.single (h,i) 1 ≤ b := by rw [Finsupp.single_le_iff]; omega
        have hceq : c + Finsupp.single (h,i) 1 = b := tsub_add_cancel_of_le hle
        have hcount : (∑ g : Fin m, c (g,i)) + 1 = n := by
          have hs := congrArg (fun d : RothBlockVars2 m →₀ ℕ => ∑ g : Fin m, d (g,i)) hceq
          simpa [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
            Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', hn] using hs
        have hcoord : binaryLocalCoordinateWeight r i c + 1 / (r h : ℝ) =
            binaryLocalCoordinateWeight r i b := by
          rw [← binaryLocal_coordinate_weight_single r i h, ← binaryLocal_coordinate_weight_add, hceq]
        have hz (j : Fin 2) : (binaryLocalExpansion L (J + Finsupp.single (h,j) 1) P).coeff c = 0 := by
          apply ih (∑ g : Fin m, c (g,i)) (by omega) _ c rfl
          rw [binary_source_weight_add, binary_source_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,i) (binaryLocalExpansion L J P)).coeff c = 0 := by
          rw [binaryLocal_expansion_chain, MvPolynomial.coeff_sum]
          apply Finset.sum_eq_zero
          intro j hj
          rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_smul, hz j, smul_zero, mul_zero]
        rw [binaryLocal_pderiv_coeff, hceq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad

theorem binaryLocal_chart_block_weight {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ)
    (h : Fin m) (u : RothBlockVars2 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars2 m => if v.1 = h then 1 else 0)
      (binaryLocalLinearChart B u) (if u.1 = h then 1 else 0) := by
  unfold binaryLocalLinearChart
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  simpa only [zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C _ (B u.2 j)).mul
      (MvPolynomial.isWeightedHomogeneous_X ℚ (fun v : RothBlockVars2 m => if v.1 = h then 1 else 0) (u.1,j))

theorem binaryLocal_expansion_block_weight {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 2) (Fin 2) ℤ) (J : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars2 m => if v.1 = h then 1 else 0)
      (binaryLocalExpansion L J P) (r h - ∑ j : Fin 2, J (h,j)) := by
  classical
  let Q := binaryDividedDerivative J P
  let w := fun v : RothBlockVars2 m => if v.1 = h then 1 else 0
  have hdegree (d : RothBlockVars2 m →₀ ℕ) (hd : d ∈ Q.support) :
      (∑ j : Fin 2, d (h,j)) = r h - ∑ j : Fin 2, J (h,j) := by
    have hcoeff : P.coeff (d + J) ≠ 0 := by
      intro hz
      have hn := MvPolynomial.mem_support_iff.mp hd
      rw [binary_derivative_coeff, hz, zero_mul] at hn
      exact hn rfl
    have hh := hP (d + J) (MvPolynomial.mem_support_iff.mpr hcoeff) h
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hh
    omega
  change MvPolynomial.IsWeightedHomogeneous w
    (MvPolynomial.eval₂Hom (Int.castRingHom _)
      (binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹) Q) _
  conv_lhs => arg 2; rw [MvPolynomial.as_sum Q]
  rw [map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have hw : (∑ u : RothBlockVars2 m, d u * w u) = ∑ j : Fin 2, d (h,j) := by
    have he := binary_weight_block d h
    rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
    simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : RothBlockVars2 m => binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹ u ^ d u)
    (fun u => d u * w u)
    (fun u _ => by simpa only [nsmul_eq_mul] using
      (binaryLocal_chart_block_weight (binaryLocalRationalMatrix L)⁻¹ h u).pow (d u))
  have hcast :
      (Int.castRingHom (MvPolynomial (RothBlockVars2 m) ℚ)) (Q.coeff d) =
        MvPolynomial.C (((Q.coeff d : ℤ) : ℚ)) := by
    change ((Q.coeff d : ℤ) : MvPolynomial (RothBlockVars2 m) ℚ) =
      MvPolynomial.C (((Q.coeff d : ℤ) : ℚ))
    exact (map_intCast
      (MvPolynomial.C : ℚ →+* MvPolynomial (RothBlockVars2 m) ℚ)
      (Q.coeff d)).symm
  rw [hcast]
  simpa only [zero_add, hw, hdegree d hd] using
    (MvPolynomial.isWeightedHomogeneous_C w
      (((Q.coeff d : ℤ) : ℚ))).mul hprod

theorem binaryLocal_expansion_block_degree {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 2) (Fin 2) ℤ) (J : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (b : RothBlockVars2 m →₀ ℕ) (hb : (binaryLocalExpansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ j : Fin 2, b (h,j)) = r h - ∑ j : Fin 2, J (h,j) := by
  have hw := binaryLocal_expansion_block_weight r L J P hP h hb
  rwa [binary_weight_block] at hw

theorem binaryLocal_total_coordinate_weight_le {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 2) (Fin 2) ℤ) (J : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (b : RothBlockVars2 m →₀ ℕ) (hb : (binaryLocalExpansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 2, binaryLocalCoordinateWeight r i b) ≤ (m : ℝ) := by
  unfold binaryLocalCoordinateWeight
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ h : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [← Finset.sum_div]
      have hrh : (0 : ℝ) < r h := by exact_mod_cast hr h
      apply (div_le_one hrh).mpr
      have hdeg := binaryLocal_expansion_block_degree r L J P hP b hb h
      exact_mod_cast (show (∑ i : Fin 2, b (h,i)) ≤ r h by omega)
    _ = _ := by simp

theorem binaryLocal_nonzero_row (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (i : Fin 2) : ∃ p, L i p ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  apply hL
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  simp [binaryLocalRationalMatrix, hzero j]

theorem binaryLocal_coefficient_balance {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hP : binaryBlockHomogeneous r P)
    (hindex : ∀ i : Fin 2, binarySourceHighIndex r (fun _ : Fin m => L i) ((1 / 2 - eta) * m) P)
    (J b : RothBlockVars2 m →₀ ℕ)
    (hJ : binarySourceDerivativeWeight r J ≤ 2 * eta * m)
    (hb : (binaryLocalExpansion L J P).coeff b ≠ 0) :
    ∀ i : Fin 2, |binaryLocalCoordinateWeight r i b - (m : ℝ) / 2| ≤ 3 * m * eta := by
  have hlower (i : Fin 2) : (m : ℝ) / 2 - 3 * m * eta ≤ binaryLocalCoordinateWeight r i b := by
    obtain ⟨p, hp⟩ := binaryLocal_nonzero_row L hL i
    have hlow : (1 / 2 - eta) * m ≤ binarySourceDerivativeWeight r J + binaryLocalCoordinateWeight r i b := by
      by_contra! hbad
      exact hb (binaryLocal_coeff_zero_below_index r L hL i p hp _ P (hindex i) J b hbad)
    nlinarith
  have hsum := binaryLocal_total_coordinate_weight_le r hr L J P hP b hb
  rw [Fin.sum_univ_two] at hsum
  have h0 := hlower 0
  have h1 := hlower 1
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> apply abs_le.mpr <;> constructor <;> nlinarith

end JSP000334
