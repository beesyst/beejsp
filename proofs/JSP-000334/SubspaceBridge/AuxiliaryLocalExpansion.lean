import SubspaceBridge.AuxiliarySourceIndex

open scoped BigOperators Classical
namespace JSP000334

noncomputable def rothLocalRationalMatrix (L : Matrix (Fin 3) (Fin 3) ℤ) :
    Matrix (Fin 3) (Fin 3) ℚ := fun i j => (L i j : ℚ)

noncomputable def rothLocalLinearChart {m : ℕ} (B : Matrix (Fin 3) (Fin 3) ℚ)
    (u : RothBlockVars m) : MvPolynomial (RothBlockVars m) ℚ :=
  ∑ i : Fin 3, MvPolynomial.C (B u.2 i) * MvPolynomial.X (u.1,i)

noncomputable def rothLocalSubstitution {m : ℕ} (B : Matrix (Fin 3) (Fin 3) ℚ) :
    MvPolynomial (RothBlockVars m) ℚ →+* MvPolynomial (RothBlockVars m) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (rothLocalLinearChart B)

noncomputable def rothLocalExpansion {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial (RothBlockVars m) ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹)
    (rothBlockIntegerDividedDerivative J P)

noncomputable def rothLocalAbs (tau : Fin 3) (q : ℚ) : ℝ :=
  if tau = 0 then |(q : ℝ)| else if tau = 1 then padicNorm 2 q else padicNorm 3 q

theorem rothLocal_chart_one {m : ℕ} (u : RothBlockVars m) :
    rothLocalLinearChart (1 : Matrix (Fin 3) (Fin 3) ℚ) u = MvPolynomial.X u := by
  simp [rothLocalLinearChart, Matrix.one_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem rothLocal_chart_comp {m : ℕ} (A B : Matrix (Fin 3) (Fin 3) ℚ)
    (u : RothBlockVars m) :
    rothLocalSubstitution A (rothLocalLinearChart B u) = rothLocalLinearChart (B * A) u := by
  classical
  simp only [rothLocalLinearChart, rothLocalSubstitution, map_sum, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mul_apply]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  ring

theorem rothLocal_expansion_reconstruct {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) :
    rothLocalSubstitution (rothLocalRationalMatrix L) (rothLocalExpansion L J P) =
      MvPolynomial.map (Int.castRingHom ℚ) (rothBlockIntegerDividedDerivative J P) := by
  classical
  have hinv := Matrix.nonsing_inv_mul (rothLocalRationalMatrix L) (isUnit_iff_ne_zero.mpr hL)
  have he : (rothLocalSubstitution (m := m) (rothLocalRationalMatrix L)).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom _)
        (rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹)) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [rothLocalSubstitution]
    · intro u
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [rothLocal_chart_comp, hinv, rothLocal_chart_one]
      simp
  exact congrArg (fun f => f (rothBlockIntegerDividedDerivative J P)) he

theorem rothLocal_chart_pderiv {m : ℕ} (B : Matrix (Fin 3) (Fin 3) ℚ)
    (h : Fin m) (i : Fin 3) (u : RothBlockVars m) :
    MvPolynomial.pderiv (h,i) (rothLocalLinearChart B u) =
      if u.1 = h then MvPolynomial.C (B u.2 i) else 0 := by
  classical
  rcases u with ⟨g,j⟩
  by_cases hg : g = h
  · subst g
    simp [rothLocalLinearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · simp [rothLocalLinearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg]

theorem rothLocal_substitution_one {m : ℕ} (P : MvPolynomial (RothBlockVars m) ℚ) :
    rothLocalSubstitution (1 : Matrix (Fin 3) (Fin 3) ℚ) P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rothLocalSubstitution]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P u hP =>
    rw [map_mul, hP]
    simp [rothLocalSubstitution, rothLocal_chart_one]

theorem rothLocal_substitution_comp {m : ℕ} (A B : Matrix (Fin 3) (Fin 3) ℚ)
    (P : MvPolynomial (RothBlockVars m) ℚ) :
    rothLocalSubstitution A (rothLocalSubstitution B P) = rothLocalSubstitution (B * A) P := by
  have he : (rothLocalSubstitution (m := m) A).comp (rothLocalSubstitution B) =
      rothLocalSubstitution (B * A) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [rothLocalSubstitution]
    · intro u
      simp only [RingHom.comp_apply, rothLocalSubstitution, MvPolynomial.eval₂Hom_X']
      exact rothLocal_chart_comp A B u
  exact congrArg (fun f => f P) he

theorem rothLocal_substitution_injective {m : ℕ} (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : M.det ≠ 0) : Function.Injective (rothLocalSubstitution (m := m) M) := by
  intro P Q h
  have he := congrArg (rothLocalSubstitution M⁻¹) h
  rw [rothLocal_substitution_comp, rothLocal_substitution_comp,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
    rothLocal_substitution_one, rothLocal_substitution_one] at he
  exact he

theorem rothLocal_expansion_unique {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (Q : MvPolynomial (RothBlockVars m) ℚ)
    (hQ : rothLocalSubstitution (rothLocalRationalMatrix L) Q =
      MvPolynomial.map (Int.castRingHom ℚ) (rothBlockIntegerDividedDerivative J P)) :
    Q = rothLocalExpansion L J P := by
  apply rothLocal_substitution_injective (rothLocalRationalMatrix L) hL
  exact hQ.trans (rothLocal_expansion_reconstruct L hL J P).symm

theorem rothLocal_substitution_chain {m : ℕ} (B : Matrix (Fin 3) (Fin 3) ℚ)
    (h : Fin m) (i : Fin 3) (P : MvPolynomial (RothBlockVars m) ℚ) :
    MvPolynomial.pderiv (h,i) (rothLocalSubstitution B P) =
      ∑ j : Fin 3, MvPolynomial.C (B j i) *
        rothLocalSubstitution B (MvPolynomial.pderiv (h,j) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [rothLocalSubstitution]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add, Finset.sum_add_distrib]
  | mul_X P u hP =>
    have hdelta : (∑ j : Fin 3, (MvPolynomial.C (B j i) * rothLocalSubstitution B P) *
        (if (h,j) = u then 1 else 0)) =
        rothLocalSubstitution B P * (if u.1 = h then MvPolynomial.C (B u.2 i) else 0) := by
      rcases u with ⟨g,l⟩
      by_cases hg : g = h
      · subst g
        simp [Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]
      · simp [Prod.mk.injEq, hg, Ne.symm hg]
    have hX : rothLocalSubstitution B (MvPolynomial.X u) = rothLocalLinearChart B u := by
      simp [rothLocalSubstitution]
    have hD (j : Fin 3) :
        rothLocalSubstitution B (MvPolynomial.pderiv (h,j) (P * MvPolynomial.X u)) =
          rothLocalSubstitution B (MvPolynomial.pderiv (h,j) P) * rothLocalLinearChart B u +
          rothLocalSubstitution B P * (if (h,j) = u then 1 else 0) := by
      by_cases he : (h,j) = u <;>
        simp [MvPolynomial.pderiv_mul, hX, MvPolynomial.pderiv_X, Pi.single_apply, he, eq_comm] <;> ring
    rw [map_mul, MvPolynomial.pderiv_mul, hP, hX, rothLocal_chart_pderiv]
    simp_rw [hD, mul_add, ← mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hdelta]

noncomputable def rothLocalZeroCoordinate {m : ℕ} (i : Fin 3) :
    MvPolynomial (RothBlockVars m) ℚ →+* MvPolynomial (RothBlockVars m) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = i then 0 else MvPolynomial.X u)

noncomputable def rothLocalKernelImage {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (i : Fin 3) (u : RothBlockVars m) : MvPolynomial (RothBlockVars m) ℚ :=
  rothLocalZeroCoordinate i (rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹ u)

theorem rothLocal_kernel_image_form {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0) (i : Fin 3) (h : Fin m) :
    (∑ j : Fin 3, MvPolynomial.C (L i j : ℚ) * rothLocalKernelImage L i (h,j)) = 0 := by
  have he := rothLocal_chart_comp (rothLocalRationalMatrix L)⁻¹ (rothLocalRationalMatrix L) (h,i)
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL), rothLocal_chart_one] at he
  change rothLocalSubstitution (rothLocalRationalMatrix L)⁻¹
    (∑ j : Fin 3, MvPolynomial.C (rothLocalRationalMatrix L i j) * MvPolynomial.X (h,j)) =
      MvPolynomial.X (h,i) at he
  simp only [map_sum, map_mul, rothLocalSubstitution,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at he
  have hz := congrArg (rothLocalZeroCoordinate i) he
  have hC (q : ℚ) : rothLocalZeroCoordinate (m := m) i (MvPolynomial.C q) = MvPolynomial.C q := by
    simp [rothLocalZeroCoordinate]
  simp only [map_sum, map_mul, hC] at hz
  rw [show rothLocalZeroCoordinate i (MvPolynomial.X (h,i)) = 0 by
    simp [rothLocalZeroCoordinate]] at hz
  exact hz

theorem rothLocal_kernel_factor_variable {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0) (i p : Fin 3) (hp : L i p ≠ 0)
    (u : RothBlockVars m) :
    MvPolynomial.eval₂Hom MvPolynomial.C (rothLocalKernelImage L i)
      (rothKernelChart (fun _ : Fin m => L i) (fun _ => p) u) =
      rothLocalKernelImage L i u := by
  classical
  have ha : (L i p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hcancel : (MvPolynomial.C ((L i p : ℚ)⁻¹) : MvPolynomial (RothBlockVars m) ℚ) *
      MvPolynomial.C (L i p : ℚ) = 1 := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, map_one]
  by_cases hu : u.2 = p
  · have hs := rothLocal_kernel_image_form L hL i u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hs
    have hr : -(∑ j ∈ Finset.univ.erase p,
        MvPolynomial.C (L i j : ℚ) * rothLocalKernelImage L i (u.1,j)) =
        MvPolynomial.C (L i p : ℚ) * rothLocalKernelImage L i (u.1,p) := by
      linear_combination -hs
    simp only [rothKernelChart, hu, if_pos rfl, ite_true, map_neg, map_sum, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((L i p : ℚ)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p,
            MvPolynomial.C (L i j : ℚ) * rothLocalKernelImage L i (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv, MvPolynomial.C_mul]
        ring
      _ = _ := by rw [hr, ← mul_assoc, hcancel, one_mul]; simp [← hu]
  · simp [rothKernelChart, hu]

theorem rothLocal_kernel_factor {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0) (i p : Fin 3) (hp : L i p ≠ 0)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (rothLocalKernelImage L i)
      (rothKernelRestriction (fun _ : Fin m => L i) (fun _ => p)
        (rothBlockIntegerDividedDerivative J P)) =
      rothLocalZeroCoordinate i (rothLocalExpansion L J P) := by
  have he : (MvPolynomial.eval₂Hom MvPolynomial.C (rothLocalKernelImage (m := m) L i)).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom _)
        (rothKernelChart (fun _ : Fin m => L i) (fun _ => p))) =
      (rothLocalZeroCoordinate i).comp (MvPolynomial.eval₂Hom (Int.castRingHom _)
        (rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [rothLocalZeroCoordinate]
    · intro u
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact rothLocal_kernel_factor_variable L hL i p hp u
  exact congrArg (fun f => f (rothBlockIntegerDividedDerivative J P)) he

theorem rothLocal_index_zero_slice {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (hL : (rothLocalRationalMatrix L).det ≠ 0)
    (i p : Fin 3) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (RothBlockVars m) ℤ)
    (hindex : rothSourceHighIndex r (fun _ : Fin m => L i) T P)
    (J : RothBlockVars m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J < T) :
    rothLocalZeroCoordinate i (rothLocalExpansion L J P) = 0 := by
  rw [← rothLocal_kernel_factor L hL i p hp]
  rw [hindex J hJ (fun _ => p) (fun _ => hp), map_zero]

theorem rothLocal_zero_monomial {m : ℕ} (i : Fin 3)
    (b : RothBlockVars m →₀ ℕ) (c : ℚ) :
    rothLocalZeroCoordinate i (MvPolynomial.monomial b c) =
      if (∀ h, b (h,i) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [rothLocalZeroCoordinate, MvPolynomial.eval₂Hom_monomial]
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
    have hz : (∏ u : RothBlockVars m, (if u.2 = i then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (RothBlockVars m) ℚ) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,i))
      simp [hh]
    rw [hz, mul_zero]

theorem rothLocal_zero_coeff {m : ℕ} (i : Fin 3)
    (Q : MvPolynomial (RothBlockVars m) ℚ) (b : RothBlockVars m →₀ ℕ) :
    (rothLocalZeroCoordinate i Q).coeff b = if (∀ h, b (h,i) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [rothLocal_zero_monomial]
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

theorem rothLocal_pderiv_coeff {m : ℕ} (u : RothBlockVars m)
    (Q : MvPolynomial (RothBlockVars m) ℚ) (b : RothBlockVars m →₀ ℕ) :
    (MvPolynomial.pderiv u Q).coeff b =
      (b u + 1 : ℕ) * Q.coeff (b + Finsupp.single u 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]; ring
  | monomial a c =>
    by_cases ha : a u = 0
    · have hab : a ≠ b + Finsupp.single u 1 := by
        intro he
        have h := congrArg (fun d : RothBlockVars m →₀ ℕ => d u) he
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

theorem rothLocal_substitution_map {m : ℕ} (B : Matrix (Fin 3) (Fin 3) ℚ)
    (Q : MvPolynomial (RothBlockVars m) ℤ) :
    rothLocalSubstitution B (MvPolynomial.map (Int.castRingHom ℚ) Q) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothLocalLinearChart B) Q := by
  have hc : (MvPolynomial.C : ℚ →+* MvPolynomial (RothBlockVars m) ℚ).comp
      (Int.castRingHom ℚ) = Int.castRingHom _ := by
    ext z
    simp
  simp only [rothLocalSubstitution, MvPolynomial.eval₂Hom_map_hom, hc]

theorem rothLocal_expansion_chain {m : ℕ} (L : Matrix (Fin 3) (Fin 3) ℤ)
    (h : Fin m) (i : Fin 3) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.pderiv (h,i) (rothLocalExpansion L J P) =
      ∑ j : Fin 3, MvPolynomial.C ((rothLocalRationalMatrix L)⁻¹ j i) *
        (J (h,j) + 1) • rothLocalExpansion L (J + Finsupp.single (h,j) 1) P := by
  change MvPolynomial.pderiv (h,i)
    (MvPolynomial.eval₂Hom (Int.castRingHom _)
      (rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹)
      (rothBlockIntegerDividedDerivative J P)) = _
  rw [← rothLocal_substitution_map, rothLocal_substitution_chain]
  simp only [MvPolynomial.pderiv_map, rothSource_pderiv_hasse, map_nsmul]
  simp only [rothLocal_substitution_map, rothLocalExpansion]

noncomputable def rothLocalCoordinateWeight {m : ℕ} (r : Fin m → ℕ) (i : Fin 3)
    (b : RothBlockVars m →₀ ℕ) : ℝ := ∑ h, (b (h,i) : ℝ) / r h

theorem rothLocal_coordinate_weight_add {m : ℕ} (r : Fin m → ℕ) (i : Fin 3)
    (b c : RothBlockVars m →₀ ℕ) :
    rothLocalCoordinateWeight r i (b + c) =
      rothLocalCoordinateWeight r i b + rothLocalCoordinateWeight r i c := by
  simp [rothLocalCoordinateWeight, Finsupp.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]

theorem rothLocal_coordinate_weight_single {m : ℕ} (r : Fin m → ℕ)
    (i : Fin 3) (h : Fin m) :
    rothLocalCoordinateWeight r i (Finsupp.single (h,i) 1) = 1 / (r h : ℝ) := by
  simp [rothLocalCoordinateWeight, Finsupp.single_apply, Prod.mk.injEq,
    ite_div, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem rothLocal_coeff_zero_below_index {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (hL : (rothLocalRationalMatrix L).det ≠ 0)
    (i p : Fin 3) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (RothBlockVars m) ℤ)
    (hindex : rothSourceHighIndex r (fun _ : Fin m => L i) T P)
    (J b : RothBlockVars m →₀ ℕ)
    (hbad : rothSourceDerivativeWeight r J + rothLocalCoordinateWeight r i b < T) :
    (rothLocalExpansion L J P).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : RothBlockVars m →₀ ℕ,
      (∑ h : Fin m, b (h,i)) = n →
      rothSourceDerivativeWeight r J + rothLocalCoordinateWeight r i b < T →
      (rothLocalExpansion L J P).coeff b = 0 := by
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
        have hnonneg : 0 ≤ rothLocalCoordinateWeight r i b := by
          unfold rothLocalCoordinateWeight
          positivity
        have hJ : rothSourceDerivativeWeight r J < T := by linarith
        have hz := rothLocal_index_zero_slice r L hL i p hp T P hindex J hJ
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [rothLocal_zero_coeff, if_pos hbzero, MvPolynomial.coeff_zero] at he
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
          have hs := congrArg (fun d : RothBlockVars m →₀ ℕ => ∑ g : Fin m, d (g,i)) hceq
          simpa [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
            Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', hn] using hs
        have hcoord : rothLocalCoordinateWeight r i c + 1 / (r h : ℝ) =
            rothLocalCoordinateWeight r i b := by
          rw [← rothLocal_coordinate_weight_single r i h, ← rothLocal_coordinate_weight_add, hceq]
        have hz (j : Fin 3) : (rothLocalExpansion L (J + Finsupp.single (h,j) 1) P).coeff c = 0 := by
          apply ih (∑ g : Fin m, c (g,i)) (by omega) _ c rfl
          rw [rothSource_weight_add, rothSource_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,i) (rothLocalExpansion L J P)).coeff c = 0 := by
          rw [rothLocal_expansion_chain, MvPolynomial.coeff_sum]
          apply Finset.sum_eq_zero
          intro j hj
          rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_smul, hz j, smul_zero, mul_zero]
        rw [rothLocal_pderiv_coeff, hceq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad

theorem rothLocal_chart_block_weight {m : ℕ} (B : Matrix (Fin 3) (Fin 3) ℚ)
    (h : Fin m) (u : RothBlockVars m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars m => if v.1 = h then 1 else 0)
      (rothLocalLinearChart B u) (if u.1 = h then 1 else 0) := by
  unfold rothLocalLinearChart
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  simpa only [zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C _ (B u.2 j)).mul
      (MvPolynomial.isWeightedHomogeneous_X ℚ (fun v : RothBlockVars m => if v.1 = h then 1 else 0) (u.1,j))

theorem rothLocal_expansion_block_weight {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : RothBlockVars m => if v.1 = h then 1 else 0)
      (rothLocalExpansion L J P) (r h - ∑ j : Fin 3, J (h,j)) := by
  classical
  let Q := rothBlockIntegerDividedDerivative J P
  let w := fun v : RothBlockVars m => if v.1 = h then 1 else 0
  have hdegree (d : RothBlockVars m →₀ ℕ) (hd : d ∈ Q.support) :
      (∑ j : Fin 3, d (h,j)) = r h - ∑ j : Fin 3, J (h,j) := by
    have hcoeff : P.coeff (d + J) ≠ 0 := by
      intro hz
      have hn := MvPolynomial.mem_support_iff.mp hd
      rw [rothBlockIntegerDividedDerivative_coeff, hz, zero_mul] at hn
      exact hn rfl
    have hh := hP (d + J) (MvPolynomial.mem_support_iff.mpr hcoeff) h
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hh
    omega
  change MvPolynomial.IsWeightedHomogeneous w
    (MvPolynomial.eval₂Hom (Int.castRingHom _)
      (rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹) Q) _
  conv_lhs => arg 2; rw [MvPolynomial.as_sum Q]
  rw [map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have hw : (∑ u : RothBlockVars m, d u * w u) = ∑ j : Fin 3, d (h,j) := by
    have he := rothAux_weight_block d h
    rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
    simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : RothBlockVars m => rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹ u ^ d u)
    (fun u => d u * w u)
    (fun u _ => by simpa only [nsmul_eq_mul] using
      (rothLocal_chart_block_weight (rothLocalRationalMatrix L)⁻¹ h u).pow (d u))
  have hcast :
      (Int.castRingHom (MvPolynomial (RothBlockVars m) ℚ)) (Q.coeff d) =
        MvPolynomial.C (((Q.coeff d : ℤ) : ℚ)) := by
    change ((Q.coeff d : ℤ) : MvPolynomial (RothBlockVars m) ℚ) =
      MvPolynomial.C (((Q.coeff d : ℤ) : ℚ))
    exact (map_intCast
      (MvPolynomial.C : ℚ →+* MvPolynomial (RothBlockVars m) ℚ)
      (Q.coeff d)).symm
  rw [hcast]
  simpa only [zero_add, hw, hdegree d hd] using
    (MvPolynomial.isWeightedHomogeneous_C w
      (((Q.coeff d : ℤ) : ℚ))).mul hprod

theorem rothLocal_expansion_block_degree {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 3) (Fin 3) ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (b : RothBlockVars m →₀ ℕ) (hb : (rothLocalExpansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ j : Fin 3, b (h,j)) = r h - ∑ j : Fin 3, J (h,j) := by
  have hw := rothLocal_expansion_block_weight r L J P hP h hb
  rwa [rothAux_weight_block] at hw

theorem rothLocal_total_coordinate_weight_le {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 3) (Fin 3) ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (b : RothBlockVars m →₀ ℕ) (hb : (rothLocalExpansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 3, rothLocalCoordinateWeight r i b) ≤ (m : ℝ) := by
  unfold rothLocalCoordinateWeight
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ h : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [← Finset.sum_div]
      have hrh : (0 : ℝ) < r h := by exact_mod_cast hr h
      apply (div_le_one hrh).mpr
      have hdeg := rothLocal_expansion_block_degree r L J P hP b hb h
      exact_mod_cast (show (∑ i : Fin 3, b (h,i)) ≤ r h by omega)
    _ = _ := by simp

theorem rothLocal_nonzero_row (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0) (i : Fin 3) : ∃ p, L i p ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  apply hL
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  simp [rothLocalRationalMatrix, hzero j]

theorem rothLocal_coefficient_balance {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (L : Matrix (Fin 3) (Fin 3) ℤ)
    (hL : (rothLocalRationalMatrix L).det ≠ 0) (P : MvPolynomial (RothBlockVars m) ℤ)
    (hP : rothBlockHomogeneous r P)
    (hindex : ∀ i : Fin 3, rothSourceHighIndex r (fun _ : Fin m => L i) ((1 / 3 - eta) * m) P)
    (J b : RothBlockVars m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J ≤ 2 * eta * m)
    (hb : (rothLocalExpansion L J P).coeff b ≠ 0) :
    ∀ i : Fin 3, |rothLocalCoordinateWeight r i b - (m : ℝ) / 3| ≤ 9 * m * eta := by
  have hlower (i : Fin 3) : (m : ℝ) / 3 - 3 * m * eta ≤ rothLocalCoordinateWeight r i b := by
    obtain ⟨p, hp⟩ := rothLocal_nonzero_row L hL i
    have hlow : (1 / 3 - eta) * m ≤ rothSourceDerivativeWeight r J + rothLocalCoordinateWeight r i b := by
      by_contra! hbad
      exact hb (rothLocal_coeff_zero_below_index r L hL i p hp _ P (hindex i) J b hbad)
    nlinarith
  have hsum := rothLocal_total_coordinate_weight_le r hr L J P hP b hb
  simp only [Fin.sum_univ_three] at hsum
  have h0 := hlower 0
  have h1 := hlower 1
  have h2 := hlower 2
  have hmeta : (0 : ℝ) ≤ (m : ℝ) * eta := mul_nonneg (Nat.cast_nonneg _) heta.le
  have hb0 : |rothLocalCoordinateWeight r 0 b - (m : ℝ) / 3| ≤ 9 * m * eta :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hb1 : |rothLocalCoordinateWeight r 1 b - (m : ℝ) / 3| ≤ 9 * m * eta :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hb2 : |rothLocalCoordinateWeight r 2 b - (m : ℝ) / 3| ≤ 9 * m * eta :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  intro i
  fin_cases i
  · exact hb0
  · exact hb1
  · exact hb2

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem rothLocalAbs_nonneg (tau : Fin 3) (q : ℚ) : 0 ≤ rothLocalAbs tau q := by
  fin_cases tau
  · change (0 : ℝ) ≤ |(q : ℝ)|
    exact abs_nonneg _
  · change (0 : ℝ) ≤ (padicNorm 2 q : ℝ)
    exact_mod_cast (padicNorm.nonneg (p := 2) q)
  · change (0 : ℝ) ≤ (padicNorm 3 q : ℝ)
    exact_mod_cast (padicNorm.nonneg (p := 3) q)

theorem rothLocalAbs_zero (tau : Fin 3) : rothLocalAbs tau 0 = 0 := by
  fin_cases tau <;> simp [rothLocalAbs]

theorem rothLocalAbs_one (tau : Fin 3) : rothLocalAbs tau 1 = 1 := by
  fin_cases tau <;> simp [rothLocalAbs, padicNorm.one]

theorem rothLocalAbs_mul (tau : Fin 3) (q s : ℚ) :
    rothLocalAbs tau (q * s) = rothLocalAbs tau q * rothLocalAbs tau s := by
  fin_cases tau <;> simp [rothLocalAbs, abs_mul, padicNorm.mul]

theorem rothLocalAbs_add (tau : Fin 3) (q s : ℚ) :
    rothLocalAbs tau (q + s) ≤ rothLocalAbs tau q + rothLocalAbs tau s := by
  fin_cases tau
  · simpa [rothLocalAbs] using abs_add (q : ℝ) (s : ℝ)
  · change (padicNorm 2 (q + s) : ℝ) ≤ (padicNorm 2 q : ℝ) + (padicNorm 2 s : ℝ)
    exact_mod_cast (padicNorm.triangle_ineq (p := 2) q s)
  · change (padicNorm 3 (q + s) : ℝ) ≤ (padicNorm 3 q : ℝ) + (padicNorm 3 s : ℝ)
    exact_mod_cast (padicNorm.triangle_ineq (p := 3) q s)

theorem rothLocalAbs_int (tau : Fin 3) (z : ℤ) :
    rothLocalAbs tau (z : ℚ) ≤ (z.natAbs : ℝ) := by
  have habs : |(z : ℝ)| = (z.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  by_cases hz : z = 0
  · simp [hz, rothLocalAbs_zero]
  have h1 : (1 : ℝ) ≤ z.natAbs := by exact_mod_cast (Int.natAbs_pos.mpr hz)
  fin_cases tau
  · simpa [rothLocalAbs] using habs.le
  · simp only [rothLocalAbs, Fin.isValue, Fin.reduceEq, ite_false, ite_true]
    have hp : (padicNorm 2 (z : ℚ) : ℝ) ≤ 1 := by exact_mod_cast (padicNorm.of_int (p := 2) z)
    exact hp.trans h1
  · simp only [rothLocalAbs, Fin.isValue, Fin.reduceEq, ite_false]
    have hp : (padicNorm 3 (z : ℚ) : ℝ) ≤ 1 := by exact_mod_cast (padicNorm.of_int (p := 3) z)
    exact hp.trans h1

noncomputable def rothLocalMass {σ : Type*} (tau : Fin 3) (P : MvPolynomial σ ℚ) : ℝ :=
  ∑ d ∈ P.support, rothLocalAbs tau (P.coeff d)

theorem rothLocalMass_nonneg {σ : Type*} (tau : Fin 3) (P : MvPolynomial σ ℚ) :
    0 ≤ rothLocalMass tau P := Finset.sum_nonneg (fun _ _ => rothLocalAbs_nonneg _ _)

theorem rothLocalMass_monomial {σ : Type*} (tau : Fin 3) (d : σ →₀ ℕ) (c : ℚ) :
    rothLocalMass tau (MvPolynomial.monomial d c) = rothLocalAbs tau c := by
  by_cases hc : c = 0
  · simp [hc, rothLocalMass, rothLocalAbs_zero]
  · simp [rothLocalMass, MvPolynomial.support_monomial, hc]

theorem rothLocalMass_support_sum {σ : Type*} (tau : Fin 3) (P : MvPolynomial σ ℚ)
    (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) :
    rothLocalMass tau P = ∑ d ∈ s, rothLocalAbs tau (P.coeff d) := by
  apply Finset.sum_subset hs
  intro d _ hd
  rw [MvPolynomial.not_mem_support_iff.mp hd, rothLocalAbs_zero]

theorem rothLocalMass_add {σ : Type*} (tau : Fin 3) (P Q : MvPolynomial σ ℚ) :
    rothLocalMass tau (P + Q) ≤ rothLocalMass tau P + rothLocalMass tau Q := by
  let s := P.support ∪ Q.support
  have hP : P.support ⊆ s := Finset.subset_union_left
  have hQ : Q.support ⊆ s := Finset.subset_union_right
  rw [rothLocalMass_support_sum tau (P + Q) s MvPolynomial.support_add,
    rothLocalMass_support_sum tau P s hP, rothLocalMass_support_sum tau Q s hQ, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun d _ => by simpa using rothLocalAbs_add tau (P.coeff d) (Q.coeff d))

theorem rothLocalMass_sum {σ ι : Type*} (tau : Fin 3) (s : Finset ι)
    (f : ι → MvPolynomial σ ℚ) :
    rothLocalMass tau (∑ i ∈ s, f i) ≤ ∑ i ∈ s, rothLocalMass tau (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [rothLocalMass]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rothLocalMass_add tau _ _).trans (add_le_add_left ih _)

theorem rothLocalMass_mul {σ : Type*} (tau : Fin 3) (P Q : MvPolynomial σ ℚ) :
    rothLocalMass tau (P * Q) ≤ rothLocalMass tau P * rothLocalMass tau Q := by
  rw [MvPolynomial.mul_def, MvPolynomial.sum_def]
  calc
    _ ≤ ∑ a ∈ P.support, rothLocalMass tau (Q.sum fun b c =>
        MvPolynomial.monomial (a + b) (P.coeff a * c)) := rothLocalMass_sum _ _ _
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support,
        rothLocalMass tau (MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      apply Finset.sum_le_sum
      intro a _
      exact rothLocalMass_sum _ _ _
    _ = _ := by
      simp only [rothLocalMass_monomial, rothLocalAbs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      rfl

theorem rothLocalMass_pow {σ : Type*} (tau : Fin 3) (P : MvPolynomial σ ℚ) (n : ℕ) :
    rothLocalMass tau (P ^ n) ≤ rothLocalMass tau P ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, MvPolynomial.one_def, rothLocalMass_monomial, rothLocalAbs_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (rothLocalMass_mul tau _ _).trans
      (mul_le_mul_of_nonneg_right ih (rothLocalMass_nonneg tau P))

theorem rothLocalMass_prod {σ ι : Type*} (tau : Fin 3) (s : Finset ι)
    (f : ι → MvPolynomial σ ℚ) :
    rothLocalMass tau (∏ i ∈ s, f i) ≤ ∏ i ∈ s, rothLocalMass tau (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [MvPolynomial.one_def, rothLocalMass_monomial, rothLocalAbs_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (rothLocalMass_mul tau _ _).trans
      (mul_le_mul_of_nonneg_left ih (rothLocalMass_nonneg tau _))

theorem rothLocal_coeff_le_mass {σ : Type*} (tau : Fin 3)
    (P : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    rothLocalAbs tau (P.coeff d) ≤ rothLocalMass tau P := by
  by_cases hd : d ∈ P.support
  · exact Finset.single_le_sum (fun b _ => rothLocalAbs_nonneg tau (P.coeff b)) hd
  · rw [MvPolynomial.not_mem_support_iff.mp hd, rothLocalAbs_zero]
    exact rothLocalMass_nonneg _ _

theorem rothLocalMass_C {σ : Type*} (tau : Fin 3) (c : ℚ) :
    rothLocalMass tau (MvPolynomial.C c : MvPolynomial σ ℚ) = rothLocalAbs tau c := by
  change rothLocalMass tau (MvPolynomial.monomial 0 c) = _
  rw [rothLocalMass_monomial]

theorem rothLocalMass_C_mul_X {σ : Type*} (tau : Fin 3) (c : ℚ) (u : σ) :
    rothLocalMass tau (MvPolynomial.C c * MvPolynomial.X u) = rothLocalAbs tau c := by
  rw [MvPolynomial.X, MvPolynomial.C_mul_monomial, mul_one, rothLocalMass_monomial]


noncomputable def rothLocalInverseBound
    (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (fun u : Fin 3 × Fin 3 × Fin 3 =>
      rothLocalAbs u.1 ((rothLocalRationalMatrix (L u.1))⁻¹ u.2.1 u.2.2)))

theorem rothLocalInverseBound_one_le (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ) :
    1 ≤ rothLocalInverseBound L := le_max_left _ _

theorem rothLocalInverseBound_entry (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ)
    (tau i j : Fin 3) :
    rothLocalAbs tau ((rothLocalRationalMatrix (L tau))⁻¹ i j) ≤ rothLocalInverseBound L := by
  exact (Finset.le_sup' (fun u : Fin 3 × Fin 3 × Fin 3 =>
    rothLocalAbs u.1 ((rothLocalRationalMatrix (L u.1))⁻¹ u.2.1 u.2.2))
      (Finset.mem_univ (tau,i,j))).trans (le_max_right _ _)

theorem rothLocal_chart_mass {m : ℕ} (tau : Fin 3) (B : Matrix (Fin 3) (Fin 3) ℚ)
    (G : ℝ) (hB : ∀ i j, rothLocalAbs tau (B i j) ≤ G) (u : RothBlockVars m) :
    rothLocalMass tau (rothLocalLinearChart B u) ≤ 3 * G := by
  calc
    _ ≤ ∑ j : Fin 3, rothLocalMass tau (MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)) :=
      rothLocalMass_sum _ _ _
    _ ≤ ∑ _j : Fin 3, G := by
      apply Finset.sum_le_sum
      intro j _
      rw [rothLocalMass_C_mul_X]
      exact hB _ _
    _ = _ := by simp

theorem rothLocal_support_index {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (d : RothBlockVars m →₀ ℕ) (hd : d ∈ P.support) :
    ∃ b : RothAuxCoefficients r, rothAuxExponent b = d := by
  classical
  have hle (h : Fin m) (i : Fin 3) : d (h,i) ≤ r h := by
    rw [← hP d hd h]
    exact Finset.single_le_sum (f := fun j : Fin 3 => d (h,j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨fun h => ⟨fun i => ⟨d (h,i), by have hh := hle h i; omega⟩, hP d hd h⟩, ?_⟩
  ext u
  rfl

theorem rothLocal_support_card {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P) :
    P.support.card ≤ 3 ^ (∑ h, r h) := by
  classical
  have hs : P.support ⊆ Finset.univ.image (@rothAuxExponent m r) := by
    intro d hd
    obtain ⟨b,hb⟩ := rothLocal_support_index r P hP d hd
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hb⟩
  calc
    _ ≤ (Finset.univ.image (@rothAuxExponent m r)).card := Finset.card_le_card hs
    _ ≤ Fintype.card (RothAuxCoefficients r) := by simpa using Finset.card_image_le (s := Finset.univ) (f := @rothAuxExponent m r)
    _ ≤ _ := rothAuxDimension_le_three_pow r


theorem rothLocal_transformed_monomial_mass {m : ℕ} {r : Fin m → ℕ}
    (tau : Fin 3) (L : Matrix (Fin 3) (Fin 3) ℤ) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, rothLocalAbs tau ((rothLocalRationalMatrix L)⁻¹ i j) ≤ G)
    (b : RothAuxCoefficients r) (J : RothBlockVars m →₀ ℕ) (c : ℤ) :
    rothLocalMass tau (rothLocalExpansion L J (MvPolynomial.monomial (rothAuxExponent b) c)) ≤
      (c.natAbs : ℝ) * (6 * G) ^ (∑ h, r h) := by
  classical
  let R := ∑ h, r h
  let B := (rothLocalRationalMatrix L)⁻¹
  let a : ℤ := ∏ u : RothBlockVars m, (Nat.choose (rothAuxExponent b u) (J u) : ℤ)
  have hbase : 1 ≤ 3 * G := by linarith
  have hsum : (∑ u : RothBlockVars m, (rothAuxExponent b - J) u) ≤ R := by
    change (∑ u : RothBlockVars m, (rothAuxExponent b - J) u) ≤ ∑ h, r h
    rw [← rothAux_exponent_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  have hprod : rothLocalMass tau (∏ u : RothBlockVars m,
      rothLocalLinearChart B u ^ (rothAuxExponent b - J) u) ≤ (3 * G) ^ R := by
    calc
      _ ≤ ∏ u : RothBlockVars m,
          rothLocalMass tau (rothLocalLinearChart B u ^ (rothAuxExponent b - J) u) :=
        rothLocalMass_prod _ _ _
      _ ≤ ∏ u : RothBlockVars m, (3 * G) ^ (rothAuxExponent b - J) u := by
        apply Finset.prod_le_prod
        · intro u _; exact rothLocalMass_nonneg _ _
        · intro u _
          exact (rothLocalMass_pow tau _ _).trans
            (pow_le_pow_left₀ (rothLocalMass_nonneg _ _) (rothLocal_chart_mass tau B G hentry u) _)
      _ = (3 * G) ^ (∑ u : RothBlockVars m, (rothAuxExponent b - J) u) :=
        Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ _ := pow_le_pow_right₀ hbase hsum
  have hbin : rothLocalAbs tau (a : ℚ) ≤ (2 : ℝ) ^ R := by
    have h := rothAux_binomial_product_bound b J
    change |a| ≤ (2 : ℤ) ^ R at h
    rw [← Int.natCast_natAbs] at h
    have h' : (a.natAbs : ℝ) ≤ (2 : ℝ) ^ R := by exact_mod_cast h
    exact (rothLocalAbs_int tau a).trans h'
  have hconst : rothLocalAbs tau ((c * a : ℤ) : ℚ) ≤ (c.natAbs : ℝ) * (2 : ℝ) ^ R := by
    rw [Int.cast_mul, rothLocalAbs_mul]
    exact mul_le_mul (rothLocalAbs_int tau c) hbin (rothLocalAbs_nonneg _ _) (Nat.cast_nonneg _)
  have he : rothLocalExpansion L J (MvPolynomial.monomial (rothAuxExponent b) c) =
      MvPolynomial.C (((c * a : ℤ) : ℚ)) *
        ∏ u : RothBlockVars m, rothLocalLinearChart B u ^ (rothAuxExponent b - J) u := by
    rw [rothLocalExpansion, rothAux_derivative_monomial, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [he]
  calc
    _ ≤ rothLocalMass tau (MvPolynomial.C (((c * a : ℤ) : ℚ))) *
        rothLocalMass tau (∏ u : RothBlockVars m,
          rothLocalLinearChart B u ^ (rothAuxExponent b - J) u) := rothLocalMass_mul _ _ _
    _ ≤ ((c.natAbs : ℝ) * (2 : ℝ) ^ R) * (3 * G) ^ R := by
      rw [rothLocalMass_C]
      exact mul_le_mul hconst hprod (rothLocalMass_nonneg _ _) (by positivity)
    _ = _ := by rw [mul_assoc, ← mul_pow]; congr 2; ring


theorem rothLocal_expansion_coeff_bound {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (D : ℝ) (hD : 1 ≤ D) (hheight : (rothKernelBlockHeight P : ℝ) ≤ D ^ (∑ h, r h))
    (tau : Fin 3) (L : Matrix (Fin 3) (Fin 3) ℤ) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, rothLocalAbs tau ((rothLocalRationalMatrix L)⁻¹ i j) ≤ G)
    (J b : RothBlockVars m →₀ ℕ) :
    rothLocalAbs tau ((rothLocalExpansion L J P).coeff b) ≤
      (18 * D * G) ^ (∑ h, r h) := by
  classical
  let R := ∑ h, r h
  have hDpos : 0 ≤ D := le_trans (by norm_num) hD
  have hGpos : 0 ≤ G := le_trans (by norm_num) hG
  have hexp : rothLocalExpansion L J P =
      ∑ d ∈ P.support, rothLocalExpansion L J (MvPolynomial.monomial d (P.coeff d)) := by
    change MvPolynomial.eval₂Hom (Int.castRingHom _)
      (rothLocalLinearChart (rothLocalRationalMatrix L)⁻¹)
      (P.sum fun d c => MvPolynomial.monomial (d - J)
        (c * ∏ u : RothBlockVars m, (Nat.choose (d u) (J u) : ℤ))) = _
    rw [MvPolynomial.sum_def, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [rothLocalExpansion, rothAux_derivative_monomial]
  have hmass : rothLocalMass tau (rothLocalExpansion L J P) ≤ (18 * D * G) ^ R := by
    rw [hexp]
    calc
      _ ≤ ∑ d ∈ P.support,
          rothLocalMass tau (rothLocalExpansion L J (MvPolynomial.monomial d (P.coeff d))) :=
        rothLocalMass_sum _ _ _
      _ ≤ ∑ _d ∈ P.support, D ^ R * (6 * G) ^ R := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨a,ha⟩ := rothLocal_support_index r P hP d hd
        have hc : ((P.coeff d).natAbs : ℝ) ≤ D ^ R := by
          have hnat : (P.coeff d).natAbs ≤ rothKernelBlockHeight P :=
            Finset.le_sup (f := fun e => (P.coeff e).natAbs) hd
          have hreal : ((P.coeff d).natAbs : ℝ) ≤ (rothKernelBlockHeight P : ℝ) := by
            exact_mod_cast hnat
          exact hreal.trans hheight
        have hm := rothLocal_transformed_monomial_mass tau L G hG hentry a J (P.coeff d)
        rw [ha] at hm
        exact hm.trans (mul_le_mul_of_nonneg_right hc (by positivity))
      _ = (P.support.card : ℝ) * (D ^ R * (6 * G) ^ R) := by simp
      _ ≤ (3 : ℝ) ^ R * (D ^ R * (6 * G) ^ R) := by
        have hcard : (P.support.card : ℝ) ≤ (3 : ℝ) ^ R := by
          exact_mod_cast rothLocal_support_card r P hP
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring
  exact (rothLocal_coeff_le_mass tau _ b).trans hmass


theorem roth_auxiliary_integer_satz33
    (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ)
    (hL : ∀ tau, (rothLocalRationalMatrix (L tau)).det ≠ 0) :
    ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (RothBlockVars m) ℤ,
        P ≠ 0 ∧ rothBlockHomogeneous r P ∧
        (rothKernelBlockHeight P : ℝ) ≤ D ^ (∑ h, r h) ∧
        (∀ tau i, rothSourceHighIndex r (fun _ => L tau i) ((1 / 3 - eta) * m) P) ∧
        (∀ (tau : Fin 3) (J b : RothBlockVars m →₀ ℕ),
          rothLocalAbs tau ((rothLocalExpansion (L tau) J P).coeff b) ≤ E ^ (∑ h, r h)) ∧
        (∀ (tau : Fin 3) (J b : RothBlockVars m →₀ ℕ),
          rothSourceDerivativeWeight r J ≤ 2 * eta * m →
          (rothLocalExpansion (L tau) J P).coeff b ≠ 0 →
          ∀ i : Fin 3, |rothLocalCoordinateWeight r i b - (m : ℝ) / 3| ≤ 9 * m * eta) := by
  have hrows : ∀ tau i, ∃ j, L tau i j ≠ 0 :=
    fun tau i => rothLocal_nonzero_row (L tau) (hL tau) i
  obtain ⟨D0,hD0,hconstruction⟩ := roth_auxiliary_integer_three_place L hrows
  let G := rothLocalInverseBound L
  have hG : 1 ≤ G := rothLocalInverseBound_one_le L
  have hD : 1 ≤ 3 * D0 := by linarith
  have hE : 1 ≤ 6 * (3 * D0) * G := by
    have h6 : 1 ≤ 6 * (3 * D0) := by linarith
    exact h6.trans (le_mul_of_one_le_right (by linarith) hG)
  refine ⟨3 * D0,6 * (3 * D0) * G,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hnonzero,hhom,hheight,hindex⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hnonzero,hhom,?_,hindex,?_,?_⟩
  · exact hheight.trans (pow_le_pow_left₀ (by linarith) (by linarith) _)
  · intro tau J b
    have hbound := rothLocal_expansion_coeff_bound r P hhom D0 hD0 hheight
      tau (L tau) G hG (rothLocalInverseBound_entry L tau) J b
    have heq : 18 * D0 * G = 6 * (3 * D0) * G := by ring
    rwa [heq] at hbound
  · intro tau J b hJ hb
    exact rothLocal_coefficient_balance r hr eta heta (L tau) (hL tau) P hhom
      (hindex tau) J b hJ hb

end JSP000334
