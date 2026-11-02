import SubspaceBridge.AuxiliaryLocalExpansion

open scoped BigOperators Classical
namespace JSP000334

noncomputable def rothNormalForm (V : Fin 3 → ℤ) : (Fin 3 → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ i : Fin 3, (V i : ℚ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

noncomputable def rothNormalKernel (V : Fin 3 → ℤ) : Submodule ℚ (Fin 3 → ℚ) :=
  LinearMap.ker (rothNormalForm V)

theorem rothNormalKernel_finrank (V : Fin 3 → ℤ) (hnz : ∃ p, V p ≠ 0) :
    Module.finrank ℚ (rothNormalKernel V) = 2 := by
  obtain ⟨p,hp⟩ := hnz
  have hpQ : (V p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hsurj : Function.Surjective (rothNormalForm V) := by
    intro q
    refine ⟨Pi.single p (q / (V p : ℚ)), ?_⟩
    simp [rothNormalForm, Pi.single_apply, mul_ite, Finset.sum_ite_eq', hpQ]
    field_simp
  have hrange : LinearMap.range (rothNormalForm V) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hd := LinearMap.finrank_range_add_finrank_ker (rothNormalForm V)
  rw [hrange] at hd
  norm_num [Module.finrank_pi] at hd
  change Module.finrank ℚ (LinearMap.ker (rothNormalForm V)) = 2
  omega

noncomputable def rothNormalKernelVector (V : Fin 3 → ℤ) (w : Fin 2 → Fin 3 → ℤ)
    (horth : ∀ j : Fin 2, (∑ i : Fin 3, V i * w j i) = 0) (j : Fin 2) :
    rothNormalKernel V :=
  ⟨fun i => (w j i : ℚ), by
    change (∑ i : Fin 3, (V i : ℚ) * (w j i : ℚ)) = 0
    exact_mod_cast horth j⟩

noncomputable def rothNormalBasis (V : Fin 3 → ℤ) (hnz : ∃ p, V p ≠ 0)
    (w : Fin 2 → Fin 3 → ℤ)
    (hli : LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w j i : ℚ)))
    (horth : ∀ j : Fin 2, (∑ i : Fin 3, V i * w j i) = 0) :
    Basis (Fin 2) ℚ (rothNormalKernel V) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := rothNormalKernelVector V w horth)
    (LinearIndependent.of_comp (v := rothNormalKernelVector V w horth)
      (rothNormalKernel V).subtype hli)
    (by rw [Fintype.card_fin, rothNormalKernel_finrank V hnz])

theorem rothNormalBasis_apply (V : Fin 3 → ℤ) (hnz : ∃ p, V p ≠ 0)
    (w : Fin 2 → Fin 3 → ℤ)
    (hli : LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w j i : ℚ)))
    (horth : ∀ j : Fin 2, (∑ i : Fin 3, V i * w j i) = 0) (j : Fin 2) (i : Fin 3) :
    (rothNormalBasis V hnz w hli horth j : Fin 3 → ℚ) i = (w j i : ℚ) := by
  simp only [rothNormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

theorem rothNormalBasis_reconstruct (V : Fin 3 → ℤ) (hnz : ∃ p, V p ≠ 0)
    (w : Fin 2 → Fin 3 → ℤ)
    (hli : LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w j i : ℚ)))
    (horth : ∀ j : Fin 2, (∑ i : Fin 3, V i * w j i) = 0)
    (x : rothNormalKernel V) (i : Fin 3) :
    (∑ j : Fin 2, (rothNormalBasis V hnz w hli horth).repr x j * (w j i : ℚ)) = x.val i := by
  have hs := (rothNormalBasis V hnz w hli horth).sum_repr x
  have he := congrArg (fun z : rothNormalKernel V => z.val i) hs
  simpa [Submodule.coe_sum, rothNormalBasis_apply] using he


noncomputable def rothNormalChartColumn (V : Fin 3 → ℤ) (k l i : Fin 3) : ℚ :=
  (if i = l then 1 else 0) - (V l : ℚ) / (V k : ℚ) * (if i = k then 1 else 0)

theorem rothNormalChartColumn_mem (V : Fin 3 → ℤ) (k : Fin 3) (hk : V k ≠ 0)
    (l : Fin 3) : (fun i => rothNormalChartColumn V k l i) ∈ rothNormalKernel V := by
  have hkQ : (V k : ℚ) ≠ 0 := by exact_mod_cast hk
  change (∑ i : Fin 3, (V i : ℚ) * rothNormalChartColumn V k l i) = 0
  simp [rothNormalChartColumn, mul_sub, Finset.sum_sub_distrib, mul_ite,
    Finset.sum_ite_eq', Finset.sum_ite_eq]
  field_simp

theorem rothNormalChartColumn_chart {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0) (h : Fin m) (i : Fin 3) :
    (∑ l : Fin 3, MvPolynomial.C (rothNormalChartColumn (V h) (k h) l i) *
      MvPolynomial.X (h,l)) = rothKernelChart V k (h,i) := by
  classical
  by_cases hi : i = k h
  · subst i
    have hkQ : (V h (k h) : ℚ) ≠ 0 := by exact_mod_cast hk h
    have he : (∑ l : Fin 3, MvPolynomial.C (rothNormalChartColumn (V h) (k h) l (k h)) *
        MvPolynomial.X (h,l)) = MvPolynomial.X (h,k h) -
        ∑ l : Fin 3, MvPolynomial.C ((V h l : ℚ) / (V h (k h) : ℚ)) * MvPolynomial.X (h,l) := by
      simp [rothNormalChartColumn, map_sub, sub_mul, Finset.sum_sub_distrib,
        mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hs : (∑ l : Fin 3, MvPolynomial.C ((V h l : ℚ) / (V h (k h) : ℚ)) * MvPolynomial.X (h,l)) =
        (∑ l ∈ Finset.univ.erase (k h), MvPolynomial.C ((V h l : ℚ) / (V h (k h) : ℚ)) *
          MvPolynomial.X (h,l)) + MvPolynomial.X (h,k h) := by
      calc
        _ = (∑ l ∈ Finset.univ.erase (k h), MvPolynomial.C ((V h l : ℚ) / (V h (k h) : ℚ)) *
            MvPolynomial.X (h,l)) + MvPolynomial.C ((V h (k h) : ℚ) / (V h (k h) : ℚ)) *
              MvPolynomial.X (h,k h) :=
          (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k h))).symm
        _ = _ := by rw [div_self hkQ, map_one, one_mul]
    rw [he, hs]
    simp [rothKernelChart]
  · simp [rothNormalChartColumn, rothKernelChart, hi, map_sub, sub_mul,
      Finset.sum_sub_distrib, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

abbrev RothNormalVars (m : ℕ) := Fin m × Fin 2

noncomputable def rothNormalVectorChart {m : ℕ}
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (u : RothBlockVars m) :
    MvPolynomial (RothNormalVars m) ℚ :=
  ∑ j : Fin 2, MvPolynomial.C (w u.1 j u.2 : ℚ) * MvPolynomial.X (u.1,j)

noncomputable def rothNormalSubstitution {m : ℕ}
    (w : Fin m → Fin 2 → Fin 3 → ℤ) :
    MvPolynomial (RothBlockVars m) ℚ →+* MvPolynomial (RothNormalVars m) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalVectorChart w)

noncomputable def rothNormalDerivativeRestriction {m : ℕ}
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) : MvPolynomial (RothNormalVars m) ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w)
    (rothBlockIntegerDividedDerivative J P)


theorem rothNormalVectorChart_form {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0) (h : Fin m) :
    (∑ i : Fin 3, MvPolynomial.C (V h i : ℚ) * rothNormalVectorChart w (h,i)) = 0 := by
  have hq (j : Fin 2) : (∑ i : Fin 3, (V h i : ℚ) * (w h j i : ℚ)) = 0 := by
    exact_mod_cast horth h j
  calc
    _ = ∑ j : Fin 2, MvPolynomial.C (∑ i : Fin 3, (V h i : ℚ) * (w h j i : ℚ)) *
        MvPolynomial.X (h,j) := by
      simp only [rothNormalVectorChart, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← map_sum]
    _ = _ := by simp only [hq, map_zero, zero_mul, Finset.sum_const_zero]

theorem rothNormal_chart_factor_variable {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0) (u : RothBlockVars m) :
    rothNormalSubstitution w (rothKernelChart V k u) = rothNormalVectorChart w u := by
  classical
  have ha : (V u.1 (k u.1) : ℚ) ≠ 0 := by exact_mod_cast hk u.1
  have hcancel : (MvPolynomial.C ((V u.1 (k u.1) : ℚ)⁻¹) : MvPolynomial (RothNormalVars m) ℚ) *
      MvPolynomial.C (V u.1 (k u.1) : ℚ) = 1 := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, map_one]
  by_cases hu : u.2 = k u.1
  · have hs := rothNormalVectorChart_form V w horth u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k u.1))] at hs
    have hr : -(∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (V u.1 j : ℚ) * rothNormalVectorChart w (u.1,j)) =
        MvPolynomial.C (V u.1 (k u.1) : ℚ) * rothNormalVectorChart w (u.1,k u.1) := by
      linear_combination -hs
    simp only [rothKernelChart, hu, if_pos rfl, ite_true, map_neg, map_sum, map_mul,
      rothNormalSubstitution, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((V u.1 (k u.1) : ℚ)⁻¹) *
          -(∑ j ∈ Finset.univ.erase (k u.1), MvPolynomial.C (V u.1 j : ℚ) *
            rothNormalVectorChart w (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv, MvPolynomial.C_mul]
        ring
      _ = _ := by rw [hr, ← mul_assoc, hcancel, one_mul]; simp [← hu]
  · simp [rothKernelChart, hu, rothNormalSubstitution]

noncomputable def rothNormalBackChart {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (hli : ∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ)))
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0)
    (u : RothNormalVars m) : MvPolynomial (RothBlockVars m) ℚ :=
  ∑ l : Fin 3, MvPolynomial.C
    ((rothNormalBasis (V u.1) ⟨k u.1,hk u.1⟩ (w u.1) (hli u.1) (horth u.1)).repr
      ⟨fun i => rothNormalChartColumn (V u.1) (k u.1) l i,
        rothNormalChartColumn_mem (V u.1) (k u.1) (hk u.1) l⟩ u.2) *
      MvPolynomial.X (u.1,l)

theorem rothNormal_back_chart_variable {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (hli : ∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ)))
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0) (u : RothBlockVars m) :
    MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalBackChart V k hk w hli horth)
      (rothNormalVectorChart w u) = rothKernelChart V k u := by
  classical
  simp only [rothNormalVectorChart, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', rothNormalBackChart]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm, ← rothNormalChartColumn_chart V k hk u.1 u.2]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.sum_mul, ← map_sum]
  congr 1
  apply congrArg MvPolynomial.C
  have hr := rothNormalBasis_reconstruct (V u.1) ⟨k u.1,hk u.1⟩
    (w u.1) (hli u.1) (horth u.1)
    ⟨fun i => rothNormalChartColumn (V u.1) (k u.1) l i,
      rothNormalChartColumn_mem (V u.1) (k u.1) (hk u.1) l⟩ u.2
  simpa only [mul_comm] using hr


theorem rothNormal_chart_factor {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0)
    (Q : MvPolynomial (RothBlockVars m) ℤ) :
    rothNormalSubstitution w (rothKernelRestriction V k Q) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w) Q := by
  have he : (rothNormalSubstitution w).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom _) (rothKernelChart V k)) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [rothNormalSubstitution]
    · intro u
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact rothNormal_chart_factor_variable V k hk w horth u
  exact congrArg (fun f => f Q) he

theorem rothNormal_chart_recover {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (hli : ∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ)))
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0)
    (Q : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalBackChart V k hk w hli horth)
      (MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w) Q) =
      rothKernelRestriction V k Q := by
  have he : (MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalBackChart V k hk w hli horth)).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w)) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothKernelChart V k) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro u
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact rothNormal_back_chart_variable V k hk w hli horth u
  exact congrArg (fun f => f Q) he

theorem rothNormal_restriction_ne_zero_iff {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (hli : ∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ)))
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0)
    (Q : MvPolynomial (RothBlockVars m) ℤ) :
    rothKernelRestriction V k Q ≠ 0 ↔
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w) Q ≠ 0 := by
  constructor
  · intro hn hz
    have he := rothNormal_chart_recover V k hk w hli horth Q
    rw [hz, map_zero] at he
    exact hn he.symm
  · intro hn hz
    have he := rothNormal_chart_factor V k hk w horth Q
    rw [hz, map_zero] at he
    exact hn he.symm

theorem rothNormal_derivative_ne_zero_iff {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, V h (k h) ≠ 0)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (hli : ∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ)))
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    rothKernelRestriction V k (rothBlockIntegerDividedDerivative J P) ≠ 0 ↔
      rothNormalDerivativeRestriction w J P ≠ 0 :=
  rothNormal_restriction_ne_zero_iff V k hk w hli horth (rothBlockIntegerDividedDerivative J P)

theorem rothNormal_exists_basis (V : Fin 3 → ℤ) (hnz : ∃ p, V p ≠ 0)
    (w : Fin 2 → Fin 3 → ℤ)
    (hli : LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w j i : ℚ)))
    (horth : ∀ j : Fin 2, (∑ i : Fin 3, V i * w j i) = 0) :
    ∃ B : Basis (Fin 2) ℚ (rothNormalKernel V),
      ∀ j i, (B j : Fin 3 → ℚ) i = (w j i : ℚ) :=
  ⟨rothNormalBasis V hnz w hli horth, rothNormalBasis_apply V hnz w hli horth⟩


noncomputable def rothNormalIntegerVectorChart {m : ℕ}
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (u : RothBlockVars m) :
    MvPolynomial (RothNormalVars m) ℤ :=
  ∑ j : Fin 2, MvPolynomial.C (w u.1 j u.2) * MvPolynomial.X (u.1,j)

noncomputable def rothNormalIntegerRestriction {m : ℕ}
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) : MvPolynomial (RothNormalVars m) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalIntegerVectorChart w)
    (rothBlockIntegerDividedDerivative J P)

theorem rothNormal_integer_map {m : ℕ} (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) (rothNormalIntegerRestriction w J P) =
      rothNormalDerivativeRestriction w J P := by
  have he : (MvPolynomial.map (Int.castRingHom ℚ)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C (rothNormalIntegerVectorChart w)) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothNormalVectorChart w) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro u
      simp [rothNormalIntegerVectorChart, rothNormalVectorChart]
  exact congrArg (fun f => f (rothBlockIntegerDividedDerivative J P)) he

theorem rothNormal_integer_coeff {m : ℕ} (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (b : RothNormalVars m →₀ ℕ) :
    (rothNormalDerivativeRestriction w J P).coeff b =
      (((rothNormalIntegerRestriction w J P).coeff b : ℤ) : ℚ) := by
  rw [← rothNormal_integer_map, MvPolynomial.coeff_map]
  rfl

theorem rothNormal_integer_support {m : ℕ} (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    (rothNormalDerivativeRestriction w J P).support =
      (rothNormalIntegerRestriction w J P).support := by
  rw [← rothNormal_integer_map]
  exact MvPolynomial.support_map_of_injective _ Int.cast_injective

noncomputable def rothNormalFiniteExponents {m : ℕ}
    (w : Fin m → Fin 2 → Fin 3 → ℤ) (J : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) : Finset (RothNormalVars m → ℕ) :=
  (rothNormalIntegerRestriction w J P).support.image Finsupp.equivFunOnFinite

theorem rothNormal_finite_exponents_mem {m : ℕ} (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (e : RothNormalVars m → ℕ) :
    e ∈ rothNormalFiniteExponents w J P ↔
      (rothNormalDerivativeRestriction w J P).coeff (Finsupp.equivFunOnFinite.symm e) ≠ 0 := by
  classical
  rw [← MvPolynomial.mem_support_iff, rothNormal_integer_support]
  change e ∈ (rothNormalIntegerRestriction w J P).support.image Finsupp.equivFunOnFinite ↔ _
  constructor
  · intro he
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp he
    simpa only [← he, Equiv.symm_apply_apply] using hb
  · intro he
    exact Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite.symm e,he,Equiv.apply_symm_apply _ _⟩

theorem rothNormal_derivative_expansion {m : ℕ} (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    rothNormalDerivativeRestriction w J P =
      ∑ d ∈ P.support, MvPolynomial.C (((P.coeff d *
        ∏ u : RothBlockVars m, (Nat.choose (d u) (J u) : ℤ) : ℤ) : ℚ)) *
          ∏ u : RothBlockVars m, rothNormalVectorChart w u ^ (d - J) u := by
  unfold rothNormalDerivativeRestriction rothBlockIntegerDividedDerivative
  rw [MvPolynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem rothNormal_nonzero_coefficient {m : ℕ} (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (hn : rothNormalDerivativeRestriction w J P ≠ 0) :
    ∃ (e : RothNormalVars m → ℕ) (z : ℤ),
      e ∈ rothNormalFiniteExponents w J P ∧ z ≠ 0 ∧
      (rothNormalDerivativeRestriction w J P).coeff (Finsupp.equivFunOnFinite.symm e) = (z : ℚ) := by
  obtain ⟨b,hb⟩ := MvPolynomial.exists_coeff_ne_zero hn
  refine ⟨Finsupp.equivFunOnFinite b,(rothNormalIntegerRestriction w J P).coeff b,?_,?_,?_⟩
  · rw [rothNormal_finite_exponents_mem, Equiv.symm_apply_apply]
    exact hb
  · intro hz
    apply hb
    rw [rothNormal_integer_coeff, hz, Int.cast_zero]
  · rw [Equiv.symm_apply_apply, rothNormal_integer_coeff]

theorem rothNormal_kernel_basis_bridge {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (hrow : ∀ h, (∃ i, V h i ≠ 0) ∧ Ideal.span (Set.range (V h)) = ⊤)
    (w : Fin m → Fin 2 → Fin 3 → ℤ)
    (hli : ∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ)))
    (horth : ∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    (∀ h, ∃ B : Basis (Fin 2) ℚ (rothNormalKernel (V h)),
      ∀ j i, (B j : Fin 3 → ℚ) i = (w h j i : ℚ)) ∧
    ∀ (k : Fin m → Fin 3), (∀ h, V h (k h) ≠ 0) →
      (rothKernelRestriction V k (rothBlockIntegerDividedDerivative J P) ≠ 0 ↔
        ∃ (e : RothNormalVars m → ℕ) (z : ℤ),
          e ∈ rothNormalFiniteExponents w J P ∧ z ≠ 0 ∧
          (rothNormalDerivativeRestriction w J P).coeff (Finsupp.equivFunOnFinite.symm e) = (z : ℚ)) := by
  refine ⟨fun h => rothNormal_exists_basis (V h) (hrow h).1 (w h) (hli h) (horth h), ?_⟩
  intro k hk
  rw [rothNormal_derivative_ne_zero_iff V k hk w hli horth]
  constructor
  · exact rothNormal_nonzero_coefficient w J P
  · rintro ⟨e,z,he,hz,hcoeff⟩
    apply MvPolynomial.ne_zero_iff.mpr
    refine ⟨Finsupp.equivFunOnFinite.symm e,?_⟩
    rw [hcoeff]
    exact_mod_cast hz

end JSP000334
