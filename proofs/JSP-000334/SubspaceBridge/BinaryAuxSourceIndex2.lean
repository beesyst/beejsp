import SubspaceBridge.BinaryAuxSupport2
import SubspaceBridge.BinaryAuxSiegel2
import Mathlib.Algebra.MvPolynomial.PDeriv
open scoped BigOperators Classical
namespace JSP000334

theorem binary_derivative_add {m : ℕ} (J : RothBlockVars2 m →₀ ℕ)
    (P Q : MvPolynomial (RothBlockVars2 m) ℤ) :
    binaryDividedDerivative J (P+Q) = binaryDividedDerivative J P+binaryDividedDerivative J Q := by
  apply MvPolynomial.ext
  intro e
  simp only [binary_derivative_coeff,MvPolynomial.coeff_add,add_mul]

theorem binary_source_pderiv_eq_single {m : ℕ} (u : RothBlockVars2 m)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial.pderiv u P = binaryDividedDerivative (Finsupp.single u 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, binary_derivative_add, hP, hQ]
  | monomial b c =>
    rw [MvPolynomial.pderiv_monomial, binary_derivative_monomial]
    congr 1
    congr 1
    rw [Finset.prod_eq_single u]
    · simp [Finsupp.single_apply, add_comm]
    · intro x hx hxu
      simp [Finsupp.single_apply, Ne.symm hxu]
    · simp

theorem binary_source_derivative_comp {m : ℕ} (a b : RothBlockVars2 m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    binaryDividedDerivative a (binaryDividedDerivative b P) =
      (∏ k : RothBlockVars2 m, (Nat.choose ((a + b) k) (a k) : ℤ)) •
        binaryDividedDerivative (a + b) P := by
  classical
  apply MvPolynomial.ext
  intro c
  simp only [binary_derivative_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  have hch (k : RothBlockVars2 m) :
      Nat.choose ((c + a + b) k) (b k) * Nat.choose ((c + a) k) (a k) =
        Nat.choose ((a + b) k) (a k) * Nat.choose ((c + a + b) k) ((a + b) k) := by
    simp only [Finsupp.add_apply]
    have h := Nat.choose_mul (n := c k + a k + b k) (k := a k + b k) (s := b k)
      (by omega) (by omega)
    have hn : c k + a k + b k - b k = c k + a k := by omega
    have ha : a k + b k - b k = a k := by omega
    rw [hn, ha] at h
    have hs : Nat.choose (a k + b k) (b k) = Nat.choose (a k + b k) (a k) :=
      Nat.choose_symm_add.symm
    rw [hs] at h
    nlinarith
  calc
    _ = P.coeff (c + (a + b)) *
        ∏ k : RothBlockVars2 m, ((Nat.choose ((c + a + b) k) (b k) : ℤ) *
          (Nat.choose ((c + a) k) (a k) : ℤ)) := by
      rw [Finset.prod_mul_distrib]
      simp only [add_assoc]
      ring
    _ = P.coeff (c + (a + b)) *
        ∏ k : RothBlockVars2 m, ((Nat.choose ((a + b) k) (a k) : ℤ) *
          (Nat.choose ((c + a + b) k) ((a + b) k) : ℤ)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      exact_mod_cast hch k
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [add_assoc]; ring

theorem binary_source_pderiv_hasse {m : ℕ} (u : RothBlockVars2 m)
    (J : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial.pderiv u (binaryDividedDerivative J P) =
      (J u + 1) • binaryDividedDerivative (J + Finsupp.single u 1) P := by
  rw [binary_source_pderiv_eq_single, binary_source_derivative_comp, add_comm J]
  congr 1
  rw [Finset.prod_eq_single u]
  · simp [Finsupp.single_apply, add_comm]
  · intro x hx hxu
    simp [Finsupp.single_apply, Ne.symm hxu]
  · simp


noncomputable def binarySourceDerivativeWeight {m : ℕ} (r : Fin m → ℕ) (J : RothBlockVars2 m →₀ ℕ) : ℝ :=
  ∑ h, (∑ i : Fin 2, (J (h,i) : ℝ))/(r h : ℝ)

theorem binary_source_scaled_chart_pderiv {m : ℕ} (a : Fin 2 → ℤ) (k j : Fin 2)
    (h : Fin m) (hj : j ≠ k) (v : RothBlockVars2 m) :
    MvPolynomial.pderiv (h,j) (binaryScaledChart a k v) =
      MvPolynomial.C (a k)*(if v=(h,j) then 1 else 0)-
        MvPolynomial.C (a j)*(if v=(h,k) then 1 else 0) := by
  rcases v with ⟨g,l⟩
  by_cases hg : g=h
  · subst g
    fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp_all [binaryScaledChart,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,
        Pi.single_apply,Prod.mk.injEq]
  · fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp_all [binaryScaledChart,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,
        Pi.single_apply,Prod.mk.injEq,eq_comm]

theorem binary_source_scaled_chain {m : ℕ} (a : Fin 2 → ℤ) (k j : Fin 2)
    (h : Fin m) (hj : j ≠ k) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial.pderiv (h,j) (binaryScaledSubstitution a k P) =
      MvPolynomial.C (a k)*binaryScaledSubstitution a k (MvPolynomial.pderiv (h,j) P)-
        MvPolynomial.C (a j)*binaryScaledSubstitution a k (MvPolynomial.pderiv (h,k) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [binaryScaledSubstitution]
  | add P Q hP hQ => simp only [map_add,hP,hQ]; ring
  | mul_X P v hP =>
    simp only [map_mul,MvPolynomial.pderiv_mul,map_add,hP]
    rw [show binaryScaledSubstitution a k (MvPolynomial.X v) = binaryScaledChart a k v by
        simp [binaryScaledSubstitution],binary_source_scaled_chart_pderiv a k j h hj v]
    simp only [MvPolynomial.pderiv_X,Pi.single_apply,apply_ite,map_one,map_zero]
    split_ifs <;> simp_all <;> ring

theorem binary_source_weight_add {m : ℕ} (r : Fin m → ℕ) (J K : RothBlockVars2 m →₀ ℕ) :
    binarySourceDerivativeWeight r (J + K) =
      binarySourceDerivativeWeight r J + binarySourceDerivativeWeight r K := by
  simp [binarySourceDerivativeWeight, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, add_div]

theorem binary_source_weight_mono {m : ℕ} (r : Fin m → ℕ)
    (J K : RothBlockVars2 m →₀ ℕ) (hJK : J ≤ K) :
    binarySourceDerivativeWeight r J ≤ binarySourceDerivativeWeight r K := by
  apply Finset.sum_le_sum
  intro h _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact_mod_cast hJK (h,i)

theorem binary_source_weight_single {m : ℕ} (r : Fin m → ℕ) (u : RothBlockVars2 m) :
    binarySourceDerivativeWeight r (Finsupp.single u 1) = 1 / (r u.1 : ℝ) := by
  classical
  rcases u with ⟨h,j⟩
  simp [binarySourceDerivativeWeight, Finsupp.single_apply, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [ite_div, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem binary_source_weight_pivot {m : ℕ} (r : Fin m → ℕ) (k : Fin 2) (i : Fin m → ℕ) :
    binarySourceDerivativeWeight r (binaryPivotDerivative k i) = ∑ h, (i h : ℝ) / r h := by
  simp [binarySourceDerivativeWeight, binaryPivotDerivative, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

noncomputable def binarySourceFreeOrder {m : ℕ} (k : Fin 2) (J : RothBlockVars2 m →₀ ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : RothBlockVars2 m => u.2 ≠ k), J u

theorem binary_source_free_add {m : ℕ} (k : Fin 2) (J K : RothBlockVars2 m →₀ ℕ) :
    binarySourceFreeOrder k (J + K) = binarySourceFreeOrder k J + binarySourceFreeOrder k K := by
  simp [binarySourceFreeOrder, Finsupp.add_apply, Finset.sum_add_distrib]

theorem binary_source_free_single {m : ℕ} (k : Fin 2) (u : RothBlockVars2 m) :
    binarySourceFreeOrder k (Finsupp.single u 1) = if u.2 = k then 0 else 1 := by
  classical
  simp [binarySourceFreeOrder, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem binary_source_free_zero_pivot {m : ℕ} (k : Fin 2) (J : RothBlockVars2 m →₀ ℕ)
    (hJ : binarySourceFreeOrder k J = 0) :
    J = binaryPivotDerivative k (fun h => J (h,k)) := by
  classical
  ext u
  by_cases hu : u.2 = k
  · have he : u = (u.1,k) := Prod.ext rfl hu
    simpa [binaryPivotDerivative, hu] using congrArg J he
  · have hle : J u ≤ binarySourceFreeOrder k J :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ u,hu⟩)
    have hz : J u = 0 := by omega
    simp [binaryPivotDerivative, hu, hz]

theorem binary_source_scaled_mixed_vanishing {m : ℕ} (r : Fin m → ℕ)
    (a : Fin 2 → ℤ) (k : Fin 2) (ha : a k ≠ 0) (T : ℝ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hpivot : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      binaryScaledSubstitution a k
        (binaryDividedDerivative (binaryPivotDerivative k i) P) = 0)
    (J : RothBlockVars2 m →₀ ℕ) (hw : binarySourceDerivativeWeight r J < T) :
    binaryScaledSubstitution a k (binaryDividedDerivative J P) = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J : RothBlockVars2 m →₀ ℕ,
      binarySourceFreeOrder k J = n → binarySourceDerivativeWeight r J < T →
      binaryScaledSubstitution a k (binaryDividedDerivative J P) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hn hw
      by_cases hz : n = 0
      · have he := binary_source_free_zero_pivot k J (hn.trans hz)
        have hweight : (∑ h, (J (h,k) : ℝ) / r h) < T := by
          rw [← binary_source_weight_pivot r k, ← he]
          exact hw
        rw [he]
        exact hpivot _ hweight
      · have hex : ∃ u : RothBlockVars2 m, u.2 ≠ k ∧ J u ≠ 0 := by
          by_contra! hno
          have hzero : binarySourceFreeOrder k J = 0 := by
            apply Finset.sum_eq_zero
            intro u hu
            exact hno u (Finset.mem_filter.mp hu).2
          omega
        obtain ⟨u, hu, hJu⟩ := hex
        let K := J - Finsupp.single u 1
        let Kp := K + Finsupp.single (u.1,k) 1
        have hle : Finsupp.single u 1 ≤ J := by
          rw [Finsupp.single_le_iff]
          omega
        have hKeq : K + Finsupp.single u 1 = J := tsub_add_cancel_of_le hle
        have hKcount : binarySourceFreeOrder k K + 1 = n := by
          have hc := congrArg (binarySourceFreeOrder k) hKeq
          simpa [binary_source_free_add, binary_source_free_single, hu, hn] using hc
        have hKpcount : binarySourceFreeOrder k Kp = binarySourceFreeOrder k K := by
          simp [Kp, binary_source_free_add, binary_source_free_single]
        have hKweight : binarySourceDerivativeWeight r K ≤ binarySourceDerivativeWeight r J :=
          binary_source_weight_mono r K J tsub_le_self
        have hKpweight : binarySourceDerivativeWeight r Kp = binarySourceDerivativeWeight r J := by
          calc
            _ = binarySourceDerivativeWeight r K + 1 / (r u.1 : ℝ) := by
              rw [binary_source_weight_add, binary_source_weight_single]
            _ = _ := by rw [← hKeq, binary_source_weight_add, binary_source_weight_single]
        have hK := ih (binarySourceFreeOrder k K) (by omega) K rfl (lt_of_le_of_lt hKweight hw)
        have hKp := ih (binarySourceFreeOrder k Kp) (by omega) Kp rfl (hKpweight ▸ hw)
        change binaryScaledSubstitution a k
          (binaryDividedDerivative (K + Finsupp.single (u.1,k) 1) P) = 0 at hKp
        have hc := binary_source_scaled_chain a k u.2 u.1 hu
          (binaryDividedDerivative K P)
        rw [binary_source_pderiv_hasse, binary_source_pderiv_hasse] at hc
        simp only [hK, map_zero, map_nsmul, hKp, nsmul_zero, mul_zero, sub_zero] at hc
        rw [hKeq] at hc
        have hcoeff : (MvPolynomial.C (a k) : MvPolynomial (RothBlockVars2 m) ℤ) ≠ 0 := by
          intro hz
          apply ha
          apply MvPolynomial.C_injective (σ := RothBlockVars2 m)
          simpa only [map_zero] using hz
        have hsm := (mul_eq_zero.mp hc.symm).resolve_left hcoeff
        rw [nsmul_eq_mul] at hsm
        exact (mul_eq_zero.mp hsm).resolve_left (by
          intro hh
          have hz : ((K (u.1,u.2) + 1 : ℕ) : ℤ) = 0 := by
            apply MvPolynomial.C_injective (σ := RothBlockVars2 m)
            simpa only [map_natCast, map_zero] using hh
          omega)
  exact go _ J rfl hw


noncomputable def binaryKernelChart {m : ℕ} (V : Fin m → Fin 2 → ℤ)
    (k : Fin m → Fin 2) (u : RothBlockVars2 m) : MvPolynomial (RothBlockVars2 m) ℚ :=
  if u.2 = k u.1 then
    -(∑ i ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C ((V u.1 i : ℚ) / (V u.1 (k u.1) : ℚ)) * MvPolynomial.X (u.1, i))
  else MvPolynomial.X u

noncomputable def binaryKernelRestriction {m : ℕ} (V : Fin m → Fin 2 → ℤ)
    (k : Fin m → Fin 2) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    MvPolynomial (RothBlockVars2 m) ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom _) (binaryKernelChart V k) P

theorem binary_scaled_chart_eq {m : ℕ} (a : Fin 2 → ℤ) (k : Fin 2) (u : RothBlockVars2 m) :
    binaryScaledChart a k u = if u.2=k then
      -(∑ j ∈ Finset.univ.erase k, MvPolynomial.C (a j)*MvPolynomial.X (u.1,j))
      else MvPolynomial.C (a k)*MvPolynomial.X u := by
  rcases u with ⟨h,j⟩
  fin_cases k <;> fin_cases j <;> simp [binaryScaledChart]

theorem binary_source_kernel_chart_form {m : ℕ} (a : Fin 2 → ℤ)
    (k : Fin m → Fin 2) (hk : ∀ h, a (k h) ≠ 0) (h : Fin m) :
    (∑ j : Fin 2, MvPolynomial.C (a j : ℚ) *
      binaryKernelChart (fun _ : Fin m => a) k (h,j)) = 0 := by
  classical
  have ha : (a (k h) : ℚ) ≠ 0 := by exact_mod_cast hk h
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k h))]
  have hfree : (∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j : ℚ) *
      binaryKernelChart (fun _ : Fin m => a) k (h,j)) =
      ∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j : ℚ) * MvPolynomial.X (h,j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [binaryKernelChart, (Finset.mem_erase.mp hj).1]
  rw [hfree]
  have hpivot : MvPolynomial.C (a (k h) : ℚ) *
      binaryKernelChart (fun _ : Fin m => a) k (h,k h) =
      -(∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j : ℚ) * MvPolynomial.X (h,j)) := by
    simp only [binaryKernelChart, Prod.fst, Prod.snd, if_pos rfl, ite_true, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    congr 1
    field_simp [ha]
  rw [hpivot]
  ring

noncomputable def binarySourceChartTransport {m : ℕ} (a : Fin 2 → ℤ) (p : Fin 2)
    (k : Fin m → Fin 2) :
    MvPolynomial (RothBlockVars2 m) ℤ →+* MvPolynomial (RothBlockVars2 m) ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun u =>
    MvPolynomial.C ((a p : ℚ)⁻¹) * binaryKernelChart (fun _ : Fin m => a) k u)

theorem binary_source_chart_transport_variable {m : ℕ} (a : Fin 2 → ℤ)
    (p : Fin 2) (hp : a p ≠ 0) (k : Fin m → Fin 2)
    (hk : ∀ h, a (k h) ≠ 0) (u : RothBlockVars2 m) :
    binarySourceChartTransport a p k (binaryScaledChart a p u) =
      binaryKernelChart (fun _ : Fin m => a) k u := by
  classical
  have ha : (a p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hcancel : (MvPolynomial.C (a p : ℚ) : MvPolynomial (RothBlockVars2 m) ℚ) *
      MvPolynomial.C ((a p : ℚ)⁻¹) = 1 := by rw [← MvPolynomial.C_mul, mul_inv_cancel₀ ha, map_one]
  have hcast (z : ℤ) :
      (Int.castRingHom (MvPolynomial (RothBlockVars2 m) ℚ)) z = MvPolynomial.C (z : ℚ) :=
    (map_intCast (MvPolynomial.C : ℚ →+* MvPolynomial (RothBlockVars2 m) ℚ) z).symm
  by_cases hu : u.2 = p
  · have hsum := binary_source_kernel_chart_form a k hk u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hsum
    have hrel : -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j : ℚ) *
        binaryKernelChart (fun _ : Fin m => a) k (u.1,j)) =
        MvPolynomial.C (a p : ℚ) * binaryKernelChart (fun _ : Fin m => a) k (u.1,p) := by
      linear_combination -hsum
    simp only [binary_scaled_chart_eq, if_pos hu, map_neg, map_sum, map_mul]
    simp only [binarySourceChartTransport, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      hcast]
    calc
      _ = MvPolynomial.C ((a p : ℚ)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j : ℚ) *
            binaryKernelChart (fun _ : Fin m => a) k (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hrel]; rw [← mul_assoc, mul_comm _ (MvPolynomial.C (a p : ℚ)), hcancel]; simp [← hu]
  · simp only [binary_scaled_chart_eq, if_neg hu, map_mul]
    simp only [binarySourceChartTransport, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      hcast]
    rw [← mul_assoc, hcancel, one_mul]

theorem binary_source_chart_transport {m : ℕ} (a : Fin 2 → ℤ)
    (p : Fin 2) (hp : a p ≠ 0) (k : Fin m → Fin 2)
    (hk : ∀ h, a (k h) ≠ 0) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    binarySourceChartTransport a p k (binaryScaledSubstitution a p P) =
      binaryKernelRestriction (fun _ : Fin m => a) k P := by
  have he : (binarySourceChartTransport a p k).comp (binaryScaledSubstitution a p) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (binaryKernelChart (fun _ : Fin m => a) k) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [binaryScaledSubstitution, binarySourceChartTransport]
    · intro u
      simpa [binaryScaledSubstitution] using binary_source_chart_transport_variable a p hp k hk u
  exact congrArg (fun f => f P) he

theorem binary_source_derivative_zero_of_block_excess {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (J : RothBlockVars2 m →₀ ℕ) (h : Fin m) (hJ : r h < ∑ j : Fin 2, J (h,j)) :
    binaryDividedDerivative J P = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [binary_derivative_coeff, MvPolynomial.coeff_zero]
  have hz : P.coeff (d + J) = 0 := by
    by_contra hn
    have hdegree := hP (d + J) (MvPolynomial.mem_support_iff.mpr hn) h
    have hle : (∑ j : Fin 2, J (h,j)) ≤ ∑ j : Fin 2, (d + J) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finsupp.add_apply]
      omega
    omega
  rw [hz, zero_mul]


def binarySourceHighIndex {m : ℕ} (r : Fin m → ℕ) (V : Fin m → Fin 2 → ℤ)
    (T : ℝ) (P : MvPolynomial (RothBlockVars2 m) ℤ) : Prop :=
  ∀ J, binarySourceDerivativeWeight r J < T → ∀ k, (∀ h, V h (k h) ≠ 0) →
    binaryKernelRestriction V k (binaryDividedDerivative J P) = 0

theorem binary_pivot_derivative_excess {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (k : Fin 2) (i : Fin m → ℕ) (h : Fin m) (hi : r h < i h) :
    binaryDividedDerivative (binaryPivotDerivative k i) P = 0 := by
  apply MvPolynomial.ext
  intro e
  rw [binary_derivative_coeff,MvPolynomial.coeff_zero]
  have hz : P.coeff (e+binaryPivotDerivative k i) = 0 := by
    by_contra hn
    have hs := hP _ (MvPolynomial.mem_support_iff.mpr hn) h
    have hle := Finset.single_le_sum
      (fun j _ => Nat.zero_le ((e+binaryPivotDerivative k i) (h,j))) (Finset.mem_univ k)
    have hh : (e+binaryPivotDerivative k i) (h,k) = e (h,k)+i h := by simp [binaryPivotDerivative]
    omega
  rw [hz,zero_mul]

theorem binary_kernel_pivot_vanishing {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (c : BinaryAuxCoefficients r → ℤ) (hc : (binaryAuxMatrix r eta L hL).mulVec c = 0)
    (f : Fin 3 × Fin 2) (i : Fin m → ℕ) (hi : (∑ h, (i h : ℝ)/(r h : ℝ)) < (1/2-eta)*m) :
    binaryScaledSubstitution (L f.1 f.2) (binaryAuxPivot L hL f)
      (binaryDividedDerivative (binaryPivotDerivative (binaryAuxPivot L hL f) i)
        (binaryAuxPolynomial c)) = 0 := by
  by_cases hb : ∀ h, i h ≤ r h
  · let b : BinaryAuxCoefficients r := fun h => ⟨i h,by have hh := hb h; omega⟩
    exact (binary_matrix_kernel_iff r eta L hL c).mp hc f b hi
  · push_neg at hb
    obtain ⟨h,hh⟩ := hb
    rw [binary_pivot_derivative_excess r _ (binary_polynomial_homogeneous c) _ i h hh,map_zero]

theorem binary_kernel_source_high_index {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (c : BinaryAuxCoefficients r → ℤ) (hc : (binaryAuxMatrix r eta L hL).mulVec c = 0)
    (tau : Fin 3) (i : Fin 2) :
    binarySourceHighIndex r (fun _ => L tau i) ((1/2-eta)*m) (binaryAuxPolynomial c) := by
  let p := binaryAuxPivot L hL (tau,i)
  have hp : L tau i p ≠ 0 := (hL tau i).choose_spec
  intro J hJ k hk
  rw [← binary_source_chart_transport (L tau i) p hp k hk]
  rw [binary_source_scaled_mixed_vanishing r (L tau i) p hp _ _
    (fun j hj => binary_kernel_pivot_vanishing r eta L hL c hc (tau,i) j hj) J hJ,map_zero]

theorem binary_auxiliary_integer_three_place
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ)
    (hL : ∀ tau, Matrix.det (fun i j => (L tau i j : ℚ)) ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ eta : ℝ, 0 < eta → eta < 1/2 →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log 12 ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (RothBlockVars2 m) ℤ,
        P ≠ 0 ∧ binaryBlockHomogeneous r P ∧
        (binaryPolynomialHeight P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau : Fin 3, ∀ i : Fin 2,
          binarySourceHighIndex r (fun _ => L tau i) ((1/2-eta)*m) P := by
  have hrows : ∀ tau i, ∃ j, L tau i j ≠ 0 := by
    intro tau i
    by_contra hh
    push_neg at hh
    apply hL tau
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [hh j])
  obtain ⟨D,hD,hpoly⟩ := binary_auxiliary_coefficient_kernel L hrows
  refine ⟨D,hD,?_⟩
  intro eta heta heta1 m hm r hr
  obtain ⟨c,hc,hker,hP,hhom,hheight⟩ := hpoly eta heta heta1 m hm r hr
  exact ⟨binaryAuxPolynomial c,hP,hhom,hheight,
    fun tau i => binary_kernel_source_high_index r eta L hrows c hker tau i⟩

end JSP000334
