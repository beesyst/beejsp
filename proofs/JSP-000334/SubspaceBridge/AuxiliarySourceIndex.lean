import SubspaceBridge.AuxiliaryPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators Classical
namespace JSP000334

noncomputable def rothSourceDerivativeWeight {m : ℕ} (r : Fin m → ℕ)
    (J : RothBlockVars m →₀ ℕ) : ℝ :=
  ∑ h, (∑ i : Fin 3, (J (h,i) : ℝ)) / (r h : ℝ)

def rothSourceHighIndex {m : ℕ} (r : Fin m → ℕ)
    (V : Fin m → Fin 3 → ℤ) (T : ℝ) (P : MvPolynomial (RothBlockVars m) ℤ) : Prop :=
  ∀ J, rothSourceDerivativeWeight r J < T →
    ∀ k, (∀ h, V h (k h) ≠ 0) →
      rothKernelRestriction V k (rothBlockIntegerDividedDerivative J P) = 0

theorem rothSource_pderiv_eq_single {m : ℕ} (u : RothBlockVars m)
    (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.pderiv u P = rothBlockIntegerDividedDerivative (Finsupp.single u 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, rothBlockIntegerDividedDerivative_add, hP, hQ]
  | monomial b c =>
    rw [MvPolynomial.pderiv_monomial, rothAux_derivative_monomial]
    congr 1
    congr 1
    rw [Finset.prod_eq_single u]
    · simp [Finsupp.single_apply, add_comm]
    · intro x hx hxu
      simp [Finsupp.single_apply, Ne.symm hxu]
    · simp

theorem rothSource_derivative_comp {m : ℕ} (a b : RothBlockVars m →₀ ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) :
    rothBlockIntegerDividedDerivative a (rothBlockIntegerDividedDerivative b P) =
      (∏ k : RothBlockVars m, (Nat.choose ((a + b) k) (a k) : ℤ)) •
        rothBlockIntegerDividedDerivative (a + b) P := by
  classical
  apply MvPolynomial.ext
  intro c
  simp only [rothBlockIntegerDividedDerivative_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  have hch (k : RothBlockVars m) :
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
        ∏ k : RothBlockVars m, ((Nat.choose ((c + a + b) k) (b k) : ℤ) *
          (Nat.choose ((c + a) k) (a k) : ℤ)) := by
      rw [Finset.prod_mul_distrib]
      simp only [add_assoc]
      ring
    _ = P.coeff (c + (a + b)) *
        ∏ k : RothBlockVars m, ((Nat.choose ((a + b) k) (a k) : ℤ) *
          (Nat.choose ((c + a + b) k) ((a + b) k) : ℤ)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      exact_mod_cast hch k
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [add_assoc]; ring

theorem rothSource_pderiv_hasse {m : ℕ} (u : RothBlockVars m)
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.pderiv u (rothBlockIntegerDividedDerivative J P) =
      (J u + 1) • rothBlockIntegerDividedDerivative (J + Finsupp.single u 1) P := by
  rw [rothSource_pderiv_eq_single, rothSource_derivative_comp, add_comm J]
  congr 1
  rw [Finset.prod_eq_single u]
  · simp [Finsupp.single_apply, add_comm]
  · intro x hx hxu
    simp [Finsupp.single_apply, Ne.symm hxu]
  · simp

theorem rothSource_scaled_chart_pderiv {m : ℕ} (a : Fin 3 → ℤ) (k j : Fin 3)
    (h : Fin m) (hj : j ≠ k) (v : RothBlockVars m) :
    MvPolynomial.pderiv (h,j) (rothAuxScaledChart a k v) =
      MvPolynomial.C (a k) * (if v = (h,j) then 1 else 0) -
        MvPolynomial.C (a j) * (if v = (h,k) then 1 else 0) := by
  classical
  rcases v with ⟨g,l⟩
  by_cases hg : g = h
  · subst g
    by_cases hl : l = k
    · subst l
      simp [rothAuxScaledChart, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hj, Ne.symm hj, map_sum, mul_ite,
        Finset.sum_ite_eq', Finset.sum_ite_eq, eq_comm]
    · simp [rothAuxScaledChart, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hl, Ne.symm hl, eq_comm]
  · by_cases hl : l = k <;>
      simp [rothAuxScaledChart, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg, map_sum]

theorem rothSource_scaled_chain {m : ℕ} (a : Fin 3 → ℤ) (k j : Fin 3)
    (h : Fin m) (hj : j ≠ k) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.pderiv (h,j) (rothAuxScaledSubstitution a k P) =
      MvPolynomial.C (a k) * rothAuxScaledSubstitution a k (MvPolynomial.pderiv (h,j) P) -
        MvPolynomial.C (a j) * rothAuxScaledSubstitution a k (MvPolynomial.pderiv (h,k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [rothAuxScaledSubstitution]
  | add P Q hP hQ => simp only [map_add, hP, hQ]; ring
  | mul_X P v hP =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    rw [show rothAuxScaledSubstitution a k (MvPolynomial.X v) = rothAuxScaledChart a k v by simp [rothAuxScaledSubstitution],
      rothSource_scaled_chart_pderiv a k j h hj v]
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero]
    split_ifs <;> simp_all <;> ring

theorem rothSource_weight_add {m : ℕ} (r : Fin m → ℕ) (J K : RothBlockVars m →₀ ℕ) :
    rothSourceDerivativeWeight r (J + K) =
      rothSourceDerivativeWeight r J + rothSourceDerivativeWeight r K := by
  simp [rothSourceDerivativeWeight, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, add_div]

theorem rothSource_weight_mono {m : ℕ} (r : Fin m → ℕ)
    (J K : RothBlockVars m →₀ ℕ) (hJK : J ≤ K) :
    rothSourceDerivativeWeight r J ≤ rothSourceDerivativeWeight r K := by
  apply Finset.sum_le_sum
  intro h _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact_mod_cast hJK (h,i)

theorem rothSource_weight_single {m : ℕ} (r : Fin m → ℕ) (u : RothBlockVars m) :
    rothSourceDerivativeWeight r (Finsupp.single u 1) = 1 / (r u.1 : ℝ) := by
  classical
  rcases u with ⟨h,j⟩
  simp [rothSourceDerivativeWeight, Finsupp.single_apply, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [ite_div, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_weight_pivot {m : ℕ} (r : Fin m → ℕ) (k : Fin 3) (i : Fin m → ℕ) :
    rothSourceDerivativeWeight r (rothAuxPivotDerivative k i) = ∑ h, (i h : ℝ) / r h := by
  simp [rothSourceDerivativeWeight, rothAuxPivotDerivative, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

noncomputable def rothSourceFreeOrder {m : ℕ} (k : Fin 3) (J : RothBlockVars m →₀ ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : RothBlockVars m => u.2 ≠ k), J u

theorem rothSource_free_add {m : ℕ} (k : Fin 3) (J K : RothBlockVars m →₀ ℕ) :
    rothSourceFreeOrder k (J + K) = rothSourceFreeOrder k J + rothSourceFreeOrder k K := by
  simp [rothSourceFreeOrder, Finsupp.add_apply, Finset.sum_add_distrib]

theorem rothSource_free_single {m : ℕ} (k : Fin 3) (u : RothBlockVars m) :
    rothSourceFreeOrder k (Finsupp.single u 1) = if u.2 = k then 0 else 1 := by
  classical
  simp [rothSourceFreeOrder, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_free_zero_pivot {m : ℕ} (k : Fin 3) (J : RothBlockVars m →₀ ℕ)
    (hJ : rothSourceFreeOrder k J = 0) :
    J = rothAuxPivotDerivative k (fun h => J (h,k)) := by
  classical
  ext u
  by_cases hu : u.2 = k
  · have he : u = (u.1,k) := Prod.ext rfl hu
    simpa [rothAuxPivotDerivative, hu] using congrArg J he
  · have hle : J u ≤ rothSourceFreeOrder k J :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ u,hu⟩)
    have hz : J u = 0 := by omega
    simp [rothAuxPivotDerivative, hu, hz]

theorem rothSource_scaled_mixed_vanishing {m : ℕ} (r : Fin m → ℕ)
    (a : Fin 3 → ℤ) (k : Fin 3) (ha : a k ≠ 0) (T : ℝ)
    (P : MvPolynomial (RothBlockVars m) ℤ)
    (hpivot : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      rothAuxScaledSubstitution a k
        (rothBlockIntegerDividedDerivative (rothAuxPivotDerivative k i) P) = 0)
    (J : RothBlockVars m →₀ ℕ) (hw : rothSourceDerivativeWeight r J < T) :
    rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative J P) = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J : RothBlockVars m →₀ ℕ,
      rothSourceFreeOrder k J = n → rothSourceDerivativeWeight r J < T →
      rothAuxScaledSubstitution a k (rothBlockIntegerDividedDerivative J P) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hn hw
      by_cases hz : n = 0
      · have he := rothSource_free_zero_pivot k J (hn.trans hz)
        have hweight : (∑ h, (J (h,k) : ℝ) / r h) < T := by
          rw [← rothSource_weight_pivot r k, ← he]
          exact hw
        rw [he]
        exact hpivot _ hweight
      · have hex : ∃ u : RothBlockVars m, u.2 ≠ k ∧ J u ≠ 0 := by
          by_contra! hno
          have hzero : rothSourceFreeOrder k J = 0 := by
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
        have hKcount : rothSourceFreeOrder k K + 1 = n := by
          have hc := congrArg (rothSourceFreeOrder k) hKeq
          simpa [rothSource_free_add, rothSource_free_single, hu, hn] using hc
        have hKpcount : rothSourceFreeOrder k Kp = rothSourceFreeOrder k K := by
          simp [Kp, rothSource_free_add, rothSource_free_single]
        have hKweight : rothSourceDerivativeWeight r K ≤ rothSourceDerivativeWeight r J :=
          rothSource_weight_mono r K J tsub_le_self
        have hKpweight : rothSourceDerivativeWeight r Kp = rothSourceDerivativeWeight r J := by
          calc
            _ = rothSourceDerivativeWeight r K + 1 / (r u.1 : ℝ) := by
              rw [rothSource_weight_add, rothSource_weight_single]
            _ = _ := by rw [← hKeq, rothSource_weight_add, rothSource_weight_single]
        have hK := ih (rothSourceFreeOrder k K) (by omega) K rfl (lt_of_le_of_lt hKweight hw)
        have hKp := ih (rothSourceFreeOrder k Kp) (by omega) Kp rfl (hKpweight ▸ hw)
        change rothAuxScaledSubstitution a k
          (rothBlockIntegerDividedDerivative (K + Finsupp.single (u.1,k) 1) P) = 0 at hKp
        have hc := rothSource_scaled_chain a k u.2 u.1 hu
          (rothBlockIntegerDividedDerivative K P)
        rw [rothSource_pderiv_hasse, rothSource_pderiv_hasse] at hc
        simp only [hK, map_zero, map_nsmul, hKp, nsmul_zero, mul_zero, sub_zero] at hc
        rw [hKeq] at hc
        have hcoeff : (MvPolynomial.C (a k) : MvPolynomial (RothBlockVars m) ℤ) ≠ 0 := by
          intro hz
          apply ha
          apply MvPolynomial.C_injective (σ := RothBlockVars m)
          simpa only [map_zero] using hz
        have hsm := (mul_eq_zero.mp hc.symm).resolve_left hcoeff
        rw [nsmul_eq_mul] at hsm
        exact (mul_eq_zero.mp hsm).resolve_left (by
          intro hh
          have hz : ((K (u.1,u.2) + 1 : ℕ) : ℤ) = 0 := by
            apply MvPolynomial.C_injective (σ := RothBlockVars m)
            simpa only [map_natCast, map_zero] using hh
          omega)
  exact go _ J rfl hw

theorem rothSource_kernel_chart_form {m : ℕ} (a : Fin 3 → ℤ)
    (k : Fin m → Fin 3) (hk : ∀ h, a (k h) ≠ 0) (h : Fin m) :
    (∑ j : Fin 3, MvPolynomial.C (a j : ℚ) *
      rothKernelChart (fun _ : Fin m => a) k (h,j)) = 0 := by
  classical
  have ha : (a (k h) : ℚ) ≠ 0 := by exact_mod_cast hk h
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k h))]
  have hfree : (∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j : ℚ) *
      rothKernelChart (fun _ : Fin m => a) k (h,j)) =
      ∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j : ℚ) * MvPolynomial.X (h,j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [rothKernelChart, (Finset.mem_erase.mp hj).1]
  rw [hfree]
  have hpivot : MvPolynomial.C (a (k h) : ℚ) *
      rothKernelChart (fun _ : Fin m => a) k (h,k h) =
      -(∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j : ℚ) * MvPolynomial.X (h,j)) := by
    simp only [rothKernelChart, Prod.fst, Prod.snd, if_pos rfl, ite_true, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    congr 1
    field_simp [ha]
  rw [hpivot]
  ring

noncomputable def rothSourceChartTransport {m : ℕ} (a : Fin 3 → ℤ) (p : Fin 3)
    (k : Fin m → Fin 3) :
    MvPolynomial (RothBlockVars m) ℤ →+* MvPolynomial (RothBlockVars m) ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun u =>
    MvPolynomial.C ((a p : ℚ)⁻¹) * rothKernelChart (fun _ : Fin m => a) k u)

theorem rothSource_chart_transport_variable {m : ℕ} (a : Fin 3 → ℤ)
    (p : Fin 3) (hp : a p ≠ 0) (k : Fin m → Fin 3)
    (hk : ∀ h, a (k h) ≠ 0) (u : RothBlockVars m) :
    rothSourceChartTransport a p k (rothAuxScaledChart a p u) =
      rothKernelChart (fun _ : Fin m => a) k u := by
  classical
  have ha : (a p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hcancel : (MvPolynomial.C (a p : ℚ) : MvPolynomial (RothBlockVars m) ℚ) *
      MvPolynomial.C ((a p : ℚ)⁻¹) = 1 := by rw [← MvPolynomial.C_mul, mul_inv_cancel₀ ha, map_one]
  have hcast (z : ℤ) :
      (Int.castRingHom (MvPolynomial (RothBlockVars m) ℚ)) z = MvPolynomial.C (z : ℚ) :=
    (map_intCast (MvPolynomial.C : ℚ →+* MvPolynomial (RothBlockVars m) ℚ) z).symm
  by_cases hu : u.2 = p
  · have hsum := rothSource_kernel_chart_form a k hk u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hsum
    have hrel : -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j : ℚ) *
        rothKernelChart (fun _ : Fin m => a) k (u.1,j)) =
        MvPolynomial.C (a p : ℚ) * rothKernelChart (fun _ : Fin m => a) k (u.1,p) := by
      linear_combination -hsum
    simp only [rothAuxScaledChart, if_pos hu, map_neg, map_sum, map_mul]
    simp only [rothSourceChartTransport, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      hcast]
    calc
      _ = MvPolynomial.C ((a p : ℚ)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j : ℚ) *
            rothKernelChart (fun _ : Fin m => a) k (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hrel]; rw [← mul_assoc, mul_comm _ (MvPolynomial.C (a p : ℚ)), hcancel]; simp [← hu]
  · simp only [rothAuxScaledChart, if_neg hu, map_mul]
    simp only [rothSourceChartTransport, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      hcast]
    rw [← mul_assoc, hcancel, one_mul]

theorem rothSource_chart_transport {m : ℕ} (a : Fin 3 → ℤ)
    (p : Fin 3) (hp : a p ≠ 0) (k : Fin m → Fin 3)
    (hk : ∀ h, a (k h) ≠ 0) (P : MvPolynomial (RothBlockVars m) ℤ) :
    rothSourceChartTransport a p k (rothAuxScaledSubstitution a p P) =
      rothKernelRestriction (fun _ : Fin m => a) k P := by
  have he : (rothSourceChartTransport a p k).comp (rothAuxScaledSubstitution a p) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) (rothKernelChart (fun _ : Fin m => a) k) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [rothAuxScaledSubstitution, rothSourceChartTransport]
    · intro u
      simpa [rothAuxScaledSubstitution] using rothSource_chart_transport_variable a p hp k hk u
  exact congrArg (fun f => f P) he

theorem rothSource_derivative_zero_of_block_excess {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (J : RothBlockVars m →₀ ℕ) (h : Fin m) (hJ : r h < ∑ j : Fin 3, J (h,j)) :
    rothBlockIntegerDividedDerivative J P = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [rothBlockIntegerDividedDerivative_coeff, MvPolynomial.coeff_zero]
  have hz : P.coeff (d + J) = 0 := by
    by_contra hn
    have hdegree := hP (d + J) (MvPolynomial.mem_support_iff.mpr hn) h
    have hle : (∑ j : Fin 3, J (h,j)) ≤ ∑ j : Fin 3, (d + J) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finsupp.add_apply]
      omega
    omega
  rw [hz, zero_mul]

theorem rothSource_highIndex_of_scaled {m : ℕ} (r : Fin m → ℕ)
    (a : Fin 3 → ℤ) (p : Fin 3) (hp : a p ≠ 0) (T : ℝ)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : rothBlockHomogeneous r P)
    (hpivot : ∀ i : RothAuxPivots r, (∑ h, ((i h).val : ℝ) / r h) < T →
      rothAuxScaledSubstitution a p (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative p (fun h => (i h).val)) P) = 0) :
    rothSourceHighIndex r (fun _ : Fin m => a) T P := by
  classical
  have hall : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      rothAuxScaledSubstitution a p
        (rothBlockIntegerDividedDerivative (rothAuxPivotDerivative p i) P) = 0 := by
    intro i hi
    by_cases hb : ∀ h, i h ≤ r h
    · let iFin : RothAuxPivots r := fun h => ⟨i h, by have hh := hb h; omega⟩
      exact hpivot iFin hi
    · push_neg at hb
      obtain ⟨h, hh⟩ := hb
      have hsum : (∑ j : Fin 3, rothAuxPivotDerivative p i (h,j)) = i h := by
        simp [rothAuxPivotDerivative, Finset.sum_ite_eq, Finset.sum_ite_eq']
      have hz := rothSource_derivative_zero_of_block_excess r P hP
        (rothAuxPivotDerivative p i) h (by rw [hsum]; exact hh)
      simp [hz]
  intro J hw k hk
  rw [← rothSource_chart_transport a p hp k hk]
  rw [rothSource_scaled_mixed_vanishing r a p hp T P hall J hw, map_zero]

theorem roth_auxiliary_integer_three_place
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (eta : ℝ), 0 < eta →
      ∀ (m : ℕ), 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ) →
      ∀ (r : Fin m → ℕ), (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (RothBlockVars m) ℤ,
        P ≠ 0 ∧ rothBlockHomogeneous r P ∧
        (rothKernelBlockHeight P : ℝ) ≤ D ^ (∑ h, r h) ∧
        ∀ tau i, rothSourceHighIndex r (fun _ => L tau i) ((1 / 3 - eta) * m) P := by
  obtain ⟨D, hD, hconstruction⟩ := roth_auxiliary_integer_polynomial L hL
  refine ⟨D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hnonzero, hhom, hheight, hequations⟩ := hconstruction eta heta m hm r hr
  refine ⟨P, hnonzero, hhom, hheight, ?_⟩
  intro tau i
  let f := rothAuxFormEquiv.symm (tau,i)
  have hf : rothAuxFormEquiv f = (tau,i) := rothAuxFormEquiv.apply_symm_apply _
  have hp : L tau i (rothAuxPivot L hL f) ≠ 0 := by
    simpa only [hf] using rothAuxPivot_ne_zero L hL f
  apply rothSource_highIndex_of_scaled r (L tau i) (rothAuxPivot L hL f) hp _ P hhom
  intro j hj
  have he := hequations f ⟨j,hj⟩
  simpa only [hf] using he

end JSP000334
