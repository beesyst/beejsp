import SubspaceBridge.SourceExpansion6
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary6.SourceSupport
open SourceExpansion
variable {K : Type*} [Field K] [CharZero K]
theorem chart_pderiv {m : ℕ} (B : Matrix (Fin 6) (Fin 6) K)
    (h : Fin m) (i : Fin 6) (u : Vars6 m) :
    MvPolynomial.pderiv (h,i) (linearChart B u) =
      if u.1 = h then MvPolynomial.C (B u.2 i) else 0 := by
  classical
  rcases u with ⟨g,j⟩
  by_cases hg : g = h
  · subst g
    simp [linearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · simp [linearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg]

theorem substitution_chain {m : ℕ} (B : Matrix (Fin 6) (Fin 6) K)
    (h : Fin m) (i : Fin 6) (P : MvPolynomial (Vars6 m) K) :
    MvPolynomial.pderiv (h,i) (substitution B P) =
      ∑ j : Fin 6, MvPolynomial.C (B j i) *
        substitution B (MvPolynomial.pderiv (h,j) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add, Finset.sum_add_distrib]
  | mul_X P u hP =>
    have hdelta : (∑ j : Fin 6, (MvPolynomial.C (B j i) * substitution B P) *
        (if (h,j) = u then 1 else 0)) =
        substitution B P * (if u.1 = h then MvPolynomial.C (B u.2 i) else 0) := by
      rcases u with ⟨g,l⟩
      by_cases hg : g = h
      · subst g
        simp [Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]
      · simp [Prod.mk.injEq, hg, Ne.symm hg]
    have hX : substitution B (MvPolynomial.X u) = linearChart B u := by
      simp [substitution]
    have hD (j : Fin 6) :
        substitution B (MvPolynomial.pderiv (h,j) (P * MvPolynomial.X u)) =
          substitution B (MvPolynomial.pderiv (h,j) P) * linearChart B u +
          substitution B P * (if (h,j) = u then 1 else 0) := by
      by_cases he : (h,j) = u <;>
        simp [MvPolynomial.pderiv_mul, hX, MvPolynomial.pderiv_X, Pi.single_apply, he, eq_comm] <;> ring
    rw [map_mul, MvPolynomial.pderiv_mul, hP, hX, chart_pderiv]
    simp_rw [hD, mul_add, ← mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hdelta]

noncomputable def zeroCoordinate {m : ℕ} (i : Fin 6) :
    MvPolynomial (Vars6 m) K →+* MvPolynomial (Vars6 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = i then 0 else MvPolynomial.X u)

noncomputable def kernelImage {m : ℕ} (L : Matrix (Fin 6) (Fin 6) K)
    (i : Fin 6) (u : Vars6 m) : MvPolynomial (Vars6 m) K :=
  zeroCoordinate i (linearChart (L)⁻¹ u)

theorem kernel_image_form {m : ℕ} (L : Matrix (Fin 6) (Fin 6) K)
    (hL : (L).det ≠ 0) (i : Fin 6) (h : Fin m) :
    (∑ j : Fin 6, MvPolynomial.C (L i j : K) * kernelImage L i (h,j)) = 0 := by
  have he := chart_comp (L)⁻¹ (L) (h,i)
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL), chart_one] at he
  change substitution (L)⁻¹
    (∑ j : Fin 6, MvPolynomial.C (L i j) * MvPolynomial.X (h,j)) =
      MvPolynomial.X (h,i) at he
  simp only [map_sum, map_mul, substitution,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at he
  have hz := congrArg (zeroCoordinate i) he
  have hC (q : K) : zeroCoordinate (m := m) i (MvPolynomial.C q) = MvPolynomial.C q := by
    simp [zeroCoordinate]
  simp only [map_sum, map_mul, hC] at hz
  rw [show zeroCoordinate i (MvPolynomial.X (h,i)) = 0 by
    simp [zeroCoordinate]] at hz
  exact hz

theorem kernel_factor_variable {m : ℕ} (L : Matrix (Fin 6) (Fin 6) K)
    (hL : (L).det ≠ 0) (i p : Fin 6) (hp : L i p ≠ 0)
    (u : Vars6 m) :
    MvPolynomial.eval₂Hom MvPolynomial.C (kernelImage L i)
      (kernelChart6 (L i) (fun _ => p) u) =
      kernelImage L i u := by
  classical
  have ha : (L i p : K) ≠ 0 := by exact_mod_cast hp
  have hcancel : (MvPolynomial.C ((L i p : K)⁻¹) : MvPolynomial (Vars6 m) K) *
      MvPolynomial.C (L i p : K) = 1 := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, map_one]
  by_cases hu : u.2 = p
  · have hs := kernel_image_form L hL i u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hs
    have hr : -(∑ j ∈ Finset.univ.erase p,
        MvPolynomial.C (L i j : K) * kernelImage L i (u.1,j)) =
        MvPolynomial.C (L i p : K) * kernelImage L i (u.1,p) := by
      linear_combination -hs
    simp only [kernelChart6, hu, if_pos rfl, ite_true, map_neg, map_sum, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((L i p : K)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p,
            MvPolynomial.C (L i j : K) * kernelImage L i (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv, MvPolynomial.C_mul]
        ring
      _ = _ := by rw [hr, ← mul_assoc, hcancel, one_mul]; simp [← hu]
  · simp [kernelChart6, hu]

theorem zero_monomial {m : ℕ} (i : Fin 6)
    (b : Vars6 m →₀ ℕ) (c : K) :
    zeroCoordinate i (MvPolynomial.monomial b c) =
      if (∀ h, b (h,i) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [zeroCoordinate, MvPolynomial.eval₂Hom_monomial]
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
    have hz : (∏ u : Vars6 m, (if u.2 = i then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (Vars6 m) K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,i))
      simp [hh]
    rw [hz, mul_zero]

theorem zero_coeff {m : ℕ} (i : Fin 6)
    (Q : MvPolynomial (Vars6 m) K) (b : Vars6 m →₀ ℕ) :
    (zeroCoordinate i Q).coeff b = if (∀ h, b (h,i) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [zero_monomial]
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

theorem pderiv_coeff {m : ℕ} (u : Vars6 m)
    (Q : MvPolynomial (Vars6 m) K) (b : Vars6 m →₀ ℕ) :
    (MvPolynomial.pderiv u Q).coeff b =
      (b u + 1 : ℕ) * Q.coeff (b + Finsupp.single u 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]; ring
  | monomial a c =>
    by_cases ha : a u = 0
    · have hab : a ≠ b + Finsupp.single u 1 := by
        intro he
        have h := congrArg (fun d : Vars6 m →₀ ℕ => d u) he
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

theorem kernel_factor {m : ℕ} (L : Matrix (Fin 6) (Fin 6) K)
    (hL : L.det ≠ 0) (i p : Fin 6) (hp : L i p ≠ 0)
    (Q : MvPolynomial (Vars6 m) K) :
    MvPolynomial.eval₂Hom MvPolynomial.C (kernelImage L i)
      (kernelRestriction6 (L i) (fun _ => p) Q) =
      zeroCoordinate i (substitution L⁻¹ Q) := by
  have he : (MvPolynomial.eval₂Hom MvPolynomial.C (kernelImage (m := m) L i)).comp
      (kernelRestriction6 (L i) (fun _ => p)) =
      (zeroCoordinate i).comp (substitution L⁻¹) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [kernelRestriction6, substitution, zeroCoordinate]
    · intro u
      simp only [RingHom.comp_apply, kernelRestriction6, substitution, MvPolynomial.eval₂Hom_X']
      exact kernel_factor_variable L hL i p hp u
  exact congrArg (fun f => f Q) he

theorem index_zero_slice {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 6) (Fin 6) K) (hL : L.det ≠ 0)
    (i p : Fin 6) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars6 m) ℤ)
    (hindex : ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < T →
      kernelRestriction6 (L i) (fun _ => p) (derivative6 J (P.map (Int.castRingHom K))) = 0)
    (J : Vars6 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J < T) :
    zeroCoordinate i (expansion L J P) = 0 := by
  rw [expansion, ← kernel_factor L hL i p hp, hindex J hJ, map_zero]

theorem expansion_chain {m : ℕ} (L : Matrix (Fin 6) (Fin 6) K)
    (h : Fin m) (i : Fin 6) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) :
    MvPolynomial.pderiv (h,i) (expansion L J P) =
      ∑ j : Fin 6, MvPolynomial.C (L⁻¹ j i) *
        (J (h,j) + 1) • expansion L (J + Finsupp.single (h,j) 1) P := by
  rw [expansion, substitution_chain]
  simp only [rothSource_pderiv_hasse, map_nsmul, expansion]

noncomputable def coordinateWeight {m : ℕ} (r : Fin m → ℕ) (i : Fin 6)
    (b : Vars6 m →₀ ℕ) : ℝ := ∑ h, (b (h,i) : ℝ) / r h

theorem coordinate_weight_add {m : ℕ} (r : Fin m → ℕ) (i : Fin 6)
    (b c : Vars6 m →₀ ℕ) :
    coordinateWeight r i (b + c) =
      coordinateWeight r i b + coordinateWeight r i c := by
  simp [coordinateWeight, Finsupp.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]

theorem coordinate_weight_single {m : ℕ} (r : Fin m → ℕ)
    (i : Fin 6) (h : Fin m) :
    coordinateWeight r i (Finsupp.single (h,i) 1) = 1 / (r h : ℝ) := by
  simp [coordinateWeight, Finsupp.single_apply, Prod.mk.injEq,
    ite_div, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem coeff_zero_below_index {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 6) (Fin 6) K) (hL : (L).det ≠ 0)
    (i p : Fin 6) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars6 m) ℤ)
    (hindex : ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < T →
      kernelRestriction6 (L i) (fun _ => p) (derivative6 J (P.map (Int.castRingHom K))) = 0)
    (J b : Vars6 m →₀ ℕ)
    (hbad : rothSourceDerivativeWeight r J + coordinateWeight r i b < T) :
    (expansion L J P).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : Vars6 m →₀ ℕ,
      (∑ h : Fin m, b (h,i)) = n →
      rothSourceDerivativeWeight r J + coordinateWeight r i b < T →
      (expansion L J P).coeff b = 0 := by
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
        have hnonneg : 0 ≤ coordinateWeight r i b := by
          unfold coordinateWeight
          positivity
        have hJ : rothSourceDerivativeWeight r J < T := by linarith
        have hz := index_zero_slice r L hL i p hp T P hindex J hJ
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [zero_coeff, if_pos hbzero, MvPolynomial.coeff_zero] at he
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
          have hs := congrArg (fun d : Vars6 m →₀ ℕ => ∑ g : Fin m, d (g,i)) hceq
          simpa [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
            Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', hn] using hs
        have hcoord : coordinateWeight r i c + 1 / (r h : ℝ) =
            coordinateWeight r i b := by
          rw [← coordinate_weight_single r i h, ← coordinate_weight_add, hceq]
        have hz (j : Fin 6) : (expansion L (J + Finsupp.single (h,j) 1) P).coeff c = 0 := by
          apply ih (∑ g : Fin m, c (g,i)) (by omega) _ c rfl
          rw [rothSource_weight_add, rothSource_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,i) (expansion L J P)).coeff c = 0 := by
          rw [expansion_chain, MvPolynomial.coeff_sum]
          apply Finset.sum_eq_zero
          intro j hj
          rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_smul, hz j, smul_zero, mul_zero]
        rw [pderiv_coeff, hceq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad




theorem polynomial_map_int {F E : Type*} [CommRing F] [CommRing E]
    (f : F →+* E) {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) :
    (P.map (Int.castRingHom F)).map f = P.map (Int.castRingHom E) := by
  have hc : f.comp (Int.castRingHom F) = Int.castRingHom E := by
    ext z
    simp
  rw [MvPolynomial.map_map, hc]

theorem restriction_map {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E]
    (f : F →+* E) {m : ℕ} (a : Fin 6 → F) (k : Fin m → Fin 6)
    (J : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) ℤ) :
    (kernelRestriction6 a k (derivative6 J (P.map (Int.castRingHom F)))).map f =
      kernelRestriction6 (fun j => f (a j)) k (derivative6 J (P.map (Int.castRingHom E))) := by
  rw [kernelRestriction6_map, derivative6_map, polynomial_map_int]

theorem map_injective {F E : Type*} [Field F] [Field E] (f : F →+* E)
    {m : ℕ} : Function.Injective (MvPolynomial.map (σ := Vars6 m) f) := by
  intro P Q he
  apply MvPolynomial.ext
  intro b
  apply f.injective
  have hh := congrArg (MvPolynomial.coeff b) he
  simpa only [MvPolynomial.coeff_map] using hh

theorem rational_restriction_zero {m : ℕ} (a : Fin 6 → ℚ) (k : Fin m → Fin 6)
    (J : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) ℤ)
    (hz : kernelRestriction6 (fun j => (a j : ℝ)) k
      (derivative6 J (P.map (Int.castRingHom ℝ))) = 0) :
    kernelRestriction6 a k (derivative6 J (P.map (Int.castRingHom ℚ))) = 0 := by
  apply map_injective (algebraMap ℚ ℝ)
  rw [map_zero, restriction_map]
  exact hz

theorem padic_restriction_zero (p : ℕ) [Fact p.Prime] {m : ℕ}
    (a : Fin 6 → ℚ) (k : Fin m → Fin 6) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ)
    (hz : kernelRestriction6 (fun j => (a j : ℝ)) k
      (derivative6 J (P.map (Int.castRingHom ℝ))) = 0) :
    kernelRestriction6 (fun j => (algebraMap ℚ ℚ_[p]) (a j)) k
      (derivative6 J (P.map (Int.castRingHom ℚ_[p]))) = 0 := by
  have hq := rational_restriction_zero a k J P hz
  have hh := congrArg (MvPolynomial.map (algebraMap ℚ ℚ_[p])) hq
  rw [restriction_map, map_zero] at hh
  exact hh

end CompoundFeasibility.Auxiliary6.SourceSupport
