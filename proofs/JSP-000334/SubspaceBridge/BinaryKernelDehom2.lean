import SubspaceBridge.BinaryAuxSourceIndex2
open scoped BigOperators Classical
namespace JSP000334

noncomputable def binaryKernelPivotExponent {m : ℕ} (k : Fin m → Fin 2)
    (b : RothBlockVars2 m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun h => b (h, k h))

noncomputable def binaryKernelDehom {m : ℕ} (k : Fin m → Fin 2)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) : MvPolynomial (Fin m) ℤ :=
  P.sum fun b c => MvPolynomial.monomial (binaryKernelPivotExponent k b) c

theorem binaryKernelPivotExponent_injective {m : ℕ}
    (k : Fin m → Fin 2) (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (r : Fin m → ℕ) (hhom : binaryBlockHomogeneous r P) :
    Set.InjOn (binaryKernelPivotExponent k) (P.support : Set (RothBlockVars2 m →₀ ℕ)) := by
  intro b hb c hc he
  have hp (h) : b (h, k h) = c (h, k h) := congrArg (fun a : Fin m →₀ ℕ => a h) he
  ext ⟨h,i⟩
  have hbh := hhom b hb h
  have hch := hhom c hc h
  rw [Fin.sum_univ_two] at hbh hch
  have hh := hp h
  generalize hk : k h = l at hh
  fin_cases l <;> dsimp at hh
  all_goals fin_cases i <;> dsimp <;> omega

theorem binaryKernelDehom_coeff_at {m : ℕ} (k : Fin m → Fin 2)
    (P : MvPolynomial (RothBlockVars2 m) ℤ)
    (hinj : Set.InjOn (binaryKernelPivotExponent k) (P.support : Set (RothBlockVars2 m →₀ ℕ)))
    (b : RothBlockVars2 m →₀ ℕ) (hb : b ∈ P.support) :
    (binaryKernelDehom k P).coeff (binaryKernelPivotExponent k b) = P.coeff b := by
  classical
  rw [binaryKernelDehom, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c hc hcb
    have hne : binaryKernelPivotExponent k c ≠ binaryKernelPivotExponent k b :=
      fun he => hcb (hinj hc hb he)
    simp [MvPolynomial.coeff_monomial, hne]
  · exact fun h => (h hb).elim

theorem binaryKernelDehom_nonzero_height_degree {m : ℕ}
    (k : Fin m → Fin 2)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : P ≠ 0) (r : Fin m → ℕ)
    (hhom : binaryBlockHomogeneous r P) :
    binaryKernelDehom k P ≠ 0 ∧
    rothIntegerHeight (binaryKernelDehom k P) ≤ P.support.sup (fun b => (P.coeff b).natAbs) ∧
    (∀ a ∈ (binaryKernelDehom k P).support, ∀ h, a h ≤ r h) := by
  classical
  have hinj := binaryKernelPivotExponent_injective k P r hhom
  have hcoeff (a : Fin m →₀ ℕ) (ha : a ∈ (binaryKernelDehom k P).support) :
      ∃ b ∈ P.support, binaryKernelPivotExponent k b = a := by
    have hne := MvPolynomial.mem_support_iff.mp ha
    rw [binaryKernelDehom, MvPolynomial.sum_def, MvPolynomial.coeff_sum] at hne
    obtain ⟨b, hb, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨b, hb, ?_⟩
    by_contra h
    exact hnonzero (by simp [MvPolynomial.coeff_monomial, h])
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr hP
    intro he
    have hh := binaryKernelDehom_coeff_at k P hinj b hb
    rw [he, MvPolynomial.coeff_zero] at hh
    exact (MvPolynomial.mem_support_iff.mp hb) hh.symm
  · apply Finset.sup_le
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hcoeff a ha
    rw [binaryKernelDehom_coeff_at k P hinj b hb]
    exact Finset.le_sup (f := fun b => (P.coeff b).natAbs) hb
  · intro a ha h
    obtain ⟨b, hb, rfl⟩ := hcoeff a ha
    have hle : b (h, k h) ≤ ∑ i : Fin 2, b (h, i) :=
      Finset.single_le_sum (f := fun i : Fin 2 => b (h, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (k h))
    simpa [binaryKernelPivotExponent, hhom b hb h] using hle

noncomputable def binaryKernelPivotOrder {m : ℕ} (k : Fin m → Fin 2)
    (a : Fin m →₀ ℕ) : RothBlockVars2 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k u.1 then a u.1 else 0)

theorem binaryKernelDehom_monomial {m : ℕ} (k : Fin m → Fin 2)
    (b : RothBlockVars2 m →₀ ℕ) (c : ℤ) :
    binaryKernelDehom k (MvPolynomial.monomial b c) =
      MvPolynomial.monomial (binaryKernelPivotExponent k b) c := by
  simp [binaryKernelDehom]

theorem binaryKernelDehom_add {m : ℕ} (k : Fin m → Fin 2)
    (P Q : MvPolynomial (RothBlockVars2 m) ℤ) :
    binaryKernelDehom k (P + Q) = binaryKernelDehom k P + binaryKernelDehom k Q := by
  apply Finsupp.sum_add_index'
  · intro b
    simp
  · intro b c d
    simp [map_add]

theorem binaryKernelDehom_derivative {m : ℕ} (k : Fin m → Fin 2)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (a : Fin m →₀ ℕ) :
    rothIntegerDividedDerivative a (binaryKernelDehom k P) =
      binaryKernelDehom k (binaryDividedDerivative (binaryKernelPivotOrder k a) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [binaryKernelDehom_monomial]
    simp only [rothIntegerDividedDerivative, binaryDividedDerivative,
      MvPolynomial.sum_monomial_eq, zero_mul, MvPolynomial.monomial_zero]
    rw [binaryKernelDehom_monomial]
    have he : binaryKernelPivotExponent k (b - binaryKernelPivotOrder k a) =
        binaryKernelPivotExponent k b - a := by
      ext h
      simp [binaryKernelPivotExponent, binaryKernelPivotOrder, Finsupp.sub_apply]
    rw [he]
    congr 2
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro h _
    symm
    calc
      ∏ i : Fin 2, (Nat.choose (b (h, i)) (binaryKernelPivotOrder k a (h, i)) : ℤ) =
          (Nat.choose (b (h, k h)) (binaryKernelPivotOrder k a (h, k h)) : ℤ) := by
        apply Finset.prod_eq_single (k h)
        · intro i hi hine
          simp [binaryKernelPivotOrder, hine]
        · simp
      _ = _ := by simp [binaryKernelPivotExponent, binaryKernelPivotOrder]
  | add P Q hP hQ =>
    rw [binaryKernelDehom_add, rothKernel_scalarDerivative_add,
      binary_derivative_add, binaryKernelDehom_add, hP, hQ]

theorem binaryKernelPivotOrder_budget {m : ℕ} (k : Fin m → Fin 2)
    (a : Fin m →₀ ℕ) (r : Fin m → ℕ) :
    (∑ h : Fin m, (∑ i : Fin 2, (binaryKernelPivotOrder k a (h, i) : ℝ)) / (r h : ℝ)) =
      ∑ h : Fin m, (a h : ℝ) / (r h : ℝ) := by
  apply Finset.sum_congr rfl
  intro h _
  simp [binaryKernelPivotOrder]

theorem binaryKernelDehom_eval {m : ℕ} (k : Fin m → Fin 2)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (x : Fin m → ℚ) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) x (binaryKernelDehom k P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun u => if u.2 = k u.1 then x u.1 else 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [binaryKernelDehom_monomial, MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial]
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp),
      Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
    congr 1
    apply Finset.prod_congr rfl
    intro h _
    symm
    calc
      ∏ i : Fin 2, (if i = k h then x h else 1) ^ b (h, i) =
          (if k h = k h then x h else 1) ^ b (h, k h) := by
        apply Finset.prod_eq_single (k h)
        · intro i hi hine
          simp [hine]
        · simp
      _ = _ := by simp [binaryKernelPivotExponent]
  | add P Q hP hQ =>
    rw [binaryKernelDehom_add, MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, hP, hQ]

end JSP000334
