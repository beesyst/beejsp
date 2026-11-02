import SubspaceBridge.AuxiliaryCount

open scoped BigOperators Classical
namespace JSP000334

theorem rothAux_derivative_monomial {m : ℕ} (J b : RothBlockVars m →₀ ℕ) (c : ℤ) :
    rothBlockIntegerDividedDerivative J (MvPolynomial.monomial b c) =
      MvPolynomial.monomial (b - J)
        (c * ∏ u : RothBlockVars m, (Nat.choose (b u) (J u) : ℤ)) := by
  unfold rothBlockIntegerDividedDerivative
  exact MvPolynomial.sum_monomial_eq (by simp)

theorem rothAux_transformed_coeff_sum {m : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → RothBlockVars m →₀ ℕ) (c : ι → ℤ)
    (J d : RothBlockVars m →₀ ℕ)
    (S : MvPolynomial (RothBlockVars m) ℤ →+* MvPolynomial (RothBlockVars m) ℤ) :
    (S (rothBlockIntegerDividedDerivative J (∑ b, MvPolynomial.monomial (e b) (c b)))).coeff d =
      ∑ b, c b * (S (rothBlockIntegerDividedDerivative J
        (MvPolynomial.monomial (e b) 1))).coeff d := by
  have hadd : rothBlockIntegerDividedDerivative J
      (∑ b, MvPolynomial.monomial (e b) (c b)) =
      ∑ b, rothBlockIntegerDividedDerivative J (MvPolynomial.monomial (e b) (c b)) := by
    apply MvPolynomial.ext
    intro a
    simp only [rothBlockIntegerDividedDerivative_coeff, MvPolynomial.coeff_sum,
      Finset.sum_mul]
  rw [hadd, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [rothAux_derivative_monomial, rothAux_derivative_monomial]
  simp only [one_mul]
  have hc : MvPolynomial.monomial (e b - J)
      (c b * ∏ u : RothBlockVars m, (Nat.choose (e b u) (J u) : ℤ)) =
      MvPolynomial.C (c b) * MvPolynomial.monomial (e b - J)
        (∏ u : RothBlockVars m, (Nat.choose (e b u) (J u) : ℤ)) := by
    rw [MvPolynomial.C_mul_monomial]
  rw [hc, map_mul]
  have hC : S (MvPolynomial.C (c b)) = MvPolynomial.C (c b) := by
    exact map_intCast S (c b)
  rw [hC, MvPolynomial.coeff_C_mul]


noncomputable def rothAuxExponent {m : ℕ} {r : Fin m → ℕ}
    (b : RothAuxCoefficients r) : RothBlockVars m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => ((b u.1).val u.2).val)

theorem rothAuxExponent_injective {m : ℕ} (r : Fin m → ℕ) :
    Function.Injective (@rothAuxExponent m r) := by
  intro b c h
  funext g
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrArg (fun e : RothBlockVars m →₀ ℕ => e (g,j)) h

noncomputable def rothAuxPolynomial {m : ℕ} {r : Fin m → ℕ}
    (c : RothAuxCoefficients r → ℤ) : MvPolynomial (RothBlockVars m) ℤ :=
  ∑ b, MvPolynomial.monomial (rothAuxExponent b) (c b)

theorem rothAuxPolynomial_coeff {m : ℕ} {r : Fin m → ℕ}
    (c : RothAuxCoefficients r → ℤ) (b : RothAuxCoefficients r) :
    (rothAuxPolynomial c).coeff (rothAuxExponent b) = c b := by
  simp only [rothAuxPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    (rothAuxExponent_injective r).eq_iff]
  simp

theorem rothAuxPolynomial_eq_zero_iff {m : ℕ} {r : Fin m → ℕ}
    (c : RothAuxCoefficients r → ℤ) : rothAuxPolynomial c = 0 ↔ ∀ b, c b = 0 := by
  constructor
  · intro hz b
    have hc := rothAuxPolynomial_coeff c b
    rw [hz, MvPolynomial.coeff_zero] at hc
    exact hc.symm
  · intro hz
    simp [rothAuxPolynomial, hz]

theorem rothAuxPolynomial_homogeneous {m : ℕ} {r : Fin m → ℕ}
    (c : RothAuxCoefficients r → ℤ) : rothBlockHomogeneous r (rothAuxPolynomial c) := by
  intro a ha h
  obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ha)
  have hab := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
  subst a
  exact (b h).property

noncomputable def rothAuxFormEquiv : Fin 9 ≃ Fin 3 × Fin 3 := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3)).symm

noncomputable def rothAuxPivot (L : Fin 3 → Fin 3 → Fin 3 → ℤ)
    (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) (f : Fin 9) : Fin 3 :=
  Classical.choose (hL (rothAuxFormEquiv f).1 (rothAuxFormEquiv f).2)

theorem rothAuxPivot_ne_zero (L : Fin 3 → Fin 3 → Fin 3 → ℤ)
    (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) (f : Fin 9) :
    L (rothAuxFormEquiv f).1 (rothAuxFormEquiv f).2 (rothAuxPivot L hL f) ≠ 0 :=
  Classical.choose_spec (hL (rothAuxFormEquiv f).1 (rothAuxFormEquiv f).2)

noncomputable def rothAuxScaledChart {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3)
    (u : RothBlockVars m) : MvPolynomial (RothBlockVars m) ℤ :=
  if u.2 = k then
    -(∑ j ∈ Finset.univ.erase k, MvPolynomial.C (a j) * MvPolynomial.X (u.1,j))
  else MvPolynomial.C (a k) * MvPolynomial.X u

noncomputable def rothAuxScaledSubstitution {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3) :
    MvPolynomial (RothBlockVars m) ℤ →+* MvPolynomial (RothBlockVars m) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (rothAuxScaledChart a k)


noncomputable def rothAuxPivotDerivative {m : ℕ} (k : Fin 3) (i : Fin m → ℕ) :
    RothBlockVars m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k then i u.1 else 0)

noncomputable def rothAuxFreeExponent {m : ℕ} (d : Fin m → ℕ)
    (k : Fin 3) (j : (h : Fin m) → Fin (d h + 1)) : RothBlockVars m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u =>
    if u.2 = Equiv.swap (0 : Fin 3) k 1 then (j u.1).val else
      if u.2 = Equiv.swap (0 : Fin 3) k 2 then d u.1 - (j u.1).val else 0)

noncomputable def rothAuxEquation {m : ℕ} {r : Fin m → ℕ} {eta : ℝ}
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (f : Fin 9) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
    (j : (h : Fin m) → Fin (r h - (i.val h).val + 1))
    (P : MvPolynomial (RothBlockVars m) ℤ) : ℤ :=
  ((rothAuxScaledSubstitution (L (rothAuxFormEquiv f).1 (rothAuxFormEquiv f).2)
    (rothAuxPivot L hL f))
      (rothBlockIntegerDividedDerivative
        (rothAuxPivotDerivative (rothAuxPivot L hL f) (fun h => (i.val h).val)) P)).coeff
    (rothAuxFreeExponent (fun h => r h - (i.val h).val) (rothAuxPivot L hL f) j)

noncomputable def rothAuxMatrix {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    Matrix (RothAuxEquations r eta) (RothAuxCoefficients r) ℤ :=
  fun q b => rothAuxEquation L hL q.1 (rothAuxBadPivotEquiv r eta q.2).1
    (rothAuxBadPivotEquiv r eta q.2).2 (MvPolynomial.monomial (rothAuxExponent b) 1)

theorem rothAuxMatrix_mulVec {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (c : RothAuxCoefficients r → ℤ) (q : RothAuxEquations r eta) :
    (rothAuxMatrix r eta L hL).mulVec c q =
      rothAuxEquation L hL q.1 (rothAuxBadPivotEquiv r eta q.2).1
        (rothAuxBadPivotEquiv r eta q.2).2 (rothAuxPolynomial c) := by
  unfold rothAuxEquation rothAuxPolynomial
  rw [rothAux_transformed_coeff_sum]
  simp only [Matrix.mulVec, dotProduct, rothAuxMatrix, rothAuxEquation]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem rothAuxMatrix_mulVec_zero_iff {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (c : RothAuxCoefficients r → ℤ) :
    (rothAuxMatrix r eta L hL).mulVec c = 0 ↔
      ∀ (f : Fin 9) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
        (j : (h : Fin m) → Fin (r h - (i.val h).val + 1)),
        rothAuxEquation L hL f i j (rothAuxPolynomial c) = 0 := by
  constructor
  · intro hz f i j
    have h := congrFun hz (f, (rothAuxBadPivotEquiv r eta).symm ⟨i,j⟩)
    rw [rothAuxMatrix_mulVec] at h
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using h
  · intro hz
    funext q
    rw [rothAuxMatrix_mulVec]
    exact hz q.1 (rothAuxBadPivotEquiv r eta q.2).1 (rothAuxBadPivotEquiv r eta q.2).2

theorem rothAuxMatrix_cardinalities {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ)) :
    Fintype.card (RothAuxCoefficients r) = ∏ h, (r h + 2).choose 2 ∧
      0 < Fintype.card (RothAuxCoefficients r) ∧
      Fintype.card (RothAuxEquations r eta) = rothAuxConstraintCount r eta ∧
      (Fintype.card (RothAuxEquations r eta) : ℝ) ≤
        (Fintype.card (RothAuxCoefficients r) : ℝ) / 2 :=
  ⟨rothAuxDimension_eq r, rothAuxDimension_pos r, rfl,
    rothAuxConstraintCount_le_half r hr eta heta hm⟩

noncomputable def rothAuxMass {σ : Type*} (P : MvPolynomial σ ℤ) : ℤ :=
  ∑ d ∈ P.support, |P.coeff d|

theorem rothAuxMass_nonneg {σ : Type*} (P : MvPolynomial σ ℤ) : 0 ≤ rothAuxMass P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem rothAuxMass_monomial {σ : Type*} (d : σ →₀ ℕ) (c : ℤ) :
    rothAuxMass (MvPolynomial.monomial d c) = |c| := by
  by_cases hc : c = 0
  · simp [hc, rothAuxMass]
  · simp [rothAuxMass, MvPolynomial.support_monomial, hc]

theorem rothAuxMass_support_sum {σ : Type*} (P : MvPolynomial σ ℤ)
    (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) :
    rothAuxMass P = ∑ d ∈ s, |P.coeff d| := by
  apply Finset.sum_subset hs
  intro d _ hd
  rw [MvPolynomial.not_mem_support_iff.mp hd, abs_zero]

theorem rothAuxMass_add {σ : Type*} (P Q : MvPolynomial σ ℤ) :
    rothAuxMass (P + Q) ≤ rothAuxMass P + rothAuxMass Q := by
  let s := P.support ∪ Q.support
  have hP : P.support ⊆ s := Finset.subset_union_left
  have hQ : Q.support ⊆ s := Finset.subset_union_right
  rw [rothAuxMass_support_sum (P + Q) s MvPolynomial.support_add,
    rothAuxMass_support_sum P s hP, rothAuxMass_support_sum Q s hQ, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun d _ => by simpa using abs_add (P.coeff d) (Q.coeff d))

theorem rothAuxMass_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    rothAuxMass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, rothAuxMass (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [rothAuxMass]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rothAuxMass_add _ _).trans (add_le_add_left ih _)

theorem rothAuxMass_mul {σ : Type*} (P Q : MvPolynomial σ ℤ) :
    rothAuxMass (P * Q) ≤ rothAuxMass P * rothAuxMass Q := by
  rw [MvPolynomial.mul_def, MvPolynomial.sum_def]
  calc
    _ ≤ ∑ a ∈ P.support, rothAuxMass (Q.sum fun b c =>
        MvPolynomial.monomial (a + b) (P.coeff a * c)) := rothAuxMass_sum _ _
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support,
        rothAuxMass (MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      apply Finset.sum_le_sum
      intro a _
      exact rothAuxMass_sum _ _
    _ = _ := by
      simp only [rothAuxMass_monomial, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      rfl

theorem rothAuxMass_pow {σ : Type*} (P : MvPolynomial σ ℤ) (n : ℕ) :
    rothAuxMass (P ^ n) ≤ rothAuxMass P ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, MvPolynomial.one_def, rothAuxMass_monomial]
    norm_num
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (rothAuxMass_mul _ _).trans
      (mul_le_mul_of_nonneg_right ih (rothAuxMass_nonneg P))

theorem rothAuxMass_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    rothAuxMass (∏ i ∈ s, f i) ≤ ∏ i ∈ s, rothAuxMass (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [MvPolynomial.one_def, rothAuxMass_monomial]
    norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (rothAuxMass_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (rothAuxMass_nonneg _))

theorem rothAux_coeff_le_mass {σ : Type*} (P : MvPolynomial σ ℤ) (d : σ →₀ ℕ) :
    |P.coeff d| ≤ rothAuxMass P := by
  by_cases hd : d ∈ P.support
  · change |P.coeff d| ≤ ∑ b ∈ P.support, |P.coeff b|
    exact Finset.single_le_sum (fun b _ => abs_nonneg (P.coeff b)) hd
  · rw [MvPolynomial.not_mem_support_iff.mp hd, abs_zero]
    exact rothAuxMass_nonneg _


theorem rothAuxMass_neg {σ : Type*} (P : MvPolynomial σ ℤ) :
    rothAuxMass (-P) = rothAuxMass P := by
  simp [rothAuxMass]

theorem rothAuxMass_C_mul_X {σ : Type*} (c : ℤ) (u : σ) :
    rothAuxMass (MvPolynomial.C c * MvPolynomial.X u) = |c| := by
  rw [MvPolynomial.X, MvPolynomial.C_mul_monomial, mul_one, rothAuxMass_monomial]

noncomputable def rothAuxSourceHeight (L : Fin 3 → Fin 3 → Fin 3 → ℤ) : ℕ :=
  max 1 (Finset.univ.sup fun u : Fin 3 × Fin 3 × Fin 3 => (L u.1 u.2.1 u.2.2).natAbs)

theorem rothAuxSourceHeight_one_le (L : Fin 3 → Fin 3 → Fin 3 → ℤ) :
    1 ≤ rothAuxSourceHeight L := Nat.le_max_left _ _

theorem rothAuxSourceHeight_coeff (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (tau i j : Fin 3) :
    |L tau i j| ≤ (rothAuxSourceHeight L : ℤ) := by
  have hn : (L tau i j).natAbs ≤ rothAuxSourceHeight L :=
    (Finset.le_sup (f := fun u : Fin 3 × Fin 3 × Fin 3 =>
      (L u.1 u.2.1 u.2.2).natAbs) (Finset.mem_univ (tau,i,j))).trans (Nat.le_max_right _ _)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hn

theorem rothAuxScaledChart_mass {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3)
    (A : ℤ) (hA : 1 ≤ A) (ha : ∀ j, |a j| ≤ A) (u : RothBlockVars m) :
    rothAuxMass (rothAuxScaledChart a k u) ≤ 3 * A := by
  unfold rothAuxScaledChart
  split_ifs
  · rw [rothAuxMass_neg]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase k,
          rothAuxMass (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) := rothAuxMass_sum _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase k, A := by
        apply Finset.sum_le_sum
        intro j _
        rw [rothAuxMass_C_mul_X]
        exact ha j
      _ ≤ 3 * A := by simp; omega
  · rw [rothAuxMass_C_mul_X]
    exact (ha k).trans (by omega)

theorem rothAux_scaled_derivative_monomial {m : ℕ} (a : Fin 3 → ℤ) (k : Fin 3)
    (J b : RothBlockVars m →₀ ℕ) :
    rothAuxScaledSubstitution a k
      (rothBlockIntegerDividedDerivative J (MvPolynomial.monomial b 1)) =
      MvPolynomial.C (∏ u : RothBlockVars m, (Nat.choose (b u) (J u) : ℤ)) *
        ∏ u : RothBlockVars m, rothAuxScaledChart a k u ^ (b - J) u := by
  rw [rothAux_derivative_monomial]
  change MvPolynomial.eval₂ MvPolynomial.C (rothAuxScaledChart a k)
    (MvPolynomial.monomial (b - J) (1 * ∏ u, (Nat.choose (b u) (J u) : ℤ))) = _
  rw [MvPolynomial.eval₂_monomial, one_mul]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

theorem rothAux_exponent_sum {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) :
    (∑ u : RothBlockVars m, rothAuxExponent b u) = ∑ h, r h := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun h _ => (b h).property)

theorem rothAux_binomial_product_bound {m : ℕ} {r : Fin m → ℕ}
    (b : RothAuxCoefficients r) (J : RothBlockVars m →₀ ℕ) :
    |∏ u : RothBlockVars m, (Nat.choose (rothAuxExponent b u) (J u) : ℤ)| ≤
      (2 : ℤ) ^ (∑ h, r h) := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ u : RothBlockVars m, (2 : ℤ) ^ rothAuxExponent b u := by
      apply Finset.prod_le_prod
      · intro u _
        exact abs_nonneg _
      · intro u _
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        have hc : (rothAuxExponent b u).choose (J u) ≤ 2 ^ rothAuxExponent b u := by
          rcases Nat.eq_zero_or_pos (rothAuxExponent b u) with hz | hp
          · rw [hz]; cases J u <;> simp
          · exact (Nat.choose_le_two_pow _ _ hp).le
        exact_mod_cast hc
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, rothAux_exponent_sum]

theorem rothAux_transformed_entry_bound {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 3 → ℤ) (k : Fin 3) (A : ℤ) (hA : 1 ≤ A) (ha : ∀ j, |a j| ≤ A)
    (b : RothAuxCoefficients r) (J d : RothBlockVars m →₀ ℕ) :
    |(rothAuxScaledSubstitution a k
      (rothBlockIntegerDividedDerivative J (MvPolynomial.monomial (rothAuxExponent b) 1))).coeff d| ≤
        (6 * A) ^ (∑ h, r h) := by
  have hbase : 1 ≤ 3 * A := by omega
  have hsum : (∑ u : RothBlockVars m, (rothAuxExponent b - J) u) ≤ ∑ h, r h := by
    rw [← rothAux_exponent_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  rw [rothAux_scaled_derivative_monomial]
  calc
    _ ≤ rothAuxMass (MvPolynomial.C (∏ u : RothBlockVars m,
        (Nat.choose (rothAuxExponent b u) (J u) : ℤ)) *
        ∏ u : RothBlockVars m, rothAuxScaledChart a k u ^ (rothAuxExponent b - J) u) :=
      rothAux_coeff_le_mass _ _
    _ ≤ rothAuxMass (MvPolynomial.C (∏ u : RothBlockVars m,
        (Nat.choose (rothAuxExponent b u) (J u) : ℤ))) *
        rothAuxMass (∏ u : RothBlockVars m, rothAuxScaledChart a k u ^ (rothAuxExponent b - J) u) :=
      rothAuxMass_mul _ _
    _ ≤ (2 : ℤ) ^ (∑ h, r h) * (3 * A) ^ (∑ h, r h) := by
      apply mul_le_mul
      · simpa only [MvPolynomial.C_apply, rothAuxMass_monomial] using rothAux_binomial_product_bound b J
      · calc
          _ ≤ ∏ u : RothBlockVars m, rothAuxMass (rothAuxScaledChart a k u ^
              (rothAuxExponent b - J) u) := rothAuxMass_prod _ _
          _ ≤ ∏ u : RothBlockVars m, (3 * A) ^ (rothAuxExponent b - J) u := by
            apply Finset.prod_le_prod
            · intro u _; exact rothAuxMass_nonneg _
            · intro u _
              exact (rothAuxMass_pow _ _).trans
                (pow_le_pow_left₀ (rothAuxMass_nonneg _) (rothAuxScaledChart_mass a k A hA ha u) _)
          _ = (3 * A) ^ (∑ u : RothBlockVars m, (rothAuxExponent b - J) u) :=
            Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ _ := pow_le_pow_right₀ hbase hsum
      · exact rothAuxMass_nonneg _
      · positivity
    _ = _ := by rw [← mul_pow]; congr 1; ring


theorem rothAuxMatrix_entry_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (q : RothAuxEquations r eta) (b : RothAuxCoefficients r) :
    |rothAuxMatrix r eta L hL q b| ≤
      (6 * (rothAuxSourceHeight L : ℤ)) ^ (∑ h, r h) := by
  exact rothAux_transformed_entry_bound _ _ _
    (by exact_mod_cast rothAuxSourceHeight_one_le L)
    (fun j => rothAuxSourceHeight_coeff L _ _ j) b _ _

end JSP000334
