import SubspaceBridge.SourceGrid10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceVanishing10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10 SourceExpansion10 SourceSupport10 SourceBalance10 SourceEvaluation10 SourceGrid10

theorem evaluation_identity_of_reconstruction {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 10) (Fin 10) K)
    (J : Vars10 m →₀ ℕ) (P : MvPolynomial (Vars10 m) ℤ) (v : Fin m → Fin 10 → ℤ)
    (hrec : substitution A (expansion A J P) = derivative10 J (P.map (Int.castRingHom K))) :
    (integerValue J P v : K) = ∑ b ∈ (expansion A J P).support,
      (expansion A J P).coeff b * ∏ u : Vars10 m,
        ((A *ᵥ (fun i => (v u.1 i : K))) u.2) ^ b u := by
  rw [integerValue_cast, ← hrec]
  have he : (MvPolynomial.eval (fun u : Vars10 m => (v u.1 u.2 : K))).comp
      (substitution A) = MvPolynomial.eval (fun u : Vars10 m =>
        (A *ᵥ (fun i => (v u.1 i : K))) u.2) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [substitution]
    · intro u; simp [substitution, linearChart, Matrix.mulVec, dotProduct]
  rw [← RingHom.comp_apply, he]
  conv_lhs => arg 2; rw [MvPolynomial.as_sum (expansion A J P)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
theorem evaluation_upper_of_reconstruction {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (A : Matrix (Fin 10) (Fin 10) K)
    (r : Fin m → ℕ) (J : Vars10 m →₀ ℕ) (P : MvPolynomial (Vars10 m) ℤ)
    (hP : homogeneous10 r P)
    (hrec : substitution A (expansion A J P) = derivative10 J (P.map (Int.castRingHom K))) (v : Fin m → Fin 10 → ℤ)
    (E T : ℝ) (hE : 0 ≤ E) (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 10 → ℝ)
    (hv : ∀ h i, ‖(A *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i))
    (hc : ∀ b, ‖(expansion A J P).coeff b‖ ≤ E^(∑ h, r h))
    (ht : ∀ b ∈ (expansion A J P).support, (∑ i, c i * logWeight Q b i) ≤ T) :
    ‖(integerValue J P v : K)‖ ≤ (1060*E)^(∑ h, r h)*Real.exp T := by
  rw [evaluation_identity_of_reconstruction A J P v hrec]
  calc
    _ ≤ ∑ b ∈ (expansion A J P).support, ‖(expansion A J P).coeff b *
        ∏ u : Vars10 m, ((A *ᵥ (fun i => (v u.1 i : K))) u.2)^b u‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ (expansion A J P).support, E^(∑ h, r h)*Real.exp T := by
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul]
      exact (mul_le_mul (hc b) (monomial_bound A v Q hQ c hv b)
        (norm_nonneg _) (pow_nonneg hE _)).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (ht b hb)) (pow_nonneg hE _))
    _ = ((expansion A J P).support.card : ℝ)*(E^(∑ h, r h)*Real.exp T) := by simp
    _ ≤ (1060 : ℝ)^(∑ h, r h)*(E^(∑ h, r h)*Real.exp T) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hs : ((expansion A J P).support.card : ℝ) ≤ (1024 : ℝ)^(∑ h,r h) := by
        exact_mod_cast expansion_support_card r A J P hP
      exact hs.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
    _ = _ := by rw [← mul_assoc, ← mul_pow]
theorem local_upper_from_claims {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (B : Matrix (Fin 10) (Fin 10) K)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (eta delta A E : ℝ) (heta : 0 < eta) (hd : 4000*eta < delta) (hd1 : delta < 1)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P) (hclaims : Claims r eta B P)
    (hcfs : ∀ J b, ‖(expansion B J P).coeff b‖ ≤ E^(∑ h, r h))
    (c : Fin 10 → ℝ) (hc : ∀ i, |c i| ≤ 1) (arch : Bool)
    (v : Fin m → Fin 10 → ℤ)
    (hv : ∀ h i, ‖(B *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i-(if arch then delta else 0)+eta))
    (J : Vars10 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m) :
    ‖(integerValue J P v : K)‖ ≤ (1060*E)^(∑ h, r h)*
      Real.exp (A*m*((∑ i,c i)/10+(if arch then -2000*eta else 560*eta))) := by
  apply evaluation_upper_of_reconstruction B r J P hP (hclaims.1 J) v E _ hE Q (fun h => lt_trans zero_lt_one (hQ h))
    (fun i => c i-(if arch then delta else 0)+eta) hv (hcfs J)
  intro b hb
  have hn := MvPolynomial.mem_support_iff.mp hb
  have he := source_exponents r hr Q hQ eta delta A heta hd hd1 hA hlog J b hJ
    (hclaims.2.2.1 J b hn) (hclaims.2.2.2.2 J b hJ hn) c hc
  cases arch
  · simpa using he.2
  · simpa using he.1

theorem three_place_upper {m : ℕ} (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (r : Fin m → ℕ) (hr : ∀ h,0<r h) (Q : Fin m → ℝ) (hQ : ∀ h,1<Q h) (h0 : Fin m)
    (eta delta E : ℝ) (heta : 0<eta) (hd : 4000*eta<delta) (hd1 : delta<1) (hE : 1≤E)
    (hg : ∀ h,10*(eta⁻¹+1)<(Q h)^eta)
    (hlog : ∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0)))
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (hclaims : Claims r eta (L) P ∧ Claims r eta (SourceForms10.finiteMatrix10 2 A2) P ∧ Claims r eta (SourceForms10.finiteMatrix10 3 A3) P)
    (hcfs : ∀ J b, ‖(expansion (L) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 2 A2) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 3 A3) J P).coeff b‖≤E^(∑ h,r h))
    (c : Fin 3 → Fin 10 → ℝ) (hc : ∀ tau i,|c tau i|≤1)
    (w : Fin m → Fin 9 → Fin 10 → ℤ)
    (hw0 : ∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta))
    (hw2 : ∀ h j i,‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i))
    (hw3 : ∀ h j i,‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i))
    (a : Fin m → Fin 9 → ℕ) (ha : ∀ h j,a h j≤Nat.floor eta⁻¹+1)
    (J : Vars10 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J≤2*eta*m) :
    ‖(integerValue J P (gridPoint w a) : ℝ)‖≤sourceBound r E eta Q h0 c 0 ∧
    ‖(integerValue J P (gridPoint w a) : ℚ_[2])‖≤sourceBound r E eta Q h0 c 1 ∧
    ‖(integerValue J P (gridPoint w a) : ℚ_[3])‖≤sourceBound r E eta Q h0 c 2 := by
  have hA : 0≤(r h0 : ℝ)*Real.log (Q h0) := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (hQ h0)).le
  have hEp : 0≤E := by linarith
  have hQp : ∀ h,0<Q h := fun h => lt_trans zero_lt_one (hQ h)
  have hv0 := real_grid_bounds (L) w a Q hQp (c 0) eta delta heta ha hg hw0
  have hv2 := padic_grid_bounds 2 (SourceForms10.finiteMatrix10 2 A2) w a Q hQp (c 1) eta heta hg hw2
  have hv3 := padic_grid_bounds 3 (SourceForms10.finiteMatrix10 3 A3) w a Q hQp (c 2) eta heta hg hw3
  constructor
  · simpa only [sourceBound,if_pos rfl,Bool.true_eq] using
      (local_upper_from_claims (L) r hr Q hQ eta delta
        ((r h0 : ℝ)*Real.log (Q h0)) E heta hd hd1 hA hEp hlog P hP hclaims.1
        (fun J b => (hcfs J b).1) (c 0) (hc 0) true (gridPoint w a) hv0 J hJ)
  · constructor
    · simpa [sourceBound] using
        (local_upper_from_claims (SourceForms10.finiteMatrix10 2 A2) r hr Q hQ eta delta
          ((r h0 : ℝ)*Real.log (Q h0)) E heta hd hd1 hA hEp hlog P hP hclaims.2.1
          (fun J b => (hcfs J b).2.1) (c 1) (hc 1) false (gridPoint w a) (by simpa using hv2) J hJ)
    · simpa [sourceBound] using
        (local_upper_from_claims (SourceForms10.finiteMatrix10 3 A3) r hr Q hQ eta delta
          ((r h0 : ℝ)*Real.log (Q h0)) E heta hd hd1 hA hEp hlog P hP hclaims.2.2
          (fun J b => (hcfs J b).2.2) (c 2) (hc 2) false (gridPoint w a) (by simpa using hv3) J hJ)


theorem sourceBound_product {m : ℕ} (r : Fin m → ℕ) (E eta : ℝ) (Q : Fin m → ℝ)
    (h0 : Fin m) (c : Fin 3 → Fin 10 → ℝ) (hc : (∑ tau, ∑ i, c tau i) = 0) :
    sourceBound r E eta Q h0 c 0 * sourceBound r E eta Q h0 c 1 *
      sourceBound r E eta Q h0 c 2 =
      (1060*E)^(3*(∑ h,r h))*Real.exp (-880*((r h0 : ℝ)*Real.log (Q h0))*m*eta) := by
  have hs : (∑ i,c 0 i)+(∑ i,c 1 i)+(∑ i,c 2 i)=0 := by
    simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,
      Fin.val_one,Fin.val_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,add_zero,add_assoc] using hc
  let F : ℝ := (1060*E)^(∑ h,r h)
  let T : Fin 3 → ℝ := fun tau => ((r h0 : ℝ)*Real.log (Q h0))*m*
    ((∑ i,c tau i)/10+(if tau=0 then -2000*eta else 560*eta))
  have ht : T 0+T 1+T 2 = -880*((r h0 : ℝ)*Real.log (Q h0))*m*eta := by
    dsimp [T]
    linear_combination ((r h0 : ℝ)*Real.log (Q h0)*(m : ℝ)/10)*hs
  have hf : F*F*F = (1060*E)^(3*(∑ h,r h)) := by
    dsimp [F]
    rw [← pow_add,← pow_add]
    congr 1
    omega
  change (F*Real.exp (T 0))*(F*Real.exp (T 1))*(F*Real.exp (T 2)) = _
  calc
    _ = (F*F*F)*Real.exp (T 0+T 1+T 2) := by rw [Real.exp_add,Real.exp_add]; ring
    _ = _ := by rw [hf,ht]

theorem three_place_product_lt_one {m : ℕ} (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (r : Fin m → ℕ) (hr : ∀ h,0<r h) (Q : Fin m → ℝ) (hQ : ∀ h,1<Q h) (h0 : Fin m)
    (eta delta E : ℝ) (heta : 0<eta) (hd : 4000*eta<delta) (hd1 : delta<1) (hE : 1≤E)
    (hg610 : ∀ h,1060*E<(Q h)^eta)
    (hg : ∀ h,10*(eta⁻¹+1)<(Q h)^eta)
    (hlog : ∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0)))
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (hclaims : Claims r eta (L) P ∧ Claims r eta (SourceForms10.finiteMatrix10 2 A2) P ∧ Claims r eta (SourceForms10.finiteMatrix10 3 A3) P)
    (hcfs : ∀ J b, ‖(expansion (L) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 2 A2) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 3 A3) J P).coeff b‖≤E^(∑ h,r h))
    (c : Fin 3 → Fin 10 → ℝ) (hc : ∀ tau i,|c tau i|≤1)
    (hbalance : (∑ tau,∑ i,c tau i)=0)
    (w : Fin m → Fin 9 → Fin 10 → ℤ)
    (hw0 : ∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta))
    (hw2 : ∀ h j i,‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i))
    (hw3 : ∀ h j i,‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i))
    (a : Fin m → Fin 9 → ℕ) (ha : ∀ h j,a h j≤Nat.floor eta⁻¹+1)
    (J : Vars10 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J≤2*eta*m) :
    ‖(integerValue J P (gridPoint w a) : ℝ)‖ *
      ‖(integerValue J P (gridPoint w a) : ℚ_[2])‖ *
      ‖(integerValue J P (gridPoint w a) : ℚ_[3])‖ < 1 := by
  have hu := three_place_upper A2 A3 L h2 h3 hL r hr Q hQ h0 eta delta E heta hd hd1 hE hg hlog P hP hclaims hcfs c hc w hw0 hw2 hw3 a ha J hJ
  have hEp : 0≤E := by linarith
  have hn (tau : Fin 3) : 0≤sourceBound r E eta Q h0 c tau := by
    unfold sourceBound
    positivity
  have hu01 := mul_le_mul hu.1 hu.2.1 (norm_nonneg _) (hn 0)
  have hu012 := mul_le_mul hu01 hu.2.2 (norm_nonneg _) (mul_nonneg (hn 0) (hn 1))
  rw [sourceBound_product r E eta Q h0 c hbalance] at hu012
  exact hu012.trans_lt (strict_product_bound r hr Q hQ h0 eta E heta (by linarith)
    hE hg610 (fun h => (hlog h).2))
theorem grid_derivative_vanishes {m : ℕ} (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (r : Fin m → ℕ) (hr : ∀ h,0<r h) (Q : Fin m → ℝ) (hQ : ∀ h,1<Q h) (h0 : Fin m)
    (eta delta E : ℝ) (heta : 0<eta) (hd : 4000*eta<delta) (hd1 : delta<1) (hE : 1≤E)
    (hg610 : ∀ h,1060*E<(Q h)^eta)
    (hg : ∀ h,10*(eta⁻¹+1)<(Q h)^eta)
    (hlog : ∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0)))
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (hclaims : Claims r eta (L) P ∧ Claims r eta (SourceForms10.finiteMatrix10 2 A2) P ∧ Claims r eta (SourceForms10.finiteMatrix10 3 A3) P)
    (hcfs : ∀ J b, ‖(expansion (L) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 2 A2) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 3 A3) J P).coeff b‖≤E^(∑ h,r h))
    (c : Fin 3 → Fin 10 → ℝ) (hc : ∀ tau i,|c tau i|≤1)
    (hbalance : (∑ tau,∑ i,c tau i)=0)
    (w : Fin m → Fin 9 → Fin 10 → ℤ)
    (hw0 : ∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta))
    (hw2 : ∀ h j i,‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i))
    (hw3 : ∀ h j i,‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i))
    (a : Fin m → Fin 9 → ℕ) (ha : ∀ h j,a h j≤Nat.floor eta⁻¹+1)
    (J : Vars10 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J≤2*eta*m) :
    integerValue J P (gridPoint w a) = 0 := by
  by_contra hz
  have hl := integerValue_lower J P (gridPoint w a) hz
  have hu := three_place_product_lt_one A2 A3 L h2 h3 hL r hr Q hQ h0 eta delta E heta hd hd1 hE hg610 hg hlog P hP hclaims hcfs c hc hbalance w hw0 hw2 hw3 a ha J hJ
  linarith


theorem source_auxiliary10_grid_vanishing (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms10.forms10 A2 A3 L tau i j ∈ K,
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ, P ≠ 0 ∧ homogeneous10 r P ∧
      (height10 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex10 (fun i j => (⟨SourceForms10.forms10 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex10 (SourceForms10.forms10 A2 A3 L tau) r eta P) ∧
      matrixIndex10 (SourceForms10.finiteMatrix10 2 A2) r eta P ∧
      matrixIndex10 (SourceForms10.finiteMatrix10 3 A3) r eta P ∧
      (Claims r eta L P ∧ Claims r eta (SourceForms10.finiteMatrix10 2 A2) P ∧
        Claims r eta (SourceForms10.finiteMatrix10 3 A3) P) ∧
      (∀ J b : Vars10 m →₀ ℕ,
        ‖(expansion L J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms10.finiteMatrix10 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms10.finiteMatrix10 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) ∧
        (∀ (Q : Fin m → ℝ), (∀ h,1<Q h) → ∀ h0 : Fin m,
          ∀ delta : ℝ, 4000*eta<delta → delta<1 →
          (∀ h,1060*E<(Q h)^eta) → (∀ h,10*(eta⁻¹+1)<(Q h)^eta) →
          (∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0))) →
          ∀ c : Fin 3 → Fin 10 → ℝ, (∀ tau i,|c tau i|≤1) → (∑ tau,∑ i,c tau i)=0 →
          ∀ w : Fin m → Fin 9 → Fin 10 → ℤ,
          (∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta)) →
          (∀ h j i,‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i)) →
          (∀ h j i,‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i)) →
          ∀ a : Fin m → Fin 9 → ℕ, (∀ h j,1≤a h j ∧ a h j≤Nat.floor eta⁻¹+1) →
          ∀ J : Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J<2*eta*m →
          integerValue J P (gridPoint w a)=0) := by
  obtain ⟨K,hK,hmem,D,E,hD,hE,hconstruction⟩ := source_auxiliary10_balanced A2 A3 L h2 h3 hL ha
  refine ⟨K,hK,hmem,D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,?_⟩
  intro Q hQ h0 delta hd hd1 hg16 hg hlog c hc hbalance w hw0 hw2 hw3 a haGrid J hJ
  exact grid_derivative_vanishes A2 A3 L h2 h3 hL r hr Q hQ h0 eta delta E heta hd hd1 hE
    hg16 hg hlog P hhom hclaims hcfs c hc hbalance w hw0 hw2 hw3 a
    (fun h j => (haGrid h j).2) J hJ.le

end CompoundFeasibility.Auxiliary10.SourceVanishing10
