import SubspaceBridge.OriginalDeformedFrame4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalAuxiliaryGeometry4
open OriginalLastDual4 OriginalAuxiliaryDual4 OriginalDeformedFrame4 OriginalDeformation4

def primeProduct4 (e2 e3 : Fin 4 → ℕ) : ℕ := 2^(∑ i, e2 i)*3^(∑ i, e3 i)

def auxiliaryInteger4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ)
    (y : Fin 4 → ℤ) : Prop :=
  (∀ i, ‖(L⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i‖ ≤
    ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3))/A i) ∧
  (∀ i, ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[2]))) i‖ ≤
    (2 : ℝ)^(∑ k : Fin 3, -(e2 (i.succAbove k) : ℤ))) ∧
  (∀ i, ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[3]))) i‖ ≤
    (3 : ℝ)^(∑ k : Fin 3, -(e3 (i.succAbove k) : ℤ)))

theorem auxiliary_pairing_dvd4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (e : Fin 4 → ℕ) (x y : Fin 4 → ℤ) (hx : x ∈ lattice4 p A e)
    (hy : ∀ i, ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ)^(∑ k : Fin 3, -(e (i.succAbove k) : ℤ))) :
    (p : ℤ)^(∑ i, e i) ∣ integerPairing4 x y := by
  have hB : (A.map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
    rw [mapped_det_one4 A hA]
    exact one_ne_zero
  have h := native_ultrametric_pairing4 p _ hB (fun i => -(e i : ℤ)) x y
    (original_lattice_finite_bound4 p A e x hx) hy
  apply (SchlickeweiIntegerPairing6.integer_norm_dvd6 p _ (∑ i, e i)).mp
  simpa only [Finset.sum_neg_distrib,← Nat.cast_sum] using h

theorem auxiliary_pairing_primeProduct4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ)
    (x : sourceLattice4 A2 A3 e2 e3) (y : Fin 4 → ℤ)
    (hy : auxiliaryInteger4 A2 A3 L e2 e3 A y) :
    (primeProduct4 e2 e3 : ℤ) ∣ integerPairing4 (x : Fin 4 → ℤ) y := by
  have hcop : IsCoprime ((2 : ℤ)^(∑ i, e2 i)) ((3 : ℤ)^(∑ i, e3 i)) :=
    IsCoprime.pow (show IsCoprime (2 : ℤ) 3 from ⟨-1,1,by norm_num⟩)
  simpa only [primeProduct4,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    hcop.mul_dvd (auxiliary_pairing_dvd4 2 A2 h2 e2 _ y x.property.1 hy.2.1)
      (auxiliary_pairing_dvd4 3 A3 h3 e3 _ y x.property.2 hy.2.2)

theorem auxiliary_pairing_real4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det ≠ 0) (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (x y : Fin 4 → ℤ)
    (hx : ∀ i, |(L *ᵥ (fun k => (x k : ℝ))) i| ≤ epsilon*A i)
    (hy : auxiliaryInteger4 A2 A3 L e2 e3 A y) :
    ‖(integerPairing4 x y : ℝ)‖ ≤
      4*epsilon*ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) := by
  have hb := real_pairing_bound4 L hL x y (fun i => epsilon*A i)
    (fun i => ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3))/A i)
    (fun i => mul_nonneg he (hA i).le) (by simpa only [Real.norm_eq_abs] using hx) hy.1
  apply hb.trans_eq
  calc
    _ = ∑ _i : Fin 4, epsilon*ZLattice.covolume
        (integerRealImage (sourceLattice4 A2 A3 e2 e3)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hA i).ne']
      ring
    _ = _ := by simp; ring

theorem auxiliary_pairing_zero4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det ≠ 0)
    (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (K epsilon : ℝ) (he : 0 ≤ epsilon)
    (hcov : ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) ≤
      K*(primeProduct4 e2 e3 : ℝ)) (hsmall : 4*epsilon*K < 1)
    (x : sourceLattice4 A2 A3 e2 e3) (y : Fin 4 → ℤ)
    (hx : ∀ i, |(L *ᵥ (fun k => ((x : Fin 4 → ℤ) k : ℝ))) i| ≤ epsilon*A i)
    (hy : auxiliaryInteger4 A2 A3 L e2 e3 A y) :
    integerPairing4 (x : Fin 4 → ℤ) y = 0 := by
  have hP : 0 < primeProduct4 e2 e3 := by unfold primeProduct4; positivity
  have hPR : (0 : ℝ) < primeProduct4 e2 e3 := by exact_mod_cast hP
  have hbound := auxiliary_pairing_real4 A2 A3 L hL e2 e3 A hA epsilon he _ y hx hy
  have hle := mul_le_mul_of_nonneg_left hcov (show 0 ≤ 4*epsilon by positivity)
  have hlt := mul_lt_mul_of_pos_right hsmall hPR
  have hsmallreal : ‖(integerPairing4 (x : Fin 4 → ℤ) y : ℝ)‖ < (primeProduct4 e2 e3 : ℝ) := by
    nlinarith
  by_contra hz
  have hab := Int.natAbs_le_of_dvd_ne_zero
    (auxiliary_pairing_primeProduct4 A2 A3 L h2 h3 e2 e3 A x y hy) hz
  have habR : (primeProduct4 e2 e3 : ℝ) ≤ ‖(integerPairing4 (x : Fin 4 → ℤ) y : ℝ)‖ := by
    simpa only [Int.natAbs_natCast,Int.cast_natAbs,Int.cast_abs,Real.norm_eq_abs] using
      (show ((primeProduct4 e2 e3 : ℤ).natAbs : ℝ) ≤
        ((integerPairing4 (x : Fin 4 → ℤ) y).natAbs : ℝ) by exact_mod_cast hab)
  exact (not_lt_of_ge habR) hsmallreal

theorem rational_annihilator_line4 (w : Fin 4 → Fin 4 → ℚ)
    (hw : LinearIndependent ℚ w) (y : Fin 4 → ℚ)
    (hann : ∀ j : Fin 3, (∑ i, w j.castSucc i*y i) = 0) :
    y ∈ Submodule.span ℚ {lastDual4 w hw} := by
  let f : Module.Dual ℚ (Fin 4 → ℚ) := ∑ i, y i • LinearMap.proj i
  have hf : ∀ j : Fin 3, f (w j.castSucc) = 0 := by
    intro j
    simpa only [f,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,
      smul_eq_mul,mul_comm] using hann j
  have he := functional_lastDual4 w hw f hf
  have hy : y = f (w 3) • lastDual4 w hw := by
    funext i
    have hi := congrArg (fun g : Module.Dual ℚ (Fin 4 → ℚ) => g (Pi.single i 1)) he
    simpa [f,lastDual4,Pi.single_apply] using hi
  rw [hy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))


theorem source_auxiliary_line4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det ≠ 0)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ), T < Q → ∀ (hQ : 1 < Q) (c2 c3 A : Fin 4 → ℝ),
      (∀ i, 0 < A i) →
      ∀ w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3,
      ∀ hw : LinearIndependent ℚ (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)),
      (∀ (j : Fin 3) i, |(L *ᵥ (fun k => ((w j.castSucc : Fin 4 → ℤ) k : ℝ))) i| ≤
        (Q^(5 : ℕ))^(-delta)*A i) →
      ∀ y : Fin 4 → ℤ,
      auxiliaryInteger4 A2 A3 L
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))) A y →
      (∀ j : Fin 3, integerPairing4 (w j.castSucc : Fin 4 → ℤ) y = 0) ∧
      (fun i => (y i : ℚ)) ∈ Submodule.span ℚ {lastDual4 (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)) hw} := by
  obtain ⟨K,hK,hindex⟩ := sourceLattice4_uniform_index_upper A2 A3 (sourceUnit42 A2 h2) (sourceUnit42 A3 h3)
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (4*(K : ℝ)) (2*delta) (by positivity)
  refine ⟨T,hT,?_⟩
  intro Q hTQ hQ c2 c3 A hA w hw hx y hy
  let e2 := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i))
  let e3 := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))
  have hcov : ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) ≤
      (K : ℝ)*(primeProduct4 e2 e3 : ℝ) := by
    rw [sourceLattice4_covolume_index]
    have h := hindex e2 e3
    have hn : (sourceLattice4 A2 A3 e2 e3).index ≤ K*primeProduct4 e2 e3 := by
      simpa only [primeProduct4,Nat.mul_assoc] using h
    exact_mod_cast hn
  have hQ5 : 1 < Q^(5 : ℕ) := one_lt_pow₀ hQ (by decide)
  have hQQ5 : Q ≤ Q^(5 : ℕ) := le_self_pow₀ hQ.le (by decide)
  have hsmall : 4*(Q^(5 : ℕ))^(-delta)*(K : ℝ) < 1 := by
    have hb : 4*(K : ℝ) < (Q^(5 : ℕ))^delta := by
      convert hcut (Q^(5 : ℕ)) (hTQ.trans_le hQQ5) using 1 <;> congr 1 <;> ring
    rw [Real.rpow_neg (zero_lt_one.trans hQ5).le]
    have he := (div_lt_one (Real.rpow_pos_of_pos (zero_lt_one.trans hQ5) delta)).mpr hb
    convert he using 1 <;> ring
  have hz (j : Fin 3) : integerPairing4 (w j.castSucc : Fin 4 → ℤ) y = 0 :=
    auxiliary_pairing_zero4 A2 A3 L h2 h3 hL e2 e3 A hA K _ (by positivity)
      hcov hsmall (w j.castSucc) y (hx j) hy
  refine ⟨hz,rational_annihilator_line4 _ hw _ ?_⟩
  intro j
  exact_mod_cast hz j

theorem source_prime_product_covolume4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (e2 e3 : Fin 4 → ℕ) :
    (primeProduct4 e2 e3 : ℝ) ≤ ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) := by
  obtain ⟨b⟩ := sourceLattice4_has_basis A2 A3 e2 e3
  have h := integerRealImage_padic_covolume_lower (sourceLattice4 A2 A3 e2 e3) b A2 A3 e2 e3
    (fun x hx i => (lattice4_spec 2 A2 e2 x).mp hx.1 i)
    (fun x hx i => (lattice4_spec 3 A3 e3 x).mp hx.2 i)
  simpa only [primeProduct4,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,h2,h3,padicNorm.one,
    Rat.cast_one,one_mul] using h

theorem balanced_width_product_covolume4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (Q : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 4 → ℝ)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (∏ i, A i) ≤ ZLattice.covolume (integerRealImage (originalSourceGroup4 A2 A3 Q c2 c3)) := by
  have hQp := zero_lt_one.trans hQ
  have hp : 0 < ∏ i, Q^(c2 i+c3 i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos hQp _)
  have heq : (∏ i, A i) = (∏ i, Q^(-c2 i))*(∏ i, Q^(-c3 i)) := by
    have hinv : (∏ i, A i) = (∏ i, Q^(c2 i+c3 i))⁻¹ := by
      rw [← one_div]
      apply (eq_div_iff hp.ne').mpr
      simpa using hb
    rw [hinv]
    simp_rw [Real.rpow_add hQp,Real.rpow_neg hQp.le]
    rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,Finset.prod_inv_distrib]
    ring
  have hbound (p : ℕ) (hp : 1 < p) (c : ℝ) :
      Q^(-c) ≤ (p : ℝ)^Nat.ceil (JSP000334.qThreshold p Q c) := by
    rw [← JSP000334.qThreshold_rpow p hp Q c hQ,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
  rw [heq]
  apply le_trans _ (source_prime_product_covolume4 A2 A3 h2 h3 _ _)
  unfold primeProduct4
  push_cast
  rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul (Finset.prod_le_prod (fun i _ => (Real.rpow_pos_of_pos hQp _).le)
      (fun i _ => hbound 2 (by decide) (c2 i)))
    (Finset.prod_le_prod (fun i _ => (Real.rpow_pos_of_pos hQp _).le)
      (fun i _ => hbound 3 (by decide) (c3 i)))
    (Finset.prod_nonneg (fun i _ => (Real.rpow_pos_of_pos hQp _).le)) (by positivity)

end CompoundFeasibility.OriginalAuxiliaryGeometry4
