import SubspaceBridge.CompoundMinima6
open scoped BigOperators Matrix Pointwise
open MeasureTheory Filter
namespace CompoundFeasibility

theorem sourceLattice4_multiple (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ j : Fin 4, Pi.single j D ∈ sourceLattice4 A₂ A₃ e₂ e₃ := by
  obtain ⟨D₂,h₂,hD₂⟩ := clear_matrix_denominators A₂
  obtain ⟨D₃,h₃,hD₃⟩ := clear_matrix_denominators A₃
  let D : ℤ := D₂ * D₃ * 2 ^ (∑ s, e₂ s) * 3 ^ (∑ s, e₃ s)
  refine ⟨D, by dsimp [D]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h₂ h₃) (by positivity)) (by positivity), ?_⟩
  intro j
  constructor
  · apply (lattice4_spec 2 A₂ e₂ _).mpr
    have he : D = D₂ * 2 ^ (∑ s, e₂ s) * (D₃ * 3 ^ (∑ s, e₃ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 2 A₂ e₂ D₂ hD₂ _ j
  · apply (lattice4_spec 3 A₃ e₃ _).mpr
    have he : D = D₃ * 3 ^ (∑ s, e₃ s) * (D₂ * 2 ^ (∑ s, e₂ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 3 A₃ e₃ D₃ hD₃ _ j

theorem sourceLattice4_has_basis (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : Nonempty (Basis (Fin 4) ℤ (sourceLattice4 A₂ A₃ e₂ e₃)) := by
  obtain ⟨D,hD,hm⟩ := sourceLattice4_multiple A₂ A₃ e₂ e₃
  exact integer_subgroup_has_basis _ D hD hm

instance sourceLattice4_isZLattice (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : IsZLattice ℝ (integerRealImage (sourceLattice4 A₂ A₃ e₂ e₃)) where
  span_top := by
    obtain ⟨D,hD,hm⟩ := sourceLattice4_multiple A₂ A₃ e₂ e₃
    exact integerRealImage_span_top _ D hD hm

theorem sourceLattice4_covolume_det (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) (c : Basis (Fin 4) ℤ (sourceLattice4 A₂ A₃ e₂ e₃)) :
    ZLattice.covolume (integerRealImage (sourceLattice4 A₂ A₃ e₂ e₃)) =
      |(Matrix.of (fun j i => ((c j : Fin 4 → ℤ) i : ℝ))).det| :=
  integerRealImage_covolume_det _ c

theorem sourceLattice4_covolume_index (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) :
    ZLattice.covolume (integerRealImage (sourceLattice4 A₂ A₃ e₂ e₃)) =
      ((sourceLattice4 A₂ A₃ e₂ e₃).index : ℝ) := by
  obtain ⟨c⟩ := sourceLattice4_has_basis A₂ A₃ e₂ e₃
  exact integerRealImage_covolume_index _ c

theorem integer_span4_index_det
    {M : Type*} [AddCommGroup M]
    (c : Basis (Fin 4) ℤ M) (u : Fin 4 → M) (hu : LinearIndependent ℤ u) :
    Finite (M ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index = (c.toMatrix u).det.natAbs ∧
      (c.toMatrix u).det ≠ 0 := by
  letI : Module.Free ℤ M := Module.Free.of_basis c
  letI : Module.Finite ℤ M := Module.Finite.of_basis c
  let N := Submodule.span ℤ (Set.range u)
  let e : M ≃+ N := by
    letI : Module ℤ N := N.module
    exact (c.equiv (Basis.span hu) (Equiv.refl _)).toAddEquiv
  have hfinite : Finite (M ⧸ N) :=
    Submodule.finiteQuotientOfFreeOfRankEq N e.toIntLinearEquiv.symm.finrank_eq
  have hcard : Nat.card (M ⧸ N) = (c.toMatrix u).det.natAbs := by
    have h := (Submodule.natAbs_det_basis_change c N (Basis.span hu)).symm

    have hspan :
        (Subtype.val ∘ (Basis.span hu : Fin 4 → N)) = u := by
      funext i
      exact Basis.span_apply hu i

    have hmat :
        c.toMatrix (Subtype.val ∘ (Basis.span hu : Fin 4 → N)) =
          c.toMatrix u :=
      congrArg (fun w : Fin 4 → M => c.toMatrix w) hspan

    calc
      Nat.card (M ⧸ N) =
          (c.toMatrix (Subtype.val ∘ (Basis.span hu : Fin 4 → N))).det.natAbs := by
            simpa only [Basis.det_apply] using h
      _ = (c.toMatrix u).det.natAbs := by
            rw [hmat]
  refine ⟨hfinite, hcard, ?_⟩
  letI := hfinite
  have hpos := Nat.card_pos (α := M ⧸ N)
  rw [hcard] at hpos
  exact Int.natAbs_ne_zero.mp (ne_of_gt hpos)


theorem integer_matrix_index_upper4 (G : AddSubgroup (Fin 4 → ℤ))
    (U : Matrix (Fin 4) (Fin 4) ℤ) (hU : U.det ≠ 0) (hm : ∀ j, U.col j ∈ G) :
    G.index ≤ U.det.natAbs := by
  classical
  let N := Submodule.span ℤ (Set.range U.col)
  obtain ⟨hf,hi,hd⟩ := integer_span4_index_det (Pi.basisFun ℤ (Fin 4)) U.col
    (Matrix.linearIndependent_cols_of_det_ne_zero hU)
  have he : (Pi.basisFun ℤ (Fin 4)).toMatrix U.col = U := by ext i j; rfl
  rw [he] at hi
  letI : N.toAddSubgroup.FiniteIndex := ⟨by rw [hi]; exact Int.natAbs_ne_zero.mpr hU⟩
  have hle : N.toAddSubgroup ≤ G := by
    change N ≤ G.toIntSubmodule
    exact Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hm j)
  exact (AddSubgroup.index_antitone hle).trans_eq hi

theorem inverse_integral_frame4 (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : IsUnit A) :
    ∃ (D : ℤ) (B : Matrix (Fin 4) (Fin 4) ℤ), D ≠ 0 ∧ B.det ≠ 0 ∧
      B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
  classical
  obtain ⟨D,hD,hm⟩ := clear_matrix_denominators A⁻¹
  choose b hB using hm
  let B : Matrix (Fin 4) (Fin 4) ℤ := b
  have he : (B : Matrix (Fin 4) (Fin 4) ℤ).map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
    ext i j
    exact hB i j
  refine ⟨D,B,hD,?_,he⟩
  have hd : ((B : Matrix (Fin 4) (Fin 4) ℤ).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [he, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hD))
      (inv_ne_zero (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)))
  intro h
  apply hd
  rw [← integer_matrix_det_cast, h, Int.cast_zero]

theorem lattice4_index_upper (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (D : ℤ) (B : Matrix (Fin 4) (Fin 4) ℤ)
    (hB : B.det ≠ 0)
    (he : B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹) (hA : IsUnit A)
    (e : Fin 4 → ℕ) :
    (lattice4 p A e).index ≤ B.det.natAbs * p ^ (∑ i, e i) := by
  classical
  let U := B * Matrix.diagonal (fun i => (p : ℤ) ^ e i)
  have hd : U.det = B.det * (p : ℤ) ^ (∑ i, e i) := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hU : U.det ≠ 0 := by rw [hd]; exact mul_ne_zero hB (pow_ne_zero _ (by exact_mod_cast hp))
  have hm (j : Fin 4) : U.col j ∈ lattice4 p A e := by
    apply (lattice4_spec p A e _).mpr
    have hcol : (fun k => (U.col j k : ℚ)) =
        (p : ℚ) ^ e j • (B.map (Int.castRingHom ℚ)).col j := by
      ext k
      simp [U,Matrix.mul_diagonal,Matrix.col_apply,smul_eq_mul,mul_comm]
    have hmul : A * B.map (Int.castRingHom ℚ) = (D : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
      rw [he,Matrix.mul_smul,Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    have hact : A *ᵥ (B.map (Int.castRingHom ℚ)).col j =
        ((D : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ)).col j := by
      change (A * B.map (Int.castRingHom ℚ)).col j = _
      rw [hmul]
    intro i
    rw [hcol,Matrix.mulVec_smul,hact]
    by_cases hij : i = j
    · subst i
      simp only [Pi.smul_apply,smul_eq_mul,Matrix.col_apply,Matrix.smul_apply,Matrix.one_apply_eq,mul_one]
      rw [show (p : ℚ) ^ e j * (D : ℚ) = (((p : ℤ) ^ e j * D : ℤ) : ℚ) by push_cast; ring]
      apply padicNorm.dvd_iff_norm_le.mp
      exact_mod_cast (dvd_mul_right ((p : ℤ) ^ e j) D)
    · simp [Matrix.col_apply,Matrix.one_apply,hij,Ne.symm hij]
  have h := integer_matrix_index_upper4 (lattice4 p A e) U hU hm
  rw [hd,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at h
  exact h

theorem sourceLattice4_uniform_index_upper (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) :
    ∃ K : ℕ, 0 < K ∧ ∀ e₂ e₃ : Fin 4 → ℕ,
      (sourceLattice4 A₂ A₃ e₂ e₃).index ≤
        K * 2 ^ (∑ i, e₂ i) * 3 ^ (∑ i, e₃ i) := by
  obtain ⟨D₂,B₂,hD₂,hB₂,he₂⟩ := inverse_integral_frame4 A₂ h₂
  obtain ⟨D₃,B₃,hD₃,hB₃,he₃⟩ := inverse_integral_frame4 A₃ h₃
  refine ⟨B₂.det.natAbs * B₃.det.natAbs,
    Nat.mul_pos (Int.natAbs_pos.mpr hB₂) (Int.natAbs_pos.mpr hB₃),?_⟩
  intro e₂ e₃
  have h2 := lattice4_index_upper 2 A₂ D₂ B₂ hB₂ he₂ h₂ e₂
  have h3 := lattice4_index_upper 3 A₃ D₃ B₃ hB₃ he₃ h₃ e₃
  have h := (AddSubgroup.index_inf_le (H := lattice4 2 A₂ e₂) (K := lattice4 3 A₃ e₃)).trans
    (Nat.mul_le_mul h2 h3)
  simpa only [sourceLattice4, Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

theorem q_prime_powers_product_upper4 (p : ℕ) (hp : 1 < p)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) :
    (p : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold p Q (c i))) ≤
      (p : ℝ) ^ 4 * ∏ i, Q ^ (-c i) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hstep (i : Fin 4) :
      (p : ℝ) ^ Nat.ceil (JSP000334.qThreshold p Q (c i)) ≤ (p : ℝ) * Q ^ (-c i) := by
    rw [← JSP000334.qThreshold_rpow p hp Q (c i) hQ, ← Real.rpow_natCast]
    calc
      _ ≤ (p : ℝ) ^ (JSP000334.qThreshold p Q (c i) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le)
          (Nat.ceil_lt_add_one (JSP000334.qThreshold_nonneg p hp Q (c i) hQ (hc i))).le
      _ = _ := by rw [Real.rpow_add hp0,Real.rpow_one]; ring
  rw [← Finset.prod_pow_eq_pow_sum]
  have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => pow_nonneg hp0.le _) (fun i _ => hstep i)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem q_prime_powers_normalized_upper4 (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (h₂ : ∀ i, c₂ i ≤ 0) (h₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (2 : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
      3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) ≤
      1296 * ∏ i, Q ^ c₀ i := by
  have hQ0 := lt_trans zero_lt_one hQ
  have hprod : (∏ i, Q ^ (-c₂ i)) * (∏ i, Q ^ (-c₃ i)) = ∏ i, Q ^ c₀ i := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [← Real.rpow_add hQ0]
    rw [← Real.rpow_sum_of_pos hQ0 _ Finset.univ, ← Real.rpow_sum_of_pos hQ0 _ Finset.univ]
    congr 1
    simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib] at hb ⊢
    linarith
  have h := mul_le_mul (q_prime_powers_product_upper4 2 (by decide) Q hQ c₂ h₂)
    (q_prime_powers_product_upper4 3 (by decide) Q hQ c₃ h₃)
    (by positivity) (by positivity)
  calc
    _ ≤ ((2 : ℝ) ^ 4 * ∏ i, Q ^ (-c₂ i)) * (3 ^ 4 * ∏ i, Q ^ (-c₃ i)) := h
    _ = ((2 : ℝ) ^ 4 * 3 ^ 4) * ((∏ i, Q ^ (-c₂ i)) * ∏ i, Q ^ (-c₃ i)) := by ring
    _ = _ := by rw [hprod]; norm_num

theorem sourceLattice4_uniform_normalized_covolume_upper
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) :
    ∃ K : ℕ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q → ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
      (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
      (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
      ZLattice.covolume (integerRealImage (sourceLattice4 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))) /
        (∏ i, Q ^ c₀ i) ≤ (K : ℝ) * 1296 := by
  obtain ⟨K,hK,hindex⟩ := sourceLattice4_uniform_index_upper A₂ A₃ h₂ h₃
  refine ⟨K,hK,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  have hW : 0 < ∏ i, Q ^ c₀ i := Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  apply (div_le_iff₀ hW).mpr
  rw [sourceLattice4_covolume_index]
  have hi := hindex (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hiR : (((sourceLattice4 A₂ A₃
      (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))).index : ℝ) ≤
      (K : ℝ) * 2 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
        3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) := by exact_mod_cast hi
  have hn := mul_le_mul_of_nonneg_left (q_prime_powers_normalized_upper4 Q hQ c₀ c₂ c₃ hc₂ hc₃ hb)
    (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  exact hiR.trans (by simpa only [mul_assoc] using hn)

abbrev lattice4Span (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) : Submodule ℤ (Fin 4 → ℝ) :=
  Submodule.span ℤ (Set.range b)
def coordinateGauge4 (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (x : Fin 4 → ℝ) : ℝ := ‖e x‖
theorem lattice4Span_gauge_ball_finite (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (r : ℝ) :
    ({x : (Fin 4 → ℝ) | coordinateGauge4 e x ≤ r} ∩ (lattice4Span b : Set (Fin 4 → ℝ))).Finite := by
  have hf := ZSpan.setFinite_inter (b.map e) (Metric.isBounded_closedBall (x := 0) (r := r))
  apply (hf.preimage e.injective.injOn).subset
  intro x hx
  refine ⟨?_, ?_⟩
  · simpa [coordinateGauge4, Metric.mem_closedBall, dist_zero_right] using hx.1
  · have hm := Submodule.mem_map_of_mem (f := (e.restrictScalars ℤ).toLinearMap) hx.2
    simpa only [lattice4Span, Submodule.map_span, Set.range_comp,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Basis.coe_map] using hm

theorem exists_shortest_lattice4Span_vector_outside (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (W : Submodule ℝ (Fin 4 → ℝ)) (hW : W ≠ ⊤) :
    ∃ x ∈ lattice4Span b, x ∉ W ∧ 0 < coordinateGauge4 e x ∧
      ∀ y ∈ lattice4Span b, y ∉ W → coordinateGauge4 e x ≤ coordinateGauge4 e y := by
  classical
  have hex : ∃ i, b i ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  obtain ⟨i, hi⟩ := hex
  let s : Set (Fin 4 → ℝ) :=
    {x | coordinateGauge4 e x ≤ coordinateGauge4 e (b i)} ∩
      (lattice4Span b : Set (Fin 4 → ℝ)) ∩ {x | x ∉ W}
  have hs : s.Finite := (lattice4Span_gauge_ball_finite b e _).inter_of_left _
  have hbi : b i ∈ lattice4Span b := Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image s (coordinateGauge4 e) hs
    ⟨b i, ⟨⟨show coordinateGauge4 e (b i) ≤ coordinateGauge4 e (b i) from le_rfl, hbi⟩, hi⟩⟩
  refine ⟨x, hx.1.2, hx.2, ?_, ?_⟩
  · apply norm_pos_iff.mpr
    intro h0
    have : x = 0 := e.injective (h0.trans e.map_zero.symm)
    exact hx.2 (this ▸ W.zero_mem)
  · intro y hy hyW
    by_cases hle : coordinateGauge4 e y ≤ coordinateGauge4 e (b i)
    · exact hmin y ⟨⟨hle, hy⟩, hyW⟩
    · exact hx.1.1.trans (le_of_not_ge hle)

noncomputable def successiveRadius4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (k : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val + 1) → (Fin 4 → ℝ),
    LinearIndependent ℝ u ∧ (∀ i, u i ∈ lattice4Span b) ∧
      ∀ i, coordinateGauge4 e (u i) ≤ r}

theorem independent_family_escapes_subspace4 {n : ℕ} (u : Fin n → (Fin 4 → ℝ))
    (hu : LinearIndependent ℝ u) (W : Submodule ℝ (Fin 4 → ℝ))
    (hW : Module.finrank ℝ W < n) : ∃ i, u i ∉ W := by
  by_contra! h
  have hs : Submodule.span ℝ (Set.range u) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  have hd := Submodule.finrank_mono hs
  rw [finrank_span_eq_card hu, Fintype.card_fin] at hd
  omega


theorem exists_successive_minima4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :
    ∃ v : Fin 4 → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ lattice4Span b) ∧
      (∀ i, 0 < successiveRadius4 b e i) ∧
      Monotone (successiveRadius4 b e) ∧
      ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i := by
  classical
  let W0 : Submodule ℝ (Fin 4 → ℝ) := ⊥
  have hdim0 : Module.finrank ℝ W0 = 0 := by simp [W0]
  have hW0 : W0 ≠ ⊤ := bot_ne_top
  obtain ⟨x0, hx0L, hx0W, hx0pos, hx0min⟩ :=
    exists_shortest_lattice4Span_vector_outside b e W0 hW0
  let u1 : Fin 1 → (Fin 4 → ℝ) := ![x0]
  have hu1 : LinearIndependent ℝ u1 := linearIndependent_unique u1 (by simpa [W0] using hx0W)
  let W1 := Submodule.span ℝ (Set.range u1)
  have hdim1 : Module.finrank ℝ W1 = 1 := by
    simpa [W1] using finrank_span_eq_card hu1
  have hW1 : W1 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W1 = 4 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x1, hx1L, hx1W, hx1pos, hx1min⟩ :=
    exists_shortest_lattice4Span_vector_outside b e W1 hW1
  let u2 : Fin 2 → (Fin 4 → ℝ) := Fin.snoc u1 x1
  have hu2 : LinearIndependent ℝ u2 := linearIndependent_fin_snoc.mpr ⟨hu1,hx1W⟩
  let W2 := Submodule.span ℝ (Set.range u2)
  have hdim2 : Module.finrank ℝ W2 = 2 := by
    simpa [W2] using finrank_span_eq_card hu2
  have hW2 : W2 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W2 = 4 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x2, hx2L, hx2W, hx2pos, hx2min⟩ :=
    exists_shortest_lattice4Span_vector_outside b e W2 hW2
  let u3 : Fin 3 → (Fin 4 → ℝ) := Fin.snoc u2 x2
  have hu3 : LinearIndependent ℝ u3 := linearIndependent_fin_snoc.mpr ⟨hu2,hx2W⟩
  let W3 := Submodule.span ℝ (Set.range u3)
  have hdim3 : Module.finrank ℝ W3 = 3 := by
    simpa [W3] using finrank_span_eq_card hu3
  have hW3 : W3 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W3 = 4 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x3, hx3L, hx3W, hx3pos, hx3min⟩ :=
    exists_shortest_lattice4Span_vector_outside b e W3 hW3
  let u4 : Fin 4 → (Fin 4 → ℝ) := Fin.snoc u3 x3
  have hu4 : LinearIndependent ℝ u4 := linearIndependent_fin_snoc.mpr ⟨hu3,hx3W⟩
  have hle0 : coordinateGauge4 e x0 ≤ coordinateGauge4 e x1 := by
    apply hx0min x1 hx1L
    intro h
    exact hx1W (show x1 ∈ W1 from (show W0 ≤ W1 from bot_le) h)
  have hle1 : coordinateGauge4 e x1 ≤ coordinateGauge4 e x2 := by
    apply hx1min x2 hx2L
    intro h
    apply hx2W
    apply (Submodule.span_mono (show Set.range u1 ⊆ Set.range u2 from ?_)) h
    rintro _ ⟨j,rfl⟩
    exact ⟨j.castSucc,by simp [u2]⟩
  have hle2 : coordinateGauge4 e x2 ≤ coordinateGauge4 e x3 := by
    apply hx2min x3 hx3L
    intro h
    apply hx3W
    apply (Submodule.span_mono (show Set.range u2 ⊆ Set.range u3 from ?_)) h
    rintro _ ⟨j,rfl⟩
    exact ⟨j.castSucc,by simp [u3]⟩
  have hrad0 : successiveRadius4 b e 0 = coordinateGauge4 e x0 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u1,hu1,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, Fin.snoc,hx0L,hx1L,hx2L,hx3L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x0 ≤ coordinateGauge4 e x0 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace4 u hu W0 (by omega)
      exact (hx0min (u j) (huL j) hj).trans (hur j)
  have hrad1 : successiveRadius4 b e 1 = coordinateGauge4 e x1 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u2,hu2,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, Fin.snoc,hx0L,hx1L,hx2L,hx3L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x0 ≤ coordinateGauge4 e x1 from hle0)
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x1 ≤ coordinateGauge4 e x1 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace4 u hu W1 (by omega)
      exact (hx1min (u j) (huL j) hj).trans (hur j)
  have hrad2 : successiveRadius4 b e 2 = coordinateGauge4 e x2 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u3,hu3,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, Fin.snoc,hx0L,hx1L,hx2L,hx3L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x0 ≤ coordinateGauge4 e x2 from (hle0).trans hle1)
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x1 ≤ coordinateGauge4 e x2 from hle1)
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x2 ≤ coordinateGauge4 e x2 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace4 u hu W2 (by omega)
      exact (hx2min (u j) (huL j) hj).trans (hur j)
  have hrad3 : successiveRadius4 b e 3 = coordinateGauge4 e x3 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u4,hu4,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, Fin.snoc,hx0L,hx1L,hx2L,hx3L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x0 ≤ coordinateGauge4 e x3 from ((hle0).trans hle1).trans hle2)
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x1 ≤ coordinateGauge4 e x3 from (hle1).trans hle2)
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x2 ≤ coordinateGauge4 e x3 from hle2)
        · simpa [u1, u2, u3, u4, Fin.snoc] using (show coordinateGauge4 e x3 ≤ coordinateGauge4 e x3 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace4 u hu W3 (by omega)
      exact (hx3min (u j) (huL j) hj).trans (hur j)
  refine ⟨u4,hu4,?_,?_,?_,?_⟩
  · intro j
    fin_cases j <;> norm_num [u1,u2,u3,u4,Fin.snoc,hx0L,hx1L,hx2L,hx3L]
  · intro j
    fin_cases j
    · simpa [hrad0] using hx0pos
    · simpa [hrad1] using hx1pos
    · simpa [hrad2] using hx2pos
    · simpa [hrad3] using hx3pos
  · apply Fin.monotone_iff_le_succ.mpr
    intro j
    fin_cases j
    · change successiveRadius4 b e 0 ≤ successiveRadius4 b e 1
      rw [hrad0,hrad1]
      exact hle0
    · change successiveRadius4 b e 1 ≤ successiveRadius4 b e 2
      rw [hrad1,hrad2]
      exact hle1
    · change successiveRadius4 b e 2 ≤ successiveRadius4 b e 3
      rw [hrad2,hrad3]
      exact hle2
  · intro j
    fin_cases j
    · change coordinateGauge4 e (u4 0) = successiveRadius4 b e 0
      rw [hrad0]
      rfl
    · change coordinateGauge4 e (u4 1) = successiveRadius4 b e 1
      rw [hrad1]
      rfl
    · change coordinateGauge4 e (u4 2) = successiveRadius4 b e 2
      rw [hrad2]
      rfl
    · change coordinateGauge4 e (u4 3) = successiveRadius4 b e 3
      rw [hrad3]
      rfl

noncomputable def weightedCoordinates4 (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x i := e x i / w i
  invFun y := e.symm (fun i => y i * w i)
  map_add' x y := by ext i; simp [add_div]
  map_smul' r x := by ext i; simp [smul_eq_mul,mul_div_assoc]
  left_inv x := by
    change e.symm (fun i => (e x i / w i) * w i) = x
    have h : (fun i => (e x i / w i) * w i) = e x :=
      funext (fun i => div_mul_cancel₀ _ (hw i).ne')
    rw [h,e.symm_apply_apply]
  right_inv y := by
    change (fun i => e (e.symm (fun j => y j * w j)) i / w i) = y
    rw [e.apply_symm_apply]
    exact funext (fun i => mul_div_cancel_right₀ _ (hw i).ne')

noncomputable def originalFormEquiv4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' L) (by
    have hu := hL
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem originalFormEquiv4_apply (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (x : Fin 4 → ℝ) : originalFormEquiv4 L hL x = L *ᵥ x := rfl

noncomputable def originalCoordinates4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  weightedCoordinates4 (originalFormEquiv4 L hL)
    (fun s => Q ^ c₀ s)
    (fun s => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)

def originalBody4 (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {x | ∀ s, |(L *ᵥ x) s| ≤ Q ^ c₀ s}

theorem originalCoordinates4_bounds (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 4 → ℝ) (r : ℝ) :
    ‖originalCoordinates4 L hL Q hQ c₀ x‖ ≤ r ↔
      ∀ s, |(L *ᵥ x) s| ≤ r * (Q ^ c₀ s) := by
  rw [pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro s
  have hw : 0 < Q ^ c₀ s := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  change ‖(L *ᵥ x) s / (Q ^ c₀ s)‖ ≤ r ↔ _
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hw,div_le_iff₀ hw]

theorem originalBody4_mem_iff (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    x ∈ originalBody4 L Q c₀ ↔ ‖originalCoordinates4 L hL Q hQ c₀ x‖ ≤ 1 := by
  rw [originalCoordinates4_bounds]
  simp only [one_mul,originalBody4,Set.mem_setOf_eq]


noncomputable def sourceRealBasis4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
  (integerRealImageBasis (sourceLattice4 A₂ A₃ e₂ e₃)
    (sourceLattice4_has_basis A₂ A₃ e₂ e₃).some).ofZLatticeBasis ℝ
      (integerRealImage (sourceLattice4 A₂ A₃ e₂ e₃))

theorem sourceRealBasis4_span (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) :
    lattice4Span (sourceRealBasis4 A₂ A₃ e₂ e₃) = integerRealImage (sourceLattice4 A₂ A₃ e₂ e₃) :=
  Basis.ofZLatticeBasis_span ℝ (integerRealImage (sourceLattice4 A₂ A₃ e₂ e₃))
    (integerRealImageBasis (sourceLattice4 A₂ A₃ e₂ e₃) (sourceLattice4_has_basis A₂ A₃ e₂ e₃).some)

noncomputable def originalSourceGroup4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : AddSubgroup (Fin 4 → ℤ) :=
  sourceLattice4 A₂ A₃ (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))

noncomputable def sourceMinima4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ u ∧
    (∀ i, u i ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) ∧
    ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (u i) ≤ r}

theorem sourceMinima4_eq_radius (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) :
    sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j =
      successiveRadius4 (sourceRealBasis4 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))
        (originalCoordinates4 L hL Q hQ c₀) j := by
  simp only [sourceMinima4,successiveRadius4,sourceRealBasis4_span,originalSourceGroup4]

theorem exists_sourceMinima4_attaining (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 4 → ℤ)) ∧
      (∀ j, 0 < sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ j, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀)
        (integerReal (u j : Fin 4 → ℤ)) = sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      ∀ j s, |(L *ᵥ integerReal (u j : Fin 4 → ℤ)) s| ≤
        sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j * (Q ^ c₀ s) := by
  classical
  let e₂ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))
  let e₃ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))
  let b := sourceRealBasis4 A₂ A₃ e₂ e₃
  let e := originalCoordinates4 L hL Q hQ c₀
  obtain ⟨v,hv,hvL,hpos,hmono,hatt⟩ := exists_successive_minima4 b e
  have hrad (j : Fin 4) : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = successiveRadius4 b e j :=
    sourceMinima4_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hvImage (j : Fin 4) : v j ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃) := by
    change v j ∈ integerRealImage (sourceLattice4 A₂ A₃ e₂ e₃)
    rw [← sourceRealBasis4_span A₂ A₃ e₂ e₃]
    exact hvL j
  have hlift (j : Fin 4) : ∃ x : originalSourceGroup4 A₂ A₃ Q c₂ c₃,
      integerReal (x : Fin 4 → ℤ) = v j := by
    obtain ⟨x,hx,he⟩ := hvImage j
    exact ⟨⟨x,hx⟩,he⟩
  choose u hu using hlift
  have hfun : (fun j => integerReal (u j : Fin 4 → ℤ)) = v := funext hu
  refine ⟨u,?_,?_,?_,?_,?_⟩
  · rw [hfun]
    exact hv
  · intro j
    rw [hrad]
    exact hpos j
  · intro i j hij
    rw [hrad,hrad]
    exact hmono hij
  · intro j
    rw [hu j,hrad]
    exact hatt j
  · intro j
    apply (originalCoordinates4_bounds L hL Q hQ c₀ _ _).mp
    change coordinateGauge4 e (integerReal (u j : Fin 4 → ℤ)) ≤ _
    rw [hu j,hrad,hatt j]


theorem sourceMinima4_admissible (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) :
    ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (v i) ≤
        sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima4_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let f : Fin (j.val+1) → Fin 4 := Fin.castLE (by omega)
  refine ⟨fun i => integerReal (u (f i) : Fin 4 → ℤ),
    hu.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    exact ⟨(u (f i) : Fin 4 → ℤ),(u (f i)).property,rfl⟩
  · intro i
    rw [hatt]
    exact hmono (show f i ≤ j from (by change i.val ≤ j.val; omega))

theorem sourceMinima4_radius_set_properties (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) :
    let S := {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (v i) ≤ r}
    S.Nonempty ∧ BddBelow S ∧ IsLeast S (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) := by
  dsimp only
  have hm := sourceMinima4_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hne : ({r : ℝ | ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (v i) ≤ r}).Nonempty := ⟨_,hm⟩
  have hb : BddBelow {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (v i) ≤ r} := by
    refine ⟨0,?_⟩
    rintro r ⟨v,_,_,hv⟩
    exact (norm_nonneg _).trans (hv 0)
  refine ⟨hne,hb,hm,?_⟩
  intro r hr
  exact csInf_le hb hr

theorem sourceMinima4_pos_mono (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∀ j, 0 < sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima4_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨hpos,hmono⟩

end CompoundFeasibility

open scoped Topology
open JSP000334
namespace CompoundFeasibility
noncomputable section
def parallelepipedBody4 (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) : Set (Fin 4 → ℝ) :=
  e ⁻¹' Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-1 : ℝ) 1)

theorem mem_parallelepipedBody4_iff (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (x : (Fin 4 → ℝ)) :
    x ∈ parallelepipedBody4 e ↔ coordinateGauge4 e x ≤ 1 := by
  simp [parallelepipedBody4, coordinateGauge4, pi_norm_le_iff_of_nonempty,
    Real.norm_eq_abs, abs_le, Pi.le_def, forall_and]

open scoped Pointwise in
theorem mem_dilate_parallelepipedBody4_iff (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (x : (Fin 4 → ℝ)) (r : ℝ) (hr : 0 < r) :
    x ∈ r • parallelepipedBody4 e ↔ coordinateGauge4 e x ≤ r := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_parallelepipedBody4_iff]
  simp only [coordinateGauge4, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hr]
  simpa using (inv_mul_le_iff₀ hr : r⁻¹ * ‖e x‖ ≤ 1 ↔ ‖e x‖ ≤ r * 1)

theorem parallelepipedBody4_volume (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :
    MeasureTheory.volume.real (parallelepipedBody4 e) =
      16 / |LinearMap.det e.toLinearMap| := by
  rw [MeasureTheory.measureReal_def, parallelepipedBody4,
    MeasureTheory.Measure.addHaar_preimage_linearEquiv,
    MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp only [Real.volume_Icc, LinearEquiv.det_coe_symm, abs_inv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal, abs_nonneg, div_eq_mul_inv]
  norm_num
  ring

def minimaFlag4 (v : Fin 4 → (Fin 4 → ℝ)) (k : Fin 4) : Submodule ℝ (Fin 4 → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin k.val => v (Fin.castLE (by omega) i)))

theorem minimaFlag4_finrank (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (k : Fin 4) :
    Module.finrank ℝ (minimaFlag4 v k) = k.val := by
  simpa [minimaFlag4] using
    finrank_span_eq_card (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))

theorem successiveRadius4_le_family (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (k : Fin 4)
    (u : Fin (k.val + 1) → (Fin 4 → ℝ)) (hu : LinearIndependent ℝ u)
    (huL : ∀ i, u i ∈ lattice4Span b) (r : ℝ)
    (hr : ∀ i, coordinateGauge4 e (u i) ≤ r) :
    successiveRadius4 b e k ≤ r := by
  unfold successiveRadius4
  apply csInf_le (s := {s : ℝ | ∃ w : Fin (k.val + 1) → (Fin 4 → ℝ),
    LinearIndependent ℝ w ∧ (∀ i, w i ∈ lattice4Span b) ∧
      ∀ i, coordinateGauge4 e (w i) ≤ s}) _ ⟨u, hu, huL, hr⟩
  refine ⟨0, ?_⟩
  rintro s ⟨w, _, _, hw⟩
  exact (norm_nonneg (e (w 0))).trans (hw 0)

theorem lattice4Span_short_mem_minimaFlag (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b)
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (k : Fin 4) (hgap : ∀ i : Fin 4, i < k →
      successiveRadius4 b e i < successiveRadius4 b e k)
    (x : (Fin 4 → ℝ)) (hx : x ∈ lattice4Span b)
    (hxr : coordinateGauge4 e x < successiveRadius4 b e k) :
    x ∈ minimaFlag4 v k := by
  classical
  by_contra hxW
  let u : Fin k.val → (Fin 4 → ℝ) := fun i => v (Fin.castLE (by omega) i)
  have hu : LinearIndependent ℝ u := hv.comp _ (Fin.castLE_injective _)
  let w : Fin (k.val + 1) → (Fin 4 → ℝ) := Fin.snoc u x
  have hux : LinearIndependent ℝ w :=
    linearIndependent_fin_snoc.mpr ⟨hu, hxW⟩
  have hL : ∀ i : Fin (k.val + 1), w i ∈ lattice4Span b := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hx
    · simpa [w, u] using hvL (Fin.castLE (by omega) j)
  have hlt : ∀ i : Fin (k.val + 1), coordinateGauge4 e (w i) < successiveRadius4 b e k := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hxr
    · simpa [w, u, hvr] using hgap (Fin.castLE (by omega) j) (by exact j.isLt)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => coordinateGauge4 e (w i)) (Finset.univ_nonempty)
  have hle := successiveRadius4_le_family b e k w hux hL _
    (fun j => hi j (Finset.mem_univ j))
  exact (not_lt_of_ge hle) (hlt i)

theorem exists_minimaFlag4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :
    ∃ v : Fin 4 → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ lattice4Span b) ∧
      (∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i) ∧
      (∀ k, Module.finrank ℝ (minimaFlag4 v k) = k.val) ∧
      ∀ k, (∀ i : Fin 4, i < k → successiveRadius4 b e i < successiveRadius4 b e k) →
        ∀ x ∈ lattice4Span b, coordinateGauge4 e x < successiveRadius4 b e k →
          x ∈ minimaFlag4 v k := by
  obtain ⟨v, hv, hvL, _, _, hvr⟩ := exists_successive_minima4 b e
  exact ⟨v, hv, hvL, hvr, minimaFlag4_finrank v hv,
    fun k hgap x hx hxr => lattice4Span_short_mem_minimaFlag b e v hv hvL hvr k hgap x hx hxr⟩

theorem minimaFlag4_mono (v : Fin 4 → (Fin 4 → ℝ)) (k l : Fin 4) (hkl : k ≤ l) :
    minimaFlag4 v k ≤ minimaFlag4 v l := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨Fin.castLE hkl i, ?_⟩
  rfl

theorem lattice4Span_halfBody_cosets_disjoint (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (W : Submodule ℝ (Fin 4 → ℝ)) (mu r : ℝ)
    (hshort : ∀ z ∈ lattice4Span b, coordinateGauge4 e z < mu → z ∈ W)
    (hr : 0 < r) (hrmu : r < mu) (x y : (Fin 4 → ℝ))
    (hx : x ∈ lattice4Span b) (hy : y ∈ lattice4Span b) (hxy : x - y ∉ W)
    (Q : Set (Fin 4 → ℝ)) (hQ : Q ⊆ (lattice4Span b : Set (Fin 4 → ℝ)) ∩ (W : Set (Fin 4 → ℝ))) :
    Disjoint (x +ᵥ (Q + (r / 2) • parallelepipedBody4 e))
      (y +ᵥ (Q + (r / 2) • parallelepipedBody4 e)) := by
  apply Set.disjoint_left.mpr
  intro z hxz hyz
  obtain ⟨u, hu, hxu⟩ := Set.mem_vadd_set.mp hxz
  obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_add.mp hu
  obtain ⟨w, hw, hyw⟩ := Set.mem_vadd_set.mp hyz
  obtain ⟨d, hd, f, hf, hdf⟩ := Set.mem_add.mp hw
  have heq : x + a + c = y + d + f := by
    simpa [vadd_eq_add, ← hac, ← hdf, add_assoc] using hxu.trans hyw.symm
  have hz : x + a - (y + d) = f - c := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa [add_comm, add_left_comm, add_assoc] using heq
  have hdiffL : f - c ∈ lattice4Span b := by
    rw [← hz]
    exact (lattice4Span b).sub_mem
      ((lattice4Span b).add_mem hx (hQ ha).1) ((lattice4Span b).add_mem hy (hQ hd).1)
  have hcr := (mem_dilate_parallelepipedBody4_iff e c (r / 2) (by linarith)).mp hc
  have hfr := (mem_dilate_parallelepipedBody4_iff e f (r / 2) (by linarith)).mp hf
  have hbound : coordinateGauge4 e (f - c) ≤ r := by
    calc
      coordinateGauge4 e (f - c) = ‖e f - e c‖ := by simp [coordinateGauge4]
      _ ≤ ‖e f‖ + ‖e c‖ := norm_sub_le _ _
      _ ≤ r := by change coordinateGauge4 e f + coordinateGauge4 e c ≤ r; linarith
  have hW := hshort (f - c) hdiffL (hbound.trans_lt hrmu)
  apply hxy
  have hadW : a - d ∈ W := W.sub_mem (hQ ha).2 (hQ hd).2
  have hsub := W.sub_mem hW hadW
  convert hsub using 1
  rw [← hz]
  abel

theorem minimaFlag4_halfBody_cosets_disjoint (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b)
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (k : Fin 4) (hgap : ∀ i : Fin 4, i < k →
      successiveRadius4 b e i < successiveRadius4 b e k)
    (r : ℝ) (hr : 0 < r) (hrmu : r < successiveRadius4 b e k)
    (x y : (Fin 4 → ℝ)) (hx : x ∈ lattice4Span b) (hy : y ∈ lattice4Span b)
    (hxy : x - y ∉ minimaFlag4 v k)
    (Q : Set (Fin 4 → ℝ))
    (hQ : Q ⊆ (lattice4Span b : Set (Fin 4 → ℝ)) ∩ (minimaFlag4 v k : Set (Fin 4 → ℝ))) :
    Disjoint (x +ᵥ (Q + (r / 2) • parallelepipedBody4 e))
      (y +ᵥ (Q + (r / 2) • parallelepipedBody4 e)) := by
  exact lattice4Span_halfBody_cosets_disjoint b e (minimaFlag4 v k) _ r
    (fun z hz hzr => lattice4Span_short_mem_minimaFlag b e v hv hvL hvr k hgap z hz hzr)
    hr hrmu x y hx hy hxy Q hQ


def latticeFlag4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (k : Fin 4) : Submodule ℤ (lattice4Span b) :=
  ((minimaFlag4 v k).restrictScalars ℤ).comap (lattice4Span b).subtype

def flagLattice4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (k : Fin 4) : Submodule ℤ (minimaFlag4 v k) :=
  (lattice4Span b).comap ((minimaFlag4 v k).subtype.restrictScalars ℤ)

theorem latticeFlag4_saturated (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (v : Fin 4 → (Fin 4 → ℝ)) (k : Fin 4) (n : ℤ) (hn : n ≠ 0)
    (x : lattice4Span b) (hx : n • x ∈ latticeFlag4 b v k) :
    x ∈ latticeFlag4 b v k := by
  change n • (x : (Fin 4 → ℝ)) ∈ minimaFlag4 v k at hx
  rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  change (x : (Fin 4 → ℝ)) ∈ minimaFlag4 v k
  exact (Submodule.smul_mem_iff (minimaFlag4 v k) (by exact_mod_cast hn : (n : ℝ) ≠ 0)).mp hx

noncomputable def latticeFlag4_equiv_flagLattice4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (v : Fin 4 → (Fin 4 → ℝ)) (k : Fin 4) :
    latticeFlag4 b v k ≃ₗ[ℤ] flagLattice4 b v k where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance flagLattice4_discrete (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (v : Fin 4 → (Fin 4 → ℝ)) (k : Fin 4) : DiscreteTopology (flagLattice4 b v k) := by
  let f : flagLattice4 b v k → lattice4Span b := fun x => ⟨x.val.val, x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : lattice4Span b => (z : (Fin 4 → ℝ))) h

instance flagLattice4_isZLattice (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice4Span b) (k : Fin 4) :
    IsZLattice ℝ (flagLattice4 b v k) where
  span_top := by
    let u : Fin k.val → (Fin 4 → ℝ) := fun i => v (Fin.castLE (by omega) i)
    let B : Basis (Fin k.val) ℝ (minimaFlag4 v k) :=
      Basis.span (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    change (B i : (Fin 4 → ℝ)) ∈ lattice4Span b
    have hB : (B i : (Fin 4 → ℝ)) = u i :=
      Basis.span_apply (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _)) i
    rw [hB]
    exact hvL (Fin.castLE (by omega) i)

theorem latticeFlag4_finrank (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice4Span b) (k : Fin 4) :
    Module.finrank ℤ (latticeFlag4 b v k) = k.val := by
  letI := flagLattice4_isZLattice b v hv hvL k
  rw [(latticeFlag4_equiv_flagLattice4 b v k).finrank_eq,
    ZLattice.rank ℝ (flagLattice4 b v k), minimaFlag4_finrank v hv k]


theorem latticeFlag4_basis_real_span {ι : Type*}
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hvL : ∀ i, v i ∈ lattice4Span b) (k : Fin 4)
    (a : @Basis ι ℤ (latticeFlag4 b v k) _ _ (latticeFlag4 b v k).module) :
    Submodule.span ℝ (Set.range (fun i =>
      (((a i : latticeFlag4 b v k) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k := by
  let N := latticeFlag4 b v k
  letI nModule : Module ℤ N := N.module
  let W := Submodule.span ℝ (Set.range (fun i =>
    (((a i : latticeFlag4 b v k) : lattice4Span b) : (Fin 4 → ℝ))))
  have hw : ∀ x : N, ((x : lattice4Span b) : (Fin 4 → ℝ)) ∈ W := by
    have h : Submodule.span ℤ (Set.range a) ≤
        ((W.restrictScalars ℤ).comap (lattice4Span b).subtype).comap N.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [a.span_eq] at h
    intro x
    exact h (Submodule.mem_top : x ∈ (⊤ : Submodule ℤ N))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (a i).property
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let x : N := ⟨⟨v (Fin.castLE (by omega) i), hvL _⟩,
      Submodule.subset_span (Set.mem_range_self i)⟩
    exact hw x


theorem exists_adapted_integer_basis4
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b) :
    ∃ c : Basis (Fin 4) ℤ (lattice4Span b), ∀ k : Fin 4,
      Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k := by
  classical
  let L := lattice4Span b
  let N1 : Submodule ℤ L := latticeFlag4 b v 1
  let N2 : Submodule ℤ L := latticeFlag4 b v 2
  let N3 : Submodule ℤ L := latticeFlag4 b v 3
  letI lModule : Module ℤ L := (lattice4Span b).module
  letI n1Module : Module ℤ N1 := N1.module
  letI n2Module : Module ℤ N2 := N2.module
  letI n3Module : Module ℤ N3 := N3.module
  have h12 : N1 ≤ N2 := fun _ hx => minimaFlag4_mono v 1 2 (by decide) hx
  have h23 : N2 ≤ N3 := fun _ hx => minimaFlag4_mono v 2 3 (by decide) hx
  let S12 : Submodule ℤ N2 := N1.comap N2.subtype
  let S23 : Submodule ℤ N3 := N2.comap N3.subtype
  letI s12Module : Module ℤ S12 := S12.module
  letI s23Module : Module ℤ S23 := S23.module
  let e12 : S12 ≃ₗ[ℤ] N1 := Submodule.comapSubtypeEquivOfLe h12
  let e23 : S23 ≃ₗ[ℤ] N2 := Submodule.comapSubtypeEquivOfLe h23
  have hr1 : Module.finrank ℤ N1 = 1 := latticeFlag4_finrank b v hv hvL 1
  have hr2 : Module.finrank ℤ N2 = 2 := latticeFlag4_finrank b v hv hvL 2
  have hr3 : Module.finrank ℤ N3 = 3 := latticeFlag4_finrank b v hv hvL 3
  have hrL : Module.finrank ℤ L = 4 := by
    simpa using Module.finrank_eq_card_basis (b.restrictScalars ℤ)
  let t : @Basis (Fin 1) ℤ N1 _ _ n1Module := Module.finBasisOfFinrankEq ℤ N1 hr1
  let aS12 : @Basis (Fin 1) ℤ S12 _ _ s12Module := t.map e12.symm
  obtain ⟨a2,ha2⟩ := saturated_integer_basis_extend S12 aS12 hr2
    (fun z hz x hx => latticeFlag4_saturated b v 1 z hz (x : L) hx)
  let aS23 : @Basis (Fin 2) ℤ S23 _ _ s23Module := a2.map e23.symm
  obtain ⟨a3,ha3⟩ := saturated_integer_basis_extend S23 aS23 hr3
    (fun z hz x hx => latticeFlag4_saturated b v 2 z hz (x : L) hx)
  obtain ⟨c,hc⟩ := saturated_integer_basis_extend N3 a3 hrL (latticeFlag4_saturated b v 3)
  have h2 (i : Fin 2) : ((a3 i.castSucc : N3) : L) = (a2 i : L) := by
    simpa only [aS23,Basis.map_apply,e23,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N3 => (x : L)) (ha3 i)
  have h1 : ((a2 0 : N2) : L) = (t 0 : L) := by
    simpa only [aS12,Basis.map_apply,e12,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N2 => (x : L)) (ha2 0)
  refine ⟨c,?_⟩
  intro k
  fin_cases k
  · simp [minimaFlag4]
  · have heq : (fun i : Fin 1 => ((c (Fin.castLE (by omega) i) : L) : (Fin 4 → ℝ))) =
        (fun i : Fin 1 => (((t i : N1) : L) : (Fin 4 → ℝ))) := by
      funext i
      fin_cases i
      exact congrArg (fun x : L => (x : (Fin 4 → ℝ))) (((hc 0).trans (h2 0)).trans h1)
    rw [heq]
    exact latticeFlag4_basis_real_span b v hvL 1 t
  · have heq : (fun i : Fin 2 => ((c (Fin.castLE (by omega) i) : L) : (Fin 4 → ℝ))) =
        (fun i : Fin 2 => (((a2 i : N2) : L) : (Fin 4 → ℝ))) := by
      funext i
      exact congrArg (fun x : L => (x : (Fin 4 → ℝ))) ((hc i.castSucc).trans (h2 i))
    rw [heq]
    exact latticeFlag4_basis_real_span b v hvL 2 a2
  · have heq : (fun i : Fin 3 => ((c (Fin.castLE (by omega) i) : L) : (Fin 4 → ℝ))) =
        (fun i : Fin 3 => (((a3 i : N3) : L) : (Fin 4 → ℝ))) := by
      funext i
      exact congrArg (fun x : L => (x : (Fin 4 → ℝ))) (hc i)
    rw [heq]
    exact latticeFlag4_basis_real_span b v hvL 3 a3


theorem convex_fiber4_dilate_subset_translate (m : Fin 4)
    (C : Set (Fin m.val → ℝ)) (hC : Convex ℝ C)
    (c : Fin m.val → ℝ) (hc : c ∈ C) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    s • C ⊆ (s - t) • c +ᵥ (t • C) := by
  rintro _ ⟨x, hx, rfl⟩
  let z := (s / t) • x + (1 - s / t) • c
  have hz : z ∈ C := by
    apply hC hx hc (div_nonneg hs ht.le) _ (by ring)
    exact sub_nonneg.mpr ((div_le_one ht).mpr hst)
  apply Set.mem_vadd_set.mpr
  refine ⟨t • z, Set.smul_mem_smul_set hz, ?_⟩
  change (s - t) • c + t • ((s / t) • x + (1 - s / t) • c) = s • x
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

open scoped Pointwise in
theorem convex_fiber4_translate_union_volume_mono (m : Fin 4)
    (C Q : Set (Fin m.val → ℝ)) (hC : Convex ℝ C)
    (c : Fin m.val → ℝ) (hc : c ∈ C) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    MeasureTheory.volume (Q + s • C) ≤ MeasureTheory.volume (Q + t • C) := by
  have hsub : Q + s • C ⊆ (s - t) • c +ᵥ (Q + t • C) := by
    rintro _ ⟨q, hq, x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ :=
      Set.mem_vadd_set.mp (convex_fiber4_dilate_subset_translate m C hC c hc s t hs hst ht hx)
    apply Set.mem_vadd_set.mpr
    refine ⟨q + y, Set.mem_add.mpr ⟨q, hq, y, hy, rfl⟩, ?_⟩
    simp [vadd_eq_add, add_left_comm]
  calc
    MeasureTheory.volume (Q + s • C) ≤
        MeasureTheory.volume ((s - t) • c +ᵥ (Q + t • C)) := MeasureTheory.measure_mono hsub
    _ = MeasureTheory.volume (Q + t • C) := MeasureTheory.measure_vadd _ _ _


def flagFiberUnion4 (m : Fin 4) (Q : Finset (Fin m.val → ℝ)) (r : ℝ)
    (C : Set ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ))) :
    Set ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ)) :=
  ⋃ q ∈ Q, (fun z => (q + r • z.1, z.2)) '' C

theorem flagFiberUnion4_fiber (m : Fin 4) (Q : Finset (Fin m.val → ℝ)) (r : ℝ)
    (C : Set ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ)))
    (y : Fin (4 - m.val) → ℝ) :
    (fun x => (x, y)) ⁻¹' flagFiberUnion4 m Q r C =
      (Q : Set (Fin m.val → ℝ)) + r • ((fun x => (x, y)) ⁻¹' C) := by
  ext x
  simp only [flagFiberUnion4, Set.mem_preimage, Set.mem_iUnion, Set.mem_image,
    Set.mem_add, Set.mem_smul_set]
  constructor
  · rintro ⟨q, hq, ⟨u, w⟩, hC, heq⟩
    rcases Prod.mk.inj heq with ⟨hx, hy⟩
    refine ⟨q, hq, r • u, ⟨u, ?_, rfl⟩, hx⟩
    simpa only [← hy] using hC
  · rintro ⟨q, hq, _, ⟨u, hu, rfl⟩, hx⟩
    exact ⟨q, hq, (u, y), hu, Prod.ext hx rfl⟩

theorem convex_flagFiberUnion4_volume_mono (m : Fin 4)
    (Q : Finset (Fin m.val → ℝ))
    (C : Set ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ)))
    (hCc : IsCompact C) (hC : Convex ℝ C)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    volume (flagFiberUnion4 m Q s C) ≤ volume (flagFiberUnion4 m Q t C) := by
  have hm (r : ℝ) : MeasurableSet (flagFiberUnion4 m Q r C) := by
    apply IsCompact.measurableSet
    apply Q.isCompact_biUnion
    intro q _
    exact hCc.image ((continuous_const.add (continuous_const.smul continuous_fst)).prodMk
      continuous_snd)
  change (volume.prod volume) (flagFiberUnion4 m Q s C) ≤
    (volume.prod volume) (flagFiberUnion4 m Q t C)
  rw [Measure.prod_apply_symm (hm s), Measure.prod_apply_symm (hm t)]
  apply lintegral_mono
  intro y
  dsimp only
  rw [flagFiberUnion4_fiber, flagFiberUnion4_fiber]
  let Cy := (fun x : Fin m.val → ℝ => (x, y)) ⁻¹' C
  have hCy : Convex ℝ Cy := by
    intro x hx z hz a b ha hb hab
    have h := hC hx hz ha hb hab
    change (a • x + b • z, a • y + b • y) ∈ C at h
    change (a • x + b • z, y) ∈ C
    simpa only [← add_smul, hab, one_smul] using h
  by_cases hn : Cy.Nonempty
  · obtain ⟨c, hc⟩ := hn
    exact convex_fiber4_translate_union_volume_mono m Cy Q hCy c hc s t hs hst ht
  · have hempty : Cy = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change volume ((Q : Set (Fin m.val → ℝ)) + s • Cy) ≤
      volume ((Q : Set (Fin m.val → ℝ)) + t • Cy)
    simp [hempty]


theorem flagFiberUnion4_transverse_volume (m : Fin 4)
    (Q : Finset (Fin m.val → ℝ)) (r : ℝ)
    (C : Set ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ))) :
    volume (((fun q : Fin m.val → ℝ => (q, (0 : Fin (4 - m.val) → ℝ))) ''
      (Q : Set (Fin m.val → ℝ))) + r • C) =
      ENNReal.ofReal |r ^ (4 - m.val)| * volume (flagFiberUnion4 m Q r C) := by
  letI productHaar : (volume : Measure ((Fin m.val → ℝ) ×
      (Fin (4 - m.val) → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let T : ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ)) →ₗ[ℝ]
      ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ)) :=
    LinearMap.prodMap LinearMap.id (r • LinearMap.id)
  have himage : T '' flagFiberUnion4 m Q r C =
      ((fun q : Fin m.val → ℝ => (q, (0 : Fin (4 - m.val) → ℝ))) ''
        (Q : Set (Fin m.val → ℝ))) + r • C := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases Set.mem_iUnion.mp hw with ⟨q, hw⟩
      rcases Set.mem_iUnion.mp hw with ⟨hq, hw⟩
      rcases hw with ⟨u, hu, rfl⟩
      apply Set.mem_add.mpr
      refine ⟨(q, 0), ⟨q, hq, rfl⟩, r • u, Set.smul_mem_smul_set hu, ?_⟩
      ext <;> simp [T]
    · intro hz
      obtain ⟨q, hq, w, hw, hsum⟩ := Set.mem_add.mp hz
      rcases hq with ⟨q, hq, rfl⟩
      rcases hw with ⟨u, hu, rfl⟩
      refine ⟨(q + r • u.1, u.2), ?_, ?_⟩
      · exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, ⟨u, hu, rfl⟩⟩⟩
      · calc
          T (q + r • u.1, u.2) = (q, 0) + r • u := by ext <;> simp [T]
          _ = z := hsum
  rw [← himage, Measure.addHaar_image_linearMap volume T]
  congr 2
  simp [T, LinearMap.det_prodMap, LinearMap.det_smul, Module.finrank_pi]


theorem convex_flag4_translate_union_volume_growth (m : Fin 4)
    (Q : Finset (Fin m.val → ℝ))
    (C : Set ((Fin m.val → ℝ) × (Fin (4 - m.val) → ℝ)))
    (hCc : IsCompact C) (hC : Convex ℝ C)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    ENNReal.ofReal |t ^ (4 - m.val)| *
      volume (((fun q : Fin m.val → ℝ => (q, (0 : Fin (4 - m.val) → ℝ))) ''
        (Q : Set (Fin m.val → ℝ))) + s • C) ≤
    ENNReal.ofReal |s ^ (4 - m.val)| *
      volume (((fun q : Fin m.val → ℝ => (q, (0 : Fin (4 - m.val) → ℝ))) ''
        (Q : Set (Fin m.val → ℝ))) + t • C) := by
  rw [flagFiberUnion4_transverse_volume, flagFiberUnion4_transverse_volume]
  simpa only [mul_left_comm, mul_assoc] using
    mul_le_mul_left' (convex_flagFiberUnion4_volume_mono m Q C hCc hC s t hs hst ht)
      (ENNReal.ofReal |t ^ (4 - m.val)| * ENNReal.ofReal |s ^ (4 - m.val)|)




theorem exists_adapted_lattice_coordinates4
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b) :
    ∃ B : Basis (Fin 4) ℝ (Fin 4 → ℝ),
      Submodule.span ℤ (Set.range B) = lattice4Span b ∧
      (∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        B (Fin.castLE (by omega) i))) = minimaFlag4 v k) ∧
      ∀ S : Set (Fin 4 → ℝ),
        volume (B.equivFun '' S) = volume S / ENNReal.ofReal (ZLattice.covolume (lattice4Span b)) := by
  obtain ⟨c, hc⟩ := exists_adapted_integer_basis4 b v hv hvL
  refine ⟨c.ofZLatticeBasis ℝ (lattice4Span b), c.ofZLatticeBasis_span ℝ (lattice4Span b), ?_, ?_⟩
  · intro k
    simpa only [Basis.ofZLatticeBasis_apply] using hc k
  · intro S
    exact ZLattice.volume_image_eq_volume_div_covolume (lattice4Span b) c


theorem parallelepipedBody4_compact_convex (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :
    IsCompact (parallelepipedBody4 e) ∧ Convex ℝ (parallelepipedBody4 e) := by
  have hbody : parallelepipedBody4 e = e ⁻¹' Metric.closedBall (0 : (Fin 4 → ℝ)) 1 := by
    ext x
    rw [mem_parallelepipedBody4_iff]
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, coordinateGauge4]
  rw [hbody]
  constructor
  · exact e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  · exact (convex_closedBall (0 : (Fin 4 → ℝ)) 1).linear_preimage e.toLinearMap


def integerBox4 (N : ℕ) (s : Finset (Fin 4)) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun i => if i ∈ s then Finset.Icc (-(N : ℤ)) N else {0})

theorem mem_integerBox4 (N : ℕ) (s : Finset (Fin 4)) (z : Fin 4 → ℤ) :
    z ∈ integerBox4 N s ↔ ∀ i, if i ∈ s then -(N : ℤ) ≤ z i ∧ z i ≤ N else z i = 0 := by
  simp only [integerBox4, Fintype.mem_piFinset]
  apply forall_congr'
  intro i
  split <;> simp_all

def integerLatticePoint4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (c : Basis (Fin 4) ℤ (lattice4Span b)) (z : Fin 4 → ℤ) : (Fin 4 → ℝ) :=
  (c.equivFun.symm z : lattice4Span b)

theorem integerLatticePoint4_injective (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (c : Basis (Fin 4) ℤ (lattice4Span b)) : Function.Injective (integerLatticePoint4 b c) := by
  intro z w h
  exact c.equivFun.symm.injective (Subtype.coe_injective h)

theorem integerLatticePoint4_add (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (c : Basis (Fin 4) ℤ (lattice4Span b)) (z w : Fin 4 → ℤ) :
    integerLatticePoint4 b c (z + w) = integerLatticePoint4 b c z + integerLatticePoint4 b c w := by
  exact congrArg Subtype.val (c.equivFun.symm.map_add z w)

theorem integerLatticePoint4_mem_flag_iff (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (c : Basis (Fin 4) ℤ (lattice4Span b)) (v : Fin 4 → (Fin 4 → ℝ))
    (hc : ∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k)
    (k : Fin 4) (z : Fin 4 → ℤ) :
    integerLatticePoint4 b c z ∈ minimaFlag4 v k ↔ ∀ i, k ≤ i → z i = 0 := by
  classical
  let B := c.ofZLatticeBasis ℝ (lattice4Span b)
  have hset : Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ))) =
      B '' {i : Fin 4 | i < k} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.castLE (by omega) i, i.isLt, by simp [B]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, by simp [B]⟩
  have hrepr (i : Fin 4) : B.repr (integerLatticePoint4 b c z) i = (z i : ℝ) := by
    rw [integerLatticePoint4, Basis.ofZLatticeBasis_repr_apply]
    change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = _
    simp only [LinearEquiv.apply_symm_apply]
  rw [← hc k, hset, B.mem_span_image]
  constructor
  · intro h i hi
    by_contra hz
    have hmem : i ∈ (B.repr (integerLatticePoint4 b c z)).support := by
      simp [hrepr, hz]
    have := h hmem
    exact (not_lt_of_ge hi) this
  · intro h i hi
    by_contra hik
    have hz := h i (le_of_not_gt hik)
    have hn : B.repr (integerLatticePoint4 b c z) i ≠ 0 := Finsupp.mem_support_iff.mp hi
    exact hn (by simp [hrepr, hz])

theorem integerBox4_split (N : ℕ) (s : Finset (Fin 4)) :
    (integerBox4 N Finset.univ : Set (Fin 4 → ℤ)) =
      (integerBox4 N s : Set (Fin 4 → ℤ)) + (integerBox4 N sᶜ : Set (Fin 4 → ℤ)) := by
  classical
  ext z
  constructor
  · intro hz
    have hz' := (mem_integerBox4 N Finset.univ z).mp hz
    let x : Fin 4 → ℤ := fun i => if i ∈ s then z i else 0
    let y : Fin 4 → ℤ := fun i => if i ∈ s then 0 else z i
    refine Set.mem_add.mpr ⟨x, ?_, y, ?_, ?_⟩
    · apply (mem_integerBox4 N s x).mpr
      intro i
      have := hz' i
      by_cases hi : i ∈ s <;> simp_all [x]
    · apply (mem_integerBox4 N sᶜ y).mpr
      intro i
      have := hz' i
      by_cases hi : i ∈ s <;> simp_all [y]
    · funext i
      by_cases hi : i ∈ s <;> simp [x, y, hi]
  · rintro ⟨x, hx, y, hy, rfl⟩
    apply (mem_integerBox4 N Finset.univ (x + y)).mpr
    intro i
    have hx' := (mem_integerBox4 N s x).mp hx i
    have hy' := (mem_integerBox4 N sᶜ y).mp hy i
    by_cases hi : i ∈ s <;> simp_all

theorem integerBox4_split_unique (N : ℕ) (s : Finset (Fin 4))
    (x x' y y' : Fin 4 → ℤ)
    (hx : x ∈ integerBox4 N s) (hx' : x' ∈ integerBox4 N s)
    (hy : y ∈ integerBox4 N sᶜ) (hy' : y' ∈ integerBox4 N sᶜ)
    (h : x + y = x' + y') : x = x' ∧ y = y' := by
  classical
  have hcoord (i : Fin 4) : x i = x' i ∧ y i = y' i := by
    have ha := congrFun h i
    have h1 := (mem_integerBox4 N s x).mp hx i
    have h2 := (mem_integerBox4 N s x').mp hx' i
    have h4 := (mem_integerBox4 N sᶜ y).mp hy i
    have h4 := (mem_integerBox4 N sᶜ y').mp hy' i
    by_cases hi : i ∈ s <;> simp_all
  exact ⟨funext (fun i => (hcoord i).1), funext (fun i => (hcoord i).2)⟩

theorem integerLatticePoint4_box_split (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (c : Basis (Fin 4) ℤ (lattice4Span b)) (N : ℕ) (s : Finset (Fin 4)) :
    integerLatticePoint4 b c '' (integerBox4 N Finset.univ : Set (Fin 4 → ℤ)) =
      integerLatticePoint4 b c '' (integerBox4 N s : Set (Fin 4 → ℤ)) +
      integerLatticePoint4 b c '' (integerBox4 N sᶜ : Set (Fin 4 → ℤ)) := by
  rw [integerBox4_split N s]
  ext p
  constructor
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, (integerLatticePoint4_add b c x y).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, integerLatticePoint4_add b c x y⟩

theorem integerBox4_transverse_not_mem_flag
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (v : Fin 4 → (Fin 4 → ℝ))
    (hc : ∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k)
    (N : ℕ) (k : Fin 4) (z w : Fin 4 → ℤ)
    (hz : z ∈ integerBox4 N (Finset.univ.filter (fun i => i < k))ᶜ)
    (hw : w ∈ integerBox4 N (Finset.univ.filter (fun i => i < k))ᶜ)
    (hzw : z ≠ w) :
    integerLatticePoint4 b c z - integerLatticePoint4 b c w ∉ minimaFlag4 v k := by
  classical
  intro h
  have hsub : integerLatticePoint4 b c (z - w) =
      integerLatticePoint4 b c z - integerLatticePoint4 b c w :=
    congrArg Subtype.val (c.equivFun.symm.map_sub z w)
  rw [← hsub, integerLatticePoint4_mem_flag_iff b c v hc] at h
  apply hzw
  funext i
  by_cases hi : i < k
  · have hz' := (mem_integerBox4 N _ z).mp hz i
    have hw' := (mem_integerBox4 N _ w).mp hw i
    simp_all [not_le_of_gt hi]
  · exact sub_eq_zero.mp (h i (le_of_not_gt hi))

theorem integerBox4_strict_gap_disjoint
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice4Span b)
    (hc : ∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k)
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (N : ℕ) (k : Fin 4)
    (hgap : ∀ i : Fin 4, i < k → successiveRadius4 b e i < successiveRadius4 b e k)
    (r : ℝ) (hr : 0 < r) (hrmu : r < successiveRadius4 b e k) :
    Set.PairwiseDisjoint
      (integerBox4 N (Finset.univ.filter (fun i => i < k))ᶜ : Set (Fin 4 → ℤ))
      (fun z => integerLatticePoint4 b c z +ᵥ
        ((integerLatticePoint4 b c ''
          (integerBox4 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 4 → ℤ))) +
          (r / 2) • parallelepipedBody4 e)) := by
  classical
  let s := Finset.univ.filter (fun i : Fin 4 => i < k)
  let Q := integerLatticePoint4 b c '' (integerBox4 N s : Set (Fin 4 → ℤ))
  let T := integerBox4 N sᶜ
  let A := Q + (r / 2) • parallelepipedBody4 e
  have hQ : Q ⊆ (lattice4Span b : Set (Fin 4 → ℝ)) ∩ (minimaFlag4 v k : Set (Fin 4 → ℝ)) := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨(c.equivFun.symm z).property, ?_⟩
    apply (integerLatticePoint4_mem_flag_iff b c v hc k z).mpr
    intro i hi
    have hz' := (mem_integerBox4 N s z).mp hz i
    simpa [s, not_lt_of_ge hi] using hz'
  have hdis : Set.PairwiseDisjoint (T : Set (Fin 4 → ℤ))
      (fun z => integerLatticePoint4 b c z +ᵥ A) := by
    intro z hz w hw hzw
    exact minimaFlag4_halfBody_cosets_disjoint b e v hv hvL hvr k hgap r hr hrmu
      _ _ (c.equivFun.symm z).property (c.equivFun.symm w).property
      (integerBox4_transverse_not_mem_flag b c v hc N k z w hz hw hzw) Q hQ
  exact hdis

theorem integerBox4_strict_gap_volume
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice4Span b)
    (hc : ∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k)
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (N : ℕ) (k : Fin 4)
    (hgap : ∀ i : Fin 4, i < k → successiveRadius4 b e i < successiveRadius4 b e k)
    (r : ℝ) (hr : 0 < r) (hrmu : r < successiveRadius4 b e k) :
    volume ((integerLatticePoint4 b c ''
      (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) + (r / 2) • parallelepipedBody4 e) =
    ((integerBox4 N (Finset.univ.filter (fun i => i < k))ᶜ).card : ENNReal) *
      volume ((integerLatticePoint4 b c ''
        (integerBox4 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 4 → ℤ))) +
        (r / 2) • parallelepipedBody4 e) := by
  classical
  let s := Finset.univ.filter (fun i : Fin 4 => i < k)
  let Q := integerLatticePoint4 b c '' (integerBox4 N s : Set (Fin 4 → ℤ))
  let T := integerBox4 N sᶜ
  let A := Q + (r / 2) • parallelepipedBody4 e
  have hQ : Q ⊆ (lattice4Span b : Set (Fin 4 → ℝ)) ∩ (minimaFlag4 v k : Set (Fin 4 → ℝ)) := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨(c.equivFun.symm z).property, ?_⟩
    apply (integerLatticePoint4_mem_flag_iff b c v hc k z).mpr
    intro i hi
    have hz' := (mem_integerBox4 N s z).mp hz i
    simpa [s, not_lt_of_ge hi] using hz'
  have hAc : IsCompact A :=
    ((integerBox4 N s).finite_toSet.image _).isCompact.add
      ((parallelepipedBody4_compact_convex e).1.smul (r / 2))
  have hdis : Set.PairwiseDisjoint (T : Set (Fin 4 → ℤ))
      (fun z => integerLatticePoint4 b c z +ᵥ A) := by
    intro z hz w hw hzw
    exact minimaFlag4_halfBody_cosets_disjoint b e v hv hvL hvr k hgap r hr hrmu
      _ _ (c.equivFun.symm z).property (c.equivFun.symm w).property
      (integerBox4_transverse_not_mem_flag b c v hc N k z w hz hw hzw) Q hQ
  have hdecomp : (integerLatticePoint4 b c ''
      (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) + (r / 2) • parallelepipedBody4 e =
      ⋃ z ∈ T, integerLatticePoint4 b c z +ᵥ A := by
    rw [integerLatticePoint4_box_split b c N s]
    ext x
    constructor
    · rintro ⟨_, ⟨q, hq, _, ⟨z, hz, rfl⟩, rfl⟩, u, hu, rfl⟩
      refine Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
      exact Set.mem_vadd_set.mpr ⟨q + u, ⟨q, hq, u, hu, rfl⟩, by
        change integerLatticePoint4 b c z + (q + u) = _
        ac_rfl⟩
    · rintro hx
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hzt, hx⟩ := Set.mem_iUnion.mp hz
      obtain ⟨_, ⟨q, hq, u, hu, rfl⟩, rfl⟩ := Set.mem_vadd_set.mp hx
      exact ⟨q + integerLatticePoint4 b c z, ⟨q, hq, _, ⟨z, hzt, rfl⟩, rfl⟩,
        u, hu, by change _ = integerLatticePoint4 b c z + (q + u); abel⟩
  rw [hdecomp, measure_biUnion_finset hdis (fun z _ => (hAc.vadd _).measurableSet)]
  simp only [measure_vadd, Finset.sum_const, nsmul_eq_mul]
  rfl

def splitIndex4 (k : Fin 4) : Fin k.val ⊕ Fin (4 - k.val) ≃ Fin 4 :=
  finSumFinEquiv.trans (finCongr (by omega))

def splitCoordinates4 (k : Fin 4) : (Fin 4 → ℝ) ≃ₗ[ℝ]
    ((Fin k.val → ℝ) × (Fin (4 - k.val) → ℝ)) :=
  (LinearEquiv.piCongrLeft ℝ (fun _ : Fin 4 => ℝ) (splitIndex4 k)).symm.trans
    (LinearEquiv.sumPiEquivProdPi ℝ (Fin k.val) (Fin (4 - k.val)) (fun _ => ℝ))

theorem splitCoordinates4_volume_preserving (k : Fin 4) :
    MeasurePreserving (splitCoordinates4 k) := by
  exact (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin k.val ⊕ Fin (4 - k.val) => ℝ)).comp
      ((volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) (splitIndex4 k)).symm
        (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (splitIndex4 k)))

theorem splitCoordinates4_volume (k : Fin 4) (S : Set (Fin 4 → ℝ)) (hS : IsCompact S) :
    volume (splitCoordinates4 k '' S) = volume S := by
  have h := (splitCoordinates4_volume_preserving k).measure_preimage
    (hS.image (splitCoordinates4 k).toContinuousLinearEquiv.continuous).measurableSet.nullMeasurableSet
  change volume ((splitCoordinates4 k) ⁻¹' ((splitCoordinates4 k) '' S)) =
    volume ((splitCoordinates4 k) '' S) at h
  rw [Set.preimage_image_eq _ (splitCoordinates4 k).injective] at h
  exact h.symm



theorem splitCoordinates4_integerBox_image
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (N : ℕ) (k : Fin 4) :
    (splitCoordinates4 k).comp (c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun.toLinearMap ''
      (integerLatticePoint4 b c ''
        (integerBox4 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 4 → ℤ))) =
    (fun q : Fin k.val → ℝ => (q, (0 : Fin (4 - k.val) → ℝ))) ''
      ((integerBox4 N (Finset.univ.filter (fun i => i < k))).image
        (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)) :
          Set (Fin k.val → ℝ)) := by
  classical
  have hcoord (z : Fin 4 → ℤ) :
      (c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun (integerLatticePoint4 b c z) =
        fun i => (z i : ℝ) := by
    funext i
    change (c.ofZLatticeBasis ℝ (lattice4Span b)).repr (integerLatticePoint4 b c z) i = _
    rw [integerLatticePoint4, Basis.ofZLatticeBasis_repr_apply]
    change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = _
    simp only [LinearEquiv.apply_symm_apply]
  have hsplit (z : Fin 4 → ℤ)
      (hz : z ∈ integerBox4 N (Finset.univ.filter (fun i => i < k))) :
      splitCoordinates4 k (fun i => (z i : ℝ)) =
        ((fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)), 0) := by
    apply Prod.ext
    · funext i
      change (z (splitIndex4 k (Sum.inl i)) : ℝ) = _
      congr 2
    · funext i
      have hi : ¬ splitIndex4 k (Sum.inr i) < k := by
        change ¬ k.val + i.val < k.val
        omega
      have hz' := (mem_integerBox4 N _ z).mp hz (splitIndex4 k (Sum.inr i))
      have hz0 : z (splitIndex4 k (Sum.inr i)) = 0 := by
        simpa [hi] using hz'
      change (z (splitIndex4 k (Sum.inr i)) : ℝ) = 0
      simp [hz0]
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨_, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoord, hsplit z hz]
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoord, hsplit z hz]



open MeasureTheory
open scoped Pointwise

def adaptedSplitCoordinates4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (c : Basis (Fin 4) ℤ (lattice4Span b)) (k : Fin 4) :=
  (c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun.trans (splitCoordinates4 k)

theorem adaptedSplitCoordinates4_volume
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (k : Fin 4) (S : Set (Fin 4 → ℝ)) (hS : IsCompact S) :
    volume (adaptedSplitCoordinates4 b c k '' S) =
      volume S / ENNReal.ofReal (ZLattice.covolume (lattice4Span b)) := by
  change volume ((fun x => splitCoordinates4 k
    ((c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun x)) '' S) = _
  rw [← Set.image_image]
  have hcS : IsCompact ((c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun '' S) :=
    hS.image (c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun.toContinuousLinearEquiv.continuous
  rw [splitCoordinates4_volume k _ hcS]
  exact ZLattice.volume_image_eq_volume_div_covolume (lattice4Span b) c

theorem adaptedSplitCoordinates4_box_body_image
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (N : ℕ) (k : Fin 4) (C : Set (Fin 4 → ℝ)) (r : ℝ) :
    adaptedSplitCoordinates4 b c k ''
      ((integerLatticePoint4 b c ''
        (integerBox4 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 4 → ℤ))) + r • C) =
    ((fun q : Fin k.val → ℝ => (q, (0 : Fin (4 - k.val) → ℝ))) ''
      ((integerBox4 N (Finset.univ.filter (fun i => i < k))).image
        (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)) :
          Set (Fin k.val → ℝ))) + r • (adaptedSplitCoordinates4 b c k '' C) := by
  have hb := splitCoordinates4_integerBox_image b c N k
  change adaptedSplitCoordinates4 b c k '' _ = _ at hb
  rw [← hb]
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, _, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, _, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, _, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    exact ⟨q + r • u, ⟨q, hq, r • u, ⟨u, hu, rfl⟩, rfl⟩, by simp⟩

theorem adaptedSplitCoordinates4_box_body_volume
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (N : ℕ) (k : Fin 4) (C : Set (Fin 4 → ℝ)) (hC : IsCompact C) (r : ℝ) :
    volume (((fun q : Fin k.val → ℝ => (q, (0 : Fin (4 - k.val) → ℝ))) ''
      ((integerBox4 N (Finset.univ.filter (fun i => i < k))).image
        (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)) :
          Set (Fin k.val → ℝ))) + r • (adaptedSplitCoordinates4 b c k '' C)) =
    volume ((integerLatticePoint4 b c ''
      (integerBox4 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 4 → ℤ))) + r • C) /
        ENNReal.ofReal (ZLattice.covolume (lattice4Span b)) := by
  rw [← adaptedSplitCoordinates4_box_body_image]
  exact adaptedSplitCoordinates4_volume b c k _
    (((integerBox4 N _).finite_toSet.image _).isCompact.add (hC.smul r))

theorem integerBox4_longitudinal_volume_growth
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (N : ℕ) (k : Fin 4) (C : Set (Fin 4 → ℝ)) (hCc : IsCompact C) (hC : Convex ℝ C)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    ENNReal.ofReal |t ^ (4 - k.val)| *
      volume ((integerLatticePoint4 b c ''
        (integerBox4 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 4 → ℤ))) + s • C) ≤
    ENNReal.ofReal |s ^ (4 - k.val)| *
      volume ((integerLatticePoint4 b c ''
        (integerBox4 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 4 → ℤ))) + t • C) := by
  classical
  have h := convex_flag4_translate_union_volume_growth k
    ((integerBox4 N (Finset.univ.filter (fun i => i < k))).image
      (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)))
    (adaptedSplitCoordinates4 b c k '' C)
    (hCc.image (adaptedSplitCoordinates4 b c k).toContinuousLinearEquiv.continuous)
    (hC.linear_image (adaptedSplitCoordinates4 b c k).toLinearMap) s t hs hst ht
  rw [adaptedSplitCoordinates4_box_body_volume b c N k C hCc s,
    adaptedSplitCoordinates4_box_body_volume b c N k C hCc t] at h
  have hc0 : ENNReal.ofReal (ZLattice.covolume (lattice4Span b)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos (lattice4Span b) volume))
  have h' := mul_le_mul_right' h (ENNReal.ofReal (ZLattice.covolume (lattice4Span b)))
  simpa only [mul_assoc, ENNReal.div_mul_cancel hc0 ENNReal.ofReal_ne_top] using h'

theorem integerBox4_full_volume_growth_step
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice4Span b)
    (hc : ∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k)
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (N : ℕ) (k : Fin 4) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hpacking : s = t ∨ ((∀ i : Fin 4, i < k →
      successiveRadius4 b e i < successiveRadius4 b e k) ∧ t < successiveRadius4 b e k)) :
    ENNReal.ofReal |(t / 2) ^ (4 - k.val)| *
      volume ((integerLatticePoint4 b c ''
        (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) + (s / 2) • parallelepipedBody4 e) ≤
    ENNReal.ofReal |(s / 2) ^ (4 - k.val)| *
      volume ((integerLatticePoint4 b c ''
        (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) + (t / 2) • parallelepipedBody4 e) := by
  rcases hpacking with heq | ⟨hgap, htmu⟩
  · subst t
    exact le_rfl
  have ht : 0 < t := hs.trans_le hst
  rw [integerBox4_strict_gap_volume b c v hv hvL hc e hvr N k hgap s hs (hst.trans_lt htmu),
    integerBox4_strict_gap_volume b c v hv hvL hc e hvr N k hgap t ht htmu]
  have h := integerBox4_longitudinal_volume_growth b c N k _
    (parallelepipedBody4_compact_convex e).1 (parallelepipedBody4_compact_convex e).2
    (s / 2) (t / 2) (by positivity) (by linarith) (by positivity)
  simpa only [mul_left_comm] using mul_le_mul_left' h
    ((integerBox4 N (Finset.univ.filter (fun i => i < k))ᶜ).card : ENNReal)


theorem integerBox4_full_volume_growth
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice4Span b)
    (hc : ∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k)
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (successiveRadius4 b e 1 * successiveRadius4 b e 2 * successiveRadius4 b e 3) *
      volume.real ((integerLatticePoint4 b c ''
        (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) +
        (ρ * successiveRadius4 b e 0 / 2) • parallelepipedBody4 e) ≤
    successiveRadius4 b e 0 ^ 3 *
      volume.real ((integerLatticePoint4 b c ''
        (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) +
        (ρ * successiveRadius4 b e 3 / 2) • parallelepipedBody4 e) := by
  obtain ⟨_,_,_,hpos,hmono,_⟩ := exists_successive_minima4 b e
  let μ := successiveRadius4 b e
  let U : ℝ → Set (Fin 4 → ℝ) := fun r =>
    (integerLatticePoint4 b c '' (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) +
      (r / 2) • parallelepipedBody4 e
  have hUc (r : ℝ) : IsCompact (U r) :=
    ((integerBox4 N Finset.univ).finite_toSet.image _).isCompact.add
      ((parallelepipedBody4_compact_convex e).1.smul (r / 2))
  have hstep (i j k : Fin 4) (hij : μ i ≤ μ j)
      (hgap : μ i = μ j ∨ (∀ l : Fin 4, l < k → μ l < μ k) ∧ j = k) :
      μ j ^ (4 - k.val) * volume.real (U (ρ * μ i)) ≤
      μ i ^ (4 - k.val) * volume.real (U (ρ * μ j)) := by
    have hp : ρ * μ i = ρ * μ j ∨
        (∀ l : Fin 4, l < k → μ l < μ k) ∧ ρ * μ j < μ k := by
      rcases hgap with heq | ⟨hgap,rfl⟩
      · exact Or.inl (congrArg (ρ * ·) heq)
      · exact Or.inr ⟨hgap,mul_lt_of_lt_one_left (hpos j) hρ1⟩
    have h := integerBox4_full_volume_growth_step b c v hv hvL hc e hvr N k
      (ρ * μ i) (ρ * μ j) (mul_pos hρ (hpos i)) (mul_le_mul_of_nonneg_left hij hρ.le) hp
    have hf : ENNReal.ofReal |(ρ * μ i / 2) ^ (4 - k.val)| * volume (U (ρ * μ j)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hUc _).measure_ne_top
    have ht := ENNReal.toReal_mono hf h
    have ht' : |(ρ * μ j / 2) ^ (4 - k.val)| * volume.real (U (ρ * μ i)) ≤
        |(ρ * μ i / 2) ^ (4 - k.val)| * volume.real (U (ρ * μ j)) := by
      simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),measureReal_def] using ht
    rw [abs_of_pos (pow_pos (div_pos (mul_pos hρ (hpos j)) (by norm_num)) _),
      abs_of_pos (pow_pos (div_pos (mul_pos hρ (hpos i)) (by norm_num)) _)] at ht'
    apply (mul_le_mul_left (pow_pos (div_pos hρ (by norm_num : (0 : ℝ) < 2)) (4-k.val))).mp
    simpa only [div_eq_mul_inv,mul_pow,mul_assoc,mul_left_comm,mul_comm] using ht'
  have hg (i : Fin 3) : μ i.castSucc = μ i.succ ∨
      (∀ l : Fin 4, l < i.succ → μ l < μ i.succ) ∧ i.succ = i.succ := by
    by_cases heq : μ i.castSucc = μ i.succ
    · exact Or.inl heq
    · refine Or.inr ⟨?_,rfl⟩
      intro l hl
      exact (hmono (show l ≤ i.castSucc from (by change l.val ≤ i.val; change l.val < i.val+1 at hl; omega))).trans_lt
        (lt_of_le_of_ne (hmono (by exact i.castSucc_le_succ)) heq)
  have h1 := hstep 0 1 1 (hmono (by decide)) (hg 0)
  have h2 := hstep 1 2 2 (hmono (by decide)) (hg 1)
  have h3 := hstep 2 3 3 (hmono (by decide)) (hg 2)
  change μ 1 ^ 3 * volume.real (U (ρ * μ 0)) ≤ μ 0 ^ 3 * volume.real (U (ρ * μ 1)) at h1
  change μ 2 ^ 2 * volume.real (U (ρ * μ 1)) ≤ μ 1 ^ 2 * volume.real (U (ρ * μ 2)) at h2
  have h3' : μ 3 * volume.real (U (ρ * μ 2)) ≤ μ 2 * volume.real (U (ρ * μ 3)) := by
    simpa only [show 4 - (3 : Fin 4).val = 1 from rfl,pow_one] using h3
  have h12 : μ 2 ^ 2 * μ 1 * volume.real (U (ρ * μ 0)) ≤ μ 0 ^ 3 * volume.real (U (ρ * μ 2)) := by
    apply (mul_le_mul_left (pow_pos (hpos 1) 2)).mp
    calc
      _ = μ 2 ^ 2 * (μ 1 ^ 3 * volume.real (U (ρ * μ 0))) := by ring
      _ ≤ μ 2 ^ 2 * (μ 0 ^ 3 * volume.real (U (ρ * μ 1))) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = μ 0 ^ 3 * (μ 2 ^ 2 * volume.real (U (ρ * μ 1))) := by ring
      _ ≤ μ 0 ^ 3 * (μ 1 ^ 2 * volume.real (U (ρ * μ 2))) := mul_le_mul_of_nonneg_left h2 (pow_pos (hpos 0) 3).le
      _ = _ := by ring
  apply (mul_le_mul_left (hpos 2)).mp
  calc
    _ = μ 3 * (μ 2 ^ 2 * μ 1 * volume.real (U (ρ * μ 0))) := by ring
    _ ≤ μ 3 * (μ 0 ^ 3 * volume.real (U (ρ * μ 2))) := mul_le_mul_of_nonneg_left h12 (hpos 3).le
    _ = μ 0 ^ 3 * (μ 3 * volume.real (U (ρ * μ 2))) := by ring
    _ ≤ μ 0 ^ 3 * (μ 2 * volume.real (U (ρ * μ 3))) := mul_le_mul_of_nonneg_left h3' (pow_pos (hpos 0) 3).le
    _ = _ := by ring

theorem volume_smul_fin4 (r : ℝ) (C : Set (Fin 4 → ℝ)) :
    volume (r • C) = ENNReal.ofReal |r ^ 4| * volume C := by
  let T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := r • LinearMap.id
  change volume (T '' C) = _
  rw [Measure.addHaar_image_linearMap volume T]
  congr 2
  simp [T, LinearMap.det_smul, Module.finrank_pi]

theorem integerBox4_full_volume_product_lower
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice4Span b)
    (hc : ∀ k : Fin 4, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice4Span b) : (Fin 4 → ℝ)))) = minimaFlag4 v k)
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ((integerBox4 N Finset.univ).card : ℝ) * (ρ / 2) ^ 4 *
      (∏ i, successiveRadius4 b e i) * volume.real (parallelepipedBody4 e) ≤
    volume.real ((integerLatticePoint4 b c ''
      (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) +
      (ρ * successiveRadius4 b e 3 / 2) • parallelepipedBody4 e) := by
  classical
  obtain ⟨_, _, _, hpos, _, _⟩ := exists_successive_minima4 b e
  have hfilter : Finset.univ.filter (fun i : Fin 4 => i < 0) = ∅ := by simp
  have hzero : integerBox4 N ∅ = {0} := by
    ext z
    rw [mem_integerBox4]
    simp only [Finset.not_mem_empty, ite_false, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  have hpoint : integerLatticePoint4 b c 0 = 0 := by
    simp [integerLatticePoint4]
  have hpack := integerBox4_strict_gap_volume b c v hv hvL hc e hvr N 0
    (by intro i hi; exact False.elim (Fin.not_lt_zero i hi))
    (ρ * successiveRadius4 b e 0) (mul_pos hρ (hpos 0))
    (mul_lt_of_lt_one_left (hpos 0) hρ1)
  rw [hfilter, Finset.compl_empty, hzero] at hpack
  simp only [Finset.coe_singleton, Set.image_singleton, hpoint] at hpack
  change volume _ = _ * volume ((0 : Set (Fin 4 → ℝ)) + _) at hpack
  rw [zero_add] at hpack
  rw [volume_smul_fin4] at hpack
  have hreal := congrArg ENNReal.toReal hpack
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (abs_nonneg _), ← measureReal_def] at hreal
  rw [abs_of_pos (pow_pos (div_pos (mul_pos hρ (hpos 0)) (by norm_num)) 4)] at hreal
  have hg := integerBox4_full_volume_growth b c v hv hvL hc e hvr N ρ hρ hρ1
  rw [hreal] at hg
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  have hfactor :
      successiveRadius4 b e 1 * successiveRadius4 b e 2 * successiveRadius4 b e 3 *
        ((integerBox4 N Finset.univ).card *
          ((ρ * successiveRadius4 b e 0 / 2) ^ 4 * volume.real (parallelepipedBody4 e))) =
      successiveRadius4 b e 0 ^ 3 *
        ((integerBox4 N Finset.univ).card * (ρ / 2) ^ 4 *
          (successiveRadius4 b e 0 * (successiveRadius4 b e 1 * (successiveRadius4 b e 2 * successiveRadius4 b e 3))) *
            volume.real (parallelepipedBody4 e)) := by ring
  rw [hfactor] at hg
  exact (mul_le_mul_left (pow_pos (hpos 0) 3)).mp hg


theorem integerBox4_full_body_fixed_enlargement
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (N : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      (c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun ''
        ((integerLatticePoint4 b c ''
          (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) +
          (ρ * successiveRadius4 b e 3 / 2) • parallelepipedBody4 e) ⊆
      Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-(N : ℝ) - R) ((N : ℝ) + R)) := by
  let B := (c.ofZLatticeBasis ℝ (lattice4Span b)).equivFun
  let A := (successiveRadius4 b e 3 / 2) • parallelepipedBody4 e
  have hAc : IsCompact A := (parallelepipedBody4_compact_convex e).1.smul _
  have hBc : IsCompact (B '' A) := hAc.image B.toContinuousLinearEquiv.continuous
  obtain ⟨R, hR, hbound⟩ := hBc.isBounded.subset_closedBall_lt 0 (0 : (Fin 4 → ℝ))
  refine ⟨R, hR, ?_⟩
  intro N ρ hρ hρ1 x hx
  obtain ⟨_, ⟨_, ⟨z, hz, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩ := hx
  have hcoord : B (integerLatticePoint4 b c z) = fun i => (z i : ℝ) := by
    funext i
    change (c.ofZLatticeBasis ℝ (lattice4Span b)).repr (integerLatticePoint4 b c z) i = _
    rw [integerLatticePoint4, Basis.ofZLatticeBasis_repr_apply]
    change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = _
    simp only [LinearEquiv.apply_symm_apply]
  have hzero : (0 : (Fin 4 → ℝ)) ∈ A := by
    refine ⟨0, ?_, by simp⟩
    rw [mem_parallelepipedBody4_iff]
    simp [coordinateGauge4]
  have hsmall : (ρ * successiveRadius4 b e 3 / 2) • u ∈ A := by
    have h := ((parallelepipedBody4_compact_convex e).2.smul
      (successiveRadius4 b e 3 / 2)).smul_mem_of_zero_mem hzero
        (show (successiveRadius4 b e 3 / 2) • u ∈ A from ⟨u, hu, rfl⟩) ⟨hρ, hρ1⟩
    simpa only [smul_smul, mul_div_assoc] using h
  have hnorm : ‖B ((ρ * successiveRadius4 b e 3 / 2) • u)‖ ≤ R := by
    have h := hbound (Set.mem_image_of_mem B hsmall)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  rw [Set.mem_pi]
  intro i _
  change B (integerLatticePoint4 b c z + (ρ * successiveRadius4 b e 3 / 2) • u) i ∈ _
  rw [map_add, Pi.add_apply, hcoord]
  have hz' := (mem_integerBox4 N Finset.univ z).mp hz i
  simp only [Finset.mem_univ, ite_true] at hz'
  have hzR : -(N : ℝ) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ N := by exact_mod_cast hz'
  have hi : |B ((ρ * successiveRadius4 b e 3 / 2) • u) i| ≤ R :=
    le_trans (by simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (B ((ρ * successiveRadius4 b e 3 / 2) • u)) i) hnorm
  exact ⟨by linarith [(abs_le.mp hi).1], by linarith [(abs_le.mp hi).2]⟩

theorem integerBox4_full_body_volume_upper
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (c : Basis (Fin 4) ℤ (lattice4Span b))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (N : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      volume.real ((integerLatticePoint4 b c ''
        (integerBox4 N Finset.univ : Set (Fin 4 → ℤ))) +
        (ρ * successiveRadius4 b e 3 / 2) • parallelepipedBody4 e) ≤
      (2 * ((N : ℝ) + R)) ^ 4 * ZLattice.covolume (lattice4Span b) := by
  obtain ⟨R, hR, hsub⟩ := integerBox4_full_body_fixed_enlargement b c e
  refine ⟨R, hR, ?_⟩
  intro N ρ hρ hρ1
  have hbox : volume (Set.pi Set.univ
      (fun _ : Fin 4 => Set.Icc (-(N : ℝ) - R) ((N : ℝ) + R))) =
      ENNReal.ofReal ((2 * ((N : ℝ) + R)) ^ 4) := by
    rw [volume_pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by linarith [Nat.cast_nonneg (α := ℝ) N])]
    congr 1
    ring
  have h := measure_mono (μ := volume) (hsub N ρ hρ hρ1)
  rw [ZLattice.volume_image_eq_volume_div_covolume (lattice4Span b) c, hbox] at h
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have hcov := ZLattice.covolume_pos (lattice4Span b) volume
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hcov.le,
    ENNReal.toReal_ofReal (by positivity)] at h'
  exact (div_le_iff₀ hcov).mp h'

theorem integerBox4_full_card (N : ℕ) :
    (integerBox4 N Finset.univ).card = (2 * N + 1) ^ 4 := by
  simp [integerBox4, Fintype.card_piFinset, Int.card_Icc]
  omega


open Filter Topology

theorem quartic_box_leading_coefficient (A B R : ℝ)
    (h : ∀ N : ℕ, (2 * (N : ℝ) + 1) ^ 4 * A ≤ (2 * ((N : ℝ) + R)) ^ 4 * B) :
    A ≤ B := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hn (n : ℕ) :
      (2 + ((n : ℝ) + 1)⁻¹) ^ 4 * A ≤
        (2 + 2 * R * ((n : ℝ) + 1)⁻¹) ^ 4 * B := by
    have hne : (n : ℝ) + 1 ≠ 0 := by positivity
    have h' := mul_le_mul_of_nonneg_right (h (n + 1))
      (show 0 ≤ (((n : ℝ) + 1) ^ 4)⁻¹ by positivity)
    push_cast at h'
    have hleft : (2 + ((n : ℝ) + 1)⁻¹) ^ 4 * A =
        (2 * ((n : ℝ) + 1) + 1) ^ 4 * A * (((n : ℝ) + 1) ^ 4)⁻¹ := by
      field_simp [hne]
    have hright : (2 + 2 * R * ((n : ℝ) + 1)⁻¹) ^ 4 * B =
        (2 * ((n : ℝ) + 1 + R)) ^ 4 * B * (((n : ℝ) + 1) ^ 4)⁻¹ := by
      field_simp [hne]
      ring_nf
      simp
    rw [hleft, hright]
    exact h'
  have hL : Tendsto (fun n : ℕ => (2 + ((n : ℝ) + 1)⁻¹) ^ 4 * A) atTop (𝓝 (2 ^ 4 * A)) := by
    simpa using ((tendsto_const_nhds.add hinv).pow 4).mul_const A
  have hR : Tendsto (fun n : ℕ => (2 + 2 * R * ((n : ℝ) + 1)⁻¹) ^ 4 * B)
      atTop (𝓝 (2 ^ 4 * B)) := by
    simpa using ((tendsto_const_nhds.add (hinv.const_mul (2 * R))).pow 4).mul_const B
  have hlim := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hn)
  norm_num at hlim
  linarith


open MeasureTheory

theorem successive_minima4_parallelepiped_volume_upper_contracted
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (ρ / 2) ^ 4 * (∏ j, successiveRadius4 b e j) *
      volume.real (parallelepipedBody4 e) ≤ ZLattice.covolume (lattice4Span b) := by
  obtain ⟨v, hv, hvL, _, _, hvr⟩ := exists_successive_minima4 b e
  obtain ⟨c, hc⟩ := exists_adapted_integer_basis4 b v hv hvL
  obtain ⟨R, _, hupper⟩ := integerBox4_full_body_volume_upper b c e
  apply quartic_box_leading_coefficient _ _ R
  intro N
  have h := (integerBox4_full_volume_product_lower b c v hv hvL hc e hvr N ρ hρ hρ1).trans
    (hupper N ρ hρ.le hρ1.le)
  rw [integerBox4_full_card] at h
  push_cast at h
  simpa only [mul_assoc] using h

theorem successive_minima4_parallelepiped_volume_upper
    (b : Basis (Fin 4) ℝ (Fin 4 → ℝ)) (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :
    (∏ j, successiveRadius4 b e j) * volume.real (parallelepipedBody4 e) ≤
      16 * ZLattice.covolume (lattice4Span b) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ =>
      ((1 - ((n : ℝ) + 2)⁻¹) / 2) ^ 4 * (∏ j, successiveRadius4 b e j) *
        volume.real (parallelepipedBody4 e)) atTop
      (𝓝 (((1 : ℝ) / 2) ^ 4 * (∏ j, successiveRadius4 b e j) *
        volume.real (parallelepipedBody4 e))) := by
    simpa using (((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).div_const 2).pow 4).mul_const
      (∏ j, successiveRadius4 b e j)).mul_const (volume.real (parallelepipedBody4 e))
  have hbound : ∀ n : ℕ,
      ((1 - ((n : ℝ) + 2)⁻¹) / 2) ^ 4 * (∏ j, successiveRadius4 b e j) *
        volume.real (parallelepipedBody4 e) ≤ ZLattice.covolume (lattice4Span b) := by
    intro n
    have hpos : 0 < (n : ℝ) + 2 := by positivity
    have hi : ((n : ℝ) + 2)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact successive_minima4_parallelepiped_volume_upper_contracted b e _
      (by linarith) (by linarith [inv_pos.mpr hpos])
  have h := le_of_tendsto hlim (Eventually.of_forall hbound)
  norm_num at h
  nlinarith


theorem weightedCoordinates4_det (A : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 < w i) :
    LinearMap.det (weightedCoordinates4 A w hw).toLinearMap = LinearMap.det A.toLinearMap / ∏ i, w i := by
  let B := Pi.basisFun ℝ (Fin 4)
  have hm : LinearMap.toMatrix B B (weightedCoordinates4 A w hw).toLinearMap =
      Matrix.diagonal (fun i => (w i)⁻¹) * LinearMap.toMatrix B B A.toLinearMap := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, Pi.basisFun_repr, Matrix.diagonal_mul,
      weightedCoordinates4, div_eq_mul_inv, mul_comm]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_mul, Matrix.det_diagonal,
    Finset.prod_inv_distrib, LinearMap.det_toMatrix]
  ring

theorem originalCoordinates4_det (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    LinearMap.det (originalCoordinates4 L hL Q hQ c₀).toLinearMap = L.det / ∏ i, Q ^ c₀ i := by
  rw [originalCoordinates4,weightedCoordinates4_det]
  congr 1
  exact LinearMap.det_toLin' L

theorem originalBody4_volume (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    volume.real (originalBody4 L Q c₀) = 16 * (∏ i, Q ^ c₀ i) / |L.det| := by
  have hw : 0 < ∏ i, Q ^ c₀ i := Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  have he : originalBody4 L Q c₀ = (originalCoordinates4 L hL Q hQ c₀) ⁻¹'
      Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-1 : ℝ) 1) := by
    ext x
    rw [originalBody4_mem_iff L hL Q hQ c₀ x,pi_norm_le_iff_of_nonempty]
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_const,Set.mem_Icc,Real.norm_eq_abs,abs_le]
  have hvol : volume.real (originalBody4 L Q c₀) =
      16 / |LinearMap.det (originalCoordinates4 L hL Q hQ c₀).toLinearMap| := by
    rw [measureReal_def,he,Measure.addHaar_preimage_linearEquiv,volume_pi,Measure.pi_pi]
    simp only [Real.volume_Icc,LinearEquiv.det_coe_symm,abs_inv,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal,abs_nonneg,div_eq_mul_inv]
    norm_num
    ring
  rw [hvol,originalCoordinates4_det,abs_div,abs_of_pos hw]
  field_simp


theorem sourceMinima4_product_volume_upper (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∏ j : Fin 4, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) *
      volume.real (originalBody4 L Q c₀) ≤
        16 * ZLattice.covolume (integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) := by
  let e₂ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))
  let e₃ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))
  let b := sourceRealBasis4 A₂ A₃ e₂ e₃
  let e := originalCoordinates4 L hL Q hQ c₀
  have hr (j : Fin 4) : successiveRadius4 b e j = sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j :=
    (sourceMinima4_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃ j).symm
  have hspan : lattice4Span b = integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃) :=
    sourceRealBasis4_span A₂ A₃ e₂ e₃
  have hbody : parallelepipedBody4 e = originalBody4 L Q c₀ := by
    ext x
    rw [mem_parallelepipedBody4_iff,originalBody4_mem_iff L hL Q hQ c₀ x]
    rfl
  have h := successive_minima4_parallelepiped_volume_upper b e
  rw [hbody,hspan] at h
  simpa only [hr] using h

theorem source_original_uniform_minima_upper4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ (K : ℕ) (C₄ : ℝ), 0 < K ∧ 0 < C₄ ∧ C₄ = |L.det| * (K : ℝ) * 1296 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∏ j : Fin 4, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ≤ C₄ := by
  obtain ⟨K,hK,hcov⟩ := sourceLattice4_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  have hdet : 0 < |L.det| := abs_pos.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det L).mp hL))
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨K,|L.det| * (K : ℝ) * 1296,hK,by positivity,rfl,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let W := ∏ i, Q ^ c₀ i
  have hW : 0 < W := Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  have hc : ZLattice.covolume (integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) ≤
      ((K : ℝ) * 1296) * W := (div_le_iff₀ hW).mp (hcov Q hQ c₀ c₂ c₃ hc₂ hc₃ hb)
  have hg := sourceMinima4_product_volume_upper A₂ A₃ L hL Q hQ c₀ c₂ c₃
  rw [originalBody4_volume L hL Q hQ c₀] at hg
  apply (mul_le_mul_right (div_pos (mul_pos (by norm_num : (0 : ℝ) < 16) hW) hdet)).mp
  calc
    _ ≤ 16 * ZLattice.covolume (integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)) := hg
    _ ≤ 16 * (((K : ℝ) * 1296) * W) := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by field_simp [hdet.ne']; ring

end
end CompoundFeasibility
