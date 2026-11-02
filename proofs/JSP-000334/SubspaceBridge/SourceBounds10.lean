import SubspaceBridge.Davenport10
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

theorem local_uniform_multiple10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℚ) (e : Fin n → ℕ) (E : ℕ) (he : ∀ i, e i ≤ E)
    (D : ℤ) (hD : ∀ i j, ∃ z : ℤ, (z : ℚ) = (D : ℚ)*A i j)
    (T : ℤ) (j : Fin n) : Pi.single j (D*(p : ℤ)^E*T) ∈ lattice10 p A e := by
  apply (lattice10_spec p A e _).mpr
  intro i
  obtain ⟨z,hz⟩ := hD i j
  have hm : (A *ᵥ (fun k => ((Pi.single j (D*(p : ℤ)^E*T) : Fin n → ℤ) k : ℚ))) i =
      (((p : ℤ)^E*T*z : ℤ) : ℚ) := by
    have hc : (fun k => ((Pi.single j (D*(p : ℤ)^E*T) : Fin n → ℤ) k : ℚ)) =
        Pi.single j ((D : ℚ)*(p : ℚ)^E*(T : ℚ)) := by
      ext k
      by_cases hk : k = j <;> simp [Pi.single_apply,hk]
    rw [hc,Matrix.mulVec_single]
    change A i j*((D : ℚ)*(p : ℚ)^E*(T : ℚ)) = _
    push_cast
    rw [hz]
    ring
  rw [hm]
  apply padicNorm.dvd_iff_norm_le.mp
  exact_mod_cast (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (he i)) T) z)

theorem source_bounded_grid10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ), 1 < Q → ∀ (c2 c3 : Fin 10 → ℝ),
      (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) → (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) →
      ∃ B : ℤ, B ≠ 0 ∧ |(B : ℝ)| ≤ C*Q^2 ∧
        ∀ j : Fin 10, Pi.single j B ∈ originalSourceGroup10 A2 A3 Q c2 c3 := by
  obtain ⟨D2,hD2,hm2⟩ := clear_matrix_denominators A2
  obtain ⟨D3,hD3,hm3⟩ := clear_matrix_denominators A3
  let C : ℝ := 6*|(D2 : ℝ)| *|(D3 : ℝ)|
  have hD2R : (D2 : ℝ) ≠ 0 := by exact_mod_cast hD2
  have hD3R : (D3 : ℝ) ≠ 0 := by exact_mod_cast hD3
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro Q hQ c2 c3 hc2 hc3
  let E (p : ℕ) := Nat.ceil (JSP000334.qThreshold p Q (-1))
  let B : ℤ := D2*D3*2^(E 2)*3^(E 3)
  have he (p : ℕ) (hp : 1 < p) (c : Fin 10 → ℝ) (hc : ∀ i, -1 ≤ c i) (i : Fin 10) :
      Nat.ceil (JSP000334.qThreshold p Q (c i)) ≤ E p := by
    apply Nat.ceil_mono
    unfold JSP000334.qThreshold
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hp.le))
    exact mul_le_mul_of_nonneg_right (by linarith [hc i]) (Real.log_nonneg hQ.le)
  have hpow (p : ℕ) (hp : 1 < p) : (p : ℝ)^(E p) ≤ (p : ℝ)*Q := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
    calc
      _ ≤ (p : ℝ)^(JSP000334.qThreshold p Q (-1)+1) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le)
          (Nat.ceil_lt_add_one (JSP000334.qThreshold_nonneg p hp Q (-1) hQ (by norm_num))).le
      _ = _ := by
        rw [Real.rpow_add hp0,Real.rpow_one,JSP000334.qThreshold_rpow p hp Q (-1) hQ]
        norm_num
        ring
  refine ⟨B,by dsimp [B]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hD2 hD3) (by positivity)) (by positivity),?_,?_⟩
  · have h2 := hpow 2 (by decide)
    have h3 := hpow 3 (by decide)
    have hprod := mul_le_mul h2 h3 (by positivity) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hprod (mul_nonneg (abs_nonneg (D2 : ℝ)) (abs_nonneg (D3 : ℝ)))
    dsimp [B,C]
    push_cast
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2^(E 2)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3^(E 3))]
    convert hmul using 1 <;> norm_num <;> ring
  · intro j
    constructor
    · have hB : B = D2*2^(E 2)*(D3*3^(E 3)) := by dsimp [B]; ring
      rw [hB]
      exact local_uniform_multiple10 2 A2 _ (E 2) (he 2 (by decide) c2 (fun i => (hc2 i).1)) D2 hm2 _ j
    · have hB : B = D3*3^(E 3)*(D2*2^(E 2)) := by dsimp [B]; ring
      rw [hB]
      exact local_uniform_multiple10 3 A3 _ (E 3) (he 3 (by decide) c3 (fun i => (hc3 i).1)) D3 hm3 _ j

theorem source_last_upper10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ),
      (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) →
      (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) →
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9 ≤ K*Q^3 := by
  obtain ⟨C,hC,hgrid⟩ := source_bounded_grid10 A2 A3
  let E := (originalFormEquiv10 L hL).toContinuousLinearEquiv
  let N := max 1 ‖E.toContinuousLinearMap‖
  have hN : 0 < N := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨N*C,mul_pos hN hC,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3
  obtain ⟨B,hB,hbound,hmem⟩ := hgrid Q hQ c2 c3 hc2 hc3
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB
  let u : Fin 10 → Fin 10 → ℝ := fun j => integerReal (Pi.single j B)
  let F : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ) := (B : ℝ) • LinearMap.id
  have hF : Function.Injective F := by
    intro x y h
    funext i
    apply mul_left_cancel₀ hBR
    exact congrFun h i
  have hufun : u = fun j => F ((Pi.basisFun ℝ (Fin 10)) j) := by
    funext j i
    by_cases hij : i = j <;> simp [u,F,integerReal,Pi.basisFun_apply,Pi.single_apply,hij]
  have hu : LinearIndependent ℝ u := by
    rw [hufun]
    exact (Pi.basisFun ℝ (Fin 10)).linearIndependent.map' F (LinearMap.ker_eq_bot.mpr hF)
  let b := sourceRealBasis10 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  rw [sourceMinima10_eq_radius]
  apply successiveRadius10_le_family b _ 9 u hu (fun j => ?_) (N*C*Q^3) (fun j => ?_)
  · rw [sourceRealBasis10_span]
    exact ⟨Pi.single j B,hmem j,rfl⟩
  · have hunorm : ‖u j‖ ≤ |(B : ℝ)| := by
      apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      by_cases hij : i = j <;> simp [u,integerReal,Pi.single_apply,hij,Real.norm_eq_abs]
    have hform : ‖originalFormEquiv10 L hL (u j)‖ ≤ N*‖u j‖ :=
      (E.toContinuousLinearMap.le_opNorm (u j)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hg : coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) (u j) ≤
        Q*‖originalFormEquiv10 L hL (u j)‖ := by
      apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      change |(L *ᵥ u j) i / Q^(c0 i)| ≤ _
      rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _),div_eq_mul_inv]
      have hw : (Q^(c0 i))⁻¹ ≤ Q := by
        rw [← Real.rpow_neg (zero_lt_one.trans hQ).le]
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le
          (show -c0 i ≤ 1 by linarith [(abs_le.mp (hc0 i)).1])
      have hn : |(L *ᵥ u j) i| ≤ ‖originalFormEquiv10 L hL (u j)‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (originalFormEquiv10 L hL (u j)) i
      exact (mul_le_mul hn hw (inv_nonneg.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le)
        (norm_nonneg _)).trans_eq (mul_comm _ _)
    calc
      _ ≤ Q*‖originalFormEquiv10 L hL (u j)‖ := hg
      _ ≤ Q*(N*‖u j‖) := mul_le_mul_of_nonneg_left hform (zero_lt_one.trans hQ).le
      _ ≤ Q*(N*(C*Q^2)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hunorm.trans hbound) hN.le) (zero_lt_one.trans hQ).le
      _ = _ := by ring

end
end CompoundFeasibility
