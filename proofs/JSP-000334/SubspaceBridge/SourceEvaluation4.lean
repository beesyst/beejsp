import SubspaceBridge.SourceBalance4
import SubspaceBridge.AuxiliaryProductFormula
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4.SourceEvaluation4
open SourceMultiblock4 SourceExpansion4 SourceBalance4 SourceSupport4

def integerValue {m : ℕ} (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ)
    (v : Fin m → Fin 4 → ℤ) : ℤ :=
  MvPolynomial.eval (fun u => v u.1 u.2) (derivative4 J P)

theorem integerValue_cast {K : Type*} [CommRing K] {m : ℕ}
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ) (v : Fin m → Fin 4 → ℤ) :
    (integerValue J P v : K) = MvPolynomial.eval (fun u => (v u.1 u.2 : K))
      (derivative4 J (P.map (Int.castRingHom K))) := by
  rw [← derivative4_map, MvPolynomial.eval_map]
  exact MvPolynomial.eval₂_comp (Int.castRingHom K) _ _

theorem integerValue_lower {m : ℕ} (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (v : Fin m → Fin 4 → ℤ)
    (hz : integerValue J P v ≠ 0) :
    1 ≤ ‖(integerValue J P v : ℝ)‖ * ‖(integerValue J P v : ℚ_[2])‖ *
      ‖(integerValue J P v : ℚ_[3])‖ := by
  have hh := JSP000334.rothInteger_three_place_lower (integerValue J P v) hz
  simpa [JSP000334.rothLocalAbs, Real.norm_eq_abs, ← Auxiliary6.SourceExpansion.finite_norm 2, ← Auxiliary6.SourceExpansion.finite_norm 3] using hh

theorem integerValue_finite_le_one (p : ℕ) [Fact p.Prime] {m : ℕ}
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ) (v : Fin m → Fin 4 → ℤ) :
    ‖(integerValue J P v : ℚ_[p])‖ ≤ 1 := by
  have hh := padicNorm.of_int (p := p) (integerValue J P v)
  have hhR : (padicNorm p (integerValue J P v : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hh
  simpa only [← Auxiliary6.SourceExpansion.finite_norm p, map_intCast] using hhR


theorem evaluation_identity {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0)
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ) (v : Fin m → Fin 4 → ℤ) :
    (integerValue J P v : K) = ∑ b ∈ (expansion A J P).support,
      (expansion A J P).coeff b * ∏ u : Vars4 m,
        ((A *ᵥ (fun i => (v u.1 i : K))) u.2) ^ b u := by
  rw [integerValue_cast, ← reconstruct A hA J P]
  have he : (MvPolynomial.eval (fun u : Vars4 m => (v u.1 u.2 : K))).comp
      (substitution A) = MvPolynomial.eval (fun u : Vars4 m =>
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

def logWeight {m : ℕ} (Q : Fin m → ℝ) (b : Vars4 m →₀ ℕ) (i : Fin 4) : ℝ :=
  ∑ h, (b (h,i) : ℝ) * Real.log (Q h)

theorem log_weight_transport {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (eta A : ℝ) (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (b : Vars4 m →₀ ℕ) (hdegree : ∀ h, (∑ i : Fin 4, b (h,i)) ≤ r h)
    (hbalance : ∀ i, |coordinateWeight r i b - (m : ℝ)/4| ≤ 18*eta*m) :
    ∀ i, |logWeight Q b i - A*m/4| ≤ 19*A*m*eta := by
  intro i
  have hnorm : coordinateWeight r i b ≤ (m : ℝ) := by
    unfold coordinateWeight
    calc
      _ ≤ ∑ _h : Fin m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        apply (div_le_one (by exact_mod_cast hr h)).mpr
        exact_mod_cast (Finset.single_le_sum (fun j _ => Nat.zero_le (b (h,j)))
          (Finset.mem_univ i)).trans (hdegree h)
      _ = _ := by simp
  have hterm (h : Fin m) : (b (h,i) : ℝ)*Real.log (Q h) =
      ((b (h,i) : ℝ)/r h)*((r h : ℝ)*Real.log (Q h)) := by
    have hn : (r h : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr h)
    field_simp [hn]
    ring
  have hlo : A*coordinateWeight r i b ≤ logWeight Q b i := by
    unfold coordinateWeight logWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [hterm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hlog h).1
      (show 0 ≤ (b (h,i) : ℝ)/(r h : ℝ) from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hhi : logWeight Q b i ≤ (1+eta)*A*coordinateWeight r i b := by
    unfold coordinateWeight logWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [hterm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hlog h).2
      (show 0 ≤ (b (h,i) : ℝ)/(r h : ℝ) from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hbal := abs_le.mp (hbalance i)
  have hs1 := mul_le_mul_of_nonneg_left hbal.1 hA
  have hs2 := mul_le_mul_of_nonneg_left hbal.2 hA
  have herr := mul_le_mul_of_nonneg_left hnorm (mul_nonneg heta hA)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem monomial_bound {K : Type*} [NormedField K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (v : Fin m → Fin 4 → ℤ)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h) (c : Fin 4 → ℝ)
    (hv : ∀ h i, ‖(A *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i))
    (b : Vars4 m →₀ ℕ) :
    ‖∏ u : Vars4 m, ((A *ᵥ (fun i => (v u.1 i : K))) u.2)^b u‖ ≤
      Real.exp (∑ i : Fin 4, c i * logWeight Q b i) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ u : Vars4 m, ((Q u.1)^(c u.2))^b u := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro u hu
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hv u.1 u.2) _
    _ = _ := by
      have he (u : Vars4 m) : ((Q u.1)^(c u.2))^b u =
          Real.exp ((b u : ℝ)*(Real.log (Q u.1)*c u.2)) := by
        rw [Real.rpow_def_of_pos (hQ u.1), ← Real.exp_nat_mul]
      simp_rw [he]
      rw [← Real.exp_sum]
      congr 1
      unfold logWeight
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring

theorem expansion_support_card {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (r : Fin m → ℕ) (A : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) :
    (expansion A J P).support.card ≤ 16^(∑ h, r h) := by
  let s : Fin m → ℕ := fun h => r h - ∑ i : Fin 4, J (h,i)
  have hs : (expansion A J P).support ⊆ Finset.univ.image (@exponent4 m s) := by
    intro b hb
    have hdeg (h : Fin m) : (∑ i : Fin 4, b (h,i)) = s h :=
      expansion_block_degree r A J P hP b (MvPolynomial.mem_support_iff.mp hb) h
    have hle (h : Fin m) (i : Fin 4) : b (h,i) ≤ s h := by
      rw [← hdeg h]
      exact Finset.single_le_sum (f := fun j : Fin 4 => b (h,j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    refine Finset.mem_image.mpr ⟨fun h => ⟨fun i => ⟨b (h,i), by have := hle h i; omega⟩,hdeg h⟩,
      Finset.mem_univ _,?_⟩
    ext u
    rfl
  have hc : Fintype.card (RothAuxCoefficients s) ≤ 16^(∑ h, s h) := by
    change rothAuxDimension s ≤ _
    rw [rothAuxDimension_eq]
    calc
      _ ≤ ∏ h, 16^s h := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro h hh
        by_cases hz : s h = 0
        · simp [hz]
        · calc
            (s h+3).choose 3 ≤ 2^(s h+3) := (Nat.choose_le_two_pow _ _ (by omega)).le
            _ ≤ 2^(4*s h) := Nat.pow_le_pow_right (by decide) (by omega)
            _ = _ := by rw [pow_mul]; norm_num
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans
    (hc.trans (Nat.pow_le_pow_right (by decide) (Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)))))

end CompoundFeasibility.Auxiliary4.SourceEvaluation4
