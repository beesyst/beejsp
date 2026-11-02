import SubspaceBridge.BinaryAuxMatrix2
import Mathlib.NumberTheory.SiegelsLemma
open scoped BigOperators Classical
attribute [local instance] Matrix.seminormedAddCommGroup
namespace JSP000334

theorem binary_dimension_pow_bound {m : ℕ} (r : Fin m → ℕ) :
    Fintype.card (BinaryAuxCoefficients r) ≤ 2^(∑ h, r h) := by
  have hb (n : ℕ) : n+1 ≤ 2^n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  rw [binary_aux_dimension]
  calc
    _ ≤ ∏ h, 2^r h := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun h _ => hb (r h))
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem binary_matrix_norm_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ‖binaryAuxMatrix r eta L hL‖ ≤ ((2*binaryAuxSourceHeight L)^(∑ h, r h) : ℕ) := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro q b
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  exact_mod_cast binary_matrix_entry_bound r eta L hL q b

theorem binary_siegel_base_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    (Fintype.card (BinaryAuxCoefficients r) : ℝ)*max 1 ‖binaryAuxMatrix r eta L hL‖ ≤
      ((4*binaryAuxSourceHeight L)^(∑ h, r h) : ℕ) := by
  have hA := binary_source_height_one_le L
  have hone : 1 ≤ ((2*binaryAuxSourceHeight L)^(∑ h, r h) : ℕ) := one_le_pow₀ (by omega)
  have hmax : max 1 ‖binaryAuxMatrix r eta L hL‖ ≤
      ((2*binaryAuxSourceHeight L)^(∑ h, r h) : ℕ) :=
    max_le (by exact_mod_cast hone) (binary_matrix_norm_bound r eta L hL)
  have hdim : (Fintype.card (BinaryAuxCoefficients r) : ℝ) ≤ (2 : ℝ)^(∑ h, r h) := by
    exact_mod_cast binary_dimension_pow_bound r
  calc
    _ ≤ (2 : ℝ)^(∑ h, r h)*((2*binaryAuxSourceHeight L)^(∑ h, r h) : ℕ) :=
      mul_le_mul hdim hmax (by positivity) (by positivity)
    _ = _ := by push_cast; rw [← mul_pow]; congr 1; ring

theorem binary_bounded_integer_kernel {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta < 1/2)
    (hm : 4*(eta^2)⁻¹*Real.log 12 ≤ (m : ℝ))
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ∃ c : BinaryAuxCoefficients r → ℤ, c ≠ 0 ∧ (binaryAuxMatrix r eta L hL).mulVec c = 0 ∧
      ∀ b, |c b| ≤ (4*(binaryAuxSourceHeight L : ℤ))^(∑ h, r h) := by
  have hhalf := binary_aux_six_le_half r hr eta heta heta1 hm
  have hlt := (binary_aux_strict_surplus r hr eta heta heta1 hm).2
  haveI : Nonempty (BinaryAuxCoefficients r) := ⟨fun _ => 0⟩
  have hN : 0 < Fintype.card (BinaryAuxCoefficients r) := Fintype.card_pos
  have hbudget : (1 : ℤ) ≤ (4*(binaryAuxSourceHeight L : ℤ))^(∑ h, r h) := by
    apply one_le_pow₀
    have hh := binary_source_height_one_le L
    exact_mod_cast (show 1 ≤ 4*binaryAuxSourceHeight L by omega)
  by_cases hM : Fintype.card (BinaryAuxEquations r eta) = 0
  · let b0 : BinaryAuxCoefficients r := fun _ => 0
    let c : BinaryAuxCoefficients r → ℤ := fun b => if b=b0 then 1 else 0
    refine ⟨c,?_,?_,?_⟩
    · intro hc
      have hh := congrFun hc b0
      simp [c] at hh
    · funext q
      have hh : 0 < Fintype.card (BinaryAuxEquations r eta) :=
        Fintype.card_pos_iff.mpr ⟨q⟩
      omega
    · intro b
      dsimp [c]
      split_ifs
      · simpa using hbudget
      · exact (by simpa using (le_trans zero_le_one hbudget))
  · obtain ⟨c,hc,hker,hnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le
      (binaryAuxMatrix r eta L hL) hlt (Nat.pos_of_ne_zero hM)
    refine ⟨c,hc,hker,?_⟩
    have hlt' : (Fintype.card (BinaryAuxEquations r eta) : ℝ) <
        Fintype.card (BinaryAuxCoefficients r) := by exact_mod_cast hlt
    have he : (Fintype.card (BinaryAuxEquations r eta) : ℝ) /
        ((Fintype.card (BinaryAuxCoefficients r) : ℝ)-Fintype.card (BinaryAuxEquations r eta)) ≤ 1 := by
      apply (div_le_one (sub_pos.mpr hlt')).mpr
      linarith
    have hb : 1 ≤ (Fintype.card (BinaryAuxCoefficients r) : ℝ)*max 1 ‖binaryAuxMatrix r eta L hL‖ := by
      have hn : (1 : ℝ) ≤ Fintype.card (BinaryAuxCoefficients r) := by exact_mod_cast hN
      nlinarith [le_max_left (1 : ℝ) ‖binaryAuxMatrix r eta L hL‖]
    have hbound := hnorm.trans ((Real.rpow_le_self_of_one_le hb he).trans (binary_siegel_base_bound r eta L hL))
    intro b
    have hh := (norm_le_pi_norm c b).trans hbound
    rw [Int.norm_eq_abs,← Int.cast_abs] at hh
    exact_mod_cast hh

noncomputable def binaryPolynomialHeight {m : ℕ} (P : MvPolynomial (RothBlockVars2 m) ℤ) : ℕ :=
  P.support.sup (fun e => (P.coeff e).natAbs)

theorem binary_polynomial_height_bound {m : ℕ} {r : Fin m → ℕ}
    (c : BinaryAuxCoefficients r → ℤ) (H : ℕ) (hc : ∀ b, (c b).natAbs ≤ H) :
    binaryPolynomialHeight (binaryAuxPolynomial c) ≤ H := by
  apply Finset.sup_le
  intro e he
  obtain ⟨b,hb⟩ := binary_polynomial_support c e he
  rw [← hb,binary_polynomial_coeff]
  exact hc b

theorem binary_auxiliary_coefficient_kernel
    (L : Fin 3 → Fin 2 → Fin 2 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ eta : ℝ, 0 < eta → eta < 1/2 →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log 12 ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ c : BinaryAuxCoefficients r → ℤ,
        c ≠ 0 ∧ (binaryAuxMatrix r eta L hL).mulVec c = 0 ∧
        binaryAuxPolynomial c ≠ 0 ∧ binaryBlockHomogeneous r (binaryAuxPolynomial c) ∧
        (binaryPolynomialHeight (binaryAuxPolynomial c) : ℝ) ≤ D^(∑ h, r h) := by
  refine ⟨4*(binaryAuxSourceHeight L : ℝ),?_,?_⟩
  · have hh : (1 : ℝ) ≤ binaryAuxSourceHeight L := by exact_mod_cast binary_source_height_one_le L
    linarith
  · intro eta heta heta1 m hm r hr
    obtain ⟨c,hc,hker,hbound⟩ := binary_bounded_integer_kernel r hr eta heta heta1 hm L hL
    refine ⟨c,hc,hker,binary_polynomial_ne_zero c hc,binary_polynomial_homogeneous c,?_⟩
    have hn : ∀ b, (c b).natAbs ≤ (4*binaryAuxSourceHeight L)^(∑ h, r h) := by
      intro b
      have hh := hbound b
      rw [← Int.natCast_natAbs] at hh
      exact_mod_cast hh
    exact_mod_cast binary_polynomial_height_bound c _ hn

end JSP000334
