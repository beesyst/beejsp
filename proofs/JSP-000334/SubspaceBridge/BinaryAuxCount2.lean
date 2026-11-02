import SubspaceBridge
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Fin.Rev
open scoped BigOperators Classical
namespace JSP000334

abbrev BinaryAuxCoefficients {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Fin (r h + 1)

noncomputable def binaryAuxCentered {m : ℕ} (r : Fin m → ℕ) (b : BinaryAuxCoefficients r) : ℝ :=
  ∑ h, (1/2 - ((b h).val : ℝ)/(r h : ℝ))

abbrev BinaryAuxBad {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :=
  {b : BinaryAuxCoefficients r // eta*m < binaryAuxCentered r b}

abbrev BinaryAuxEquations {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :=
  (Fin 3 × Fin 2) × BinaryAuxBad r eta

theorem binary_aux_dimension {m : ℕ} (r : Fin m → ℕ) :
    Fintype.card (BinaryAuxCoefficients r) = ∏ h, (r h+1) := by
  simp [Fintype.card_pi]

theorem binary_aux_bad_iff {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) (b : BinaryAuxCoefficients r) :
    eta*m < binaryAuxCentered r b ↔
      (∑ h, ((b h).val : ℝ)/(r h : ℝ)) < (1/2-eta)*m := by
  unfold binaryAuxCentered
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  constructor <;> intro h <;> nlinarith

theorem binary_block_center_sum (r : ℕ) (hr : 0 < r) :
    (∑ j : Fin (r+1), (1/2 - (j.val : ℝ)/(r : ℝ))) = 0 := by
  have hrev (j : Fin (r+1)) :
      (1/2 - (j.rev.val : ℝ)/(r : ℝ)) = -(1/2 - (j.val : ℝ)/(r : ℝ)) := by
    have hj : j.val ≤ r := by omega
    have hc : (j.rev.val : ℝ) = (r : ℝ) - (j.val : ℝ) := by
      have hn : j.rev.val+j.val = r := by rw [Fin.val_rev]; omega
      have hc := congrArg ((↑) : ℕ → ℝ) hn
      push_cast at hc
      linarith
    rw [hc]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    field_simp [hr0]
    <;> ring
  have hp := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (r+1)))
    (fun j : Fin (r+1) => (1/2 - (j.val : ℝ)/(r : ℝ)))
  change (∑ j : Fin (r+1), (1/2-(j.rev.val : ℝ)/(r : ℝ))) = _ at hp
  simp_rw [hrev] at hp
  rw [Finset.sum_neg_distrib] at hp
  linarith

theorem binary_block_exp_sum (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ j : Fin (r+1), Real.exp (u*(1/2-(j.val : ℝ)/(r : ℝ)))) ≤
      ((r+1 : ℕ) : ℝ)*Real.exp (u^2) := by
  have hpoint (j : Fin (r+1)) : Real.exp (u*(1/2-(j.val : ℝ)/(r : ℝ))) ≤
      1+u*(1/2-(j.val : ℝ)/(r : ℝ))+u^2 := by
    have h0 : 0 ≤ (j.val : ℝ)/(r : ℝ) := by positivity
    have h1 : (j.val : ℝ)/(r : ℝ) ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hr)).mpr
      exact_mod_cast (show j.val ≤ r by omega)
    have hb : |1/2-(j.val : ℝ)/(r : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hm : |u*(1/2-(j.val : ℝ)/(r : ℝ))| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hu]
      exact (mul_le_mul_of_nonneg_left hb hu).trans (by simpa using hu1)
    have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hm)).2
    have hs : (u*(1/2-(j.val : ℝ)/(r : ℝ)))^2 ≤ u^2 := by
      rw [mul_pow]
      have hc : (1/2-(j.val : ℝ)/(r : ℝ))^2 ≤ 1 := by
        nlinarith [sq_nonneg (1/2-(j.val : ℝ)/(r : ℝ))]
      nlinarith [sq_nonneg u]
    linarith
  calc
    _ ≤ ∑ j : Fin (r+1), (1+u*(1/2-(j.val : ℝ)/(r : ℝ))+u^2) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = ((r+1 : ℕ) : ℝ)*(1+u^2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, binary_block_center_sum r hr, mul_zero, add_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [add_comm] using Real.add_one_le_exp (u^2)) (by positivity)

noncomputable def binaryBlockEquiv (r : ℕ) :
    Fin (r+1) ≃ {b : Fin 2 → Fin (r+1) // ∑ j, (b j).val = r} where
  toFun i := ⟨![i, ⟨r-i.val, by omega⟩], by simp [Fin.sum_univ_two]; omega⟩
  invFun b := b.val 0
  left_inv i := rfl
  right_inv b := by
    apply Subtype.ext
    funext j
    fin_cases j
    · rfl
    · apply Fin.ext
      have hb := b.property
      simp only [Fin.sum_univ_two] at hb
      change r-(b.val 0).val = (b.val 1).val
      omega

theorem binary_block_dimension (r : ℕ) :
    Fintype.card {b : Fin 2 → Fin (r+1) // ∑ j, (b j).val = r} = r+1 := by
  rw [← Fintype.card_congr (binaryBlockEquiv r), Fintype.card_fin]

theorem binary_aux_exp_moment {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ b : BinaryAuxCoefficients r, Real.exp (u*binaryAuxCentered r b)) ≤
      (Fintype.card (BinaryAuxCoefficients r) : ℝ)*Real.exp ((m : ℝ)*u^2) := by
  have hf : (∑ b : BinaryAuxCoefficients r, Real.exp (u*binaryAuxCentered r b)) =
      ∏ h, ∑ j : Fin (r h+1), Real.exp (u*(1/2-(j.val : ℝ)/(r h : ℝ))) := by
    simp only [binaryAuxCentered, Finset.mul_sum, Real.exp_sum]
    exact (Fintype.prod_sum (fun h (j : Fin (r h+1)) =>
      Real.exp (u*(1/2-(j.val : ℝ)/(r h : ℝ))))).symm
  rw [hf]
  calc
    _ ≤ ∏ h, (((r h+1 : ℕ) : ℝ)*Real.exp (u^2)) := by
      apply Finset.prod_le_prod
      · intro h _
        exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      · intro h _
        exact binary_block_exp_sum (r h) (hr h) u hu hu1
    _ = _ := by
      simp [Finset.prod_mul_distrib, Fintype.card_pi, Nat.cast_prod, Real.exp_nat_mul]

theorem binary_aux_bad_bound {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta < 1/2) :
    (Fintype.card (BinaryAuxBad r eta) : ℝ) ≤
      (Fintype.card (BinaryAuxCoefficients r) : ℝ)*Real.exp (-eta^2*m/4) := by
  let u := eta/2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hlo : (Fintype.card (BinaryAuxBad r eta) : ℝ)*Real.exp (u*(eta*m)) ≤
      ∑ b : BinaryAuxBad r eta, Real.exp (u*binaryAuxCentered r b.val) := by
    calc
      _ = ∑ _b : BinaryAuxBad r eta, Real.exp (u*(eta*m)) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left b.property.le hu))
  have hsub : (∑ b : BinaryAuxBad r eta, Real.exp (u*binaryAuxCentered r b.val)) ≤
      ∑ b : BinaryAuxCoefficients r, Real.exp (u*binaryAuxCentered r b) := by
    have hh := Fintype.sum_subtype_add_sum_subtype
      (fun b : BinaryAuxCoefficients r => eta*m < binaryAuxCentered r b)
      (fun b => Real.exp (u*binaryAuxCentered r b))
    have hn : 0 ≤ ∑ b : {b : BinaryAuxCoefficients r // ¬ eta*m < binaryAuxCentered r b},
        Real.exp (u*binaryAuxCentered r b.val) :=
      Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    linarith
  have hb := hlo.trans (hsub.trans (binary_aux_exp_moment r hr u hu hu1))
  have hout := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(u*(eta*m)))).le
  have he : Real.exp (u*(eta*m))*Real.exp (-(u*(eta*m))) = 1 := by
    rw [← Real.exp_add]; simp
  rw [mul_assoc, he, mul_one, mul_assoc, ← Real.exp_add] at hout
  convert hout using 1 <;> congr 2 <;> dsimp [u] <;> ring

theorem binary_aux_six_count {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (BinaryAuxEquations r eta) = 6*Fintype.card (BinaryAuxBad r eta) := by
  simp [BinaryAuxEquations, Fintype.card_prod]

theorem binary_aux_six_le_half {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta < 1/2)
    (hm : 4*(eta^2)⁻¹*Real.log 12 ≤ (m : ℝ)) :
    (Fintype.card (BinaryAuxEquations r eta) : ℝ) ≤
      (Fintype.card (BinaryAuxCoefficients r) : ℝ)/2 := by
  have hs : 0 < eta^2 := sq_pos_of_pos heta
  have hh := mul_le_mul_of_nonneg_left hm hs.le
  have hid : eta^2*(4*(eta^2)⁻¹*Real.log 12) = 4*Real.log 12 := by field_simp
  rw [hid] at hh
  have he : Real.exp (-eta^2*m/4) ≤ (1/12 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 12) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hbad := binary_aux_bad_bound r hr eta heta heta1
  have hn : 0 ≤ (Fintype.card (BinaryAuxCoefficients r) : ℝ) := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_left he hn
  rw [binary_aux_six_count, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem binary_aux_strict_surplus {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta < 1/2)
    (hm : 4*(eta^2)⁻¹*Real.log 12 ≤ (m : ℝ)) :
    2*Fintype.card (BinaryAuxEquations r eta) ≤ Fintype.card (BinaryAuxCoefficients r) ∧
      Fintype.card (BinaryAuxEquations r eta) < Fintype.card (BinaryAuxCoefficients r) := by
  have hh := binary_aux_six_le_half r hr eta heta heta1 hm
  haveI : Nonempty (BinaryAuxCoefficients r) := ⟨fun _ => 0⟩
  have hn : 0 < Fintype.card (BinaryAuxCoefficients r) := Fintype.card_pos
  have hn' : (0 : ℝ) < Fintype.card (BinaryAuxCoefficients r) := by exact_mod_cast hn
  constructor
  · exact_mod_cast (show (2 : ℝ)*Fintype.card (BinaryAuxEquations r eta) ≤
      Fintype.card (BinaryAuxCoefficients r) by linarith)
  · exact_mod_cast (show (Fintype.card (BinaryAuxEquations r eta) : ℝ) <
      Fintype.card (BinaryAuxCoefficients r) by linarith)

end JSP000334
