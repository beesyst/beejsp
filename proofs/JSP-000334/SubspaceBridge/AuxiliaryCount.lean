import SubspaceBridge
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
namespace JSP000334

abbrev RothAuxBlock (r : ℕ) := {b : Fin 3 → Fin (r + 1) // ∑ i, (b i).val = r}

noncomputable def rothAuxBlockPerm (r : ℕ) (e : Equiv.Perm (Fin 3)) :
    RothAuxBlock r ≃ RothAuxBlock r where
  toFun b := ⟨fun i => b.val (e i), by
    change (∑ i, (b.val (e i)).val) = r
    exact (Equiv.sum_comp e (fun i => (b.val i).val)).trans b.property⟩
  invFun b := ⟨fun i => b.val (e.symm i), by
    change (∑ i, (b.val (e.symm i)).val) = r
    exact (Equiv.sum_comp e.symm (fun i => (b.val i).val)).trans b.property⟩
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

theorem rothAuxBlock_coordinate_sum (r : ℕ) (i : Fin 3) :
    (∑ b : RothAuxBlock r, ((b.val i).val : ℝ)) =
      ∑ b : RothAuxBlock r, ((b.val 0).val : ℝ) := by
  have h := (rothAuxBlockPerm r (Equiv.swap 0 i)).sum_comp
    (fun b : RothAuxBlock r => ((b.val 0).val : ℝ))
  simpa [rothAuxBlockPerm] using h

theorem rothAuxBlock_center_sum (r : ℕ) (hr : 0 < r) :
    (∑ b : RothAuxBlock r, (1 / 3 - ((b.val 0).val : ℝ) / r)) = 0 := by
  have htotal : (∑ b : RothAuxBlock r, ∑ i : Fin 3, ((b.val i).val : ℝ)) =
      (Fintype.card (RothAuxBlock r) : ℝ) * r := by
    calc
      _ = ∑ _b : RothAuxBlock r, (r : ℝ) := by
        apply Finset.sum_congr rfl
        intro b _
        exact_mod_cast b.property
      _ = _ := by simp
  rw [Finset.sum_comm] at htotal
  simp_rw [rothAuxBlock_coordinate_sum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  have hsum :
      (∑ b : RothAuxBlock r, ((b.val 0).val : ℝ)) =
        (Fintype.card (RothAuxBlock r) : ℝ) * r / 3 := by
    calc
      _ = (3 * (∑ b : RothAuxBlock r,
          ((b.val 0).val : ℝ))) / 3 := by ring
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          congrArg (fun x : ℝ => x / 3) htotal
  have hr' : (r : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_div, hsum]
  field_simp [hr']
  ring

theorem rothAuxBlock_center_bound (r : ℕ) (hr : 0 < r) (b : RothAuxBlock r) :
    |1 / 3 - ((b.val 0).val : ℝ) / r| ≤ 1 := by
  have hle : ((b.val 0).val : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ (b.val 0).isLt
  have hz : 0 ≤ ((b.val 0).val : ℝ) / r := by positivity
  have hu : ((b.val 0).val : ℝ) / r ≤ 1 := (div_le_one (by positivity)).mpr hle
  rw [abs_le]
  constructor <;> linarith

theorem rothAuxBlock_exp_sum (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : RothAuxBlock r, Real.exp (u * (1 / 3 - ((b.val 0).val : ℝ) / r))) ≤
      (Fintype.card (RothAuxBlock r) : ℝ) * Real.exp (u ^ 2) := by
  have hpoint (b : RothAuxBlock r) :
      Real.exp (u * (1 / 3 - ((b.val 0).val : ℝ) / r)) ≤
        1 + u * (1 / 3 - ((b.val 0).val : ℝ) / r) + u ^ 2 := by
    have hb := rothAuxBlock_center_bound r hr b
    have hmul : |u * (1 / 3 - ((b.val 0).val : ℝ) / r)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hu]
      exact (mul_le_mul_of_nonneg_left hb hu).trans (by simpa using hu')
    have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hmul)).2
    have hsq : (u * (1 / 3 - ((b.val 0).val : ℝ) / r)) ^ 2 ≤ u ^ 2 := by
      rw [mul_pow]
      have hs : (1 / 3 - ((b.val 0).val : ℝ) / r) ^ 2 ≤ 1 := by
        have hs := mul_self_le_mul_self (abs_nonneg (1 / 3 - ((b.val 0).val : ℝ) / r)) hb
        simpa only [← sq, sq_abs, one_pow] using hs
      exact (mul_le_mul_of_nonneg_left hs (sq_nonneg u)).trans_eq (mul_one _)
    linarith
  calc
    _ ≤ ∑ b : RothAuxBlock r, (1 + u * (1 / 3 - ((b.val 0).val : ℝ) / r) + u ^ 2) :=
      Finset.sum_le_sum (fun b _ => hpoint b)
    _ = (Fintype.card (RothAuxBlock r) : ℝ) * (1 + u ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, rothAuxBlock_center_sum r hr, mul_zero, add_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp (u ^ 2)) (by positivity)



noncomputable def rothAuxBlockPivotEquiv (r : ℕ) :
    RothAuxBlock r ≃ (i : Fin (r + 1)) × Fin (r - i.val + 1) where
  toFun b := ⟨b.val 0, ⟨(b.val 1).val, by
    have hb := b.property
    simp only [Fin.sum_univ_three] at hb
    omega⟩⟩
  invFun p := ⟨![p.1, ⟨p.2.val, by omega⟩,
    ⟨r - p.1.val - p.2.val, by omega⟩], by
    simp [Fin.sum_univ_three]
    have hi := p.1.isLt
    have hj := p.2.isLt
    omega⟩
  left_inv b := by
    apply Subtype.ext
    funext i
    fin_cases i <;> apply Fin.ext <;> simp
    have hb := b.property
    simp only [Fin.sum_univ_three] at hb
    omega
  right_inv p := by
    rcases p with ⟨i, j⟩
    rfl

theorem rothAuxBlock_card (r : ℕ) :
    Fintype.card (RothAuxBlock r) = (r + 2).choose 2 := by
  rw [Fintype.card_congr (rothAuxBlockPivotEquiv r), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ = ∑ i ∈ Finset.range (r + 1), (r - i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i => r - i + 1) (r + 1)
    _ = ∑ i ∈ Finset.range (r + 1), (i + 1) := by
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun i => i + 1) (r + 1)
    _ = _ := by simpa using Nat.sum_range_add_choose r 1


open scoped Classical

abbrev RothAuxCoefficients {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → RothAuxBlock (r h)

abbrev RothAuxPivots {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Fin (r h + 1)

noncomputable def rothAuxDimension {m : ℕ} (r : Fin m → ℕ) : ℕ :=
  Fintype.card (RothAuxCoefficients r)

theorem rothAuxDimension_eq {m : ℕ} (r : Fin m → ℕ) :
    rothAuxDimension r = ∏ h, (r h + 2).choose 2 := by
  simp [rothAuxDimension, Fintype.card_pi, rothAuxBlock_card]

noncomputable def rothAuxCentered {m : ℕ} (r : Fin m → ℕ) (b : RothAuxCoefficients r) : ℝ :=
  ∑ h, (1 / 3 - ((b h).val 0).val / (r h : ℝ))

abbrev RothAuxBad {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :=
  {b : RothAuxCoefficients r // eta * m < rothAuxCentered r b}

noncomputable def rothAuxPivotCondition {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (i : RothAuxPivots r) : Prop :=
  (∑ h, ((i h).val : ℝ) / r h) < (1 / 3 - eta) * m

theorem rothAux_bad_iff_pivot {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (b : RothAuxCoefficients r) :
    (eta * m < rothAuxCentered r b) ↔
      rothAuxPivotCondition r eta (fun h => (b h).val 0) := by
  unfold rothAuxCentered rothAuxPivotCondition
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  constructor <;> intro hb <;> nlinarith

noncomputable def rothAuxBadPivotEquiv {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    RothAuxBad r eta ≃
      (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}) ×
        ((h : Fin m) → Fin (r h - (i.val h).val + 1)) where
  toFun b := ⟨⟨fun h => (b.val h).val 0,
      (rothAux_bad_iff_pivot r eta b.val).mp b.property⟩,
    fun h => (rothAuxBlockPivotEquiv (r h) (b.val h)).2⟩
  invFun p := ⟨fun h => (rothAuxBlockPivotEquiv (r h)).symm ⟨p.1.val h, p.2 h⟩, by
    apply (rothAux_bad_iff_pivot r eta _).mpr
    exact p.1.property⟩
  left_inv b := by
    apply Subtype.ext
    funext h
    exact (rothAuxBlockPivotEquiv (r h)).symm_apply_apply (b.val h)
  right_inv p := by
    rcases p with ⟨⟨i, hi⟩, j⟩
    rfl

theorem rothAuxBad_card_source {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (RothAuxBad r eta) =
      ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 1) := by
  classical
  rw [Fintype.card_congr (rothAuxBadPivotEquiv r eta), Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin]


theorem rothAux_exp_moment {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) ≤
      (rothAuxDimension r : ℝ) * Real.exp ((m : ℝ) * u ^ 2) := by
  have hfactor : (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) =
      ∏ h, ∑ b : RothAuxBlock (r h),
        Real.exp (u * (1 / 3 - ((b.val 0).val : ℝ) / r h)) := by
    simp only [rothAuxCentered, Finset.mul_sum, Real.exp_sum]
    exact (Fintype.prod_sum (fun (h : Fin m) (b : RothAuxBlock (r h)) =>
      Real.exp (u * (1 / 3 - ((b.val 0).val : ℝ) / r h)))).symm
  rw [hfactor]
  calc
    _ ≤ ∏ h, ((Fintype.card (RothAuxBlock (r h)) : ℝ) * Real.exp (u ^ 2)) := by
      apply Finset.prod_le_prod
      · intro h _
        exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      · intro h _
        exact rothAuxBlock_exp_sum (r h) (hr h) u hu hu'
    _ = _ := by
      simp [Finset.prod_mul_distrib, rothAuxDimension, Fintype.card_pi,
        Nat.cast_prod, Real.exp_nat_mul]


theorem rothAux_exp_tail_parameter {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (Fintype.card (RothAuxBad r eta) : ℝ) ≤
      (rothAuxDimension r : ℝ) * Real.exp ((m : ℝ) * u ^ 2 - u * (eta * m)) := by
  have hlower : (Fintype.card (RothAuxBad r eta) : ℝ) * Real.exp (u * (eta * m)) ≤
      ∑ b : RothAuxBad r eta, Real.exp (u * rothAuxCentered r b.val) := by
    calc
      _ = ∑ _b : RothAuxBad r eta, Real.exp (u * (eta * m)) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left b.property.le hu))
  have hsub : (∑ b : RothAuxBad r eta, Real.exp (u * rothAuxCentered r b.val)) ≤
      ∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b) := by
    have hp := Fintype.sum_subtype_add_sum_subtype
      (fun b : RothAuxCoefficients r => eta * m < rothAuxCentered r b)
      (fun b => Real.exp (u * rothAuxCentered r b))
    have hn : 0 ≤ ∑ b : {b : RothAuxCoefficients r //
        ¬ eta * m < rothAuxCentered r b}, Real.exp (u * rothAuxCentered r b.val) :=
      Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    linarith
  have hb := hlower.trans (hsub.trans (rothAux_exp_moment r hr u hu hu'))
  have heq : Real.exp (u * (eta * m)) * Real.exp (-(u * (eta * m))) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ = ((Fintype.card (RothAuxBad r eta) : ℝ) * Real.exp (u * (eta * m))) *
        Real.exp (-(u * (eta * m))) := by rw [mul_assoc, heq, mul_one]
    _ ≤ ((rothAuxDimension r : ℝ) * Real.exp ((m : ℝ) * u ^ 2)) *
        Real.exp (-(u * (eta * m))) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; rfl

theorem rothAuxBad_card_zero {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) (heta : 1 / 3 ≤ eta) :
    Fintype.card (RothAuxBad r eta) = 0 := by
  have hcenter (b : RothAuxCoefficients r) : rothAuxCentered r b ≤ (m : ℝ) / 3 := by
    calc
      _ ≤ ∑ _h : Fin m, (1 / 3 : ℝ) := by
        apply Finset.sum_le_sum
        intro h _
        have hz : 0 ≤ (((b h).val 0).val : ℝ) / (r h : ℝ) := by positivity
        linarith
      _ = _ := by simp [div_eq_mul_inv]
  have hem : (m : ℝ) / 3 ≤ eta * m := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  haveI : IsEmpty (RothAuxBad r eta) := ⟨fun b =>
    (not_lt_of_ge ((hcenter b.val).trans hem)) b.property⟩
  exact Fintype.card_eq_zero

theorem rothAuxBad_exp_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta) :
    (Fintype.card (RothAuxBad r eta) : ℝ) ≤
      (rothAuxDimension r : ℝ) * Real.exp (-eta ^ 2 * m / 4) := by
  by_cases he : eta < 1 / 3
  · have hu : 0 ≤ eta / 2 := by positivity
    have hu' : eta / 2 ≤ 1 := by linarith
    have hb := rothAux_exp_tail_parameter r hr eta (eta / 2) hu hu'
    convert hb using 1 <;> congr 2 <;> ring
  · rw [rothAuxBad_card_zero r eta (le_of_not_gt he)]
    simp only [Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le


abbrev RothAuxEquations {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :=
  Fin 9 × RothAuxBad r eta

noncomputable def rothAuxConstraintCount {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) : ℕ :=
  Fintype.card (RothAuxEquations r eta)

theorem rothAuxConstraintCount_eq {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    rothAuxConstraintCount r eta = 9 * Fintype.card (RothAuxBad r eta) := by
  simp [rothAuxConstraintCount, RothAuxEquations, Fintype.card_prod]

theorem rothAuxConstraintCount_source {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    rothAuxConstraintCount r eta =
      9 * ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 1) := by
  rw [rothAuxConstraintCount_eq, rothAuxBad_card_source]

theorem rothAuxDimension_pos {m : ℕ} (r : Fin m → ℕ) : 0 < rothAuxDimension r := by
  rw [rothAuxDimension_eq]
  exact Finset.prod_pos (fun h _ => Nat.choose_pos (by omega))

theorem rothAuxConstraintCount_exp_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta) :
    (rothAuxConstraintCount r eta : ℝ) ≤
      9 * (rothAuxDimension r : ℝ) * Real.exp (-eta ^ 2 * m / 4) := by
  rw [rothAuxConstraintCount_eq, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  exact mul_le_mul_of_nonneg_left (rothAuxBad_exp_bound r hr eta heta) (by norm_num)

theorem rothAuxConstraintCount_le_half {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ)) :
    (rothAuxConstraintCount r eta : ℝ) ≤ (rothAuxDimension r : ℝ) / 2 := by
  have hs : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hmul := mul_le_mul_of_nonneg_left hm hs.le
  have hid : eta ^ 2 * (4 * (eta ^ 2)⁻¹ * Real.log 18) = 4 * Real.log 18 := by
    field_simp
  rw [hid] at hmul
  have he : Real.exp (-eta ^ 2 * m / 4) ≤ (1 / 18 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 18) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hN : 0 ≤ (rothAuxDimension r : ℝ) := Nat.cast_nonneg _
  have hb := rothAuxConstraintCount_exp_bound r hr eta heta
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 9 * (rothAuxDimension r : ℝ) by positivity)
  nlinarith

end JSP000334
