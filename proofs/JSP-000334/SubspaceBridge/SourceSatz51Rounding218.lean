import SubspaceBridge.SourceOriginalVariable10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSatz51Entry218

def roundedExponent218 (p : ℕ) (q c : ℝ) : ℤ := ⌊c*Real.log q/Real.log (p : ℝ)⌋

theorem rounded_local218 (p : ℕ) (hp : 1 < p) (q c : ℝ) (hq : 1 < q) (hc : c ≤ 0) :
    roundedExponent218 p q c ≤ 0 ∧
    q^c/(p : ℝ) < (p : ℝ)^(roundedExponent218 p q c) ∧
    (p : ℝ)^(roundedExponent218 p q c) ≤ q^c ∧
    1 ≤ q^c/(p : ℝ)^(roundedExponent218 p q c) ∧
    q^c/(p : ℝ)^(roundedExponent218 p q c) < p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hq0 : 0 < q := zero_lt_one.trans hq
  let x := c*Real.log q/Real.log (p : ℝ)
  have hx : x ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hc (Real.log_pos hq).le) (Real.log_pos hpR).le
  have he : (p : ℝ)^x = q^c := by
    rw [Real.rpow_def_of_pos hp0,Real.rpow_def_of_pos hq0]
    congr 1
    dsimp only [x]
    field_simp [(Real.log_pos hpR).ne']
    ring
  have hlo : (p : ℝ)^(roundedExponent218 p q c) ≤ q^c := by
    rw [← he,← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hpR.le (Int.floor_le x)
  have hhi : q^c < (p : ℝ)*(p : ℝ)^(roundedExponent218 p q c) := by
    calc
      _ = (p : ℝ)^x := he.symm
      _ < (p : ℝ)^((⌊x⌋ : ℝ)+1) :=
        Real.rpow_lt_rpow_of_exponent_lt hpR (Int.lt_floor_add_one x)
      _ = _ := by rw [Real.rpow_add hp0,Real.rpow_one,Real.rpow_intCast]; exact mul_comm _ _
  have hf0 : 0 < (p : ℝ)^(roundedExponent218 p q c) := zpow_pos hp0 _
  refine ⟨Int.floor_nonpos hx,(div_lt_iff₀ hp0).mpr ?_,hlo,?_,?_⟩
  · simpa only [mul_comm] using hhi
  · exact (le_div_iff₀ hf0).mpr (by simpa using hlo)
  · exact (div_lt_iff₀ hf0).mpr hhi

def roundingRatio218 (q : ℝ) (c2 c3 : Fin 10 → ℝ) : ℝ :=
  ∏ i, (q^(c2 i)/(2 : ℝ)^(roundedExponent218 2 q (c2 i))) *
    (q^(c3 i)/(3 : ℝ)^(roundedExponent218 3 q (c3 i)))

def widthScale218 (q : ℝ) (c2 c3 : Fin 10 → ℝ) : ℝ := roundingRatio218 q c2 c3 ^ ((1 : ℝ)/10)

theorem rounding_ratio_bounds218 (q : ℝ) (hq : 1 < q) (c2 c3 : Fin 10 → ℝ)
    (h2 : ∀ i, c2 i ≤ 0) (h3 : ∀ i, c3 i ≤ 0) :
    1 ≤ roundingRatio218 q c2 c3 ∧ roundingRatio218 q c2 c3 < 6^10 := by
  have hb (i : Fin 10) :
      1 ≤ (q^(c2 i)/(2 : ℝ)^(roundedExponent218 2 q (c2 i))) *
        (q^(c3 i)/(3 : ℝ)^(roundedExponent218 3 q (c3 i))) ∧
      (q^(c2 i)/(2 : ℝ)^(roundedExponent218 2 q (c2 i))) *
        (q^(c3 i)/(3 : ℝ)^(roundedExponent218 3 q (c3 i))) < 6 := by
    have ha := rounded_local218 2 (by decide) q (c2 i) hq (h2 i)
    have hb := rounded_local218 3 (by decide) q (c3 i) hq (h3 i)
    constructor
    · nlinarith [ha.2.2.2.1,hb.2.2.2.1]
    · have hm1 := mul_lt_mul_of_pos_right ha.2.2.2.2 (zero_lt_one.trans_le hb.2.2.2.1)
      have hm2 := mul_lt_mul_of_pos_left hb.2.2.2.2 (by norm_num : (0 : ℝ) < 2)
      exact hm1.trans (by norm_num at hm2 ⊢; exact hm2)
  constructor
  · have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin 10 => (1 : ℝ))
      (fun i _ => zero_le_one) (fun i _ => (hb i).1)
    simpa using h
  · have h := Finset.prod_lt_prod_of_nonempty (s := Finset.univ)
      (f := fun i => (q^(c2 i)/(2 : ℝ)^(roundedExponent218 2 q (c2 i))) *
        (q^(c3 i)/(3 : ℝ)^(roundedExponent218 3 q (c3 i))))
      (g := fun _ => (6 : ℝ)) (fun i _ => zero_lt_one.trans_le (hb i).1)
      (fun i _ => (hb i).2) Finset.univ_nonempty
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem width_scale_bounds218 (q : ℝ) (hq : 1 < q) (c2 c3 : Fin 10 → ℝ)
    (h2 : ∀ i, c2 i ≤ 0) (h3 : ∀ i, c3 i ≤ 0) :
    1 ≤ widthScale218 q c2 c3 ∧ widthScale218 q c2 c3 < 6 ∧
    0 < widthScale218 q c2 c3 ∧ (widthScale218 q c2 c3)^10 = roundingRatio218 q c2 c3 := by
  have hr := rounding_ratio_bounds218 q hq c2 c3 h2 h3
  have hr0 := zero_lt_one.trans_le hr.1
  have hlo : 1 ≤ widthScale218 q c2 c3 := Real.one_le_rpow hr.1 (by norm_num)
  have hhi := Real.rpow_lt_rpow hr0.le hr.2 (by norm_num : 0 < (1 : ℝ)/10)
  have he : ((6 : ℝ)^10)^((1 : ℝ)/10) = 6 := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  refine ⟨hlo,hhi.trans_eq he,zero_lt_one.trans_le hlo,?_⟩
  rw [widthScale218,← Real.rpow_mul_natCast hr0.le]
  norm_num

theorem corrected_width_balance218 (q : ℝ) (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ)
    (h2 : ∀ i, c2 i ≤ 0) (h3 : ∀ i, c3 i ≤ 0)
    (hbal : (∏ i, A i*q^(c2 i)*q^(c3 i)) = 1) :
    (∏ i, (widthScale218 q c2 c3*A i)*(2 : ℝ)^(roundedExponent218 2 q (c2 i))*
      (3 : ℝ)^(roundedExponent218 3 q (c3 i))) = 1 := by
  have hr := width_scale_bounds218 q hq c2 c3 h2 h3
  have he : (∏ i, A i*(2 : ℝ)^(roundedExponent218 2 q (c2 i))*
      (3 : ℝ)^(roundedExponent218 3 q (c3 i))) * roundingRatio218 q c2 c3 = 1 := by
    unfold roundingRatio218
    rw [← Finset.prod_mul_distrib]
    convert hbal using 1
    apply Finset.prod_congr rfl
    intro i _
    field_simp
    ring
  have ht : (∏ i, (widthScale218 q c2 c3*A i)*(2 : ℝ)^(roundedExponent218 2 q (c2 i))*
      (3 : ℝ)^(roundedExponent218 3 q (c3 i))) =
      (widthScale218 q c2 c3)^10 * (∏ i, A i*(2 : ℝ)^(roundedExponent218 2 q (c2 i))*
        (3 : ℝ)^(roundedExponent218 3 q (c3 i))) := by
    simp_rw [show ∀ i, (widthScale218 q c2 c3*A i)*(2 : ℝ)^(roundedExponent218 2 q (c2 i))*
      (3 : ℝ)^(roundedExponent218 3 q (c3 i)) = widthScale218 q c2 c3*
      (A i*(2 : ℝ)^(roundedExponent218 2 q (c2 i))*(3 : ℝ)^(roundedExponent218 3 q (c3 i))) from fun i => by ring]
    rw [Finset.prod_mul_distrib]
    simp
  rw [ht,hr.2.2.2,mul_comm]
  exact he

end CompoundFeasibility.SourceSatz51Entry218
