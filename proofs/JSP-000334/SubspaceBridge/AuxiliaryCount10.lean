import SubspaceBridge.SourceMultiblock10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10

abbrev Block10 (r : ℕ) := {b : Fin 10 → Fin (r + 1) // ∑ i, (b i).val = r}

def blockNatEquiv10 (r : ℕ) : Block10 r ≃ {b : Fin 10 → ℕ // ∑ i, b i = r} where
  toFun b := ⟨fun i => (b.val i).val,b.property⟩
  invFun b := ⟨fun i => ⟨b.val i,by
    have hh : b.val i ≤ ∑ j, b.val j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [b.property] at hh
    omega⟩,b.property⟩
  left_inv b := by rfl
  right_inv b := by rfl

theorem block10_card (r : ℕ) : Fintype.card (Block10 r) = (r + 9).choose 9 := by
  letI : Fintype {b : Fin 10 → ℕ // ∑ i, b i = r} := Fintype.ofEquiv (Sym (Fin 10) r) (Sym.equivNatSumOfFintype (Fin 10) r)
  rw [Fintype.card_congr (blockNatEquiv10 r),← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin 10) r),Sym.card_sym_eq_choose]
  simpa only [Fintype.card_fin,show 10 + r - 1 = r + 9 by omega] using (Nat.choose_symm_add (a := r) (b := 9))

noncomputable def rothAuxBlockPerm (r : ℕ) (e : Equiv.Perm (Fin 10)) :
    Block10 r ≃ Block10 r where
  toFun b := ⟨fun i => b.val (e i), by
    change (∑ i, (b.val (e i)).val) = r
    exact (Equiv.sum_comp e (fun i => (b.val i).val)).trans b.property⟩
  invFun b := ⟨fun i => b.val (e.symm i), by
    change (∑ i, (b.val (e.symm i)).val) = r
    exact (Equiv.sum_comp e.symm (fun i => (b.val i).val)).trans b.property⟩
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

theorem rothAuxBlock_coordinate_sum (r : ℕ) (i : Fin 10) :
    (∑ b : Block10 r, ((b.val i).val : ℝ)) =
      ∑ b : Block10 r, ((b.val 0).val : ℝ) := by
  have h := (rothAuxBlockPerm r (Equiv.swap 0 i)).sum_comp
    (fun b : Block10 r => ((b.val 0).val : ℝ))
  simpa [rothAuxBlockPerm] using h

theorem rothAuxBlock_center_sum (r : ℕ) (hr : 0 < r) :
    (∑ b : Block10 r, (1 / 10 - ((b.val 0).val : ℝ) / r)) = 0 := by
  have htotal : (∑ b : Block10 r, ∑ i : Fin 10, ((b.val i).val : ℝ)) =
      (Fintype.card (Block10 r) : ℝ) * r := by
    calc
      _ = ∑ _b : Block10 r, (r : ℝ) := by
        apply Finset.sum_congr rfl
        intro b _
        exact_mod_cast b.property
      _ = _ := by simp
  rw [Finset.sum_comm] at htotal
  simp_rw [rothAuxBlock_coordinate_sum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  have hsum :
      (∑ b : Block10 r, ((b.val 0).val : ℝ)) =
        (Fintype.card (Block10 r) : ℝ) * r / 10 := by
    calc
      _ = (10 * (∑ b : Block10 r,
          ((b.val 0).val : ℝ))) / 10 := by ring
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          congrArg (fun x : ℝ => x / 10) htotal
  have hr' : (r : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_div, hsum]
  field_simp [hr']
  ring

theorem rothAuxBlock_center_bound (r : ℕ) (hr : 0 < r) (b : Block10 r) :
    |1 / 10 - ((b.val 0).val : ℝ) / r| ≤ 1 := by
  have hle : ((b.val 0).val : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ (b.val 0).isLt
  have hz : 0 ≤ ((b.val 0).val : ℝ) / r := by positivity
  have hu : ((b.val 0).val : ℝ) / r ≤ 1 := (div_le_one (by positivity)).mpr hle
  rw [abs_le]
  constructor <;> linarith

theorem rothAuxBlock_exp_sum (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : Block10 r, Real.exp (u * (1 / 10 - ((b.val 0).val : ℝ) / r))) ≤
      (Fintype.card (Block10 r) : ℝ) * Real.exp (u ^ 2) := by
  have hpoint (b : Block10 r) :
      Real.exp (u * (1 / 10 - ((b.val 0).val : ℝ) / r)) ≤
        1 + u * (1 / 10 - ((b.val 0).val : ℝ) / r) + u ^ 2 := by
    have hb := rothAuxBlock_center_bound r hr b
    have hmul : |u * (1 / 10 - ((b.val 0).val : ℝ) / r)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hu]
      exact (mul_le_mul_of_nonneg_left hb hu).trans (by simpa using hu')
    have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hmul)).2
    have hsq : (u * (1 / 10 - ((b.val 0).val : ℝ) / r)) ^ 2 ≤ u ^ 2 := by
      rw [mul_pow]
      have hs : (1 / 10 - ((b.val 0).val : ℝ) / r) ^ 2 ≤ 1 := by
        have hs := mul_self_le_mul_self (abs_nonneg (1 / 10 - ((b.val 0).val : ℝ) / r)) hb
        simpa only [← sq, sq_abs, one_pow] using hs
      exact (mul_le_mul_of_nonneg_left hs (sq_nonneg u)).trans_eq (mul_one _)
    linarith
  calc
    _ ≤ ∑ b : Block10 r, (1 + u * (1 / 10 - ((b.val 0).val : ℝ) / r) + u ^ 2) :=
      Finset.sum_le_sum (fun b _ => hpoint b)
    _ = (Fintype.card (Block10 r) : ℝ) * (1 + u ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, rothAuxBlock_center_sum r hr, mul_zero, add_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp (u ^ 2)) (by positivity)



open scoped Classical

abbrev RothAuxCoefficients {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Block10 (r h)

abbrev RothAuxPivots {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Fin (r h + 1)

noncomputable def rothAuxDimension {m : ℕ} (r : Fin m → ℕ) : ℕ :=
  Fintype.card (RothAuxCoefficients r)

theorem rothAuxDimension_eq {m : ℕ} (r : Fin m → ℕ) :
    rothAuxDimension r = ∏ h, (r h + 9).choose 9 := by
  simp [rothAuxDimension, Fintype.card_pi, block10_card]

noncomputable def rothAuxCentered {m : ℕ} (r : Fin m → ℕ) (b : RothAuxCoefficients r) : ℝ :=
  ∑ h, (1 / 10 - ((b h).val 0).val / (r h : ℝ))

abbrev RothAuxBad {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :=
  {b : RothAuxCoefficients r // eta * m < rothAuxCentered r b}

noncomputable def rothAuxPivotCondition {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (i : RothAuxPivots r) : Prop :=
  (∑ h, ((i h).val : ℝ) / r h) < (1 / 10 - eta) * m

theorem rothAux_exp_moment {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) ≤
      (rothAuxDimension r : ℝ) * Real.exp ((m : ℝ) * u ^ 2) := by
  have hfactor : (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) =
      ∏ h, ∑ b : Block10 (r h),
        Real.exp (u * (1 / 10 - ((b.val 0).val : ℝ) / r h)) := by
    simp only [rothAuxCentered, Finset.mul_sum, Real.exp_sum]
    exact (Fintype.prod_sum (fun (h : Fin m) (b : Block10 (r h)) =>
      Real.exp (u * (1 / 10 - ((b.val 0).val : ℝ) / r h)))).symm
  rw [hfactor]
  calc
    _ ≤ ∏ h, ((Fintype.card (Block10 (r h)) : ℝ) * Real.exp (u ^ 2)) := by
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

theorem rothAuxBad_card_zero {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) (heta : 1 / 10 ≤ eta) :
    Fintype.card (RothAuxBad r eta) = 0 := by
  have hcenter (b : RothAuxCoefficients r) : rothAuxCentered r b ≤ (m : ℝ) / 10 := by
    calc
      _ ≤ ∑ _h : Fin m, (1 / 10 : ℝ) := by
        apply Finset.sum_le_sum
        intro h _
        have hz : 0 ≤ (((b h).val 0).val : ℝ) / (r h : ℝ) := by positivity
        linarith
      _ = _ := by simp [div_eq_mul_inv]
  have hem : (m : ℝ) / 10 ≤ eta * m := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  haveI : IsEmpty (RothAuxBad r eta) := ⟨fun b =>
    (not_lt_of_ge ((hcenter b.val).trans hem)) b.property⟩
  exact Fintype.card_eq_zero

theorem rothAuxBad_exp_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta) :
    (Fintype.card (RothAuxBad r eta) : ℝ) ≤
      (rothAuxDimension r : ℝ) * Real.exp (-eta ^ 2 * m / 4) := by
  by_cases he : eta < 1 / 10
  · have hu : 0 ≤ eta / 2 := by positivity
    have hu' : eta / 2 ≤ 1 := by linarith
    have hb := rothAux_exp_tail_parameter r hr eta (eta / 2) hu hu'
    convert hb using 1 <;> congr 2 <;> ring
  · rw [rothAuxBad_card_zero r eta (le_of_not_gt he)]
    simp only [Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le




abbrev Equations10 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) := Fin 30 × RothAuxBad r eta

theorem dimension10_pos {m : ℕ} (r : Fin m → ℕ) : 0 < rothAuxDimension r := by
  rw [rothAuxDimension_eq]
  exact Finset.prod_pos (fun h _ => Nat.choose_pos (by omega))

theorem coordinate_rows10_le_half {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (d : ℕ) (hd : 0 < d)
    (hm : 4 * (eta^2)⁻¹ * Real.log (60 * (d : ℝ)) ≤ (m : ℝ)) :
    (d * Fintype.card (Equations10 r eta) : ℝ) ≤ (rothAuxDimension r : ℝ) / 2 := by
  have hs : 0 < eta^2 := sq_pos_of_pos heta
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_left hm hs.le
  have hid : eta^2 * (4 * (eta^2)⁻¹ * Real.log (60 * (d : ℝ))) = 4 * Real.log (60 * (d : ℝ)) := by field_simp
  rw [hid] at hmul
  have he : Real.exp (-eta^2 * m / 4) ≤ 1 / (60 * (d : ℝ)) := by
    calc
      _ ≤ Real.exp (-Real.log (60 * (d : ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity),one_div]
  have hb := mul_le_mul_of_nonneg_left (rothAuxBad_exp_bound r hr eta heta) (show (0 : ℝ) ≤ 30 * d by positivity)
  calc
    _ = (30 * (d : ℝ)) * (Fintype.card (RothAuxBad r eta) : ℝ) := by simp only [Equations10,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]; ring
    _ ≤ (30 * (d : ℝ)) * ((rothAuxDimension r : ℝ) * Real.exp (-eta^2 * m / 4)) := hb
    _ ≤ (30 * (d : ℝ)) * ((rothAuxDimension r : ℝ) * (1 / (60 * (d : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by field_simp; ring

theorem coordinate_rows10_lt {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (d : ℕ) (hd : 0 < d)
    (hm : 4 * (eta^2)⁻¹ * Real.log (60 * (d : ℝ)) ≤ (m : ℝ)) :
    d * Fintype.card (Equations10 r eta) < rothAuxDimension r := by
  have hh := coordinate_rows10_le_half r hr eta heta d hd hm
  have hp : (0 : ℝ) < rothAuxDimension r := by exact_mod_cast dimension10_pos r
  exact_mod_cast (show (d * Fintype.card (Equations10 r eta) : ℝ) < (rothAuxDimension r : ℝ) by linarith)

abbrev Block9 (r : ℕ) := {b : Fin 9 → Fin (r + 1) // ∑ i, (b i).val = r}

def blockNatEquiv9 (r : ℕ) : Block9 r ≃ {b : Fin 9 → ℕ // ∑ i, b i = r} where
  toFun b := ⟨fun i => (b.val i).val,b.property⟩
  invFun b := ⟨fun i => ⟨b.val i,by
    have hh : b.val i ≤ ∑ j, b.val j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [b.property] at hh
    omega⟩,b.property⟩
  left_inv b := by rfl
  right_inv b := by rfl

theorem block9_card (r : ℕ) : Fintype.card (Block9 r) = (r + 8).choose 8 := by
  letI : Fintype {b : Fin 9 → ℕ // ∑ i, b i = r} := Fintype.ofEquiv (Sym (Fin 9) r) (Sym.equivNatSumOfFintype (Fin 9) r)
  rw [Fintype.card_congr (blockNatEquiv9 r),← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin 9) r),Sym.card_sym_eq_choose]
  simpa only [Fintype.card_fin,show 9 + r - 1 = r + 8 by omega] using (Nat.choose_symm_add (a := r) (b := 8))

def blockPivotEquiv10 (r : ℕ) : Block10 r ≃ (i : Fin (r+1)) × Block9 (r-i.val) where
  toFun b := ⟨b.val 0,⟨fun j => ⟨(b.val j.succ).val,by
    have hs := b.property
    rw [Fin.sum_univ_succ] at hs
    have hj : (b.val j.succ).val ≤ ∑ k : Fin 9, (b.val k.succ).val :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 9 => (b.val k.succ).val) (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    omega⟩,by
      have hs := b.property
      rw [Fin.sum_univ_succ] at hs
      change (∑ j : Fin 9, (b.val j.succ).val) = r - (b.val 0).val
      omega⟩⟩
  invFun p := ⟨Fin.cons p.1 (fun j => ⟨(p.2.val j).val,by
    have hh := (p.2.val j).isLt
    omega⟩),by
      rw [Fin.sum_univ_succ]
      change p.1.val + (∑ j : Fin 9, (p.2.val j).val) = r
      rw [p.2.property]
      omega⟩
  left_inv b := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  right_inv p := by
    rcases p with ⟨i,b⟩
    rfl

theorem bad_iff_pivot6 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (b : RothAuxCoefficients r) :
    (eta * m < rothAuxCentered r b) ↔
      rothAuxPivotCondition r eta (fun h => (b h).val 0) := by
  unfold rothAuxCentered rothAuxPivotCondition
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  constructor <;> intro hb <;> nlinarith

def badPivotEquiv4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    RothAuxBad r eta ≃
      (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}) ×
        ((h : Fin m) → Block9 (r h - (i.val h).val)) where
  toFun b := ⟨⟨fun h => (b.val h).val 0,(bad_iff_pivot6 r eta b.val).mp b.property⟩,
    fun h => (blockPivotEquiv10 (r h) (b.val h)).2⟩
  invFun p := ⟨fun h => (blockPivotEquiv10 (r h)).symm ⟨p.1.val h,p.2 h⟩,by
    apply (bad_iff_pivot6 r eta _).mpr
    exact p.1.property⟩
  left_inv b := by
    apply Subtype.ext
    funext h
    exact (blockPivotEquiv10 (r h)).symm_apply_apply (b.val h)
  right_inv p := by
    rcases p with ⟨⟨i,hi⟩,j⟩
    rfl

theorem bad_count_source10 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (RothAuxBad r eta) =
      ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 8).choose 8 := by
  rw [Fintype.card_congr (badPivotEquiv4 r eta),Fintype.card_sigma]
  simp only [Fintype.card_pi,block9_card]

theorem constraint_count_source10 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (Equations10 r eta) = 30 *
      ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 8).choose 8 := by
  simp only [Equations10,Fintype.card_prod,Fintype.card_fin,bad_count_source10]





end CompoundFeasibility.Auxiliary10
