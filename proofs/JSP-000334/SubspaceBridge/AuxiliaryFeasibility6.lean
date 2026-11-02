import Mathlib.Analysis.Matrix
import Mathlib.Algebra.MvPolynomial.PDeriv
import SubspaceBridge.AlgebraicLiouville6
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary6


abbrev Block6 (r : ℕ) := {b : Fin 6 → Fin (r + 1) // ∑ i, (b i).val = r}

def blockNatEquiv6 (r : ℕ) : Block6 r ≃ {b : Fin 6 → ℕ // ∑ i, b i = r} where
  toFun b := ⟨fun i => (b.val i).val,b.property⟩
  invFun b := ⟨fun i => ⟨b.val i,by
    have hh : b.val i ≤ ∑ j, b.val j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [b.property] at hh
    omega⟩,b.property⟩
  left_inv b := by rfl
  right_inv b := by rfl

theorem block6_card (r : ℕ) : Fintype.card (Block6 r) = (r + 5).choose 5 := by
  letI : Fintype {b : Fin 6 → ℕ // ∑ i, b i = r} := Fintype.ofEquiv (Sym (Fin 6) r) (Sym.equivNatSumOfFintype (Fin 6) r)
  rw [Fintype.card_congr (blockNatEquiv6 r),← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin 6) r),Sym.card_sym_eq_choose]
  simpa only [Fintype.card_fin,show 6 + r - 1 = r + 5 by omega] using (Nat.choose_symm_add (a := r) (b := 5))

noncomputable def rothAuxBlockPerm (r : ℕ) (e : Equiv.Perm (Fin 6)) :
    Block6 r ≃ Block6 r where
  toFun b := ⟨fun i => b.val (e i), by
    change (∑ i, (b.val (e i)).val) = r
    exact (Equiv.sum_comp e (fun i => (b.val i).val)).trans b.property⟩
  invFun b := ⟨fun i => b.val (e.symm i), by
    change (∑ i, (b.val (e.symm i)).val) = r
    exact (Equiv.sum_comp e.symm (fun i => (b.val i).val)).trans b.property⟩
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

theorem rothAuxBlock_coordinate_sum (r : ℕ) (i : Fin 6) :
    (∑ b : Block6 r, ((b.val i).val : ℝ)) =
      ∑ b : Block6 r, ((b.val 0).val : ℝ) := by
  have h := (rothAuxBlockPerm r (Equiv.swap 0 i)).sum_comp
    (fun b : Block6 r => ((b.val 0).val : ℝ))
  simpa [rothAuxBlockPerm] using h

theorem rothAuxBlock_center_sum (r : ℕ) (hr : 0 < r) :
    (∑ b : Block6 r, (1 / 6 - ((b.val 0).val : ℝ) / r)) = 0 := by
  have htotal : (∑ b : Block6 r, ∑ i : Fin 6, ((b.val i).val : ℝ)) =
      (Fintype.card (Block6 r) : ℝ) * r := by
    calc
      _ = ∑ _b : Block6 r, (r : ℝ) := by
        apply Finset.sum_congr rfl
        intro b _
        exact_mod_cast b.property
      _ = _ := by simp
  rw [Finset.sum_comm] at htotal
  simp_rw [rothAuxBlock_coordinate_sum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  have hsum :
      (∑ b : Block6 r, ((b.val 0).val : ℝ)) =
        (Fintype.card (Block6 r) : ℝ) * r / 6 := by
    calc
      _ = (6 * (∑ b : Block6 r,
          ((b.val 0).val : ℝ))) / 6 := by ring
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          congrArg (fun x : ℝ => x / 6) htotal
  have hr' : (r : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_div, hsum]
  field_simp [hr']
  ring

theorem rothAuxBlock_center_bound (r : ℕ) (hr : 0 < r) (b : Block6 r) :
    |1 / 6 - ((b.val 0).val : ℝ) / r| ≤ 1 := by
  have hle : ((b.val 0).val : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ (b.val 0).isLt
  have hz : 0 ≤ ((b.val 0).val : ℝ) / r := by positivity
  have hu : ((b.val 0).val : ℝ) / r ≤ 1 := (div_le_one (by positivity)).mpr hle
  rw [abs_le]
  constructor <;> linarith

theorem rothAuxBlock_exp_sum (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : Block6 r, Real.exp (u * (1 / 6 - ((b.val 0).val : ℝ) / r))) ≤
      (Fintype.card (Block6 r) : ℝ) * Real.exp (u ^ 2) := by
  have hpoint (b : Block6 r) :
      Real.exp (u * (1 / 6 - ((b.val 0).val : ℝ) / r)) ≤
        1 + u * (1 / 6 - ((b.val 0).val : ℝ) / r) + u ^ 2 := by
    have hb := rothAuxBlock_center_bound r hr b
    have hmul : |u * (1 / 6 - ((b.val 0).val : ℝ) / r)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hu]
      exact (mul_le_mul_of_nonneg_left hb hu).trans (by simpa using hu')
    have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hmul)).2
    have hsq : (u * (1 / 6 - ((b.val 0).val : ℝ) / r)) ^ 2 ≤ u ^ 2 := by
      rw [mul_pow]
      have hs : (1 / 6 - ((b.val 0).val : ℝ) / r) ^ 2 ≤ 1 := by
        have hs := mul_self_le_mul_self (abs_nonneg (1 / 6 - ((b.val 0).val : ℝ) / r)) hb
        simpa only [← sq, sq_abs, one_pow] using hs
      exact (mul_le_mul_of_nonneg_left hs (sq_nonneg u)).trans_eq (mul_one _)
    linarith
  calc
    _ ≤ ∑ b : Block6 r, (1 + u * (1 / 6 - ((b.val 0).val : ℝ) / r) + u ^ 2) :=
      Finset.sum_le_sum (fun b _ => hpoint b)
    _ = (Fintype.card (Block6 r) : ℝ) * (1 + u ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, rothAuxBlock_center_sum r hr, mul_zero, add_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp (u ^ 2)) (by positivity)



open scoped Classical

abbrev RothAuxCoefficients {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Block6 (r h)

abbrev RothAuxPivots {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Fin (r h + 1)

noncomputable def rothAuxDimension {m : ℕ} (r : Fin m → ℕ) : ℕ :=
  Fintype.card (RothAuxCoefficients r)

theorem rothAuxDimension_eq {m : ℕ} (r : Fin m → ℕ) :
    rothAuxDimension r = ∏ h, (r h + 5).choose 5 := by
  simp [rothAuxDimension, Fintype.card_pi, block6_card]

noncomputable def rothAuxCentered {m : ℕ} (r : Fin m → ℕ) (b : RothAuxCoefficients r) : ℝ :=
  ∑ h, (1 / 6 - ((b h).val 0).val / (r h : ℝ))

abbrev RothAuxBad {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :=
  {b : RothAuxCoefficients r // eta * m < rothAuxCentered r b}

noncomputable def rothAuxPivotCondition {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (i : RothAuxPivots r) : Prop :=
  (∑ h, ((i h).val : ℝ) / r h) < (1 / 6 - eta) * m

theorem rothAux_exp_moment {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) ≤
      (rothAuxDimension r : ℝ) * Real.exp ((m : ℝ) * u ^ 2) := by
  have hfactor : (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) =
      ∏ h, ∑ b : Block6 (r h),
        Real.exp (u * (1 / 6 - ((b.val 0).val : ℝ) / r h)) := by
    simp only [rothAuxCentered, Finset.mul_sum, Real.exp_sum]
    exact (Fintype.prod_sum (fun (h : Fin m) (b : Block6 (r h)) =>
      Real.exp (u * (1 / 6 - ((b.val 0).val : ℝ) / r h)))).symm
  rw [hfactor]
  calc
    _ ≤ ∏ h, ((Fintype.card (Block6 (r h)) : ℝ) * Real.exp (u ^ 2)) := by
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

theorem rothAuxBad_card_zero {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) (heta : 1 / 6 ≤ eta) :
    Fintype.card (RothAuxBad r eta) = 0 := by
  have hcenter (b : RothAuxCoefficients r) : rothAuxCentered r b ≤ (m : ℝ) / 6 := by
    calc
      _ ≤ ∑ _h : Fin m, (1 / 6 : ℝ) := by
        apply Finset.sum_le_sum
        intro h _
        have hz : 0 ≤ (((b h).val 0).val : ℝ) / (r h : ℝ) := by positivity
        linarith
      _ = _ := by simp [div_eq_mul_inv]
  have hem : (m : ℝ) / 6 ≤ eta * m := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  haveI : IsEmpty (RothAuxBad r eta) := ⟨fun b =>
    (not_lt_of_ge ((hcenter b.val).trans hem)) b.property⟩
  exact Fintype.card_eq_zero

theorem rothAuxBad_exp_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta) :
    (Fintype.card (RothAuxBad r eta) : ℝ) ≤
      (rothAuxDimension r : ℝ) * Real.exp (-eta ^ 2 * m / 4) := by
  by_cases he : eta < 1 / 6
  · have hu : 0 ≤ eta / 2 := by positivity
    have hu' : eta / 2 ≤ 1 := by linarith
    have hb := rothAux_exp_tail_parameter r hr eta (eta / 2) hu hu'
    convert hb using 1 <;> congr 2 <;> ring
  · rw [rothAuxBad_card_zero r eta (le_of_not_gt he)]
    simp only [Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le




abbrev Equations6 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) := Fin 18 × RothAuxBad r eta

theorem dimension6_pos {m : ℕ} (r : Fin m → ℕ) : 0 < rothAuxDimension r := by
  rw [rothAuxDimension_eq]
  exact Finset.prod_pos (fun h _ => Nat.choose_pos (by omega))

theorem coordinate_rows6_le_half {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (d : ℕ) (hd : 0 < d)
    (hm : 4 * (eta^2)⁻¹ * Real.log (36 * (d : ℝ)) ≤ (m : ℝ)) :
    (d * Fintype.card (Equations6 r eta) : ℝ) ≤ (rothAuxDimension r : ℝ) / 2 := by
  have hs : 0 < eta^2 := sq_pos_of_pos heta
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_left hm hs.le
  have hid : eta^2 * (4 * (eta^2)⁻¹ * Real.log (36 * (d : ℝ))) = 4 * Real.log (36 * (d : ℝ)) := by field_simp
  rw [hid] at hmul
  have he : Real.exp (-eta^2 * m / 4) ≤ 1 / (36 * (d : ℝ)) := by
    calc
      _ ≤ Real.exp (-Real.log (36 * (d : ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity),one_div]
  have hb := mul_le_mul_of_nonneg_left (rothAuxBad_exp_bound r hr eta heta) (show (0 : ℝ) ≤ 18 * d by positivity)
  calc
    _ = (18 * (d : ℝ)) * (Fintype.card (RothAuxBad r eta) : ℝ) := by simp only [Equations6,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]; ring
    _ ≤ (18 * (d : ℝ)) * ((rothAuxDimension r : ℝ) * Real.exp (-eta^2 * m / 4)) := hb
    _ ≤ (18 * (d : ℝ)) * ((rothAuxDimension r : ℝ) * (1 / (36 * (d : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by field_simp; ring

theorem coordinate_rows6_lt {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (d : ℕ) (hd : 0 < d)
    (hm : 4 * (eta^2)⁻¹ * Real.log (36 * (d : ℝ)) ≤ (m : ℝ)) :
    d * Fintype.card (Equations6 r eta) < rothAuxDimension r := by
  have hh := coordinate_rows6_le_half r hr eta heta d hd hm
  have hp : (0 : ℝ) < rothAuxDimension r := by exact_mod_cast dimension6_pos r
  exact_mod_cast (show (d * Fintype.card (Equations6 r eta) : ℝ) < (rothAuxDimension r : ℝ) by linarith)

abbrev Block5 (r : ℕ) := {b : Fin 5 → Fin (r + 1) // ∑ i, (b i).val = r}

def blockNatEquiv5 (r : ℕ) : Block5 r ≃ {b : Fin 5 → ℕ // ∑ i, b i = r} where
  toFun b := ⟨fun i => (b.val i).val,b.property⟩
  invFun b := ⟨fun i => ⟨b.val i,by
    have hh : b.val i ≤ ∑ j, b.val j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [b.property] at hh
    omega⟩,b.property⟩
  left_inv b := by rfl
  right_inv b := by rfl

theorem block5_card (r : ℕ) : Fintype.card (Block5 r) = (r + 4).choose 4 := by
  letI : Fintype {b : Fin 5 → ℕ // ∑ i, b i = r} := Fintype.ofEquiv (Sym (Fin 5) r) (Sym.equivNatSumOfFintype (Fin 5) r)
  rw [Fintype.card_congr (blockNatEquiv5 r),← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin 5) r),Sym.card_sym_eq_choose]
  simpa only [Fintype.card_fin,show 5 + r - 1 = r + 4 by omega] using (Nat.choose_symm_add (a := r) (b := 4))

def blockPivotEquiv6 (r : ℕ) : Block6 r ≃ (i : Fin (r+1)) × Block5 (r-i.val) where
  toFun b := ⟨b.val 0,⟨fun j => ⟨(b.val j.succ).val,by
    have hs := b.property
    rw [Fin.sum_univ_succ] at hs
    have hj : (b.val j.succ).val ≤ ∑ k : Fin 5, (b.val k.succ).val :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 5 => (b.val k.succ).val) (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    omega⟩,by
      have hs := b.property
      rw [Fin.sum_univ_succ] at hs
      change (∑ j : Fin 5, (b.val j.succ).val) = r - (b.val 0).val
      omega⟩⟩
  invFun p := ⟨Fin.cons p.1 (fun j => ⟨(p.2.val j).val,by
    have hh := (p.2.val j).isLt
    omega⟩),by
      rw [Fin.sum_univ_succ]
      change p.1.val + (∑ j : Fin 5, (p.2.val j).val) = r
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

def badPivotEquiv6 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    RothAuxBad r eta ≃
      (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}) ×
        ((h : Fin m) → Block5 (r h - (i.val h).val)) where
  toFun b := ⟨⟨fun h => (b.val h).val 0,(bad_iff_pivot6 r eta b.val).mp b.property⟩,
    fun h => (blockPivotEquiv6 (r h) (b.val h)).2⟩
  invFun p := ⟨fun h => (blockPivotEquiv6 (r h)).symm ⟨p.1.val h,p.2 h⟩,by
    apply (bad_iff_pivot6 r eta _).mpr
    exact p.1.property⟩
  left_inv b := by
    apply Subtype.ext
    funext h
    exact (blockPivotEquiv6 (r h)).symm_apply_apply (b.val h)
  right_inv p := by
    rcases p with ⟨⟨i,hi⟩,j⟩
    rfl

theorem bad_count_source6 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (RothAuxBad r eta) =
      ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 4).choose 4 := by
  rw [Fintype.card_congr (badPivotEquiv6 r eta),Fintype.card_sigma]
  simp only [Fintype.card_pi,block5_card]

theorem constraint_count_source6 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (Equations6 r eta) = 18 *
      ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 4).choose 4 := by
  simp only [Equations6,Fintype.card_prod,Fintype.card_fin,bad_count_source6]



def coordinates {K I R C : Type*} [Field K] [Algebra ℚ K]
    (b : Basis I ℚ K) (A : Matrix R C K) : Matrix (R × I) C ℚ :=
  fun q j => b.repr (A q.1 j) q.2

theorem coordinates_kernel {K I R C : Type*} [Field K] [Algebra ℚ K]
    [Fintype C] (b : Basis I ℚ K) (A : Matrix R C K) (c : C → ℤ) :
    (∀ i, ∑ j, A i j * (c j : K) = 0) ↔
      (coordinates b A).mulVec (fun j => (c j : ℚ)) = 0 := by
  have he (i : R) (k : I) :
      (coordinates b A).mulVec (fun j => (c j : ℚ)) (i,k) =
        b.repr (∑ j, A i j * (c j : K)) k := by
    simp only [Matrix.mulVec,dotProduct,coordinates,map_sum,Finsupp.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg (fun x : I →₀ ℚ => x k) (b.repr.map_smul (c j : ℚ) (A i j))
    simpa only [Finsupp.smul_apply,smul_eq_mul,Algebra.smul_def,map_intCast,mul_comm] using h.symm
  constructor
  · intro hz
    funext q
    rw [he,hz q.1,map_zero]
    rfl
  · intro hz i
    apply b.repr.injective
    ext k
    rw [map_zero]
    simpa only [← he,Pi.zero_apply] using congrFun hz (i,k)

theorem integer_matrix {R C : Type*} [Fintype R] [Fintype C]
    (A : Matrix R C ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ B : Matrix R C ℤ,
      ∀ i j, (B i j : ℚ) = (D : ℚ) * A i j := by
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun q : R × C => A q.1 q.2)
  have hh : ∀ i j, ∃ z : ℤ, (z : ℚ) = (D.val : ℚ) * A i j := by
    intro i j
    obtain ⟨z,hz⟩ := hD (i,j)
    exact ⟨z,by simpa only [Algebra.smul_def,map_intCast] using hz⟩
  choose B hB using hh
  exact ⟨D.val,mem_nonZeroDivisors_iff_ne_zero.mp D.property,B,hB⟩

theorem integer_matrix_kernel {R C : Type*} [Fintype C]
    (A : Matrix R C ℚ) (B : Matrix R C ℤ) (D : ℤ) (hD : D ≠ 0)
    (hB : ∀ i j, (B i j : ℚ) = (D : ℚ) * A i j) (c : C → ℤ) :
    B.mulVec c = 0 ↔ A.mulVec (fun j => (c j : ℚ)) = 0 := by
  have hDr : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have he (i : R) : ((B.mulVec c) i : ℚ) =
      (D : ℚ) * (A.mulVec (fun j => (c j : ℚ))) i := by
    simp only [Matrix.mulVec,dotProduct,Int.cast_sum,Int.cast_mul,hB,Finset.mul_sum,mul_assoc]
  constructor
  · intro hz
    funext i
    have hh := he i
    rw [hz,Pi.zero_apply,Int.cast_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hDr
  · intro hz
    funext i
    have hh := he i
    rw [hz,Pi.zero_apply,mul_zero] at hh
    exact_mod_cast hh


attribute [local instance] Matrix.seminormedAddCommGroup

theorem bounded_kernel {K I R C : Type*} [Field K] [Algebra ℚ K]
    [Fintype I] [Fintype R] [Fintype C] (b : Basis I ℚ K) (A : Matrix R C K)
    (hcount : Fintype.card R * Fintype.card I < Fintype.card C)
    (hrows : 0 < Fintype.card R * Fintype.card I) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ B : Matrix (R × I) C ℤ,
      (∀ i j, (B i j : ℚ) = (D : ℚ) * coordinates b A i j) ∧
      (∀ c : C → ℤ, (∀ i, ∑ j, A i j * (c j : K) = 0) ↔ B.mulVec c = 0) ∧
      ∃ c : C → ℤ, c ≠ 0 ∧ (∀ i, ∑ j, A i j * (c j : K) = 0) ∧
        ‖c‖ ≤ ((Fintype.card C : ℝ) * max 1 ‖B‖) ^
          (((Fintype.card R * Fintype.card I : ℕ) : ℝ) /
            ((Fintype.card C : ℝ) - (Fintype.card R * Fintype.card I : ℕ))) := by
  obtain ⟨D,hD,B,hB⟩ := integer_matrix (coordinates b A)
  have he (c : C → ℤ) : (∀ i, ∑ j, A i j * (c j : K) = 0) ↔ B.mulVec c = 0 :=
    (coordinates_kernel b A c).trans (integer_matrix_kernel _ _ D hD hB c).symm
  obtain ⟨c,hc,hker,hbound⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le B
    (by simpa only [Fintype.card_prod] using hcount)
    (by simpa only [Fintype.card_prod] using hrows)
  exact ⟨D,hD,B,hB,he,c,hc,(he c).mpr hker,by simpa only [Fintype.card_prod,Nat.cast_mul] using hbound⟩


open CompoundFeasibility

def forms (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (tau : Fin 3) : Matrix (Fin 6) (Fin 6) ℝ :=
  if tau = 0 then compound L else
    if tau = 1 then (compound A2).map (algebraMap ℚ ℝ) else (compound A3).map (algebraMap ℚ ℝ)

theorem common_source_field (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∀ tau s t, forms A2 A3 L tau s t ∈ K := by
  obtain ⟨K,hK,hmem⟩ := liouville6_common_field (compound L) (compound42_algebraic L ha)
  refine ⟨K,hK,?_⟩
  intro tau s t
  fin_cases tau
  · exact hmem s t
  · exact K.algebraMap_mem _
  · exact K.algebraMap_mem _


end CompoundFeasibility.Auxiliary6

open scoped NumberField

namespace Aux6Mass
variable {R : Type*} [NormedCommRing R] [NormOneClass R]

noncomputable def mass {σ : Type*} (P : MvPolynomial σ R) : ℝ :=
  ∑ d ∈ P.support, ‖P.coeff d‖

theorem mass_nonneg {σ : Type*} (P : MvPolynomial σ R) : 0 ≤ mass P :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem mass_monomial {σ : Type*} (d : σ →₀ ℕ) (c : R) :
    mass (MvPolynomial.monomial d c) = ‖c‖ := by
  by_cases hc : c = 0
  · simp [hc, mass]
  · simp [mass, MvPolynomial.support_monomial, hc]

theorem mass_support_sum {σ : Type*} (P : MvPolynomial σ R)
    (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) :
    mass P = ∑ d ∈ s, ‖P.coeff d‖ := by
  apply Finset.sum_subset hs
  intro d _ hd
  rw [MvPolynomial.not_mem_support_iff.mp hd, norm_zero]

theorem mass_add {σ : Type*} (P Q : MvPolynomial σ R) :
    mass (P + Q) ≤ mass P + mass Q := by
  let s := P.support ∪ Q.support
  have hP : P.support ⊆ s := Finset.subset_union_left
  have hQ : Q.support ⊆ s := Finset.subset_union_right
  rw [mass_support_sum (P + Q) s MvPolynomial.support_add,
    mass_support_sum P s hP, mass_support_sum Q s hQ, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun d _ => by simpa using norm_add_le (P.coeff d) (Q.coeff d))

theorem mass_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    mass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mass (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (mass_add _ _).trans (add_le_add_left ih _)

theorem mass_mul {σ : Type*} (P Q : MvPolynomial σ R) :
    mass (P * Q) ≤ mass P * mass Q := by
  rw [MvPolynomial.mul_def, MvPolynomial.sum_def]
  calc
    _ ≤ ∑ a ∈ P.support, mass (Q.sum fun b c =>
        MvPolynomial.monomial (a + b) (P.coeff a * c)) := mass_sum _ _
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support,
        mass (MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      apply Finset.sum_le_sum
      intro a _
      exact mass_sum _ _
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support, ‖P.coeff a‖ * ‖Q.coeff b‖ := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      rw [mass_monomial]
      exact norm_mul_le _ _
    _ = _ := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      rfl

theorem mass_pow {σ : Type*} (P : MvPolynomial σ R) (n : ℕ) :
    mass (P ^ n) ≤ mass P ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, MvPolynomial.one_def, mass_monomial]
    norm_num
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mass_mul _ _).trans
      (mul_le_mul_of_nonneg_right ih (mass_nonneg P))

theorem mass_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    mass (∏ i ∈ s, f i) ≤ ∏ i ∈ s, mass (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [MvPolynomial.one_def, mass_monomial]
    norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (mass_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (mass_nonneg _))

theorem coeff_le_mass {σ : Type*} (P : MvPolynomial σ R) (d : σ →₀ ℕ) :
    ‖P.coeff d‖ ≤ mass P := by
  by_cases hd : d ∈ P.support
  · change ‖P.coeff d‖ ≤ ∑ b ∈ P.support, ‖P.coeff b‖
    exact Finset.single_le_sum (fun b _ => norm_nonneg (P.coeff b)) hd
  · rw [MvPolynomial.not_mem_support_iff.mp hd, norm_zero]
    exact mass_nonneg _


theorem mass_neg {σ : Type*} (P : MvPolynomial σ R) :
    mass (-P) = mass P := by
  simp [mass]

theorem mass_C_mul_X {σ : Type*} (c : R) (u : σ) :
    mass (MvPolynomial.C c * MvPolynomial.X u) = ‖c‖ := by
  rw [MvPolynomial.X, MvPolynomial.C_mul_monomial, mul_one, mass_monomial]


end Aux6Mass




namespace CompoundFeasibility.Auxiliary6
abbrev Vars6 (m : ℕ) := Fin m × Fin 6

def exponent6 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) : Vars6 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => ((b u.1).val u.2).val)

theorem exponent6_injective {m : ℕ} (r : Fin m → ℕ) : Function.Injective (@exponent6 m r) := by
  intro b c h
  funext g
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrArg (fun e : Vars6 m →₀ ℕ => e (g,j)) h

def polynomial6 {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : MvPolynomial (Vars6 m) R :=
  ∑ b, MvPolynomial.monomial (exponent6 b) (c b)

theorem polynomial6_coeff {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) (b : RothAuxCoefficients r) :
    (polynomial6 c).coeff (exponent6 b) = c b := by
  simp only [polynomial6,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,(exponent6_injective r).eq_iff]
  simp

def homogeneous6 {m : ℕ} {R : Type*} [CommRing R] (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) R) : Prop :=
  ∀ d ∈ P.support, ∀ h, ∑ j : Fin 6, d (h,j) = r h

theorem polynomial6_homogeneous {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : homogeneous6 r (polynomial6 c) := by
  intro d hd h
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have hab := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
  subst d
  exact (b h).property

noncomputable def derivative6 {m : ℕ} {R : Type*} [CommRing R]
    (J : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) R) :
    MvPolynomial (Vars6 m) R :=
  P.sum fun b c => MvPolynomial.monomial (b - J)
    (c * ∏ u : Vars6 m, (Nat.choose (b u) (J u) : R))

theorem derivative6_coeff {m : ℕ} {R : Type*} [CommRing R]
    (a gamma : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) R) :
    (derivative6 a P).coeff gamma =
      P.coeff (gamma + a) *
        ∏ k : Vars6 m, (Nat.choose ((gamma + a) k) (a k) : R) := by
  classical
  rw [derivative6, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  calc
    _ = (MvPolynomial.monomial ((gamma + a) - a)
        (P.coeff (gamma + a) * ∏ k : Vars6 m,
          (Nat.choose ((gamma + a) k) (a k) : R))).coeff gamma := by
      apply Finset.sum_eq_single (gamma + a)
      · intro b hb hne
        by_cases hab : a ≤ b
        · have hd : b - a ≠ gamma := by
            intro hz
            apply hne
            calc
              b = (b - a) + a := (tsub_add_cancel_of_le hab).symm
              _ = gamma + a := by rw [hz]
          simp [MvPolynomial.coeff_monomial, hd]
        · change ¬ ∀ k, a k ≤ b k at hab
          push_neg at hab
          obtain ⟨k, hk⟩ := hab
          have hz : (∏ k : Vars6 m, (Nat.choose (b k) (a k) : R)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            simp [Nat.choose_eq_zero_of_lt hk]
          simp [hz]
      · intro hn
        have hz : P.coeff (gamma + a) = 0 := MvPolynomial.not_mem_support_iff.mp hn
        simp [hz]
    _ = _ := by simp


variable {R : Type*} [CommRing R]

def chart6 {m : ℕ} (a : Fin 6 → R) (k : Fin 6) (u : Vars6 m) : MvPolynomial (Vars6 m) R :=
  if u.2 = k then -(∑ j ∈ Finset.univ.erase k, MvPolynomial.C (a j) * MvPolynomial.X (u.1,j))
  else MvPolynomial.C (a k) * MvPolynomial.X u

def substitute6 {m : ℕ} (a : Fin 6 → R) (k : Fin 6) : MvPolynomial (Vars6 m) R →+* MvPolynomial (Vars6 m) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (chart6 a k)

def pivotDerivative6 {m : ℕ} (k : Fin 6) (i : Fin m → ℕ) : Vars6 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k then i u.1 else 0)

theorem derivative6_monomial {m : ℕ} (J b : Vars6 m →₀ ℕ) (c : R) :
    derivative6 J (MvPolynomial.monomial b c) = MvPolynomial.monomial (b-J)
      (c * ∏ u : Vars6 m, (Nat.choose (b u) (J u) : R)) := by
  unfold derivative6
  exact MvPolynomial.sum_monomial_eq (by simp)

theorem transformed_monomial6 {m : ℕ} (a : Fin 6 → R) (k : Fin 6) (J b : Vars6 m →₀ ℕ) :
    substitute6 a k (derivative6 J (MvPolynomial.monomial b 1)) =
      MvPolynomial.C (∏ u : Vars6 m, (Nat.choose (b u) (J u) : R)) *
        ∏ u : Vars6 m, chart6 a k u ^ (b-J) u := by
  rw [derivative6_monomial]
  change MvPolynomial.eval₂ MvPolynomial.C (chart6 a k) (MvPolynomial.monomial (b-J)
    (1 * ∏ u : Vars6 m, (Nat.choose (b u) (J u) : R))) = _
  rw [MvPolynomial.eval₂_monomial,one_mul]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

theorem exponent6_sum {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) :
    (∑ u : Vars6 m, exponent6 b u) = ∑ h, r h := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun h _ => (b h).property)


theorem transformed_coeff_sum6 {m : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Vars6 m →₀ ℕ) (c : ι → R)
    (J d : Vars6 m →₀ ℕ)
    (a : Fin 6 → R) (k : Fin 6) :
    let S := substitute6 (m := m) a k;
    (S (derivative6 J (∑ b, MvPolynomial.monomial (e b) (c b)))).coeff d =
      ∑ b, c b * (S (derivative6 J
        (MvPolynomial.monomial (e b) 1))).coeff d := by
  dsimp only
  let S := substitute6 (m := m) a k
  have hadd : derivative6 J
      (∑ b, MvPolynomial.monomial (e b) (c b)) =
      ∑ b, derivative6 J (MvPolynomial.monomial (e b) (c b)) := by
    apply MvPolynomial.ext
    intro a
    simp only [derivative6_coeff, MvPolynomial.coeff_sum,
      Finset.sum_mul]
  rw [hadd, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [derivative6_monomial, derivative6_monomial]
  simp only [one_mul]
  have hc : MvPolynomial.monomial (e b - J)
      (c b * ∏ u : Vars6 m, (Nat.choose (e b u) (J u) : R)) =
      MvPolynomial.C (c b) * MvPolynomial.monomial (e b - J)
        (∏ u : Vars6 m, (Nat.choose (e b u) (J u) : R)) := by
    rw [MvPolynomial.C_mul_monomial]
  rw [hc, map_mul]
  have hC : S (MvPolynomial.C (c b)) = MvPolynomial.C (c b) := by
    simp [S,substitute6]
  rw [hC, MvPolynomial.coeff_C_mul]


theorem rothAux_weight_block {m : ℕ} (d : Vars6 m →₀ ℕ) (h : Fin m) :
    Finsupp.weight (fun u : Vars6 m => if u.1 = h then 1 else 0) d =
      ∑ j : Fin 6, d (h,j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type, nsmul_eq_mul]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero]
  calc
    (∑ x : Fin m, ∑ j : Fin 6,
        if x = h then d (x,j) else 0) =
      ∑ x : Fin m,
        if x = h then (∑ j : Fin 6, d (x,j)) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = h
          · simp [hx]
          · simp [hx]
    _ = ∑ j : Fin 6, d (h,j) := by simp

theorem rothAux_weight_pivot {m : ℕ} (d : Vars6 m →₀ ℕ) (k : Fin 6) :
    Finsupp.weight (fun u : Vars6 m => if u.2 = k then 1 else 0) d =
      ∑ h : Fin m, d (h,k) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, nsmul_eq_mul]

theorem rothAux_weighted_neg {m : ℕ} (w : Vars6 m → ℕ)
    (P : MvPolynomial (Vars6 m) R) (n : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous w P n) :
    MvPolynomial.IsWeightedHomogeneous w (-P) n := by
  intro d hd
  apply hP
  simpa using hd

theorem chart6_block_weight {m : ℕ} (a : Fin 6 → R) (k : Fin 6)
    (h : Fin m) (u : Vars6 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars6 m => if v.1 = h then 1 else 0)
      (chart6 a k u) (if u.1 = h then 1 else 0) := by
  let w := fun v : Vars6 m => if v.1 = h then 1 else 0
  have hx (j : Fin 6) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) (if u.1 = h then 1 else 0) := by
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart6
  by_cases hu : u.2 = k
  · rw [if_pos hu]
    exact rothAux_weighted_neg w _ _
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun j _ => hx j))
  · rw [if_neg hu]
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem chart6_pivot_weight {m : ℕ} (a : Fin 6 → R) (k : Fin 6)
    (u : Vars6 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars6 m => if v.2 = k then 1 else 0)
      (chart6 a k u) 0 := by
  let w := fun v : Vars6 m => if v.2 = k then 1 else 0
  have hx (j : Fin 6) (hj : j ≠ k) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) 0 := by
    simpa only [w, hj, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart6
  split_ifs with hu
  · exact rothAux_weighted_neg w _ 0
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ 0 (fun j hj => hx j (Finset.mem_erase.mp hj).1))
  · simpa only [w, hu, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem rothAux_scaled_monomial_weighted {m : ℕ} (a : Fin 6 → R) (k : Fin 6)
    (J b : Vars6 m →₀ ℕ) (w : Vars6 m → ℕ) (v : Vars6 m → ℕ)
    (hv : ∀ u, MvPolynomial.IsWeightedHomogeneous w (chart6 a k u) (v u)) :
    MvPolynomial.IsWeightedHomogeneous w
      (substitute6 a k
        (derivative6 J (MvPolynomial.monomial b 1)))
      (∑ u : Vars6 m, (b - J) u * v u) := by
  rw [transformed_monomial6]
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars6 m => chart6 a k u ^ (b - J) u)
    (fun u => (b - J) u * v u) (fun u _ => by simpa only [nsmul_eq_mul] using (hv u).pow ((b - J) u))
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w _).mul hp



theorem rothAux_transformed_polynomial {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → R) (k : Fin 6) (J : Vars6 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    substitute6 a k (derivative6 J (polynomial6 c)) =
      ∑ b, MvPolynomial.C (c b) * substitute6 a k
        (derivative6 J (MvPolynomial.monomial (exponent6 b) 1)) := by
  apply MvPolynomial.ext
  intro d
  rw [polynomial6, transformed_coeff_sum6]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem rothAux_pivot_monomial_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → R) (k : Fin 6) (i : Fin m → ℕ) (b : RothAuxCoefficients r) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars6 m => if u.1 = h then 1 else 0)
      (substitute6 a k (derivative6
        (pivotDerivative6 k i) (MvPolynomial.monomial (exponent6 b) 1)))
      (r h - i h) := by
  let J := pivotDerivative6 k i
  let w := fun u : Vars6 m => if u.1 = h then 1 else 0
  by_cases hle : J ≤ exponent6 b
  · have hw := rothAux_scaled_monomial_weighted a k J (exponent6 b) w w
      (chart6_block_weight a k h)
    have heq : (∑ u : Vars6 m, (exponent6 b - J) u * w u) =
        ∑ j : Fin 6, (exponent6 b - J) (h,j) := by
      have he := rothAux_weight_block (exponent6 b - J) h
      rw [Finsupp.weight_apply] at he
      rw [Finsupp.sum_fintype (exponent6 b - J)
        (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
      simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
    have hdeg : (∑ j : Fin 6, (exponent6 b - J) (h,j)) = r h - i h := by
      change (∑ j : Fin 6, (exponent6 b (h,j) - J (h,j))) = _
      rw [Finset.sum_tsub_distrib _ (fun j _ => hle (h,j))]
      have hb : (∑ j : Fin 6, exponent6 b (h,j)) = r h := (b h).property
      rw [hb]
      congr 1
      simp [J, pivotDerivative6]
    rw [heq, hdeg] at hw
    exact hw
  · change ¬ ∀ u, J u ≤ exponent6 b u at hle
    push_neg at hle
    obtain ⟨u, hu⟩ := hle
    have hz : (∏ v : Vars6 m, (Nat.choose (exponent6 b v) (J v) : R)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [Nat.choose_eq_zero_of_lt hu]
    rw [transformed_monomial6, hz, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero R w _

theorem rothAux_transformed_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → R) (k : Fin 6) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars6 m => if u.1 = h then 1 else 0)
      (substitute6 a k (derivative6
        (pivotDerivative6 k i) (polynomial6 c))) (r h - i h) := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul
    (rothAux_pivot_monomial_block_weight a k i b h)

theorem rothAux_transformed_block_homogeneous {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → R) (k : Fin 6) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) :
    homogeneous6 (fun h => r h - i h)
      (substitute6 a k (derivative6
        (pivotDerivative6 k i) (polynomial6 c))) := by
  intro d hd h
  rw [← rothAux_weight_block]
  exact rothAux_transformed_block_weight a k i c h (MvPolynomial.mem_support_iff.mp hd)

theorem rothAux_transformed_pivot_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → R) (k : Fin 6) (J : Vars6 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars6 m => if u.2 = k then 1 else 0)
      (substitute6 a k (derivative6 J (polynomial6 c))) 0 := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  have hb := rothAux_scaled_monomial_weighted a k J (exponent6 b)
    (fun u : Vars6 m => if u.2 = k then 1 else 0) (fun _ => 0)
    (chart6_pivot_weight a k)
  simp only [mul_zero, Finset.sum_const_zero] at hb
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul hb

theorem rothAux_transformed_pivot_zero {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → R) (k : Fin 6) (J : Vars6 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) (d : Vars6 m →₀ ℕ)
    (hd : (substitute6 a k
      (derivative6 J (polynomial6 c))).coeff d ≠ 0) (h : Fin m) :
    d (h,k) = 0 := by
  have hw := rothAux_transformed_pivot_weight a k J c hd
  rw [rothAux_weight_pivot] at hw
  have hle : d (h,k) ≤ ∑ g : Fin m, d (g,k) :=
    Finset.single_le_sum (fun g _ => Nat.zero_le (d (g,k))) (Finset.mem_univ h)
  omega



def freeExponent6 {m : ℕ} (s : Fin m → ℕ) (k : Fin 6)
    (j : (h : Fin m) → Block5 (s h)) : Vars6 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => Fin.insertNth (α := fun _ : Fin 6 => ℕ) k 0 (fun t : Fin 5 => ((j u.1).val t).val) u.2)

theorem freeExponent6_reconstruct {m : ℕ} (s : Fin m → ℕ) (k : Fin 6)
    (d : Vars6 m →₀ ℕ) (hs : ∀ h, ∑ t : Fin 6, d (h,t) = s h)
    (hz : ∀ h, d (h,k) = 0) :
    ∃ j : (h : Fin m) → Block5 (s h), freeExponent6 s k j = d := by
  have hsum (h : Fin m) : (∑ t : Fin 5, d (h,k.succAbove t)) = s h := by
    have he := Fin.sum_univ_succAbove (fun t => d (h,t)) k
    rw [hs h,hz h,zero_add] at he
    exact he.symm
  let j : (h : Fin m) → Block5 (s h) := fun h => ⟨fun t => ⟨d (h,k.succAbove t),by
    have hh : d (h,k.succAbove t) ≤ ∑ u : Fin 6, d (h,u) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun u : Fin 6 => d (h,u)) (fun u _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [hs h] at hh
    omega⟩,hsum h⟩
  refine ⟨j,?_⟩
  ext u
  rcases u with ⟨h,t⟩
  change Fin.insertNth (α := fun _ : Fin 6 => ℕ) k 0 (fun v : Fin 5 => ((j h).val v).val) t = d (h,t)
  refine Fin.succAboveCases k ?_ (fun v => ?_) t
  · simpa only [Fin.insertNth_apply_same] using (hz h).symm
  · rw [Fin.insertNth_apply_succAbove]


end CompoundFeasibility.Auxiliary6
namespace Aux6Height
open CompoundFeasibility.Auxiliary6 Aux6Mass
variable {R : Type*} [NormedCommRing R] [NormOneClass R]

theorem chart_mass6 {m : ℕ} (a : Fin 6 → R) (k : Fin 6)
    (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A) (u : Vars6 m) :
    mass (chart6 a k u) ≤ 6 * A := by
  unfold chart6
  split_ifs
  · rw [mass_neg]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase k, mass (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) := mass_sum _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase k, A := by
        apply Finset.sum_le_sum
        intro j _
        rw [mass_C_mul_X]
        exact ha j
      _ ≤ 6 * A := by simp; linarith
  · rw [mass_C_mul_X]
    exact (ha k).trans (by linarith)

theorem binomial_norm6 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) (J : Vars6 m →₀ ℕ) :
    ‖∏ u : Vars6 m, (Nat.choose (exponent6 b u) (J u) : R)‖ ≤ (2 : ℝ)^(∑ h, r h) := by
  have hnat (n : ℕ) : ‖(n : R)‖ ≤ (n : ℝ) := by
    rw [← nsmul_one]
    exact (norm_nsmul_le (n := n) (a := (1 : R))).trans_eq (by simp)
  calc
    _ ≤ ∏ u : Vars6 m, ‖(Nat.choose (exponent6 b u) (J u) : R)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ u : Vars6 m, (2 : ℝ)^exponent6 b u := by
      apply Finset.prod_le_prod
      · intro u _; exact norm_nonneg _
      · intro u _
        apply (hnat _).trans
        have hc : (exponent6 b u).choose (J u) ≤ 2 ^ exponent6 b u := by
          rcases Nat.eq_zero_or_pos (exponent6 b u) with hz | hp
          · rw [hz]; cases J u <;> simp
          · exact (Nat.choose_le_two_pow _ _ hp).le
        exact_mod_cast hc
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum,exponent6_sum]

theorem transformed_entry_norm6 {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → R) (k : Fin 6) (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A)
    (b : RothAuxCoefficients r) (J d : Vars6 m →₀ ℕ) :
    ‖(substitute6 a k (derivative6 J (MvPolynomial.monomial (exponent6 b) 1))).coeff d‖ ≤
      (12 * A)^(∑ h, r h) := by
  have hbase : 1 ≤ 6 * A := by linarith
  have hsum : (∑ u : Vars6 m, (exponent6 b-J) u) ≤ ∑ h, r h := by
    rw [← exponent6_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  rw [transformed_monomial6]
  calc
    _ ≤ mass (MvPolynomial.C (∏ u : Vars6 m, (Nat.choose (exponent6 b u) (J u) : R)) *
        ∏ u : Vars6 m, chart6 a k u ^ (exponent6 b-J) u) := coeff_le_mass _ _
    _ ≤ mass (MvPolynomial.C (∏ u : Vars6 m, (Nat.choose (exponent6 b u) (J u) : R))) *
        mass (∏ u : Vars6 m, chart6 a k u ^ (exponent6 b-J) u) := mass_mul _ _
    _ ≤ (2 : ℝ)^(∑ h, r h) * (6*A)^(∑ h, r h) := by
      apply mul_le_mul
      · simpa only [MvPolynomial.C_apply,mass_monomial] using binomial_norm6 (R := R) b J
      · calc
          _ ≤ ∏ u : Vars6 m, mass (chart6 a k u ^ (exponent6 b-J) u) := mass_prod _ _
          _ ≤ ∏ u : Vars6 m, (6*A)^(exponent6 b-J) u := by
            apply Finset.prod_le_prod
            · intro u _; exact mass_nonneg _
            · intro u _
              exact (mass_pow _ _).trans (pow_le_pow_left₀ (mass_nonneg _) (chart_mass6 a k A hA ha u) _)
          _ = (6*A)^(∑ u : Vars6 m, (exponent6 b-J) u) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ _ := pow_le_pow_right₀ hbase hsum
      · exact mass_nonneg _
      · positivity
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Aux6Height
namespace CompoundFeasibility.Auxiliary6
variable {K : Type*} [CommRing K]

noncomputable def formEquiv6 : Fin 18 ≃ Fin 3 × Fin 6 :=
  (finProdFinEquiv : Fin 3 × Fin 6 ≃ Fin (3 * 6)).symm

noncomputable def equation6 {m : ℕ} {r : Fin m → ℕ} {eta : ℝ}
    (a : Fin 3 → Fin 6 → Fin 6 → K) (p : Fin 3 → Fin 6 → Fin 6)
    (f : Fin 18) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
    (j : (h : Fin m) → Block5 (r h - (i.val h).val))
    (P : MvPolynomial (Vars6 m) K) : K :=
  (substitute6 (a (formEquiv6 f).1 (formEquiv6 f).2)
    (p (formEquiv6 f).1 (formEquiv6 f).2)
    (derivative6 (pivotDerivative6 (p (formEquiv6 f).1 (formEquiv6 f).2)
      (fun h => (i.val h).val)) P)).coeff
    (freeExponent6 (fun h => r h - (i.val h).val)
      (p (formEquiv6 f).1 (formEquiv6 f).2) j)

noncomputable def matrix6 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → K) (p : Fin 3 → Fin 6 → Fin 6) :
    Matrix (Equations6 r eta) (RothAuxCoefficients r) K :=
  fun q b => equation6 a p q.1 (badPivotEquiv6 r eta q.2).1
    (badPivotEquiv6 r eta q.2).2 (MvPolynomial.monomial (exponent6 b) 1)

theorem matrix6_mulVec {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → K) (p : Fin 3 → Fin 6 → Fin 6)
    (c : RothAuxCoefficients r → K) (q : Equations6 r eta) :
    (matrix6 r eta a p).mulVec c q =
      equation6 a p q.1 (badPivotEquiv6 r eta q.2).1
        (badPivotEquiv6 r eta q.2).2 (polynomial6 c) := by
  unfold equation6 polynomial6
  rw [transformed_coeff_sum6]
  simp only [Matrix.mulVec, dotProduct, matrix6, equation6]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrix6_kernel_iff_coefficients {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → K) (p : Fin 3 → Fin 6 → Fin 6)
    (c : RothAuxCoefficients r → K) :
    (matrix6 r eta a p).mulVec c = 0 ↔
      ∀ (f : Fin 18) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
        (j : (h : Fin m) → Block5 (r h - (i.val h).val)),
        equation6 a p f i j (polynomial6 c) = 0 := by
  constructor
  · intro hz f i j
    have h := congrFun hz (f, (badPivotEquiv6 r eta).symm ⟨i,j⟩)
    rw [matrix6_mulVec] at h
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using h
  · intro hz
    funext q
    rw [matrix6_mulVec]
    exact hz q.1 (badPivotEquiv6 r eta q.2).1 (badPivotEquiv6 r eta q.2).2

theorem restriction6_zero_iff_coefficients {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 6 → K) (k : Fin 6) (i : RothAuxPivots r)
    (c : RothAuxCoefficients r → K) :
    substitute6 a k (derivative6 (pivotDerivative6 k (fun h => (i h).val))
      (polynomial6 c)) = 0 ↔
      ∀ j : (h : Fin m) → Block5 (r h - (i h).val),
        (substitute6 a k (derivative6 (pivotDerivative6 k (fun h => (i h).val))
          (polynomial6 c))).coeff
          (freeExponent6 (fun h => r h - (i h).val) k j) = 0 := by
  constructor
  · intro hz j
    rw [hz, MvPolynomial.coeff_zero]
  · intro hz
    apply MvPolynomial.ext
    intro d
    by_cases hd : (substitute6 a k (derivative6 (pivotDerivative6 k (fun h => (i h).val))
        (polynomial6 c))).coeff d = 0
    · exact hd
    · have hhom := rothAux_transformed_block_homogeneous a k (fun h => (i h).val) c
      have hdeg := hhom d (MvPolynomial.mem_support_iff.mpr hd)
      have hp := rothAux_transformed_pivot_zero a k
        (pivotDerivative6 k (fun h => (i h).val)) c d hd
      obtain ⟨j, hj⟩ := freeExponent6_reconstruct (fun h => r h - (i h).val) k d hdeg hp
      rw [← hj]
      exact hz j

theorem matrix6_kernel_iff_restrictions {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → K) (p : Fin 3 → Fin 6 → Fin 6)
    (c : RothAuxCoefficients r → K) :
    (matrix6 r eta a p).mulVec c = 0 ↔
      ∀ (tau : Fin 3) (s : Fin 6)
        (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}),
        substitute6 (a tau s) (p tau s)
          (derivative6 (pivotDerivative6 (p tau s) (fun h => (i.val h).val))
            (polynomial6 c)) = 0 := by
  rw [matrix6_kernel_iff_coefficients]
  constructor
  · intro hz tau s i
    apply (restriction6_zero_iff_coefficients (a tau s) (p tau s) i.val c).mpr
    intro j
    have hh := hz (formEquiv6.symm (tau,s)) i j
    simpa only [equation6, Equiv.apply_symm_apply] using hh
  · intro hz f i j
    exact (restriction6_zero_iff_coefficients _ _ i.val c).mp
      (hz (formEquiv6 f).1 (formEquiv6 f).2 i) j

end CompoundFeasibility.Auxiliary6

namespace CompoundFeasibility.Auxiliary6
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
noncomputable def rothSourceDerivativeWeight {m : ℕ} (r : Fin m → ℕ)
    (J : Vars6 m →₀ ℕ) : ℝ :=
  ∑ h, (∑ i : Fin 6, (J (h,i) : ℝ)) / (r h : ℝ)

theorem derivative6_add {m : ℕ} (J : Vars6 m →₀ ℕ)
    (P Q : MvPolynomial (Vars6 m) 𝕂) :
    derivative6 J (P + Q) = derivative6 J P + derivative6 J Q := by
  apply MvPolynomial.ext
  intro d
  simp only [derivative6_coeff, MvPolynomial.coeff_add, add_mul]

theorem rothSource_pderiv_eq_single {m : ℕ} (u : Vars6 m)
    (P : MvPolynomial (Vars6 m) 𝕂) :
    MvPolynomial.pderiv u P = derivative6 (Finsupp.single u 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, derivative6_add, hP, hQ]
  | monomial b c =>
    rw [MvPolynomial.pderiv_monomial, derivative6_monomial]
    congr 1
    congr 1
    rw [Finset.prod_eq_single u]
    · simp [Finsupp.single_apply, add_comm]
    · intro x hx hxu
      simp [Finsupp.single_apply, Ne.symm hxu]
    · simp

theorem rothSource_derivative_comp {m : ℕ} (a b : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) 𝕂) :
    derivative6 a (derivative6 b P) =
      (∏ k : Vars6 m, (Nat.choose ((a + b) k) (a k) : 𝕂)) •
        derivative6 (a + b) P := by
  classical
  apply MvPolynomial.ext
  intro c
  simp only [derivative6_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  have hch (k : Vars6 m) :
      Nat.choose ((c + a + b) k) (b k) * Nat.choose ((c + a) k) (a k) =
        Nat.choose ((a + b) k) (a k) * Nat.choose ((c + a + b) k) ((a + b) k) := by
    simp only [Finsupp.add_apply]
    have h := Nat.choose_mul (n := c k + a k + b k) (k := a k + b k) (s := b k)
      (by omega) (by omega)
    have hn : c k + a k + b k - b k = c k + a k := by omega
    have ha : a k + b k - b k = a k := by omega
    rw [hn, ha] at h
    have hs : Nat.choose (a k + b k) (b k) = Nat.choose (a k + b k) (a k) :=
      Nat.choose_symm_add.symm
    rw [hs] at h
    nlinarith
  calc
    _ = P.coeff (c + (a + b)) *
        ∏ k : Vars6 m, ((Nat.choose ((c + a + b) k) (b k) : 𝕂) *
          (Nat.choose ((c + a) k) (a k) : 𝕂)) := by
      rw [Finset.prod_mul_distrib]
      simp only [add_assoc]
      ring
    _ = P.coeff (c + (a + b)) *
        ∏ k : Vars6 m, ((Nat.choose ((a + b) k) (a k) : 𝕂) *
          (Nat.choose ((c + a + b) k) ((a + b) k) : 𝕂)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      exact_mod_cast hch k
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [add_assoc]; ring

theorem rothSource_pderiv_hasse {m : ℕ} (u : Vars6 m)
    (J : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) 𝕂) :
    MvPolynomial.pderiv u (derivative6 J P) =
      (J u + 1) • derivative6 (J + Finsupp.single u 1) P := by
  rw [rothSource_pderiv_eq_single, rothSource_derivative_comp, add_comm J]
  have he : (∏ v : Vars6 m, (Nat.choose (((Finsupp.single u 1 : Vars6 m →₀ ℕ) + J) v)
      ((Finsupp.single u 1) v) : 𝕂)) = ((J u + 1 : ℕ) : 𝕂) := by
    rw [Finset.prod_eq_single u]
    · simp [Finsupp.single_apply, add_comm]
    · intro x hx hxu
      simp [Finsupp.single_apply, Ne.symm hxu]
    · simp
  rw [he]
  simp [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul]

theorem rothSource_scaled_chart_pderiv {m : ℕ} (a : Fin 6 → 𝕂) (k j : Fin 6)
    (h : Fin m) (hj : j ≠ k) (v : Vars6 m) :
    MvPolynomial.pderiv (h,j) (chart6 a k v) =
      MvPolynomial.C (a k) * (if v = (h,j) then 1 else 0) -
        MvPolynomial.C (a j) * (if v = (h,k) then 1 else 0) := by
  classical
  rcases v with ⟨g,l⟩
  by_cases hg : g = h
  · subst g
    by_cases hl : l = k
    · subst l
      simp [chart6, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hj, Ne.symm hj, map_sum, mul_ite,
        Finset.sum_ite_eq', Finset.sum_ite_eq, eq_comm]
    · simp [chart6, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hl, Ne.symm hl, eq_comm]
  · by_cases hl : l = k <;>
      simp [chart6, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg, map_sum]

theorem rothSource_scaled_chain {m : ℕ} (a : Fin 6 → 𝕂) (k j : Fin 6)
    (h : Fin m) (hj : j ≠ k) (P : MvPolynomial (Vars6 m) 𝕂) :
    MvPolynomial.pderiv (h,j) (substitute6 a k P) =
      MvPolynomial.C (a k) * substitute6 a k (MvPolynomial.pderiv (h,j) P) -
        MvPolynomial.C (a j) * substitute6 a k (MvPolynomial.pderiv (h,k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute6]
  | add P Q hP hQ => simp only [map_add, hP, hQ]; ring
  | mul_X P v hP =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    rw [show substitute6 a k (MvPolynomial.X v) = chart6 a k v by simp [substitute6],
      rothSource_scaled_chart_pderiv a k j h hj v]
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero]
    split_ifs <;> simp_all <;> ring

theorem rothSource_weight_add {m : ℕ} (r : Fin m → ℕ) (J K : Vars6 m →₀ ℕ) :
    rothSourceDerivativeWeight r (J + K) =
      rothSourceDerivativeWeight r J + rothSourceDerivativeWeight r K := by
  simp [rothSourceDerivativeWeight, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, add_div]

theorem rothSource_weight_mono {m : ℕ} (r : Fin m → ℕ)
    (J K : Vars6 m →₀ ℕ) (hJK : J ≤ K) :
    rothSourceDerivativeWeight r J ≤ rothSourceDerivativeWeight r K := by
  apply Finset.sum_le_sum
  intro h _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact_mod_cast hJK (h,i)

theorem rothSource_weight_single {m : ℕ} (r : Fin m → ℕ) (u : Vars6 m) :
    rothSourceDerivativeWeight r (Finsupp.single u 1) = 1 / (r u.1 : ℝ) := by
  classical
  rcases u with ⟨h,j⟩
  simp [rothSourceDerivativeWeight, Finsupp.single_apply, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [ite_div, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_weight_pivot {m : ℕ} (r : Fin m → ℕ) (k : Fin 6) (i : Fin m → ℕ) :
    rothSourceDerivativeWeight r (pivotDerivative6 k i) = ∑ h, (i h : ℝ) / r h := by
  simp [rothSourceDerivativeWeight, pivotDerivative6, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

noncomputable def rothSourceFreeOrder {m : ℕ} (k : Fin 6) (J : Vars6 m →₀ ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Vars6 m => u.2 ≠ k), J u

theorem rothSource_free_add {m : ℕ} (k : Fin 6) (J K : Vars6 m →₀ ℕ) :
    rothSourceFreeOrder k (J + K) = rothSourceFreeOrder k J + rothSourceFreeOrder k K := by
  simp [rothSourceFreeOrder, Finsupp.add_apply, Finset.sum_add_distrib]

theorem rothSource_free_single {m : ℕ} (k : Fin 6) (u : Vars6 m) :
    rothSourceFreeOrder k (Finsupp.single u 1) = if u.2 = k then 0 else 1 := by
  classical
  simp [rothSourceFreeOrder, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_free_zero_pivot {m : ℕ} (k : Fin 6) (J : Vars6 m →₀ ℕ)
    (hJ : rothSourceFreeOrder k J = 0) :
    J = pivotDerivative6 k (fun h => J (h,k)) := by
  classical
  ext u
  by_cases hu : u.2 = k
  · have he : u = (u.1,k) := Prod.ext rfl hu
    simpa [pivotDerivative6, hu] using congrArg J he
  · have hle : J u ≤ rothSourceFreeOrder k J :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ u,hu⟩)
    have hz : J u = 0 := by omega
    simp [pivotDerivative6, hu, hz]

theorem rothSource_scaled_mixed_vanishing {m : ℕ} (r : Fin m → ℕ)
    (a : Fin 6 → 𝕂) (k : Fin 6) (ha : a k ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars6 m) 𝕂)
    (hpivot : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      substitute6 a k
        (derivative6 (pivotDerivative6 k i) P) = 0)
    (J : Vars6 m →₀ ℕ) (hw : rothSourceDerivativeWeight r J < T) :
    substitute6 a k (derivative6 J P) = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J : Vars6 m →₀ ℕ,
      rothSourceFreeOrder k J = n → rothSourceDerivativeWeight r J < T →
      substitute6 a k (derivative6 J P) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hn hw
      by_cases hz : n = 0
      · have he := rothSource_free_zero_pivot k J (hn.trans hz)
        have hweight : (∑ h, (J (h,k) : ℝ) / r h) < T := by
          rw [← rothSource_weight_pivot r k, ← he]
          exact hw
        rw [he]
        exact hpivot _ hweight
      · have hex : ∃ u : Vars6 m, u.2 ≠ k ∧ J u ≠ 0 := by
          by_contra! hno
          have hzero : rothSourceFreeOrder k J = 0 := by
            apply Finset.sum_eq_zero
            intro u hu
            exact hno u (Finset.mem_filter.mp hu).2
          omega
        obtain ⟨u, hu, hJu⟩ := hex
        let K := J - Finsupp.single u 1
        let Kp := K + Finsupp.single (u.1,k) 1
        have hle : Finsupp.single u 1 ≤ J := by
          rw [Finsupp.single_le_iff]
          omega
        have hKeq : K + Finsupp.single u 1 = J := tsub_add_cancel_of_le hle
        have hKcount : rothSourceFreeOrder k K + 1 = n := by
          have hc := congrArg (rothSourceFreeOrder k) hKeq
          simpa [rothSource_free_add, rothSource_free_single, hu, hn] using hc
        have hKpcount : rothSourceFreeOrder k Kp = rothSourceFreeOrder k K := by
          simp [Kp, rothSource_free_add, rothSource_free_single]
        have hKweight : rothSourceDerivativeWeight r K ≤ rothSourceDerivativeWeight r J :=
          rothSource_weight_mono r K J tsub_le_self
        have hKpweight : rothSourceDerivativeWeight r Kp = rothSourceDerivativeWeight r J := by
          calc
            _ = rothSourceDerivativeWeight r K + 1 / (r u.1 : ℝ) := by
              rw [rothSource_weight_add, rothSource_weight_single]
            _ = _ := by rw [← hKeq, rothSource_weight_add, rothSource_weight_single]
        have hK := ih (rothSourceFreeOrder k K) (by omega) K rfl (lt_of_le_of_lt hKweight hw)
        have hKp := ih (rothSourceFreeOrder k Kp) (by omega) Kp rfl (hKpweight ▸ hw)
        change substitute6 a k
          (derivative6 (K + Finsupp.single (u.1,k) 1) P) = 0 at hKp
        have hc := rothSource_scaled_chain a k u.2 u.1 hu
          (derivative6 K P)
        rw [rothSource_pderiv_hasse, rothSource_pderiv_hasse] at hc
        simp only [hK, map_zero, map_nsmul, hKp, nsmul_zero, mul_zero, sub_zero] at hc
        rw [hKeq] at hc
        have hcoeff : (MvPolynomial.C (a k) : MvPolynomial (Vars6 m) 𝕂) ≠ 0 := by
          intro hz
          apply ha
          apply MvPolynomial.C_injective (σ := Vars6 m)
          simpa only [map_zero] using hz
        have hsm := (mul_eq_zero.mp hc.symm).resolve_left hcoeff
        rw [nsmul_eq_mul] at hsm
        exact (mul_eq_zero.mp hsm).resolve_left (by
          intro hh
          have hz : ((K (u.1,u.2) + 1 : ℕ) : 𝕂) = 0 := by
            apply MvPolynomial.C_injective (σ := Vars6 m)
            simpa only [map_natCast, map_zero] using hh
          exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)) hz)
  exact go _ J rfl hw


end CompoundFeasibility.Auxiliary6
namespace CompoundFeasibility.Auxiliary6
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

def kernelChart6 {m : ℕ} (a : Fin 6 → 𝕂) (k : Fin m → Fin 6)
    (u : Vars6 m) : MvPolynomial (Vars6 m) 𝕂 :=
  if u.2 = k u.1 then
    -(∑ j ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C (a j / a (k u.1)) * MvPolynomial.X (u.1,j))
  else MvPolynomial.X u

def kernelRestriction6 {m : ℕ} (a : Fin 6 → 𝕂) (k : Fin m → Fin 6) :
    MvPolynomial (Vars6 m) 𝕂 →+* MvPolynomial (Vars6 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (kernelChart6 a k)

theorem kernelChart6_form {m : ℕ} (a : Fin 6 → 𝕂)
    (k : Fin m → Fin 6) (hk : ∀ h, a (k h) ≠ 0) (h : Fin m) :
    (∑ j : Fin 6, MvPolynomial.C (a j) * kernelChart6 a k (h,j)) = 0 := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k h))]
  have hfree : (∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) *
      kernelChart6 a k (h,j)) =
      ∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [kernelChart6, (Finset.mem_erase.mp hj).1]
  rw [hfree]
  have hpivot : MvPolynomial.C (a (k h)) * kernelChart6 a k (h,k h) =
      -(∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j)) := by
    simp only [kernelChart6, Prod.fst, Prod.snd, if_pos rfl, ite_true, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    congr 1
    field_simp [hk h]
  rw [hpivot]
  ring

def chartTransport6 {m : ℕ} (a : Fin 6 → 𝕂) (p : Fin 6) (k : Fin m → Fin 6) :
    MvPolynomial (Vars6 m) 𝕂 →+* MvPolynomial (Vars6 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u =>
    MvPolynomial.C ((a p)⁻¹) * kernelChart6 a k u)

theorem chartTransport6_variable {m : ℕ} (a : Fin 6 → 𝕂)
    (p : Fin 6) (hp : a p ≠ 0) (k : Fin m → Fin 6)
    (hk : ∀ h, a (k h) ≠ 0) (u : Vars6 m) :
    chartTransport6 a p k (chart6 a p u) = kernelChart6 a k u := by
  have hcancel : (MvPolynomial.C (a p) : MvPolynomial (Vars6 m) 𝕂) *
      MvPolynomial.C ((a p)⁻¹) = 1 := by
    rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hp, map_one]
  by_cases hu : u.2 = p
  · have hsum := kernelChart6_form a k hk u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hsum
    have hrel : -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
        kernelChart6 a k (u.1,j)) =
        MvPolynomial.C (a p) * kernelChart6 a k (u.1,p) := by
      linear_combination -hsum
    simp only [chart6, if_pos hu, map_neg, map_sum, map_mul]
    simp only [chartTransport6, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((a p)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
            kernelChart6 a k (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [hrel, ← mul_assoc, mul_comm _ (MvPolynomial.C (a p)), hcancel]
        simp [← hu]
  · simp only [chart6, if_neg hu, map_mul]
    simp only [chartTransport6, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    rw [← mul_assoc, hcancel, one_mul]

theorem chartTransport6_substitute {m : ℕ} (a : Fin 6 → 𝕂)
    (p : Fin 6) (hp : a p ≠ 0) (k : Fin m → Fin 6)
    (hk : ∀ h, a (k h) ≠ 0) (P : MvPolynomial (Vars6 m) 𝕂) :
    chartTransport6 a p k (substitute6 a p P) = kernelRestriction6 a k P := by
  have he : (chartTransport6 a p k).comp (substitute6 a p) = kernelRestriction6 a k := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [substitute6, chartTransport6, kernelRestriction6]
    · intro u
      simpa [substitute6, kernelRestriction6] using chartTransport6_variable a p hp k hk u
  exact congrArg (fun f => f P) he

theorem derivative6_zero_of_block_excess {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) 𝕂) (hP : homogeneous6 r P)
    (J : Vars6 m →₀ ℕ) (h : Fin m) (hJ : r h < ∑ j : Fin 6, J (h,j)) :
    derivative6 J P = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [derivative6_coeff, MvPolynomial.coeff_zero]
  have hz : P.coeff (d + J) = 0 := by
    by_contra hn
    have hdegree := hP (d + J) (MvPolynomial.mem_support_iff.mpr hn) h
    have hle : (∑ j : Fin 6, J (h,j)) ≤ ∑ j : Fin 6, (d + J) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finsupp.add_apply]
      omega
    omega
  rw [hz, zero_mul]

theorem matrix6_kernel_all_derivatives {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → 𝕂) (p : Fin 3 → Fin 6 → Fin 6)
    (hp : ∀ tau s, a tau s (p tau s) ≠ 0)
    (c : RothAuxCoefficients r → 𝕂)
    (hc : (matrix6 r eta a p).mulVec c = 0)
    (tau : Fin 3) (s : Fin 6) (J : Vars6 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (1 / 6 - eta) * m)
    (k : Fin m → Fin 6) (hk : ∀ h, a tau s (k h) ≠ 0) :
    kernelRestriction6 (a tau s) k (derivative6 J (polynomial6 c)) = 0 := by
  have hpivot := (matrix6_kernel_iff_restrictions r eta a p c).mp hc
  have hall : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < (1 / 6 - eta) * m →
      substitute6 (a tau s) (p tau s)
        (derivative6 (pivotDerivative6 (p tau s) i) (polynomial6 c)) = 0 := by
    intro i hi
    by_cases hb : ∀ h, i h ≤ r h
    · let iFin : RothAuxPivots r := fun h => ⟨i h, by have hh := hb h; omega⟩
      exact hpivot tau s ⟨iFin, hi⟩
    · push_neg at hb
      obtain ⟨h, hh⟩ := hb
      have hsum : (∑ j : Fin 6, pivotDerivative6 (p tau s) i (h,j)) = i h := by
        simp [pivotDerivative6, Finset.sum_ite_eq, Finset.sum_ite_eq']
      have hz := derivative6_zero_of_block_excess r (polynomial6 c) (polynomial6_homogeneous c)
        (pivotDerivative6 (p tau s) i) h (by rw [hsum]; exact hh)
      simp [hz]
  rw [← chartTransport6_substitute (a tau s) (p tau s) (hp tau s) k hk]
  rw [rothSource_scaled_mixed_vanishing r (a tau s) (p tau s) (hp tau s) _
    (polynomial6 c) hall J hJ, map_zero]

end CompoundFeasibility.Auxiliary6
namespace CompoundFeasibility.Auxiliary6
variable {R S : Type*} [CommRing R] [CommRing S]

theorem derivative6_map {m : ℕ} (f : R →+* S) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) R) :
    (derivative6 J P).map f = derivative6 J (P.map f) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_map, derivative6_coeff, map_mul, map_prod, map_natCast]

theorem chart6_map {m : ℕ} (f : R →+* S) (a : Fin 6 → R) (k : Fin 6) (u : Vars6 m) :
    (chart6 a k u).map f = chart6 (fun j => f (a j)) k u := by
  unfold chart6
  split_ifs <;> simp [map_sum, map_mul]

theorem substitute6_map {m : ℕ} (f : R →+* S) (a : Fin 6 → R) (k : Fin 6)
    (P : MvPolynomial (Vars6 m) R) :
    (substitute6 a k P).map f = substitute6 (fun j => f (a j)) k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute6]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show substitute6 a k (MvPolynomial.X v) = chart6 a k v by simp [substitute6]]
    rw [chart6_map]
    simp [substitute6]

theorem polynomial6_map {m : ℕ} {r : Fin m → ℕ} (f : R →+* S)
    (c : RothAuxCoefficients r → R) :
    (polynomial6 c).map f = polynomial6 (fun b => f (c b)) := by
  simp [polynomial6]

theorem matrix6_map {m : ℕ} (f : R →+* S) (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → R) (p : Fin 3 → Fin 6 → Fin 6)
    (q : Equations6 r eta) (b : RothAuxCoefficients r) :
    f (matrix6 r eta a p q b) = matrix6 r eta (fun tau s j => f (a tau s j)) p q b := by
  unfold matrix6 equation6
  rw [← MvPolynomial.coeff_map, substitute6_map, derivative6_map]
  simp

end CompoundFeasibility.Auxiliary6
namespace Aux6Norm

def integralNormModel (K : Type*) [Field K] [NumberField K] : NormedCommRing (𝓞 K) := by
  classical
  let b := Module.finBasis ℤ (𝓞 K)
  letI : NormedRing (Matrix (Fin (Module.finrank ℤ (𝓞 K))) (Fin (Module.finrank ℤ (𝓞 K))) ℤ) := Matrix.linftyOpNormedRing
  exact NormedCommRing.induced (𝓞 K) _ (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)

theorem integralNormModel_norm {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    @norm _ (integralNormModel K).toNorm x =
      @norm _ (Matrix.linftyOpNormedRing (n := Fin (Module.finrank ℤ (𝓞 K))) (α := ℤ)).toNorm
        (Algebra.leftMulMatrix (Module.finBasis ℤ (𝓞 K)) x) := rfl


theorem integralNormModel_one {K : Type*} [Field K] [NumberField K] :
    @norm _ (integralNormModel K).toNorm (1 : 𝓞 K) = 1 := by
  classical
  letI : Nonempty (Fin (Module.finrank ℤ (𝓞 K))) := ⟨⟨0,Module.finrank_pos⟩⟩
  letI : NormedRing (Matrix (Fin (Module.finrank ℤ (𝓞 K))) (Fin (Module.finrank ℤ (𝓞 K))) ℤ) := Matrix.linftyOpNormedRing
  rw [integralNormModel_norm,map_one]
  exact norm_one

theorem integralNormModel_coordinates {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    ‖(fun i => (Module.finBasis ℤ (𝓞 K)).repr x i)‖ ≤
      @norm _ (integralNormModel K).toNorm x *
        ‖(fun i => (Module.finBasis ℤ (𝓞 K)).repr (1 : 𝓞 K) i)‖ := by
  classical
  let b := Module.finBasis ℤ (𝓞 K)
  letI : NormedRing (Matrix (Fin (Module.finrank ℤ (𝓞 K))) (Fin (Module.finrank ℤ (𝓞 K))) ℤ) := Matrix.linftyOpNormedRing
  rw [integralNormModel_norm]
  have he : (Algebra.leftMulMatrix b x).mulVec (fun i => b.repr 1 i) = (fun i => b.repr x i) := by
    rw [Algebra.leftMulMatrix_mulVec_repr,mul_one]
  rw [← he]
  exact Matrix.linfty_opNorm_mulVec _ _

end Aux6Norm
namespace CompoundFeasibility.Auxiliary6
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

noncomputable def integralMatrix6 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) (p : Fin 3 → Fin 6 → Fin 6) :
    Matrix (Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
      (RothAuxCoefficients r) ℤ :=
  fun q b => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix6 r eta a p q.1 b) q.2

theorem integralMatrix6_kernel {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) (p : Fin 3 → Fin 6 → Fin 6)
    (c : RothAuxCoefficients r → ℤ) :
    (integralMatrix6 r eta a p).mulVec c = 0 ↔
      (matrix6 r eta a p).mulVec (fun b => (c b : 𝓞 𝕂)) = 0 := by
  let b := Module.finBasis ℤ (𝓞 𝕂)
  have he (q : Equations6 r eta) (k : Fin (Module.finrank ℤ (𝓞 𝕂))) :
      (integralMatrix6 r eta a p).mulVec c (q,k) =
        b.repr ((matrix6 r eta a p).mulVec (fun j => (c j : 𝓞 𝕂)) q) k := by
    simp only [Matrix.mulVec, dotProduct, integralMatrix6, map_sum, Finsupp.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg (fun x => x k) (b.repr.map_smul (c j) (matrix6 r eta a p q j))
    simpa only [Finsupp.smul_apply, smul_eq_mul, Algebra.smul_def, map_intCast, mul_comm, eq_intCast, b] using h.symm
  constructor
  · intro hz
    funext q
    apply b.repr.injective
    ext k
    rw [Pi.zero_apply, map_zero]
    simpa only [← he, Pi.zero_apply] using congrFun hz (q,k)
  · intro hz
    funext q
    rw [he, hz, Pi.zero_apply, map_zero]
    rfl

noncomputable def integralHeightBase6 (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) : ℝ :=
  letI := Aux6Norm.integralNormModel 𝕂
  max 1 (∑ tau : Fin 3, ∑ s : Fin 6, ∑ j : Fin 6, ‖a tau s j‖)

noncomputable def integralCoordinateConstant6 (𝕂 : Type*) [Field 𝕂] [NumberField 𝕂] : ℝ :=
  max 1 ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖

theorem integralMatrix6_entry_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) (p : Fin 3 → Fin 6 → Fin 6)
    (q : Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
    (b : RothAuxCoefficients r) :
    ‖integralMatrix6 r eta a p q b‖ ≤ integralCoordinateConstant6 𝕂 *
      (12 * integralHeightBase6 a)^(∑ h, r h) := by
  letI := Aux6Norm.integralNormModel 𝕂
  letI : NormOneClass (𝓞 𝕂) := ⟨Aux6Norm.integralNormModel_one⟩
  have ha : ∀ tau s j, ‖a tau s j‖ ≤ integralHeightBase6 a := by
    intro tau s j
    apply le_trans _ (le_max_right _ _)
    apply le_trans (Finset.single_le_sum (fun j _ => norm_nonneg (a tau s j)) (Finset.mem_univ j))
    apply le_trans (Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j))) (Finset.mem_univ s))
    exact Finset.single_le_sum (fun tau _ => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j)))) (Finset.mem_univ tau)
  have hx : ‖matrix6 r eta a p q.1 b‖ ≤ (12 * integralHeightBase6 a)^(∑ h, r h) := by
    apply Aux6Height.transformed_entry_norm6
    · exact le_max_left _ _
    · exact ha _ _
  have hc := Aux6Norm.integralNormModel_coordinates (matrix6 r eta a p q.1 b)
  have hcoord := norm_le_pi_norm (fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr
    (matrix6 r eta a p q.1 b) i) q.2
  calc
    _ ≤ ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix6 r eta a p q.1 b) i)‖ := hcoord
    _ ≤ ‖matrix6 r eta a p q.1 b‖ *
        ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖ := hc
    _ ≤ (12 * integralHeightBase6 a)^(∑ h, r h) * integralCoordinateConstant6 𝕂 :=
      mul_le_mul hx (le_max_right _ _) (norm_nonneg _) (pow_nonneg (by have hh : 1 ≤ integralHeightBase6 a := le_max_left _ _; linarith) _)
    _ = _ := mul_comm _ _

end CompoundFeasibility.Auxiliary6
namespace CompoundFeasibility.Auxiliary6
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]
attribute [local instance] Matrix.seminormedAddCommGroup

theorem dimension6_le_pow {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) :
    rothAuxDimension r ≤ 64^(∑ h, r h) := by
  rw [rothAuxDimension_eq]
  calc
    _ ≤ ∏ h, 64^r h := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro h _
      calc
        (r h + 5).choose 5 ≤ 2^(r h + 5) :=
          (Nat.choose_le_two_pow _ _ (by omega)).le
        _ ≤ 2^(6 * r h) := Nat.pow_le_pow_right (by decide) (by have hh := hr h; omega)
        _ = 64^r h := by rw [pow_mul]; norm_num
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

noncomputable def integralSiegelConstant6 (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) : ℝ :=
  64 * (12 * integralHeightBase6 a * integralCoordinateConstant6 𝕂)

theorem integralSiegelConstant6_ge_one (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) :
    1 ≤ integralSiegelConstant6 a := by
  have hA : 1 ≤ integralHeightBase6 a := le_max_left _ _
  have hC : 1 ≤ integralCoordinateConstant6 𝕂 := le_max_left _ _
  dsimp [integralSiegelConstant6]
  nlinarith

theorem integralMatrix6_uniform_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (hm : 0 < m) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) (p : Fin 3 → Fin 6 → Fin 6) :
    (Fintype.card (RothAuxCoefficients r) : ℝ) * max 1 ‖integralMatrix6 r eta a p‖ ≤
      integralSiegelConstant6 a ^ (∑ h, r h) := by
  let A := integralHeightBase6 a
  let C := integralCoordinateConstant6 𝕂
  have hA : 1 ≤ A := le_max_left _ _
  have hC : 1 ≤ C := le_max_left _ _
  have hR : 1 ≤ ∑ h, r h := by
    have hp := hr ⟨0, hm⟩
    have hh : r ⟨0, hm⟩ ≤ ∑ h, r h :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  have hbase : 1 ≤ 12 * A * C := by nlinarith
  have hnorm : ‖integralMatrix6 r eta a p‖ ≤ (12 * A * C)^(∑ h, r h) := by
    apply (Matrix.norm_le_iff (by positivity)).mpr
    intro q b
    calc
      _ ≤ C * (12 * A)^(∑ h, r h) := integralMatrix6_entry_bound r eta a p q b
      _ ≤ C^(∑ h, r h) * (12 * A)^(∑ h, r h) :=
        mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ hC hR) (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  calc
    _ ≤ (64 : ℝ)^(∑ h, r h) * (12 * A * C)^(∑ h, r h) :=
      mul_le_mul (by exact_mod_cast dimension6_le_pow r hr)
        (max_le (one_le_pow₀ hbase) hnorm) (by positivity) (by positivity)
    _ = _ := by rw [← mul_pow]; rfl

theorem integralMatrix6_bounded_kernel {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta^2)⁻¹ * Real.log (36 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ))
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) (p : Fin 3 → Fin 6 → Fin 6) :
    ∃ c : RothAuxCoefficients r → ℤ, c ≠ 0 ∧
      (integralMatrix6 r eta a p).mulVec c = 0 ∧
      ‖c‖ ≤ integralSiegelConstant6 a ^ (∑ h, r h) := by
  have hd : 0 < Module.finrank ℚ 𝕂 := Module.finrank_pos
  have hN := dimension6_pos r
  have hhalf := coordinate_rows6_le_half r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hlt := coordinate_rows6_lt r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hmpos : 0 < m := by
    have hd' : (1 : ℝ) ≤ Module.finrank ℚ 𝕂 := by exact_mod_cast hd
    have hlog : 0 < Real.log (36 * (Module.finrank ℚ 𝕂 : ℝ)) := Real.log_pos (by linarith)
    have hh : 0 < (m : ℝ) := lt_of_lt_of_le (mul_pos (by positivity) hlog) hm
    exact_mod_cast hh
  have hD := integralSiegelConstant6_ge_one a
  by_cases hrows : Fintype.card (Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) = 0
  · obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hN
    let c : RothAuxCoefficients r → ℤ := fun b => if b = b₀ then 1 else 0
    refine ⟨c, ?_, ?_, ?_⟩
    · intro hc
      have hh := congrFun hc b₀
      simp [c] at hh
    · funext q
      have hh := Fintype.card_pos_iff.mpr (Nonempty.intro q)
      omega
    · have hc : ‖c‖ ≤ (1 : ℝ) := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro b
        dsimp [c]
        split_ifs <;> norm_num
      exact hc.trans (one_le_pow₀ hD)
  · have hcount : Fintype.card (Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) <
        Fintype.card (RothAuxCoefficients r) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm] using hlt
    obtain ⟨c, hc, hker, hbound⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le
      (integralMatrix6 r eta a p) hcount (Nat.pos_of_ne_zero hrows)
    refine ⟨c, hc, hker, ?_⟩
    have hrowsR : (Fintype.card (Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) ≤
        (Fintype.card (RothAuxCoefficients r) : ℝ) / 2 := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm, Nat.cast_mul, rothAuxDimension] using hhalf
    have hden : 0 < (Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) := by
      exact sub_pos.mpr (by exact_mod_cast hcount)
    have hexp : (Fintype.card (Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) /
        ((Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))) ≤ 1 := by
      apply (div_le_one hden).mpr
      linarith
    have hbase : 1 ≤ (Fintype.card (RothAuxCoefficients r) : ℝ) *
        max 1 ‖integralMatrix6 r eta a p‖ := by
      have hn : (1 : ℝ) ≤ Fintype.card (RothAuxCoefficients r) := by exact_mod_cast hN
      nlinarith [le_max_left (1 : ℝ) ‖integralMatrix6 r eta a p‖]
    exact hbound.trans ((Real.rpow_le_self_of_one_le hbase hexp).trans
      (integralMatrix6_uniform_bound r hr hmpos eta a p))

end CompoundFeasibility.Auxiliary6
namespace CompoundFeasibility.Auxiliary6

noncomputable def height6 {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) : ℕ :=
  P.support.sup (fun d => (P.coeff d).natAbs)

theorem polynomial6_ne_zero {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ)
    (hc : c ≠ 0) : polynomial6 c ≠ 0 := by
  intro hz
  apply hc
  funext b
  have hh := polynomial6_coeff c b
  rw [hz, MvPolynomial.coeff_zero] at hh
  exact hh.symm

theorem polynomial6_height_le {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ) :
    (height6 (polynomial6 c) : ℝ) ≤ ‖c‖ := by
  have hs : ∀ d ∈ (polynomial6 c).support,
      ((polynomial6 c).coeff d).natAbs ≤ Nat.floor ‖c‖ := by
    intro d hd
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    subst d
    rw [polynomial6_coeff]
    apply Nat.le_floor
    simpa only [Int.norm_eq_abs, Int.cast_natAbs, Int.cast_abs] using norm_le_pi_norm c b
  have hh : height6 (polynomial6 c) ≤ Nat.floor ‖c‖ := Finset.sup_le hs
  exact (by exact_mod_cast hh : (height6 (polynomial6 c) : ℝ) ≤ Nat.floor ‖c‖).trans
    (Nat.floor_le (norm_nonneg _))

variable {𝕂 : Type*} [Field 𝕂]

theorem kernelChart6_scale {m : ℕ} (a : Fin 6 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 6) (u : Vars6 m) :
    kernelChart6 (fun j => M * a j) k u = kernelChart6 a k u := by
  unfold kernelChart6
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_div_mul_left _ _ hM]
  · rfl

theorem kernelRestriction6_scale {m : ℕ} (a : Fin 6 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 6) (P : MvPolynomial (Vars6 m) 𝕂) :
    kernelRestriction6 (fun j => M * a j) k P = kernelRestriction6 a k P := by
  have he : kernelChart6 (m := m) (fun j => M * a j) k = kernelChart6 a k :=
    funext (kernelChart6_scale a M hM k)
  simp only [kernelRestriction6, he]

theorem kernelRestriction6_map {𝕃 : Type*} [Field 𝕃] {m : ℕ}
    (f : 𝕂 →+* 𝕃) (a : Fin 6 → 𝕂) (k : Fin m → Fin 6)
    (P : MvPolynomial (Vars6 m) 𝕂) :
    (kernelRestriction6 a k P).map f =
      kernelRestriction6 (fun j => f (a j)) k (P.map f) := by
  have hchart (u : Vars6 m) :
      (kernelChart6 a k u).map f = kernelChart6 (fun j => f (a j)) k u := by
    unfold kernelChart6
    split_ifs <;> simp [map_sum, map_mul, map_div₀]
  induction P using MvPolynomial.induction_on with
  | C c => simp [kernelRestriction6]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show kernelRestriction6 a k (MvPolynomial.X v) = kernelChart6 a k v by simp [kernelRestriction6]]
    rw [hchart]
    simp [kernelRestriction6]

variable [NumberField 𝕂]

theorem integral_auxiliary6
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (36 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars6 m) ℤ,
        P ≠ 0 ∧ homogeneous6 r P ∧ (height6 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars6 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 6 - eta) * m →
          ∀ k : Fin m → Fin 6, (∀ h, (a tau s (k h) : 𝕂) ≠ 0) →
          kernelRestriction6 (fun j => (a tau s j : 𝕂)) k
            (derivative6 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  let p : Fin 3 → Fin 6 → Fin 6 := fun tau s => Classical.choose (ha tau s)
  have hp : ∀ tau s, a tau s (p tau s) ≠ 0 := fun tau s => Classical.choose_spec (ha tau s)
  refine ⟨integralSiegelConstant6 a, integralSiegelConstant6_ge_one a, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨c, hc, hker, hbound⟩ := integralMatrix6_bounded_kernel r hr eta heta hm a p
  refine ⟨polynomial6 c, polynomial6_ne_zero c hc, polynomial6_homogeneous c,
    (polynomial6_height_le c).trans hbound, ?_⟩
  let f : 𝓞 𝕂 →+* 𝕂 := algebraMap _ _
  have hkerO := (integralMatrix6_kernel r eta a p c).mp hker
  have hkerK : (matrix6 r eta (fun tau s j => f (a tau s j)) p).mulVec
      (fun b => (c b : 𝕂)) = 0 := by
    funext q
    have hh := congrArg f (congrFun hkerO q)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast,
      matrix6_map, Pi.zero_apply, map_zero] using hh
  intro tau s J hJ k hk
  have hpK : ∀ tau s, f (a tau s (p tau s)) ≠ 0 := fun tau s =>
    (map_ne_zero_iff f (IsFractionRing.injective (𝓞 𝕂) 𝕂)).mpr (hp tau s)
  have hh := matrix6_kernel_all_derivatives r eta (fun tau s j => f (a tau s j)) p
    hpK (fun b => (c b : 𝕂)) hkerK tau s J hJ k hk
  simpa only [polynomial6_map, map_intCast] using hh

end CompoundFeasibility.Auxiliary6
namespace CompoundFeasibility.Auxiliary6
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

theorem source_integral_scaling6 (a : Fin 3 → Fin 6 → Fin 6 → 𝕂) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ b : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂,
      ∀ tau s j, (b tau s j : 𝕂) = (M : 𝕂) * a tau s j := by
  haveI : Algebra.IsAlgebraic ℚ 𝕂 := Algebra.IsAlgebraic.of_finite ℚ 𝕂
  haveI : Algebra.IsAlgebraic ℤ 𝕂 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := 𝕂)).mpr inferInstance
  obtain ⟨M, hM, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun q : Fin 3 × Fin 6 × Fin 6 => a q.1 q.2.1 q.2.2))
  have hint : ∀ tau s j, IsIntegral ℤ ((M : 𝕂) * a tau s j) := by
    intro tau s j
    simpa only [Algebra.smul_def, eq_intCast] using
      hi (a tau s j) (Finset.mem_image.mpr ⟨(tau,s,j),Finset.mem_univ _,rfl⟩)
  exact ⟨M, hM, (fun tau s j => ⟨(M : 𝕂) * a tau s j, hint tau s j⟩), fun _ _ _ => rfl⟩

theorem algebraic_auxiliary6 (a : Fin 3 → Fin 6 → Fin 6 → 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (36 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars6 m) ℤ,
        P ≠ 0 ∧ homogeneous6 r P ∧ (height6 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars6 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 6 - eta) * m →
          ∀ k : Fin m → Fin 6, (∀ h, a tau s (k h) ≠ 0) →
          kernelRestriction6 (a tau s) k
            (derivative6 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  obtain ⟨M, hM, b, hb⟩ := source_integral_scaling6 a
  have hMK : (M : 𝕂) ≠ 0 := by exact_mod_cast hM
  have hbn : ∀ tau s, ∃ j, b tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := ha tau s
    refine ⟨j, ?_⟩
    intro hz
    exact (mul_ne_zero hMK hj) (by rw [← hb tau s j, hz]; rfl)
  obtain ⟨D, hD, hconstruction⟩ := integral_auxiliary6 b hbn
  refine ⟨D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hderiv⟩ := hconstruction eta heta m hm r hr
  refine ⟨P, hP, hhom, hheight, ?_⟩
  intro tau s J hJ k hk
  have hbk : ∀ h, (b tau s (k h) : 𝕂) ≠ 0 := by
    intro h
    rw [hb]
    exact mul_ne_zero hMK (hk h)
  have hh := hderiv tau s J hJ k hbk
  simp only [hb] at hh
  rw [kernelRestriction6_scale (a tau s) (M : 𝕂) hMK] at hh
  exact hh

end CompoundFeasibility.Auxiliary6


namespace CompoundFeasibility.Auxiliary6

theorem row_nonzero6_of_det_one {K : Type*} [Field K]
    (A : Matrix (Fin 6) (Fin 6) K) (hA : A.det = 1) (s : Fin 6) :
    ∃ j : Fin 6, A s j ≠ 0 := by
  classical
  have hn : ¬ ∀ j : Fin 6, A s j = 0 := by
    intro hz
    exact one_ne_zero (hA.symm.trans (Matrix.det_eq_zero_of_row_eq_zero s hz))
  exact not_forall.mp hn

theorem compound_rows_nonzero6 {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det = 1) (s : Fin 6) :
    ∃ j : Fin 6, compound A s j ≠ 0 := by
  apply row_nonzero6_of_det_one (compound A)
  apply compound42_det_one
  exact hA

theorem source_forms_nonzero6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) : ∀ tau s, ∃ j, forms A2 A3 L tau s j ≠ 0 := by
  intro tau s
  fin_cases tau
  · obtain ⟨j, hj⟩ := compound_rows_nonzero6 L hL s
    exact ⟨j, hj⟩
  · obtain ⟨j, hj⟩ := compound_rows_nonzero6 A2 h2 s
    refine ⟨j, ?_⟩
    change (algebraMap ℚ ℝ) (compound A2 s j) ≠ 0
    exact (map_ne_zero_iff (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective).mpr hj
  · obtain ⟨j, hj⟩ := compound_rows_nonzero6 A3 h3 s
    refine ⟨j, ?_⟩
    change (algebraMap ℚ ℝ) (compound A3 s j) ≠ 0
    exact (map_ne_zero_iff (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective).mpr hj

end CompoundFeasibility.Auxiliary6

namespace CompoundFeasibility.Auxiliary6
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

noncomputable def integralRationalBasis6 (𝕂 : Type*) [Field 𝕂] [NumberField 𝕂] :
    Basis (Fin (Module.finrank ℤ (𝓞 𝕂))) ℚ 𝕂 :=
  Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) 𝕂 (Module.finBasis ℤ (𝓞 𝕂))

theorem integralMatrix6_coordinates {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) (p : Fin 3 → Fin 6 → Fin 6)
    (q : Equations6 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) (b : RothAuxCoefficients r) :
    (integralMatrix6 r eta a p q b : ℚ) =
      coordinates (integralRationalBasis6 𝕂)
        (matrix6 r eta (fun tau s j => (a tau s j : 𝕂)) p) q b := by
  have hh := Basis.localizationLocalization_repr_algebraMap
    ℚ (nonZeroDivisors ℤ) 𝕂 (Module.finBasis ℤ (𝓞 𝕂)) (matrix6 r eta a p q.1 b) q.2
  rw [matrix6_map] at hh
  exact hh.symm

theorem integralMatrix6_field_kernel {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 6 → Fin 6 → 𝓞 𝕂) (p : Fin 3 → Fin 6 → Fin 6)
    (c : RothAuxCoefficients r → ℤ) :
    (integralMatrix6 r eta a p).mulVec c = 0 ↔
      (∀ q, ∑ b, matrix6 r eta (fun tau s j => (a tau s j : 𝕂)) p q b * (c b : 𝕂) = 0) := by
  have he := integer_matrix_kernel
    (coordinates (integralRationalBasis6 𝕂)
      (matrix6 r eta (fun tau s j => (a tau s j : 𝕂)) p))
    (integralMatrix6 r eta a p) 1 one_ne_zero
    (fun q b => by simpa only [Int.cast_one, one_mul] using integralMatrix6_coordinates r eta a p q b) c
  exact he.trans (coordinates_kernel (integralRationalBasis6 𝕂) _ c).symm

end CompoundFeasibility.Auxiliary6

namespace CompoundFeasibility.Auxiliary6

theorem source_restriction6_real (K : IntermediateField ℚ ℝ) {m : ℕ}
    (a : Fin 6 → K) (k : Fin m → Fin 6) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) :
    (kernelRestriction6 a k (derivative6 J (P.map (Int.castRingHom K)))).map
      K.val.toRingHom =
      kernelRestriction6 (fun j => (a j : ℝ)) k
        (derivative6 J (P.map (Int.castRingHom ℝ))) := by
  rw [kernelRestriction6_map, derivative6_map, MvPolynomial.map_map]
  have hf : K.val.toRingHom.comp (Int.castRingHom K) = Int.castRingHom ℝ :=
    Subsingleton.elim _ _
  rw [hf]
  rfl

theorem source_auxiliary6_field (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K,
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (36 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars6 m) ℤ,
        P ≠ 0 ∧ homogeneous6 r P ∧ (height6 P : ℝ) ≤ D^(∑ h, r h) ∧
        (∀ tau s (J : Vars6 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 6 - eta) * m →
          ∀ k : Fin m → Fin 6,
            (∀ h, (⟨forms A2 A3 L tau s (k h), hmem tau s (k h)⟩ : K) ≠ 0) →
            kernelRestriction6 (fun j => (⟨forms A2 A3 L tau s j, hmem tau s j⟩ : K)) k
              (derivative6 J (P.map (Int.castRingHom K))) = 0) ∧
        (∀ tau s (J : Vars6 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 6 - eta) * m →
          ∀ k : Fin m → Fin 6, (∀ h, forms A2 A3 L tau s (k h) ≠ 0) →
            kernelRestriction6 (forms A2 A3 L tau s) k
              (derivative6 J (P.map (Int.castRingHom ℝ))) = 0) := by
  obtain ⟨K, hK, hmem⟩ := common_source_field A2 A3 L hL ha
  letI : FiniteDimensional ℚ K := hK
  letI : NumberField K := {}
  let a : Fin 3 → Fin 6 → Fin 6 → K := fun tau s j =>
    ⟨forms A2 A3 L tau s j, hmem tau s j⟩
  have hnonzero : ∀ tau s, ∃ j, a tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := source_forms_nonzero6 A2 A3 L h2 h3 hL tau s
    refine ⟨j, ?_⟩
    intro hh
    exact hj (congrArg Subtype.val hh)
  obtain ⟨D, hD, hconstruction⟩ := algebraic_auxiliary6 a hnonzero
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hderiv⟩ := hconstruction eta heta m hm r hr
  refine ⟨P, hP, hhom, hheight, hderiv, ?_⟩
  intro tau s J hJ k hk
  have hkK : ∀ h, a tau s (k h) ≠ 0 := by
    intro h hh
    exact hk h (congrArg Subtype.val hh)
  have he := source_restriction6_real K (a tau s) k J P
  rw [hderiv tau s J hJ k hkK, map_zero] at he
  exact he.symm

theorem source_auxiliary6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau s j, forms A2 A3 L tau s j ∈ K) ∧
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (36 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars6 m) ℤ,
        P ≠ 0 ∧ homogeneous6 r P ∧ (height6 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars6 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 6 - eta) * m →
          ∀ k : Fin m → Fin 6, (∀ h, forms A2 A3 L tau s (k h) ≠ 0) →
          kernelRestriction6 (forms A2 A3 L tau s) k
            (derivative6 J (P.map (Int.castRingHom ℝ))) = 0 := by
  obtain ⟨K, hK, hmem, D, hD, hconstruction⟩ := source_auxiliary6_field A2 A3 L h2 h3 hL ha
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hfield, hreal⟩ := hconstruction eta heta m hm r hr
  exact ⟨P, hP, hhom, hheight, hreal⟩

end CompoundFeasibility.Auxiliary6
