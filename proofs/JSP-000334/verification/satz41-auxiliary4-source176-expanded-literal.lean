import SubspaceBridge.AlgebraicLiouville4
import SubspaceBridge.OriginalAuxiliaryDual4
import SubspaceBridge.AuxiliaryFeasibility6
import SubspaceBridge.SourceMultiblock4
import SubspaceBridge.AuxiliaryProductFormula
import SubspaceBridge.OriginalSelectedInputs4
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import SubspaceBridge.SourceBlocks6
import Mathlib.Algebra.MvPolynomial.Funext

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceForms4Literal176

def forms4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (tau : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  if tau = 0 then L else if tau = 1 then A2.map (algebraMap ℚ ℝ) else A3.map (algebraMap ℚ ℝ)

def finiteMatrix4 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) :
    Matrix (Fin 4) (Fin 4) ℚ_[p] := A.map (algebraMap ℚ ℚ_[p])

theorem source_det_one4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau, (forms4 A2 A3 L tau).det = 1 := by
  intro tau
  fin_cases tau
  · exact hL
  · exact OriginalAuxiliaryDual4.mapped_det_one4 A2 h2
  · exact OriginalAuxiliaryDual4.mapped_det_one4 A3 h3

theorem source_unit4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau, IsUnit (forms4 A2 A3 L tau) := by
  intro tau
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [source_det_one4 A2 A3 L h2 h3 hL tau]
  exact isUnit_one

theorem finite_det_one4 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (hA : A.det = 1) : (finiteMatrix4 p A).det = 1 :=
  OriginalAuxiliaryDual4.mapped_det_one4 A hA

theorem source_algebraic4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ tau i j, IsAlgebraic ℚ (forms4 A2 A3 L tau i j) := by
  intro tau i j
  fin_cases tau
  · exact ha i j
  · exact isAlgebraic_algebraMap _
  · exact isAlgebraic_algebraMap _

theorem common_source_field4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∀ tau i j, forms4 A2 A3 L tau i j ∈ K := by
  obtain ⟨K,hK,hmem⟩ := liouville4_common_field L ha
  refine ⟨K,hK,?_⟩
  intro tau i j
  fin_cases tau
  · exact hmem i j
  · exact K.algebraMap_mem _
  · exact K.algebraMap_mem _

theorem source_rows_nonzero4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1) :
    ∀ tau i, ∃ j, forms4 A2 A3 L tau i j ≠ 0 := by
  intro tau i
  by_contra! hz
  have he := Matrix.det_eq_zero_of_row_eq_zero i hz
  rw [source_det_one4 A2 A3 L h2 h3 hL tau] at he
  exact one_ne_zero he

end CompoundFeasibility.SourceForms4Literal176

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176

abbrev Block4 (r : ℕ) := {b : Fin 4 → Fin (r + 1) // ∑ i, (b i).val = r}

def blockNatEquiv4 (r : ℕ) : Block4 r ≃ {b : Fin 4 → ℕ // ∑ i, b i = r} where
  toFun b := ⟨fun i => (b.val i).val,b.property⟩
  invFun b := ⟨fun i => ⟨b.val i,by
    have hh : b.val i ≤ ∑ j, b.val j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [b.property] at hh
    omega⟩,b.property⟩
  left_inv b := by rfl
  right_inv b := by rfl

theorem block4_card (r : ℕ) : Fintype.card (Block4 r) = (r + 3).choose 3 := by
  letI : Fintype {b : Fin 4 → ℕ // ∑ i, b i = r} := Fintype.ofEquiv (Sym (Fin 4) r) (Sym.equivNatSumOfFintype (Fin 4) r)
  rw [Fintype.card_congr (blockNatEquiv4 r),← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin 4) r),Sym.card_sym_eq_choose]
  simpa only [Fintype.card_fin,show 4 + r - 1 = r + 3 by omega] using (Nat.choose_symm_add (a := r) (b := 3))

noncomputable def rothAuxBlockPerm (r : ℕ) (e : Equiv.Perm (Fin 4)) :
    Block4 r ≃ Block4 r where
  toFun b := ⟨fun i => b.val (e i), by
    change (∑ i, (b.val (e i)).val) = r
    exact (Equiv.sum_comp e (fun i => (b.val i).val)).trans b.property⟩
  invFun b := ⟨fun i => b.val (e.symm i), by
    change (∑ i, (b.val (e.symm i)).val) = r
    exact (Equiv.sum_comp e.symm (fun i => (b.val i).val)).trans b.property⟩
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

theorem rothAuxBlock_coordinate_sum (r : ℕ) (i : Fin 4) :
    (∑ b : Block4 r, ((b.val i).val : ℝ)) =
      ∑ b : Block4 r, ((b.val 0).val : ℝ) := by
  have h := (rothAuxBlockPerm r (Equiv.swap 0 i)).sum_comp
    (fun b : Block4 r => ((b.val 0).val : ℝ))
  simpa [rothAuxBlockPerm] using h

theorem rothAuxBlock_center_sum (r : ℕ) (hr : 0 < r) :
    (∑ b : Block4 r, (1 / 4 - ((b.val 0).val : ℝ) / r)) = 0 := by
  have htotal : (∑ b : Block4 r, ∑ i : Fin 4, ((b.val i).val : ℝ)) =
      (Fintype.card (Block4 r) : ℝ) * r := by
    calc
      _ = ∑ _b : Block4 r, (r : ℝ) := by
        apply Finset.sum_congr rfl
        intro b _
        exact_mod_cast b.property
      _ = _ := by simp
  rw [Finset.sum_comm] at htotal
  simp_rw [rothAuxBlock_coordinate_sum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  have hsum :
      (∑ b : Block4 r, ((b.val 0).val : ℝ)) =
        (Fintype.card (Block4 r) : ℝ) * r / 4 := by
    calc
      _ = (4 * (∑ b : Block4 r,
          ((b.val 0).val : ℝ))) / 4 := by ring
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          congrArg (fun x : ℝ => x / 4) htotal
  have hr' : (r : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_div, hsum]
  field_simp [hr']
  ring

theorem rothAuxBlock_center_bound (r : ℕ) (hr : 0 < r) (b : Block4 r) :
    |1 / 4 - ((b.val 0).val : ℝ) / r| ≤ 1 := by
  have hle : ((b.val 0).val : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ (b.val 0).isLt
  have hz : 0 ≤ ((b.val 0).val : ℝ) / r := by positivity
  have hu : ((b.val 0).val : ℝ) / r ≤ 1 := (div_le_one (by positivity)).mpr hle
  rw [abs_le]
  constructor <;> linarith

theorem rothAuxBlock_exp_sum (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : Block4 r, Real.exp (u * (1 / 4 - ((b.val 0).val : ℝ) / r))) ≤
      (Fintype.card (Block4 r) : ℝ) * Real.exp (u ^ 2) := by
  have hpoint (b : Block4 r) :
      Real.exp (u * (1 / 4 - ((b.val 0).val : ℝ) / r)) ≤
        1 + u * (1 / 4 - ((b.val 0).val : ℝ) / r) + u ^ 2 := by
    have hb := rothAuxBlock_center_bound r hr b
    have hmul : |u * (1 / 4 - ((b.val 0).val : ℝ) / r)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hu]
      exact (mul_le_mul_of_nonneg_left hb hu).trans (by simpa using hu')
    have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hmul)).2
    have hsq : (u * (1 / 4 - ((b.val 0).val : ℝ) / r)) ^ 2 ≤ u ^ 2 := by
      rw [mul_pow]
      have hs : (1 / 4 - ((b.val 0).val : ℝ) / r) ^ 2 ≤ 1 := by
        have hs := mul_self_le_mul_self (abs_nonneg (1 / 4 - ((b.val 0).val : ℝ) / r)) hb
        simpa only [← sq, sq_abs, one_pow] using hs
      exact (mul_le_mul_of_nonneg_left hs (sq_nonneg u)).trans_eq (mul_one _)
    linarith
  calc
    _ ≤ ∑ b : Block4 r, (1 + u * (1 / 4 - ((b.val 0).val : ℝ) / r) + u ^ 2) :=
      Finset.sum_le_sum (fun b _ => hpoint b)
    _ = (Fintype.card (Block4 r) : ℝ) * (1 + u ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, rothAuxBlock_center_sum r hr, mul_zero, add_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp (u ^ 2)) (by positivity)



open scoped Classical

abbrev RothAuxCoefficients {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Block4 (r h)

abbrev RothAuxPivots {m : ℕ} (r : Fin m → ℕ) := (h : Fin m) → Fin (r h + 1)

noncomputable def rothAuxDimension {m : ℕ} (r : Fin m → ℕ) : ℕ :=
  Fintype.card (RothAuxCoefficients r)

theorem rothAuxDimension_eq {m : ℕ} (r : Fin m → ℕ) :
    rothAuxDimension r = ∏ h, (r h + 3).choose 3 := by
  simp [rothAuxDimension, Fintype.card_pi, block4_card]

noncomputable def rothAuxCentered {m : ℕ} (r : Fin m → ℕ) (b : RothAuxCoefficients r) : ℝ :=
  ∑ h, (1 / 4 - ((b h).val 0).val / (r h : ℝ))

abbrev RothAuxBad {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :=
  {b : RothAuxCoefficients r // eta * m < rothAuxCentered r b}

noncomputable def rothAuxPivotCondition {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (i : RothAuxPivots r) : Prop :=
  (∑ h, ((i h).val : ℝ) / r h) < (1 / 4 - eta) * m

theorem rothAux_exp_moment {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) ≤
      (rothAuxDimension r : ℝ) * Real.exp ((m : ℝ) * u ^ 2) := by
  have hfactor : (∑ b : RothAuxCoefficients r, Real.exp (u * rothAuxCentered r b)) =
      ∏ h, ∑ b : Block4 (r h),
        Real.exp (u * (1 / 4 - ((b.val 0).val : ℝ) / r h)) := by
    simp only [rothAuxCentered, Finset.mul_sum, Real.exp_sum]
    exact (Fintype.prod_sum (fun (h : Fin m) (b : Block4 (r h)) =>
      Real.exp (u * (1 / 4 - ((b.val 0).val : ℝ) / r h)))).symm
  rw [hfactor]
  calc
    _ ≤ ∏ h, ((Fintype.card (Block4 (r h)) : ℝ) * Real.exp (u ^ 2)) := by
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

theorem rothAuxBad_card_zero {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) (heta : 1 / 4 ≤ eta) :
    Fintype.card (RothAuxBad r eta) = 0 := by
  have hcenter (b : RothAuxCoefficients r) : rothAuxCentered r b ≤ (m : ℝ) / 4 := by
    calc
      _ ≤ ∑ _h : Fin m, (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro h _
        have hz : 0 ≤ (((b h).val 0).val : ℝ) / (r h : ℝ) := by positivity
        linarith
      _ = _ := by simp [div_eq_mul_inv]
  have hem : (m : ℝ) / 4 ≤ eta * m := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  haveI : IsEmpty (RothAuxBad r eta) := ⟨fun b =>
    (not_lt_of_ge ((hcenter b.val).trans hem)) b.property⟩
  exact Fintype.card_eq_zero

theorem rothAuxBad_exp_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta) :
    (Fintype.card (RothAuxBad r eta) : ℝ) ≤
      (rothAuxDimension r : ℝ) * Real.exp (-eta ^ 2 * m / 4) := by
  by_cases he : eta < 1 / 4
  · have hu : 0 ≤ eta / 2 := by positivity
    have hu' : eta / 2 ≤ 1 := by linarith
    have hb := rothAux_exp_tail_parameter r hr eta (eta / 2) hu hu'
    convert hb using 1 <;> congr 2 <;> ring
  · rw [rothAuxBad_card_zero r eta (le_of_not_gt he)]
    simp only [Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le




abbrev Equations4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) := Fin 12 × RothAuxBad r eta

theorem dimension4_pos {m : ℕ} (r : Fin m → ℕ) : 0 < rothAuxDimension r := by
  rw [rothAuxDimension_eq]
  exact Finset.prod_pos (fun h _ => Nat.choose_pos (by omega))

theorem coordinate_rows4_le_half {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (d : ℕ) (hd : 0 < d)
    (hm : 4 * (eta^2)⁻¹ * Real.log (24 * (d : ℝ)) ≤ (m : ℝ)) :
    (d * Fintype.card (Equations4 r eta) : ℝ) ≤ (rothAuxDimension r : ℝ) / 2 := by
  have hs : 0 < eta^2 := sq_pos_of_pos heta
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_left hm hs.le
  have hid : eta^2 * (4 * (eta^2)⁻¹ * Real.log (24 * (d : ℝ))) = 4 * Real.log (24 * (d : ℝ)) := by field_simp
  rw [hid] at hmul
  have he : Real.exp (-eta^2 * m / 4) ≤ 1 / (24 * (d : ℝ)) := by
    calc
      _ ≤ Real.exp (-Real.log (24 * (d : ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity),one_div]
  have hb := mul_le_mul_of_nonneg_left (rothAuxBad_exp_bound r hr eta heta) (show (0 : ℝ) ≤ 12 * d by positivity)
  calc
    _ = (12 * (d : ℝ)) * (Fintype.card (RothAuxBad r eta) : ℝ) := by simp only [Equations4,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]; ring
    _ ≤ (12 * (d : ℝ)) * ((rothAuxDimension r : ℝ) * Real.exp (-eta^2 * m / 4)) := hb
    _ ≤ (12 * (d : ℝ)) * ((rothAuxDimension r : ℝ) * (1 / (24 * (d : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by field_simp; ring

theorem coordinate_rows4_lt {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (d : ℕ) (hd : 0 < d)
    (hm : 4 * (eta^2)⁻¹ * Real.log (24 * (d : ℝ)) ≤ (m : ℝ)) :
    d * Fintype.card (Equations4 r eta) < rothAuxDimension r := by
  have hh := coordinate_rows4_le_half r hr eta heta d hd hm
  have hp : (0 : ℝ) < rothAuxDimension r := by exact_mod_cast dimension4_pos r
  exact_mod_cast (show (d * Fintype.card (Equations4 r eta) : ℝ) < (rothAuxDimension r : ℝ) by linarith)

abbrev Block3 (r : ℕ) := {b : Fin 3 → Fin (r + 1) // ∑ i, (b i).val = r}

def blockNatEquiv3 (r : ℕ) : Block3 r ≃ {b : Fin 3 → ℕ // ∑ i, b i = r} where
  toFun b := ⟨fun i => (b.val i).val,b.property⟩
  invFun b := ⟨fun i => ⟨b.val i,by
    have hh : b.val i ≤ ∑ j, b.val j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [b.property] at hh
    omega⟩,b.property⟩
  left_inv b := by rfl
  right_inv b := by rfl

theorem block3_card (r : ℕ) : Fintype.card (Block3 r) = (r + 2).choose 2 := by
  letI : Fintype {b : Fin 3 → ℕ // ∑ i, b i = r} := Fintype.ofEquiv (Sym (Fin 3) r) (Sym.equivNatSumOfFintype (Fin 3) r)
  rw [Fintype.card_congr (blockNatEquiv3 r),← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin 3) r),Sym.card_sym_eq_choose]
  simpa only [Fintype.card_fin,show 3 + r - 1 = r + 2 by omega] using (Nat.choose_symm_add (a := r) (b := 2))

def blockPivotEquiv4 (r : ℕ) : Block4 r ≃ (i : Fin (r+1)) × Block3 (r-i.val) where
  toFun b := ⟨b.val 0,⟨fun j => ⟨(b.val j.succ).val,by
    have hs := b.property
    rw [Fin.sum_univ_succ] at hs
    have hj : (b.val j.succ).val ≤ ∑ k : Fin 3, (b.val k.succ).val :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 3 => (b.val k.succ).val) (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    omega⟩,by
      have hs := b.property
      rw [Fin.sum_univ_succ] at hs
      change (∑ j : Fin 3, (b.val j.succ).val) = r - (b.val 0).val
      omega⟩⟩
  invFun p := ⟨Fin.cons p.1 (fun j => ⟨(p.2.val j).val,by
    have hh := (p.2.val j).isLt
    omega⟩),by
      rw [Fin.sum_univ_succ]
      change p.1.val + (∑ j : Fin 3, (p.2.val j).val) = r
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
        ((h : Fin m) → Block3 (r h - (i.val h).val)) where
  toFun b := ⟨⟨fun h => (b.val h).val 0,(bad_iff_pivot6 r eta b.val).mp b.property⟩,
    fun h => (blockPivotEquiv4 (r h) (b.val h)).2⟩
  invFun p := ⟨fun h => (blockPivotEquiv4 (r h)).symm ⟨p.1.val h,p.2 h⟩,by
    apply (bad_iff_pivot6 r eta _).mpr
    exact p.1.property⟩
  left_inv b := by
    apply Subtype.ext
    funext h
    exact (blockPivotEquiv4 (r h)).symm_apply_apply (b.val h)
  right_inv p := by
    rcases p with ⟨⟨i,hi⟩,j⟩
    rfl

theorem bad_count_source4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (RothAuxBad r eta) =
      ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 2).choose 2 := by
  rw [Fintype.card_congr (badPivotEquiv4 r eta),Fintype.card_sigma]
  simp only [Fintype.card_pi,block3_card]

theorem constraint_count_source4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    Fintype.card (Equations4 r eta) = 12 *
      ∑ i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i},
        ∏ h, (r h - (i.val h).val + 2).choose 2 := by
  simp only [Equations4,Fintype.card_prod,Fintype.card_fin,bad_count_source4]




end CompoundFeasibility.Auxiliary4Literal176

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4

noncomputable def rothSourceDerivativeWeight {m : ℕ} (r : Fin m → ℕ)
    (J : Vars4 m →₀ ℕ) : ℝ := ∑ h, (∑ i : Fin 4, (J (h,i) : ℝ))/(r h : ℝ)

def exponent4 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => ((b u.1).val u.2).val)

theorem exponent4_injective {m : ℕ} (r : Fin m → ℕ) : Function.Injective (@exponent4 m r) := by
  intro b c h
  funext g
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrArg (fun e : Vars4 m →₀ ℕ => e (g,j)) h

def polynomial4 {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : MvPolynomial (Vars4 m) R :=
  ∑ b, MvPolynomial.monomial (exponent4 b) (c b)

theorem polynomial4_coeff {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) (b : RothAuxCoefficients r) :
    (polynomial4 c).coeff (exponent4 b) = c b := by
  simp only [polynomial4,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,(exponent4_injective r).eq_iff]
  simp

def homogeneous4 {m : ℕ} {R : Type*} [CommRing R] (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) R) : Prop :=
  ∀ d ∈ P.support, ∀ h, ∑ j : Fin 4, d (h,j) = r h

theorem polynomial4_homogeneous {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : homogeneous4 r (polynomial4 c) := by
  intro d hd h
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have hab := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
  subst d
  exact (b h).property


variable {R : Type*} [CommRing R]

def chart4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4) (u : Vars4 m) : MvPolynomial (Vars4 m) R :=
  if u.2 = k then -(∑ j ∈ Finset.univ.erase k, MvPolynomial.C (a j) * MvPolynomial.X (u.1,j))
  else MvPolynomial.C (a k) * MvPolynomial.X u

def substitute4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4) : MvPolynomial (Vars4 m) R →+* MvPolynomial (Vars4 m) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (chart4 a k)

def pivotDerivative4 {m : ℕ} (k : Fin 4) (i : Fin m → ℕ) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k then i u.1 else 0)

theorem transformed_monomial4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4) (J b : Vars4 m →₀ ℕ) :
    substitute4 a k (derivative4 J (MvPolynomial.monomial b 1)) =
      MvPolynomial.C (∏ u : Vars4 m, (Nat.choose (b u) (J u) : R)) *
        ∏ u : Vars4 m, chart4 a k u ^ (b-J) u := by
  rw [derivative4_monomial]
  change MvPolynomial.eval₂ MvPolynomial.C (chart4 a k) (MvPolynomial.monomial (b-J)
    (1 * ∏ u : Vars4 m, (Nat.choose (b u) (J u) : R))) = _
  rw [MvPolynomial.eval₂_monomial,one_mul]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

theorem exponent4_sum {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) :
    (∑ u : Vars4 m, exponent4 b u) = ∑ h, r h := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun h _ => (b h).property)


theorem transformed_coeff_sum4 {m : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Vars4 m →₀ ℕ) (c : ι → R)
    (J d : Vars4 m →₀ ℕ)
    (a : Fin 4 → R) (k : Fin 4) :
    let S := substitute4 (m := m) a k;
    (S (derivative4 J (∑ b, MvPolynomial.monomial (e b) (c b)))).coeff d =
      ∑ b, c b * (S (derivative4 J
        (MvPolynomial.monomial (e b) 1))).coeff d := by
  dsimp only
  let S := substitute4 (m := m) a k
  have hadd : derivative4 J
      (∑ b, MvPolynomial.monomial (e b) (c b)) =
      ∑ b, derivative4 J (MvPolynomial.monomial (e b) (c b)) := by
    apply MvPolynomial.ext
    intro a
    simp only [derivative4_coeff, MvPolynomial.coeff_sum,
      Finset.sum_mul]
  rw [hadd, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [derivative4_monomial, derivative4_monomial]
  simp only [one_mul]
  have hc : MvPolynomial.monomial (e b - J)
      (c b * ∏ u : Vars4 m, (Nat.choose (e b u) (J u) : R)) =
      MvPolynomial.C (c b) * MvPolynomial.monomial (e b - J)
        (∏ u : Vars4 m, (Nat.choose (e b u) (J u) : R)) := by
    rw [MvPolynomial.C_mul_monomial]
  rw [hc, map_mul]
  have hC : S (MvPolynomial.C (c b)) = MvPolynomial.C (c b) := by
    simp [S,substitute4]
  rw [hC, MvPolynomial.coeff_C_mul]


theorem rothAux_weight_block {m : ℕ} (d : Vars4 m →₀ ℕ) (h : Fin m) :
    Finsupp.weight (fun u : Vars4 m => if u.1 = h then 1 else 0) d =
      ∑ j : Fin 4, d (h,j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type, nsmul_eq_mul]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero]
  calc
    (∑ x : Fin m, ∑ j : Fin 4,
        if x = h then d (x,j) else 0) =
      ∑ x : Fin m,
        if x = h then (∑ j : Fin 4, d (x,j)) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = h
          · simp [hx]
          · simp [hx]
    _ = ∑ j : Fin 4, d (h,j) := by simp

theorem rothAux_weight_pivot {m : ℕ} (d : Vars4 m →₀ ℕ) (k : Fin 4) :
    Finsupp.weight (fun u : Vars4 m => if u.2 = k then 1 else 0) d =
      ∑ h : Fin m, d (h,k) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, nsmul_eq_mul]

theorem rothAux_weighted_neg {m : ℕ} (w : Vars4 m → ℕ)
    (P : MvPolynomial (Vars4 m) R) (n : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous w P n) :
    MvPolynomial.IsWeightedHomogeneous w (-P) n := by
  intro d hd
  apply hP
  simpa using hd

theorem chart4_block_weight {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (h : Fin m) (u : Vars4 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.1 = h then 1 else 0)
      (chart4 a k u) (if u.1 = h then 1 else 0) := by
  let w := fun v : Vars4 m => if v.1 = h then 1 else 0
  have hx (j : Fin 4) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) (if u.1 = h then 1 else 0) := by
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart4
  by_cases hu : u.2 = k
  · rw [if_pos hu]
    exact rothAux_weighted_neg w _ _
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun j _ => hx j))
  · rw [if_neg hu]
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem chart4_pivot_weight {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (u : Vars4 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.2 = k then 1 else 0)
      (chart4 a k u) 0 := by
  let w := fun v : Vars4 m => if v.2 = k then 1 else 0
  have hx (j : Fin 4) (hj : j ≠ k) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) 0 := by
    simpa only [w, hj, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart4
  split_ifs with hu
  · exact rothAux_weighted_neg w _ 0
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ 0 (fun j hj => hx j (Finset.mem_erase.mp hj).1))
  · simpa only [w, hu, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem rothAux_scaled_monomial_weighted {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (J b : Vars4 m →₀ ℕ) (w : Vars4 m → ℕ) (v : Vars4 m → ℕ)
    (hv : ∀ u, MvPolynomial.IsWeightedHomogeneous w (chart4 a k u) (v u)) :
    MvPolynomial.IsWeightedHomogeneous w
      (substitute4 a k
        (derivative4 J (MvPolynomial.monomial b 1)))
      (∑ u : Vars4 m, (b - J) u * v u) := by
  rw [transformed_monomial4]
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars4 m => chart4 a k u ^ (b - J) u)
    (fun u => (b - J) u * v u) (fun u _ => by simpa only [nsmul_eq_mul] using (hv u).pow ((b - J) u))
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w _).mul hp



theorem rothAux_transformed_polynomial {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    substitute4 a k (derivative4 J (polynomial4 c)) =
      ∑ b, MvPolynomial.C (c b) * substitute4 a k
        (derivative4 J (MvPolynomial.monomial (exponent4 b) 1)) := by
  apply MvPolynomial.ext
  intro d
  rw [polynomial4, transformed_coeff_sum4]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem rothAux_pivot_monomial_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (i : Fin m → ℕ) (b : RothAuxCoefficients r) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars4 m => if u.1 = h then 1 else 0)
      (substitute4 a k (derivative4
        (pivotDerivative4 k i) (MvPolynomial.monomial (exponent4 b) 1)))
      (r h - i h) := by
  let J := pivotDerivative4 k i
  let w := fun u : Vars4 m => if u.1 = h then 1 else 0
  by_cases hle : J ≤ exponent4 b
  · have hw := rothAux_scaled_monomial_weighted a k J (exponent4 b) w w
      (chart4_block_weight a k h)
    have heq : (∑ u : Vars4 m, (exponent4 b - J) u * w u) =
        ∑ j : Fin 4, (exponent4 b - J) (h,j) := by
      have he := rothAux_weight_block (exponent4 b - J) h
      rw [Finsupp.weight_apply] at he
      rw [Finsupp.sum_fintype (exponent4 b - J)
        (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
      simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
    have hdeg : (∑ j : Fin 4, (exponent4 b - J) (h,j)) = r h - i h := by
      change (∑ j : Fin 4, (exponent4 b (h,j) - J (h,j))) = _
      rw [Finset.sum_tsub_distrib _ (fun j _ => hle (h,j))]
      have hb : (∑ j : Fin 4, exponent4 b (h,j)) = r h := (b h).property
      rw [hb]
      congr 1
      simp [J, pivotDerivative4]
    rw [heq, hdeg] at hw
    exact hw
  · change ¬ ∀ u, J u ≤ exponent4 b u at hle
    push_neg at hle
    obtain ⟨u, hu⟩ := hle
    have hz : (∏ v : Vars4 m, (Nat.choose (exponent4 b v) (J v) : R)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [Nat.choose_eq_zero_of_lt hu]
    rw [transformed_monomial4, hz, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero R w _

theorem rothAux_transformed_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars4 m => if u.1 = h then 1 else 0)
      (substitute4 a k (derivative4
        (pivotDerivative4 k i) (polynomial4 c))) (r h - i h) := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul
    (rothAux_pivot_monomial_block_weight a k i b h)

theorem rothAux_transformed_block_homogeneous {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) :
    homogeneous4 (fun h => r h - i h)
      (substitute4 a k (derivative4
        (pivotDerivative4 k i) (polynomial4 c))) := by
  intro d hd h
  rw [← rothAux_weight_block]
  exact rothAux_transformed_block_weight a k i c h (MvPolynomial.mem_support_iff.mp hd)

theorem rothAux_transformed_pivot_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars4 m => if u.2 = k then 1 else 0)
      (substitute4 a k (derivative4 J (polynomial4 c))) 0 := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  have hb := rothAux_scaled_monomial_weighted a k J (exponent4 b)
    (fun u : Vars4 m => if u.2 = k then 1 else 0) (fun _ => 0)
    (chart4_pivot_weight a k)
  simp only [mul_zero, Finset.sum_const_zero] at hb
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul hb

theorem rothAux_transformed_pivot_zero {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) (d : Vars4 m →₀ ℕ)
    (hd : (substitute4 a k
      (derivative4 J (polynomial4 c))).coeff d ≠ 0) (h : Fin m) :
    d (h,k) = 0 := by
  have hw := rothAux_transformed_pivot_weight a k J c hd
  rw [rothAux_weight_pivot] at hw
  have hle : d (h,k) ≤ ∑ g : Fin m, d (g,k) :=
    Finset.single_le_sum (fun g _ => Nat.zero_le (d (g,k))) (Finset.mem_univ h)
  omega



def freeExponent4 {m : ℕ} (s : Fin m → ℕ) (k : Fin 4)
    (j : (h : Fin m) → Block3 (s h)) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => Fin.insertNth (α := fun _ : Fin 4 => ℕ) k 0 (fun t : Fin 3 => ((j u.1).val t).val) u.2)

theorem freeExponent4_reconstruct {m : ℕ} (s : Fin m → ℕ) (k : Fin 4)
    (d : Vars4 m →₀ ℕ) (hs : ∀ h, ∑ t : Fin 4, d (h,t) = s h)
    (hz : ∀ h, d (h,k) = 0) :
    ∃ j : (h : Fin m) → Block3 (s h), freeExponent4 s k j = d := by
  have hsum (h : Fin m) : (∑ t : Fin 3, d (h,k.succAbove t)) = s h := by
    have he := Fin.sum_univ_succAbove (fun t => d (h,t)) k
    rw [hs h,hz h,zero_add] at he
    exact he.symm
  let j : (h : Fin m) → Block3 (s h) := fun h => ⟨fun t => ⟨d (h,k.succAbove t),by
    have hh : d (h,k.succAbove t) ≤ ∑ u : Fin 4, d (h,u) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun u : Fin 4 => d (h,u)) (fun u _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [hs h] at hh
    omega⟩,hsum h⟩
  refine ⟨j,?_⟩
  ext u
  rcases u with ⟨h,t⟩
  change Fin.insertNth (α := fun _ : Fin 4 => ℕ) k 0 (fun v : Fin 3 => ((j h).val v).val) t = d (h,t)
  refine Fin.succAboveCases k ?_ (fun v => ?_) t
  · simpa only [Fin.insertNth_apply_same] using (hz h).symm
  · rw [Fin.insertNth_apply_succAbove]



end CompoundFeasibility.Auxiliary4Literal176
namespace Aux4HeightLiteral176
open CompoundFeasibility.SourceMultiblock4
open CompoundFeasibility.Auxiliary4Literal176 Aux6Mass
variable {R : Type*} [NormedCommRing R] [NormOneClass R]

theorem chart_mass4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A) (u : Vars4 m) :
    mass (chart4 a k u) ≤ 4 * A := by
  unfold chart4
  split_ifs
  · rw [mass_neg]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase k, mass (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) := mass_sum _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase k, A := by
        apply Finset.sum_le_sum
        intro j _
        rw [mass_C_mul_X]
        exact ha j
      _ ≤ 4 * A := by simp; linarith
  · rw [mass_C_mul_X]
    exact (ha k).trans (by linarith)

theorem binomial_norm4 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) (J : Vars4 m →₀ ℕ) :
    ‖∏ u : Vars4 m, (Nat.choose (exponent4 b u) (J u) : R)‖ ≤ (2 : ℝ)^(∑ h, r h) := by
  have hnat (n : ℕ) : ‖(n : R)‖ ≤ (n : ℝ) := by
    rw [← nsmul_one]
    exact (norm_nsmul_le (n := n) (a := (1 : R))).trans_eq (by simp)
  calc
    _ ≤ ∏ u : Vars4 m, ‖(Nat.choose (exponent4 b u) (J u) : R)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ u : Vars4 m, (2 : ℝ)^exponent4 b u := by
      apply Finset.prod_le_prod
      · intro u _; exact norm_nonneg _
      · intro u _
        apply (hnat _).trans
        have hc : (exponent4 b u).choose (J u) ≤ 2 ^ exponent4 b u := by
          rcases Nat.eq_zero_or_pos (exponent4 b u) with hz | hp
          · rw [hz]; cases J u <;> simp
          · exact (Nat.choose_le_two_pow _ _ hp).le
        exact_mod_cast hc
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum,exponent4_sum]

theorem transformed_entry_norm4 {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A)
    (b : RothAuxCoefficients r) (J d : Vars4 m →₀ ℕ) :
    ‖(substitute4 a k (derivative4 J (MvPolynomial.monomial (exponent4 b) 1))).coeff d‖ ≤
      (8 * A)^(∑ h, r h) := by
  have hbase : 1 ≤ 4 * A := by linarith
  have hsum : (∑ u : Vars4 m, (exponent4 b-J) u) ≤ ∑ h, r h := by
    rw [← exponent4_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  rw [transformed_monomial4]
  calc
    _ ≤ mass (MvPolynomial.C (∏ u : Vars4 m, (Nat.choose (exponent4 b u) (J u) : R)) *
        ∏ u : Vars4 m, chart4 a k u ^ (exponent4 b-J) u) := coeff_le_mass _ _
    _ ≤ mass (MvPolynomial.C (∏ u : Vars4 m, (Nat.choose (exponent4 b u) (J u) : R))) *
        mass (∏ u : Vars4 m, chart4 a k u ^ (exponent4 b-J) u) := mass_mul _ _
    _ ≤ (2 : ℝ)^(∑ h, r h) * (4*A)^(∑ h, r h) := by
      apply mul_le_mul
      · simpa only [MvPolynomial.C_apply,mass_monomial] using binomial_norm4 (R := R) b J
      · calc
          _ ≤ ∏ u : Vars4 m, mass (chart4 a k u ^ (exponent4 b-J) u) := mass_prod _ _
          _ ≤ ∏ u : Vars4 m, (4*A)^(exponent4 b-J) u := by
            apply Finset.prod_le_prod
            · intro u _; exact mass_nonneg _
            · intro u _
              exact (mass_pow _ _).trans (pow_le_pow_left₀ (mass_nonneg _) (chart_mass4 a k A hA ha u) _)
          _ = (4*A)^(∑ u : Vars4 m, (exponent4 b-J) u) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ _ := pow_le_pow_right₀ hbase hsum
      · exact mass_nonneg _
      · positivity
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Aux4HeightLiteral176

namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4
variable {K : Type*} [CommRing K]

noncomputable def formEquiv4 : Fin 12 ≃ Fin 3 × Fin 4 :=
  (finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin (3 * 4)).symm

noncomputable def equation4 {m : ℕ} {r : Fin m → ℕ} {eta : ℝ}
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (f : Fin 12) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
    (j : (h : Fin m) → Block3 (r h - (i.val h).val))
    (P : MvPolynomial (Vars4 m) K) : K :=
  (substitute4 (a (formEquiv4 f).1 (formEquiv4 f).2)
    (p (formEquiv4 f).1 (formEquiv4 f).2)
    (derivative4 (pivotDerivative4 (p (formEquiv4 f).1 (formEquiv4 f).2)
      (fun h => (i.val h).val)) P)).coeff
    (freeExponent4 (fun h => r h - (i.val h).val)
      (p (formEquiv4 f).1 (formEquiv4 f).2) j)

noncomputable def matrix4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4) :
    Matrix (Equations4 r eta) (RothAuxCoefficients r) K :=
  fun q b => equation4 a p q.1 (badPivotEquiv4 r eta q.2).1
    (badPivotEquiv4 r eta q.2).2 (MvPolynomial.monomial (exponent4 b) 1)

theorem matrix4_mulVec {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → K) (q : Equations4 r eta) :
    (matrix4 r eta a p).mulVec c q =
      equation4 a p q.1 (badPivotEquiv4 r eta q.2).1
        (badPivotEquiv4 r eta q.2).2 (polynomial4 c) := by
  unfold equation4 polynomial4
  rw [transformed_coeff_sum4]
  simp only [Matrix.mulVec, dotProduct, matrix4, equation4]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrix4_kernel_iff_coefficients {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → K) :
    (matrix4 r eta a p).mulVec c = 0 ↔
      ∀ (f : Fin 12) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
        (j : (h : Fin m) → Block3 (r h - (i.val h).val)),
        equation4 a p f i j (polynomial4 c) = 0 := by
  constructor
  · intro hz f i j
    have h := congrFun hz (f, (badPivotEquiv4 r eta).symm ⟨i,j⟩)
    rw [matrix4_mulVec] at h
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using h
  · intro hz
    funext q
    rw [matrix4_mulVec]
    exact hz q.1 (badPivotEquiv4 r eta q.2).1 (badPivotEquiv4 r eta q.2).2

theorem restriction4_zero_iff_coefficients {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → K) (k : Fin 4) (i : RothAuxPivots r)
    (c : RothAuxCoefficients r → K) :
    substitute4 a k (derivative4 (pivotDerivative4 k (fun h => (i h).val))
      (polynomial4 c)) = 0 ↔
      ∀ j : (h : Fin m) → Block3 (r h - (i h).val),
        (substitute4 a k (derivative4 (pivotDerivative4 k (fun h => (i h).val))
          (polynomial4 c))).coeff
          (freeExponent4 (fun h => r h - (i h).val) k j) = 0 := by
  constructor
  · intro hz j
    rw [hz, MvPolynomial.coeff_zero]
  · intro hz
    apply MvPolynomial.ext
    intro d
    by_cases hd : (substitute4 a k (derivative4 (pivotDerivative4 k (fun h => (i h).val))
        (polynomial4 c))).coeff d = 0
    · exact hd
    · have hhom := rothAux_transformed_block_homogeneous a k (fun h => (i h).val) c
      have hdeg := hhom d (MvPolynomial.mem_support_iff.mpr hd)
      have hp := rothAux_transformed_pivot_zero a k
        (pivotDerivative4 k (fun h => (i h).val)) c d hd
      obtain ⟨j, hj⟩ := freeExponent4_reconstruct (fun h => r h - (i h).val) k d hdeg hp
      rw [← hj]
      exact hz j

theorem matrix4_kernel_iff_restrictions {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → K) :
    (matrix4 r eta a p).mulVec c = 0 ↔
      ∀ (tau : Fin 3) (s : Fin 4)
        (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}),
        substitute4 (a tau s) (p tau s)
          (derivative4 (pivotDerivative4 (p tau s) (fun h => (i.val h).val))
            (polynomial4 c)) = 0 := by
  rw [matrix4_kernel_iff_coefficients]
  constructor
  · intro hz tau s i
    apply (restriction4_zero_iff_coefficients (a tau s) (p tau s) i.val c).mpr
    intro j
    have hh := hz (formEquiv4.symm (tau,s)) i j
    simpa only [equation4, Equiv.apply_symm_apply] using hh
  · intro hz f i j
    exact (restriction4_zero_iff_coefficients _ _ i.val c).mp
      (hz (formEquiv4 f).1 (formEquiv4 f).2 i) j

end CompoundFeasibility.Auxiliary4Literal176

namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

theorem rothSource_scaled_chart_pderiv {m : ℕ} (a : Fin 4 → 𝕂) (k j : Fin 4)
    (h : Fin m) (hj : j ≠ k) (v : Vars4 m) :
    MvPolynomial.pderiv (h,j) (chart4 a k v) =
      MvPolynomial.C (a k) * (if v = (h,j) then 1 else 0) -
        MvPolynomial.C (a j) * (if v = (h,k) then 1 else 0) := by
  classical
  rcases v with ⟨g,l⟩
  by_cases hg : g = h
  · subst g
    by_cases hl : l = k
    · subst l
      simp [chart4, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hj, Ne.symm hj, map_sum, mul_ite,
        Finset.sum_ite_eq', Finset.sum_ite_eq, eq_comm]
    · simp [chart4, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hl, Ne.symm hl, eq_comm]
  · by_cases hl : l = k <;>
      simp [chart4, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg, map_sum]

theorem rothSource_scaled_chain {m : ℕ} (a : Fin 4 → 𝕂) (k j : Fin 4)
    (h : Fin m) (hj : j ≠ k) (P : MvPolynomial (Vars4 m) 𝕂) :
    MvPolynomial.pderiv (h,j) (substitute4 a k P) =
      MvPolynomial.C (a k) * substitute4 a k (MvPolynomial.pderiv (h,j) P) -
        MvPolynomial.C (a j) * substitute4 a k (MvPolynomial.pderiv (h,k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute4]
  | add P Q hP hQ => simp only [map_add, hP, hQ]; ring
  | mul_X P v hP =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    rw [show substitute4 a k (MvPolynomial.X v) = chart4 a k v by simp [substitute4],
      rothSource_scaled_chart_pderiv a k j h hj v]
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero]
    split_ifs <;> simp_all <;> ring

theorem rothSource_weight_add {m : ℕ} (r : Fin m → ℕ) (J K : Vars4 m →₀ ℕ) :
    rothSourceDerivativeWeight r (J + K) =
      rothSourceDerivativeWeight r J + rothSourceDerivativeWeight r K := by
  simp [rothSourceDerivativeWeight, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, add_div]

theorem rothSource_weight_mono {m : ℕ} (r : Fin m → ℕ)
    (J K : Vars4 m →₀ ℕ) (hJK : J ≤ K) :
    rothSourceDerivativeWeight r J ≤ rothSourceDerivativeWeight r K := by
  apply Finset.sum_le_sum
  intro h _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact_mod_cast hJK (h,i)

theorem rothSource_weight_single {m : ℕ} (r : Fin m → ℕ) (u : Vars4 m) :
    rothSourceDerivativeWeight r (Finsupp.single u 1) = 1 / (r u.1 : ℝ) := by
  classical
  rcases u with ⟨h,j⟩
  simp [rothSourceDerivativeWeight, Finsupp.single_apply, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [ite_div, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_weight_pivot {m : ℕ} (r : Fin m → ℕ) (k : Fin 4) (i : Fin m → ℕ) :
    rothSourceDerivativeWeight r (pivotDerivative4 k i) = ∑ h, (i h : ℝ) / r h := by
  simp [rothSourceDerivativeWeight, pivotDerivative4, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

noncomputable def rothSourceFreeOrder {m : ℕ} (k : Fin 4) (J : Vars4 m →₀ ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Vars4 m => u.2 ≠ k), J u

theorem rothSource_free_add {m : ℕ} (k : Fin 4) (J K : Vars4 m →₀ ℕ) :
    rothSourceFreeOrder k (J + K) = rothSourceFreeOrder k J + rothSourceFreeOrder k K := by
  simp [rothSourceFreeOrder, Finsupp.add_apply, Finset.sum_add_distrib]

theorem rothSource_free_single {m : ℕ} (k : Fin 4) (u : Vars4 m) :
    rothSourceFreeOrder k (Finsupp.single u 1) = if u.2 = k then 0 else 1 := by
  classical
  simp [rothSourceFreeOrder, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_free_zero_pivot {m : ℕ} (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (hJ : rothSourceFreeOrder k J = 0) :
    J = pivotDerivative4 k (fun h => J (h,k)) := by
  classical
  ext u
  by_cases hu : u.2 = k
  · have he : u = (u.1,k) := Prod.ext rfl hu
    simpa [pivotDerivative4, hu] using congrArg J he
  · have hle : J u ≤ rothSourceFreeOrder k J :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ u,hu⟩)
    have hz : J u = 0 := by omega
    simp [pivotDerivative4, hu, hz]

theorem rothSource_scaled_mixed_vanishing {m : ℕ} (r : Fin m → ℕ)
    (a : Fin 4 → 𝕂) (k : Fin 4) (ha : a k ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars4 m) 𝕂)
    (hpivot : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      substitute4 a k
        (derivative4 (pivotDerivative4 k i) P) = 0)
    (J : Vars4 m →₀ ℕ) (hw : rothSourceDerivativeWeight r J < T) :
    substitute4 a k (derivative4 J P) = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J : Vars4 m →₀ ℕ,
      rothSourceFreeOrder k J = n → rothSourceDerivativeWeight r J < T →
      substitute4 a k (derivative4 J P) = 0 := by
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
      · have hex : ∃ u : Vars4 m, u.2 ≠ k ∧ J u ≠ 0 := by
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
        change substitute4 a k
          (derivative4 (K + Finsupp.single (u.1,k) 1) P) = 0 at hKp
        have hc := rothSource_scaled_chain a k u.2 u.1 hu
          (derivative4 K P)
        rw [SourceMultiblock4.source4_pderiv_hasse, SourceMultiblock4.source4_pderiv_hasse] at hc
        simp only [hK, map_zero, map_nsmul, hKp, nsmul_zero, mul_zero, sub_zero] at hc
        rw [hKeq] at hc
        have hcoeff : (MvPolynomial.C (a k) : MvPolynomial (Vars4 m) 𝕂) ≠ 0 := by
          intro hz
          apply ha
          apply MvPolynomial.C_injective (σ := Vars4 m)
          simpa only [map_zero] using hz
        have hsm := (mul_eq_zero.mp hc.symm).resolve_left hcoeff
        rw [nsmul_eq_mul] at hsm
        exact (mul_eq_zero.mp hsm).resolve_left (by
          intro hh
          have hz : ((K (u.1,u.2) + 1 : ℕ) : 𝕂) = 0 := by
            apply MvPolynomial.C_injective (σ := Vars4 m)
            simpa only [map_natCast, map_zero] using hh
          exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)) hz)
  exact go _ J rfl hw


end CompoundFeasibility.Auxiliary4Literal176

namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

def kernelChart4 {m : ℕ} (a : Fin 4 → 𝕂) (k : Fin m → Fin 4)
    (u : Vars4 m) : MvPolynomial (Vars4 m) 𝕂 :=
  if u.2 = k u.1 then
    -(∑ j ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C (a j / a (k u.1)) * MvPolynomial.X (u.1,j))
  else MvPolynomial.X u

def kernelRestriction4 {m : ℕ} (a : Fin 4 → 𝕂) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) 𝕂 →+* MvPolynomial (Vars4 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (kernelChart4 a k)

theorem kernelChart4_form {m : ℕ} (a : Fin 4 → 𝕂)
    (k : Fin m → Fin 4) (hk : ∀ h, a (k h) ≠ 0) (h : Fin m) :
    (∑ j : Fin 4, MvPolynomial.C (a j) * kernelChart4 a k (h,j)) = 0 := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k h))]
  have hfree : (∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) *
      kernelChart4 a k (h,j)) =
      ∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [kernelChart4, (Finset.mem_erase.mp hj).1]
  rw [hfree]
  have hpivot : MvPolynomial.C (a (k h)) * kernelChart4 a k (h,k h) =
      -(∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j)) := by
    simp only [kernelChart4, Prod.fst, Prod.snd, if_pos rfl, ite_true, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    congr 1
    field_simp [hk h]
  rw [hpivot]
  ring

def chartTransport4 {m : ℕ} (a : Fin 4 → 𝕂) (p : Fin 4) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) 𝕂 →+* MvPolynomial (Vars4 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u =>
    MvPolynomial.C ((a p)⁻¹) * kernelChart4 a k u)

theorem chartTransport4_variable {m : ℕ} (a : Fin 4 → 𝕂)
    (p : Fin 4) (hp : a p ≠ 0) (k : Fin m → Fin 4)
    (hk : ∀ h, a (k h) ≠ 0) (u : Vars4 m) :
    chartTransport4 a p k (chart4 a p u) = kernelChart4 a k u := by
  have hcancel : (MvPolynomial.C (a p) : MvPolynomial (Vars4 m) 𝕂) *
      MvPolynomial.C ((a p)⁻¹) = 1 := by
    rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hp, map_one]
  by_cases hu : u.2 = p
  · have hsum := kernelChart4_form a k hk u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hsum
    have hrel : -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
        kernelChart4 a k (u.1,j)) =
        MvPolynomial.C (a p) * kernelChart4 a k (u.1,p) := by
      linear_combination -hsum
    simp only [chart4, if_pos hu, map_neg, map_sum, map_mul]
    simp only [chartTransport4, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((a p)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
            kernelChart4 a k (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [hrel, ← mul_assoc, mul_comm _ (MvPolynomial.C (a p)), hcancel]
        simp [← hu]
  · simp only [chart4, if_neg hu, map_mul]
    simp only [chartTransport4, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    rw [← mul_assoc, hcancel, one_mul]

theorem chartTransport4_substitute {m : ℕ} (a : Fin 4 → 𝕂)
    (p : Fin 4) (hp : a p ≠ 0) (k : Fin m → Fin 4)
    (hk : ∀ h, a (k h) ≠ 0) (P : MvPolynomial (Vars4 m) 𝕂) :
    chartTransport4 a p k (substitute4 a p P) = kernelRestriction4 a k P := by
  have he : (chartTransport4 a p k).comp (substitute4 a p) = kernelRestriction4 a k := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [substitute4, chartTransport4, kernelRestriction4]
    · intro u
      simpa [substitute4, kernelRestriction4] using chartTransport4_variable a p hp k hk u
  exact congrArg (fun f => f P) he

theorem derivative4_zero_of_block_excess {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars4 m) 𝕂) (hP : homogeneous4 r P)
    (J : Vars4 m →₀ ℕ) (h : Fin m) (hJ : r h < ∑ j : Fin 4, J (h,j)) :
    derivative4 J P = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [derivative4_coeff, MvPolynomial.coeff_zero]
  have hz : P.coeff (d + J) = 0 := by
    by_contra hn
    have hdegree := hP (d + J) (MvPolynomial.mem_support_iff.mpr hn) h
    have hle : (∑ j : Fin 4, J (h,j)) ≤ ∑ j : Fin 4, (d + J) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finsupp.add_apply]
      omega
    omega
  rw [hz, zero_mul]

theorem matrix4_kernel_all_derivatives {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝕂) (p : Fin 3 → Fin 4 → Fin 4)
    (hp : ∀ tau s, a tau s (p tau s) ≠ 0)
    (c : RothAuxCoefficients r → 𝕂)
    (hc : (matrix4 r eta a p).mulVec c = 0)
    (tau : Fin 3) (s : Fin 4) (J : Vars4 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (1 / 4 - eta) * m)
    (k : Fin m → Fin 4) (hk : ∀ h, a tau s (k h) ≠ 0) :
    kernelRestriction4 (a tau s) k (derivative4 J (polynomial4 c)) = 0 := by
  have hpivot := (matrix4_kernel_iff_restrictions r eta a p c).mp hc
  have hall : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < (1 / 4 - eta) * m →
      substitute4 (a tau s) (p tau s)
        (derivative4 (pivotDerivative4 (p tau s) i) (polynomial4 c)) = 0 := by
    intro i hi
    by_cases hb : ∀ h, i h ≤ r h
    · let iFin : RothAuxPivots r := fun h => ⟨i h, by have hh := hb h; omega⟩
      exact hpivot tau s ⟨iFin, hi⟩
    · push_neg at hb
      obtain ⟨h, hh⟩ := hb
      have hsum : (∑ j : Fin 4, pivotDerivative4 (p tau s) i (h,j)) = i h := by
        simp [pivotDerivative4, Finset.sum_ite_eq, Finset.sum_ite_eq']
      have hz := derivative4_zero_of_block_excess r (polynomial4 c) (polynomial4_homogeneous c)
        (pivotDerivative4 (p tau s) i) h (by rw [hsum]; exact hh)
      simp [hz]
  rw [← chartTransport4_substitute (a tau s) (p tau s) (hp tau s) k hk]
  rw [rothSource_scaled_mixed_vanishing r (a tau s) (p tau s) (hp tau s) _
    (polynomial4 c) hall J hJ, map_zero]

end CompoundFeasibility.Auxiliary4Literal176
namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4
variable {R S : Type*} [CommRing R] [CommRing S]

theorem derivative4_map {m : ℕ} (f : R →+* S) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) R) :
    (derivative4 J P).map f = derivative4 J (P.map f) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_map, derivative4_coeff, map_mul, map_prod, map_natCast]

theorem chart4_map {m : ℕ} (f : R →+* S) (a : Fin 4 → R) (k : Fin 4) (u : Vars4 m) :
    (chart4 a k u).map f = chart4 (fun j => f (a j)) k u := by
  unfold chart4
  split_ifs <;> simp [map_sum, map_mul]

theorem substitute4_map {m : ℕ} (f : R →+* S) (a : Fin 4 → R) (k : Fin 4)
    (P : MvPolynomial (Vars4 m) R) :
    (substitute4 a k P).map f = substitute4 (fun j => f (a j)) k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute4]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show substitute4 a k (MvPolynomial.X v) = chart4 a k v by simp [substitute4]]
    rw [chart4_map]
    simp [substitute4]

theorem polynomial4_map {m : ℕ} {r : Fin m → ℕ} (f : R →+* S)
    (c : RothAuxCoefficients r → R) :
    (polynomial4 c).map f = polynomial4 (fun b => f (c b)) := by
  simp [polynomial4]

theorem matrix4_map {m : ℕ} (f : R →+* S) (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → R) (p : Fin 3 → Fin 4 → Fin 4)
    (q : Equations4 r eta) (b : RothAuxCoefficients r) :
    f (matrix4 r eta a p q b) = matrix4 r eta (fun tau s j => f (a tau s j)) p q b := by
  unfold matrix4 equation4
  rw [← MvPolynomial.coeff_map, substitute4_map, derivative4_map]
  simp

end CompoundFeasibility.Auxiliary4Literal176

end

open scoped BigOperators Matrix Classical NumberField
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

noncomputable def integralMatrix4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4) :
    Matrix (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
      (RothAuxCoefficients r) ℤ :=
  fun q b => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix4 r eta a p q.1 b) q.2

theorem integralMatrix4_kernel {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → ℤ) :
    (integralMatrix4 r eta a p).mulVec c = 0 ↔
      (matrix4 r eta a p).mulVec (fun b => (c b : 𝓞 𝕂)) = 0 := by
  let b := Module.finBasis ℤ (𝓞 𝕂)
  have he (q : Equations4 r eta) (k : Fin (Module.finrank ℤ (𝓞 𝕂))) :
      (integralMatrix4 r eta a p).mulVec c (q,k) =
        b.repr ((matrix4 r eta a p).mulVec (fun j => (c j : 𝓞 𝕂)) q) k := by
    simp only [Matrix.mulVec, dotProduct, integralMatrix4, map_sum, Finsupp.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg (fun x => x k) (b.repr.map_smul (c j) (matrix4 r eta a p q j))
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

noncomputable def integralHeightBase4 (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) : ℝ :=
  letI := Aux6Norm.integralNormModel 𝕂
  max 1 (∑ tau : Fin 3, ∑ s : Fin 4, ∑ j : Fin 4, ‖a tau s j‖)

noncomputable def integralCoordinateConstant4 (𝕂 : Type*) [Field 𝕂] [NumberField 𝕂] : ℝ :=
  max 1 ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖

theorem integralMatrix4_entry_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4)
    (q : Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
    (b : RothAuxCoefficients r) :
    ‖integralMatrix4 r eta a p q b‖ ≤ integralCoordinateConstant4 𝕂 *
      (8 * integralHeightBase4 a)^(∑ h, r h) := by
  letI := Aux6Norm.integralNormModel 𝕂
  letI : NormOneClass (𝓞 𝕂) := ⟨Aux6Norm.integralNormModel_one⟩
  have ha : ∀ tau s j, ‖a tau s j‖ ≤ integralHeightBase4 a := by
    intro tau s j
    apply le_trans _ (le_max_right _ _)
    apply le_trans (Finset.single_le_sum (fun j _ => norm_nonneg (a tau s j)) (Finset.mem_univ j))
    apply le_trans (Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j))) (Finset.mem_univ s))
    exact Finset.single_le_sum (fun tau _ => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j)))) (Finset.mem_univ tau)
  have hx : ‖matrix4 r eta a p q.1 b‖ ≤ (8 * integralHeightBase4 a)^(∑ h, r h) := by
    apply Aux4HeightLiteral176.transformed_entry_norm4
    · exact le_max_left _ _
    · exact ha _ _
  have hc := Aux6Norm.integralNormModel_coordinates (matrix4 r eta a p q.1 b)
  have hcoord := norm_le_pi_norm (fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr
    (matrix4 r eta a p q.1 b) i) q.2
  calc
    _ ≤ ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix4 r eta a p q.1 b) i)‖ := hcoord
    _ ≤ ‖matrix4 r eta a p q.1 b‖ *
        ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖ := hc
    _ ≤ (8 * integralHeightBase4 a)^(∑ h, r h) * integralCoordinateConstant4 𝕂 :=
      mul_le_mul hx (le_max_right _ _) (norm_nonneg _) (pow_nonneg (by have hh : 1 ≤ integralHeightBase4 a := le_max_left _ _; linarith) _)
    _ = _ := mul_comm _ _

end CompoundFeasibility.Auxiliary4Literal176
namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]
attribute [local instance] Matrix.seminormedAddCommGroup

theorem dimension4_le_pow {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) :
    rothAuxDimension r ≤ 16^(∑ h, r h) := by
  rw [rothAuxDimension_eq]
  calc
    _ ≤ ∏ h, 16^r h := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro h _
      calc
        (r h + 3).choose 3 ≤ 2^(r h + 3) :=
          (Nat.choose_le_two_pow _ _ (by omega)).le
        _ ≤ 2^(4 * r h) := Nat.pow_le_pow_right (by decide) (by have hh := hr h; omega)
        _ = 16^r h := by rw [pow_mul]; norm_num
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

noncomputable def integralSiegelConstant4 (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) : ℝ :=
  16 * (8 * integralHeightBase4 a * integralCoordinateConstant4 𝕂)

theorem integralSiegelConstant4_ge_one (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) :
    1 ≤ integralSiegelConstant4 a := by
  have hA : 1 ≤ integralHeightBase4 a := le_max_left _ _
  have hC : 1 ≤ integralCoordinateConstant4 𝕂 := le_max_left _ _
  dsimp [integralSiegelConstant4]
  nlinarith

theorem integralMatrix4_uniform_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (hm : 0 < m) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4) :
    (Fintype.card (RothAuxCoefficients r) : ℝ) * max 1 ‖integralMatrix4 r eta a p‖ ≤
      integralSiegelConstant4 a ^ (∑ h, r h) := by
  let A := integralHeightBase4 a
  let C := integralCoordinateConstant4 𝕂
  have hA : 1 ≤ A := le_max_left _ _
  have hC : 1 ≤ C := le_max_left _ _
  have hR : 1 ≤ ∑ h, r h := by
    have hp := hr ⟨0, hm⟩
    have hh : r ⟨0, hm⟩ ≤ ∑ h, r h :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  have hbase : 1 ≤ 8 * A * C := by nlinarith
  have hnorm : ‖integralMatrix4 r eta a p‖ ≤ (8 * A * C)^(∑ h, r h) := by
    apply (Matrix.norm_le_iff (by positivity)).mpr
    intro q b
    calc
      _ ≤ C * (8 * A)^(∑ h, r h) := integralMatrix4_entry_bound r eta a p q b
      _ ≤ C^(∑ h, r h) * (8 * A)^(∑ h, r h) :=
        mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ hC hR) (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  calc
    _ ≤ (16 : ℝ)^(∑ h, r h) * (8 * A * C)^(∑ h, r h) :=
      mul_le_mul (by exact_mod_cast dimension4_le_pow r hr)
        (max_le (one_le_pow₀ hbase) hnorm) (by positivity) (by positivity)
    _ = _ := by rw [← mul_pow]; rfl

theorem integralMatrix4_bounded_kernel {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ))
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4) :
    ∃ c : RothAuxCoefficients r → ℤ, c ≠ 0 ∧
      (integralMatrix4 r eta a p).mulVec c = 0 ∧
      ‖c‖ ≤ integralSiegelConstant4 a ^ (∑ h, r h) := by
  have hd : 0 < Module.finrank ℚ 𝕂 := Module.finrank_pos
  have hN := dimension4_pos r
  have hhalf := coordinate_rows4_le_half r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hlt := coordinate_rows4_lt r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hmpos : 0 < m := by
    have hd' : (1 : ℝ) ≤ Module.finrank ℚ 𝕂 := by exact_mod_cast hd
    have hlog : 0 < Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) := Real.log_pos (by linarith)
    have hh : 0 < (m : ℝ) := lt_of_lt_of_le (mul_pos (by positivity) hlog) hm
    exact_mod_cast hh
  have hD := integralSiegelConstant4_ge_one a
  by_cases hrows : Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) = 0
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
  · have hcount : Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) <
        Fintype.card (RothAuxCoefficients r) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm] using hlt
    obtain ⟨c, hc, hker, hbound⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le
      (integralMatrix4 r eta a p) hcount (Nat.pos_of_ne_zero hrows)
    refine ⟨c, hc, hker, ?_⟩
    have hrowsR : (Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) ≤
        (Fintype.card (RothAuxCoefficients r) : ℝ) / 2 := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm, Nat.cast_mul, rothAuxDimension] using hhalf
    have hden : 0 < (Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) := by
      exact sub_pos.mpr (by exact_mod_cast hcount)
    have hexp : (Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) /
        ((Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))) ≤ 1 := by
      apply (div_le_one hden).mpr
      linarith
    have hbase : 1 ≤ (Fintype.card (RothAuxCoefficients r) : ℝ) *
        max 1 ‖integralMatrix4 r eta a p‖ := by
      have hn : (1 : ℝ) ≤ Fintype.card (RothAuxCoefficients r) := by exact_mod_cast hN
      nlinarith [le_max_left (1 : ℝ) ‖integralMatrix4 r eta a p‖]
    exact hbound.trans ((Real.rpow_le_self_of_one_le hbase hexp).trans
      (integralMatrix4_uniform_bound r hr hmpos eta a p))

end CompoundFeasibility.Auxiliary4Literal176
namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4

noncomputable def height4 {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ) : ℕ :=
  P.support.sup (fun d => (P.coeff d).natAbs)

theorem polynomial4_ne_zero {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ)
    (hc : c ≠ 0) : polynomial4 c ≠ 0 := by
  intro hz
  apply hc
  funext b
  have hh := polynomial4_coeff c b
  rw [hz, MvPolynomial.coeff_zero] at hh
  exact hh.symm

theorem polynomial4_height_le {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ) :
    (height4 (polynomial4 c) : ℝ) ≤ ‖c‖ := by
  have hs : ∀ d ∈ (polynomial4 c).support,
      ((polynomial4 c).coeff d).natAbs ≤ Nat.floor ‖c‖ := by
    intro d hd
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    subst d
    rw [polynomial4_coeff]
    apply Nat.le_floor
    simpa only [Int.norm_eq_abs, Int.cast_natAbs, Int.cast_abs] using norm_le_pi_norm c b
  have hh : height4 (polynomial4 c) ≤ Nat.floor ‖c‖ := Finset.sup_le hs
  exact (by exact_mod_cast hh : (height4 (polynomial4 c) : ℝ) ≤ Nat.floor ‖c‖).trans
    (Nat.floor_le (norm_nonneg _))

variable {𝕂 : Type*} [Field 𝕂]

theorem kernelChart4_scale {m : ℕ} (a : Fin 4 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 4) (u : Vars4 m) :
    kernelChart4 (fun j => M * a j) k u = kernelChart4 a k u := by
  unfold kernelChart4
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_div_mul_left _ _ hM]
  · rfl

theorem kernelRestriction4_scale {m : ℕ} (a : Fin 4 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 4) (P : MvPolynomial (Vars4 m) 𝕂) :
    kernelRestriction4 (fun j => M * a j) k P = kernelRestriction4 a k P := by
  have he : kernelChart4 (m := m) (fun j => M * a j) k = kernelChart4 a k :=
    funext (kernelChart4_scale a M hM k)
  simp only [kernelRestriction4, he]

theorem kernelRestriction4_map {𝕃 : Type*} [Field 𝕃] {m : ℕ}
    (f : 𝕂 →+* 𝕃) (a : Fin 4 → 𝕂) (k : Fin m → Fin 4)
    (P : MvPolynomial (Vars4 m) 𝕂) :
    (kernelRestriction4 a k P).map f =
      kernelRestriction4 (fun j => f (a j)) k (P.map f) := by
  have hchart (u : Vars4 m) :
      (kernelChart4 a k u).map f = kernelChart4 (fun j => f (a j)) k u := by
    unfold kernelChart4
    split_ifs <;> simp [map_sum, map_mul, map_div₀]
  induction P using MvPolynomial.induction_on with
  | C c => simp [kernelRestriction4]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show kernelRestriction4 a k (MvPolynomial.X v) = kernelChart4 a k v by simp [kernelRestriction4]]
    rw [hchart]
    simp [kernelRestriction4]

variable [NumberField 𝕂]

theorem integral_auxiliary4
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, (a tau s (k h) : 𝕂) ≠ 0) →
          kernelRestriction4 (fun j => (a tau s j : 𝕂)) k
            (derivative4 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  let p : Fin 3 → Fin 4 → Fin 4 := fun tau s => Classical.choose (ha tau s)
  have hp : ∀ tau s, a tau s (p tau s) ≠ 0 := fun tau s => Classical.choose_spec (ha tau s)
  refine ⟨integralSiegelConstant4 a, integralSiegelConstant4_ge_one a, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨c, hc, hker, hbound⟩ := integralMatrix4_bounded_kernel r hr eta heta hm a p
  refine ⟨polynomial4 c, polynomial4_ne_zero c hc, polynomial4_homogeneous c,
    (polynomial4_height_le c).trans hbound, ?_⟩
  let f : 𝓞 𝕂 →+* 𝕂 := algebraMap _ _
  have hkerO := (integralMatrix4_kernel r eta a p c).mp hker
  have hkerK : (matrix4 r eta (fun tau s j => f (a tau s j)) p).mulVec
      (fun b => (c b : 𝕂)) = 0 := by
    funext q
    have hh := congrArg f (congrFun hkerO q)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast,
      matrix4_map, Pi.zero_apply, map_zero] using hh
  intro tau s J hJ k hk
  have hpK : ∀ tau s, f (a tau s (p tau s)) ≠ 0 := fun tau s =>
    (map_ne_zero_iff f (IsFractionRing.injective (𝓞 𝕂) 𝕂)).mpr (hp tau s)
  have hh := matrix4_kernel_all_derivatives r eta (fun tau s j => f (a tau s j)) p
    hpK (fun b => (c b : 𝕂)) hkerK tau s J hJ k hk
  simpa only [polynomial4_map, map_intCast] using hh

end CompoundFeasibility.Auxiliary4Literal176
namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

theorem source_integral_scaling4 (a : Fin 3 → Fin 4 → Fin 4 → 𝕂) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ b : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂,
      ∀ tau s j, (b tau s j : 𝕂) = (M : 𝕂) * a tau s j := by
  haveI : Algebra.IsAlgebraic ℚ 𝕂 := Algebra.IsAlgebraic.of_finite ℚ 𝕂
  haveI : Algebra.IsAlgebraic ℤ 𝕂 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := 𝕂)).mpr inferInstance
  obtain ⟨M, hM, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun q : Fin 3 × Fin 4 × Fin 4 => a q.1 q.2.1 q.2.2))
  have hint : ∀ tau s j, IsIntegral ℤ ((M : 𝕂) * a tau s j) := by
    intro tau s j
    simpa only [Algebra.smul_def, eq_intCast] using
      hi (a tau s j) (Finset.mem_image.mpr ⟨(tau,s,j),Finset.mem_univ _,rfl⟩)
  exact ⟨M, hM, (fun tau s j => ⟨(M : 𝕂) * a tau s j, hint tau s j⟩), fun _ _ _ => rfl⟩

theorem algebraic_auxiliary4 (a : Fin 3 → Fin 4 → Fin 4 → 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, a tau s (k h) ≠ 0) →
          kernelRestriction4 (a tau s) k
            (derivative4 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  obtain ⟨M, hM, b, hb⟩ := source_integral_scaling4 a
  have hMK : (M : 𝕂) ≠ 0 := by exact_mod_cast hM
  have hbn : ∀ tau s, ∃ j, b tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := ha tau s
    refine ⟨j, ?_⟩
    intro hz
    exact (mul_ne_zero hMK hj) (by rw [← hb tau s j, hz]; rfl)
  obtain ⟨D, hD, hconstruction⟩ := integral_auxiliary4 b hbn
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
  rw [kernelRestriction4_scale (a tau s) (M : 𝕂) hMK] at hh
  exact hh

end CompoundFeasibility.Auxiliary4Literal176


namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4

theorem source_restriction4_real (K : IntermediateField ℚ ℝ) {m : ℕ}
    (a : Fin 4 → K) (k : Fin m → Fin 4) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) :
    (kernelRestriction4 a k (derivative4 J (P.map (Int.castRingHom K)))).map
      K.val.toRingHom =
      kernelRestriction4 (fun j => (a j : ℝ)) k
        (derivative4 J (P.map (Int.castRingHom ℝ))) := by
  rw [kernelRestriction4_map, derivative4_map, MvPolynomial.map_map]
  have hf : K.val.toRingHom.comp (Int.castRingHom K) = Int.castRingHom ℝ :=
    Subsingleton.elim _ _
  rw [hf]
  rfl

theorem source_auxiliary4_field (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau s j, SourceForms4Literal176.forms4 A2 A3 L tau s j ∈ K,
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        (∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4,
            (∀ h, (⟨SourceForms4Literal176.forms4 A2 A3 L tau s (k h), hmem tau s (k h)⟩ : K) ≠ 0) →
            kernelRestriction4 (fun j => (⟨SourceForms4Literal176.forms4 A2 A3 L tau s j, hmem tau s j⟩ : K)) k
              (derivative4 J (P.map (Int.castRingHom K))) = 0) ∧
        (∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, SourceForms4Literal176.forms4 A2 A3 L tau s (k h) ≠ 0) →
            kernelRestriction4 (SourceForms4Literal176.forms4 A2 A3 L tau s) k
              (derivative4 J (P.map (Int.castRingHom ℝ))) = 0) := by
  obtain ⟨K, hK, hmem⟩ := SourceForms4Literal176.common_source_field4 A2 A3 L ha
  letI : FiniteDimensional ℚ K := hK
  letI : NumberField K := {}
  let a : Fin 3 → Fin 4 → Fin 4 → K := fun tau s j =>
    ⟨SourceForms4Literal176.forms4 A2 A3 L tau s j, hmem tau s j⟩
  have hnonzero : ∀ tau s, ∃ j, a tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := SourceForms4Literal176.source_rows_nonzero4 A2 A3 L h2 h3 hL tau s
    refine ⟨j, ?_⟩
    intro hh
    exact hj (congrArg Subtype.val hh)
  obtain ⟨D, hD, hconstruction⟩ := algebraic_auxiliary4 a hnonzero
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hderiv⟩ := hconstruction eta heta m hm r hr
  refine ⟨P, hP, hhom, hheight, hderiv, ?_⟩
  intro tau s J hJ k hk
  have hkK : ∀ h, a tau s (k h) ≠ 0 := by
    intro h hh
    exact hk h (congrArg Subtype.val hh)
  have he := source_restriction4_real K (a tau s) k J P
  rw [hderiv tau s J hJ k hkK, map_zero] at he
  exact he.symm

theorem source_auxiliary4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau s j, SourceForms4Literal176.forms4 A2 A3 L tau s j ∈ K) ∧
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, SourceForms4Literal176.forms4 A2 A3 L tau s (k h) ≠ 0) →
          kernelRestriction4 (SourceForms4Literal176.forms4 A2 A3 L tau s) k
            (derivative4 J (P.map (Int.castRingHom ℝ))) = 0 := by
  obtain ⟨K, hK, hmem, D, hD, hconstruction⟩ := source_auxiliary4_field A2 A3 L h2 h3 hL ha
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hfield, hreal⟩ := hconstruction eta heta m hm r hr
  exact ⟨P, hP, hhom, hheight, hreal⟩

end CompoundFeasibility.Auxiliary4Literal176

namespace CompoundFeasibility.Auxiliary4Literal176
open SourceMultiblock4

def matrixIndex4 {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) K) (r : Fin m → ℕ) (eta : ℝ)
    (P : MvPolynomial (Vars4 m) ℤ) : Prop :=
  ∀ i (J : Vars4 m →₀ ℕ), rothSourceDerivativeWeight r J < (1/4-eta)*m →
    ∀ k : Fin m → Fin 4, (∀ h, B i (k h) ≠ 0) →
      kernelRestriction4 (B i) k (derivative4 J (P.map (Int.castRingHom K))) = 0

theorem restriction4_map_int {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
    (f : K →+* E) {m : ℕ} (a : Fin 4 → K) (k : Fin m → Fin 4)
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ) :
    (kernelRestriction4 a k (derivative4 J (P.map (Int.castRingHom K)))).map f =
      kernelRestriction4 (fun j => f (a j)) k (derivative4 J (P.map (Int.castRingHom E))) := by
  rw [kernelRestriction4_map,derivative4_map,MvPolynomial.map_map]
  have hf : f.comp (Int.castRingHom K) = Int.castRingHom E := Subsingleton.elim _ _
  rw [hf]

theorem padic_restriction4_zero (p : ℕ) [Fact p.Prime] {m : ℕ}
    (a : Fin 4 → ℚ) (k : Fin m → Fin 4) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ)
    (hz : kernelRestriction4 (fun j => (a j : ℝ)) k
      (derivative4 J (P.map (Int.castRingHom ℝ))) = 0) :
    kernelRestriction4 (fun j => (algebraMap ℚ ℚ_[p]) (a j)) k
      (derivative4 J (P.map (Int.castRingHom ℚ_[p]))) = 0 := by
  have hq : kernelRestriction4 a k (derivative4 J (P.map (Int.castRingHom ℚ))) = 0 := by
    apply MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [map_zero,restriction4_map_int]
    exact hz
  have he := congrArg (MvPolynomial.map (algebraMap ℚ ℚ_[p])) hq
  rw [restriction4_map_int,map_zero] at he
  exact he

theorem finite_matrix_index4 (p : ℕ) [Fact p.Prime] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) ℚ) (r : Fin m → ℕ) (eta : ℝ)
    (P : MvPolynomial (Vars4 m) ℤ)
    (hreal : matrixIndex4 (A.map (algebraMap ℚ ℝ)) r eta P) :
    matrixIndex4 (SourceForms4Literal176.finiteMatrix4 p A) r eta P := by
  intro i J hJ k hk
  apply padic_restriction4_zero p (A i) k J P
  apply hreal i J hJ k
  intro h hz
  have hq : A i (k h) = 0 := by
    change (A i (k h) : ℝ) = 0 at hz
    exact_mod_cast hz
  apply hk h
  simp [SourceForms4Literal176.finiteMatrix4,hq]

theorem source_auxiliary4_all_places (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms4Literal176.forms4 A2 A3 L tau i j ∈ K,
      ∃ D : ℝ, 1 ≤ D ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
      (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex4 (fun i j => (⟨SourceForms4Literal176.forms4 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex4 (SourceForms4Literal176.forms4 A2 A3 L tau) r eta P) ∧
      matrixIndex4 (SourceForms4Literal176.finiteMatrix4 2 A2) r eta P ∧
      matrixIndex4 (SourceForms4Literal176.finiteMatrix4 3 A3) r eta P := by
  obtain ⟨K,hK,hmem,D,hD,hconstruction⟩ := source_auxiliary4_field A2 A3 L h2 h3 hL ha
  refine ⟨K,hK,hmem,D,hD,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hP,hhom,hheight,hfield,hreal⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hP,hhom,hheight,hfield,hreal,?_,?_⟩
  · apply finite_matrix_index4 2 A2 r eta P
    exact hreal 1
  · apply finite_matrix_index4 3 A3 r eta P
    exact hreal 2

end CompoundFeasibility.Auxiliary4Literal176

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4
open SourceMultiblock4 Aux6Mass

def linearChart {K : Type*} [CommRing K] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) K) (u : Vars4 m) : MvPolynomial (Vars4 m) K :=
  ∑ j : Fin 4, MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)

def substitution {K : Type*} [CommRing K] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) K) :
    MvPolynomial (Vars4 m) K →+* MvPolynomial (Vars4 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (linearChart B)

def expansion {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) : MvPolynomial (Vars4 m) K :=
  substitution A⁻¹ (derivative4 J (P.map (Int.castRingHom K)))

theorem chart_one {K : Type*} [CommRing K] {m : ℕ} (u : Vars4 m) :
    linearChart (1 : Matrix (Fin 4) (Fin 4) K) u = MvPolynomial.X u := by
  simp [linearChart, Matrix.one_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem chart_comp {K : Type*} [CommRing K] {m : ℕ}
    (A B : Matrix (Fin 4) (Fin 4) K) (u : Vars4 m) :
    substitution A (linearChart B u) = linearChart (B * A) u := by
  simp only [linearChart, substitution, map_sum, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mul_apply]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  ring

theorem substitution_comp {K : Type*} [CommRing K] {m : ℕ}
    (A B : Matrix (Fin 4) (Fin 4) K) (P : MvPolynomial (Vars4 m) K) :
    substitution A (substitution B P) = substitution (B * A) P := by
  have he : (substitution (m := m) A).comp (substitution B) = substitution (B * A) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [substitution]
    · intro u
      simp only [RingHom.comp_apply, substitution, MvPolynomial.eval₂Hom_X']
      exact chart_comp A B u
  exact congrArg (fun f => f P) he

theorem substitution_one {K : Type*} [CommRing K] {m : ℕ}
    (P : MvPolynomial (Vars4 m) K) : substitution 1 P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P u hP =>
    rw [map_mul, hP]
    simp [substitution, chart_one]

theorem reconstruct {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0)
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ) :
    substitution A (expansion A J P) = derivative4 J (P.map (Int.castRingHom K)) := by
  rw [expansion, substitution_comp, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
    substitution_one]

theorem unique {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0)
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ)
    (Q : MvPolynomial (Vars4 m) K)
    (hQ : substitution A Q = derivative4 J (P.map (Int.castRingHom K))) :
    Q = expansion A J P := by
  have he := congrArg (substitution A⁻¹) hQ
  rw [substitution_comp, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
    substitution_one] at he
  exact he

theorem chart_mass {K : Type*} [NormedField K] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) K) (G : ℝ)
    (hB : ∀ i j, ‖B i j‖ ≤ G) (u : Vars4 m) : mass (linearChart B u) ≤ 4 * G := by
  calc
    _ ≤ ∑ j : Fin 4, mass (MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)) := mass_sum _ _
    _ ≤ ∑ _j : Fin 4, G := by
      apply Finset.sum_le_sum
      intro j _
      rw [mass_C_mul_X]
      exact hB _ _
    _ = _ := by simp

theorem monomial_mass {K : Type*} [NormedField K] {m : ℕ} {r : Fin m → ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, ‖A⁻¹ i j‖ ≤ G)
    (b : RothAuxCoefficients r) (J : Vars4 m →₀ ℕ) (c : ℤ) :
    mass (expansion A J (MvPolynomial.monomial (exponent4 b) c)) ≤
      (c.natAbs : ℝ) * (8 * G) ^ (∑ h, r h) := by
  let R := ∑ h, r h
  have hbase : 1 ≤ 4 * G := by linarith
  have hsum : (∑ u : Vars4 m, (exponent4 b - J) u) ≤ R := by
    change (∑ u : Vars4 m, (exponent4 b - J) u) ≤ ∑ h, r h
    rw [← exponent4_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  have hprod : mass (∏ u : Vars4 m, linearChart A⁻¹ u ^ (exponent4 b - J) u) ≤ (4 * G) ^ R := by
    calc
      _ ≤ ∏ u : Vars4 m, mass (linearChart A⁻¹ u ^ (exponent4 b - J) u) := mass_prod _ _
      _ ≤ ∏ u : Vars4 m, (4 * G) ^ (exponent4 b - J) u := by
        apply Finset.prod_le_prod
        · intro u _; exact mass_nonneg _
        · intro u _
          exact (mass_pow _ _).trans
            (pow_le_pow_left₀ (mass_nonneg _) (chart_mass A⁻¹ G hentry u) _)
      _ = (4 * G) ^ (∑ u : Vars4 m, (exponent4 b - J) u) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ _ := pow_le_pow_right₀ hbase hsum
  have hc : ‖(c : K)‖ ≤ (c.natAbs : ℝ) := by
    simpa only [zsmul_eq_mul, mul_one, norm_one, Int.norm_eq_abs, Int.cast_abs, Int.cast_natAbs] using (norm_zsmul_le (n := c) (a := (1 : K)))
  have he : expansion A J (MvPolynomial.monomial (exponent4 b) c) =
      MvPolynomial.C ((c : K) * ∏ u : Vars4 m, (Nat.choose (exponent4 b u) (J u) : K)) *
        ∏ u : Vars4 m, linearChart A⁻¹ u ^ (exponent4 b - J) u := by
    rw [expansion, MvPolynomial.map_monomial, derivative4_monomial, substitution,
      MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [he]
  calc
    _ ≤ mass (MvPolynomial.C ((c : K) * ∏ u : Vars4 m,
        (Nat.choose (exponent4 b u) (J u) : K))) *
        mass (∏ u : Vars4 m, linearChart A⁻¹ u ^ (exponent4 b - J) u) := mass_mul _ _
    _ ≤ ((c.natAbs : ℝ) * (2 : ℝ)^R) * (4 * G)^R := by
      apply mul_le_mul
      · rw [MvPolynomial.C_apply, mass_monomial]
        exact (norm_mul_le _ _).trans
          (mul_le_mul hc (Aux4HeightLiteral176.binomial_norm4 b J) (norm_nonneg _) (Nat.cast_nonneg _))
      · exact hprod
      · exact mass_nonneg _
      · positivity
    _ = _ := by rw [mul_assoc, ← mul_pow]; congr 2; ring



theorem support_index {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (d : Vars4 m →₀ ℕ) (hd : d ∈ P.support) :
    ∃ b : RothAuxCoefficients r, exponent4 b = d := by
  have hle (h : Fin m) (i : Fin 4) : d (h,i) ≤ r h := by
    rw [← hP d hd h]
    exact Finset.single_le_sum (f := fun j : Fin 4 => d (h,j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨fun h => ⟨fun i => ⟨d (h,i), by have hh := hle h i; omega⟩, hP d hd h⟩, ?_⟩
  ext u
  rfl

theorem support_card {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) :
    P.support.card ≤ 16 ^ (∑ h, r h) := by
  have hs : P.support ⊆ Finset.univ.image (@exponent4 m r) := by
    intro d hd
    obtain ⟨b,hb⟩ := support_index r P hP d hd
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hb⟩
  calc
    _ ≤ (Finset.univ.image (@exponent4 m r)).card := Finset.card_le_card hs
    _ ≤ Fintype.card (RothAuxCoefficients r) := Finset.card_image_le
    _ ≤ _ := dimension4_le_pow r hr

theorem expansion_sum {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) :
    expansion A J P = ∑ d ∈ P.support, expansion A J (MvPolynomial.monomial d (P.coeff d)) := by
  unfold expansion
  rw [← derivative4_map, derivative4, MvPolynomial.sum_def, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.map_monomial, derivative4_monomial, map_mul, map_prod, map_natCast]

theorem coefficient_bound {K : Type*} [NormedField K] {m : ℕ}
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (D : ℝ) (hD : 1 ≤ D) (hheight : (height4 P : ℝ) ≤ D ^ (∑ h, r h))
    (A : Matrix (Fin 4) (Fin 4) K) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, ‖A⁻¹ i j‖ ≤ G) (J b : Vars4 m →₀ ℕ) :
    ‖(expansion A J P).coeff b‖ ≤ (128 * D * G) ^ (∑ h, r h) := by
  have hDpos : 0 ≤ D := by linarith
  have hGpos : 0 ≤ G := by linarith
  apply (coeff_le_mass _ _).trans
  rw [expansion_sum]
  calc
    _ ≤ ∑ d ∈ P.support, mass (expansion A J (MvPolynomial.monomial d (P.coeff d))) := mass_sum _ _
    _ ≤ ∑ _d ∈ P.support, D^(∑ h, r h) * (8*G)^(∑ h, r h) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨a,ha⟩ := support_index r P hP d hd
      have hc : ((P.coeff d).natAbs : ℝ) ≤ D^(∑ h, r h) := by
        have hh : (P.coeff d).natAbs ≤ height4 P := Finset.le_sup (f := fun e => (P.coeff e).natAbs) hd
        exact (by exact_mod_cast hh : ((P.coeff d).natAbs : ℝ) ≤ (height4 P : ℝ)).trans hheight
      have hm := monomial_mass A G hG hentry a J (P.coeff d)
      rw [ha] at hm
      exact hm.trans (mul_le_mul_of_nonneg_right hc (by positivity))
    _ = (P.support.card : ℝ) * (D^(∑ h, r h) * (8*G)^(∑ h, r h)) := by simp
    _ ≤ (16 : ℝ)^(∑ h, r h) * (D^(∑ h, r h) * (8*G)^(∑ h, r h)) := by
      have hc : (P.support.card : ℝ) ≤ (16 : ℝ)^(∑ h, r h) := by exact_mod_cast support_card r hr P hP
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring



def inverseBudget {K : Type*} [NormedField K] (A : Matrix (Fin 4) (Fin 4) K) : ℝ :=
  1 + ∑ i : Fin 4, ∑ j : Fin 4, ‖A⁻¹ i j‖

theorem inverseBudget_one {K : Type*} [NormedField K]
    (A : Matrix (Fin 4) (Fin 4) K) : 1 ≤ inverseBudget A := by
  unfold inverseBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

theorem inverseBudget_entry {K : Type*} [NormedField K]
    (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) : ‖A⁻¹ i j‖ ≤ inverseBudget A := by
  have hrow : ‖A⁻¹ i j‖ ≤ ∑ k : Fin 4, ‖A⁻¹ i k‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have hall : (∑ k : Fin 4, ‖A⁻¹ i k‖) ≤ ∑ h : Fin 4, ∑ k : Fin 4, ‖A⁻¹ h k‖ :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i)
  unfold inverseBudget
  linarith

theorem source_coefficient_bounds (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ (m : ℕ) (r : Fin m → ℕ), (∀ h, 0 < r h) →
      ∀ P : MvPolynomial (Vars4 m) ℤ, homogeneous4 r P →
      (height4 P : ℝ) ≤ D^(∑ h, r h) → ∀ J b : Vars4 m →₀ ℕ,
      ‖(expansion L J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h) := by
  let G := max (inverseBudget L)
    (max (inverseBudget (SourceForms4Literal176.finiteMatrix4 2 A2)) (inverseBudget (SourceForms4Literal176.finiteMatrix4 3 A3)))
  have h0 : inverseBudget L ≤ G := le_max_left _ _
  have h2 : inverseBudget (SourceForms4Literal176.finiteMatrix4 2 A2) ≤ G := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : inverseBudget (SourceForms4Literal176.finiteMatrix4 3 A3) ≤ G := (le_max_right _ _).trans (le_max_right _ _)
  have hG : 1 ≤ G := (inverseBudget_one _).trans h0
  refine ⟨128 * D * G, by nlinarith, ?_⟩
  intro m r hr P hP hheight J b
  exact ⟨coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h0) J b,
    coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h2) J b,
    coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h3) J b⟩


end CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176.SourceSupport4
open SourceMultiblock4 SourceExpansion4
variable {K : Type*} [Field K] [CharZero K]
theorem chart_pderiv {m : ℕ} (B : Matrix (Fin 4) (Fin 4) K)
    (h : Fin m) (i : Fin 4) (u : Vars4 m) :
    MvPolynomial.pderiv (h,i) (linearChart B u) =
      if u.1 = h then MvPolynomial.C (B u.2 i) else 0 := by
  classical
  rcases u with ⟨g,j⟩
  by_cases hg : g = h
  · subst g
    simp [linearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · simp [linearChart, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg]

theorem substitution_chain {m : ℕ} (B : Matrix (Fin 4) (Fin 4) K)
    (h : Fin m) (i : Fin 4) (P : MvPolynomial (Vars4 m) K) :
    MvPolynomial.pderiv (h,i) (substitution B P) =
      ∑ j : Fin 4, MvPolynomial.C (B j i) *
        substitution B (MvPolynomial.pderiv (h,j) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add, Finset.sum_add_distrib]
  | mul_X P u hP =>
    have hdelta : (∑ j : Fin 4, (MvPolynomial.C (B j i) * substitution B P) *
        (if (h,j) = u then 1 else 0)) =
        substitution B P * (if u.1 = h then MvPolynomial.C (B u.2 i) else 0) := by
      rcases u with ⟨g,l⟩
      by_cases hg : g = h
      · subst g
        simp [Prod.mk.injEq, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]
      · simp [Prod.mk.injEq, hg, Ne.symm hg]
    have hX : substitution B (MvPolynomial.X u) = linearChart B u := by
      simp [substitution]
    have hD (j : Fin 4) :
        substitution B (MvPolynomial.pderiv (h,j) (P * MvPolynomial.X u)) =
          substitution B (MvPolynomial.pderiv (h,j) P) * linearChart B u +
          substitution B P * (if (h,j) = u then 1 else 0) := by
      by_cases he : (h,j) = u <;>
        simp [MvPolynomial.pderiv_mul, hX, MvPolynomial.pderiv_X, Pi.single_apply, he, eq_comm] <;> ring
    rw [map_mul, MvPolynomial.pderiv_mul, hP, hX, chart_pderiv]
    simp_rw [hD, mul_add, ← mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hdelta]

noncomputable def zeroCoordinate {m : ℕ} (i : Fin 4) :
    MvPolynomial (Vars4 m) K →+* MvPolynomial (Vars4 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = i then 0 else MvPolynomial.X u)

noncomputable def kernelImage {m : ℕ} (L : Matrix (Fin 4) (Fin 4) K)
    (i : Fin 4) (u : Vars4 m) : MvPolynomial (Vars4 m) K :=
  zeroCoordinate i (linearChart (L)⁻¹ u)

theorem kernel_image_form {m : ℕ} (L : Matrix (Fin 4) (Fin 4) K)
    (hL : (L).det ≠ 0) (i : Fin 4) (h : Fin m) :
    (∑ j : Fin 4, MvPolynomial.C (L i j : K) * kernelImage L i (h,j)) = 0 := by
  have he := chart_comp (L)⁻¹ (L) (h,i)
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL), chart_one] at he
  change substitution (L)⁻¹
    (∑ j : Fin 4, MvPolynomial.C (L i j) * MvPolynomial.X (h,j)) =
      MvPolynomial.X (h,i) at he
  simp only [map_sum, map_mul, substitution,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at he
  have hz := congrArg (zeroCoordinate i) he
  have hC (q : K) : zeroCoordinate (m := m) i (MvPolynomial.C q) = MvPolynomial.C q := by
    simp [zeroCoordinate]
  simp only [map_sum, map_mul, hC] at hz
  rw [show zeroCoordinate i (MvPolynomial.X (h,i)) = 0 by
    simp [zeroCoordinate]] at hz
  exact hz

theorem kernel_factor_variable {m : ℕ} (L : Matrix (Fin 4) (Fin 4) K)
    (hL : (L).det ≠ 0) (i p : Fin 4) (hp : L i p ≠ 0)
    (u : Vars4 m) :
    MvPolynomial.eval₂Hom MvPolynomial.C (kernelImage L i)
      (kernelChart4 (L i) (fun _ => p) u) =
      kernelImage L i u := by
  classical
  have ha : (L i p : K) ≠ 0 := by exact_mod_cast hp
  have hcancel : (MvPolynomial.C ((L i p : K)⁻¹) : MvPolynomial (Vars4 m) K) *
      MvPolynomial.C (L i p : K) = 1 := by
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ha, map_one]
  by_cases hu : u.2 = p
  · have hs := kernel_image_form L hL i u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hs
    have hr : -(∑ j ∈ Finset.univ.erase p,
        MvPolynomial.C (L i j : K) * kernelImage L i (u.1,j)) =
        MvPolynomial.C (L i p : K) * kernelImage L i (u.1,p) := by
      linear_combination -hs
    simp only [kernelChart4, hu, if_pos rfl, ite_true, map_neg, map_sum, map_mul,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((L i p : K)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p,
            MvPolynomial.C (L i j : K) * kernelImage L i (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv, MvPolynomial.C_mul]
        ring
      _ = _ := by rw [hr, ← mul_assoc, hcancel, one_mul]; simp [← hu]
  · simp [kernelChart4, hu]

theorem zero_monomial {m : ℕ} (i : Fin 4)
    (b : Vars4 m →₀ ℕ) (c : K) :
    zeroCoordinate i (MvPolynomial.monomial b c) =
      if (∀ h, b (h,i) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [zeroCoordinate, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  by_cases hb : ∀ h, b (h,i) = 0
  · rw [if_pos hb, MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    apply Finset.prod_congr rfl
    intro u _
    by_cases hu : u.2 = i
    · have he : u = (u.1,i) := Prod.ext rfl hu
      have hz : b u = 0 := (congrArg b he).trans (hb u.1)
      simp [hu, hz]
    · simp [hu]
  · rw [if_neg hb]
    push_neg at hb
    obtain ⟨h, hh⟩ := hb
    have hz : (∏ u : Vars4 m, (if u.2 = i then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (Vars4 m) K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,i))
      simp [hh]
    rw [hz, mul_zero]

theorem zero_coeff {m : ℕ} (i : Fin 4)
    (Q : MvPolynomial (Vars4 m) K) (b : Vars4 m →₀ ℕ) :
    (zeroCoordinate i Q).coeff b = if (∀ h, b (h,i) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [zero_monomial]
    by_cases ha : ∀ h, a (h,i) = 0
    · rw [if_pos ha]
      by_cases hb : ∀ h, b (h,i) = 0
      · simp [hb]
      · have hab : a ≠ b := by intro he; subst a; exact hb ha
        simp [hb, hab]
    · rw [if_neg ha]
      by_cases hb : ∀ h, b (h,i) = 0
      · have hab : a ≠ b := by intro he; subst a; exact ha hb
        simp [hb, hab]
      · simp [hb]
  | add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, hP, hQ, MvPolynomial.coeff_add]
    split_ifs <;> simp

theorem pderiv_coeff {m : ℕ} (u : Vars4 m)
    (Q : MvPolynomial (Vars4 m) K) (b : Vars4 m →₀ ℕ) :
    (MvPolynomial.pderiv u Q).coeff b =
      (b u + 1 : ℕ) * Q.coeff (b + Finsupp.single u 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]; ring
  | monomial a c =>
    by_cases ha : a u = 0
    · have hab : a ≠ b + Finsupp.single u 1 := by
        intro he
        have h := congrArg (fun d : Vars4 m →₀ ℕ => d u) he
        simp [ha, Finsupp.add_apply, Finsupp.single_apply] at h
      simp [MvPolynomial.pderiv_monomial, ha, MvPolynomial.coeff_monomial, hab]
    · have hle : Finsupp.single u 1 ≤ a := by rw [Finsupp.single_le_iff]; omega
      have heq : a - Finsupp.single u 1 = b ↔ a = b + Finsupp.single u 1 := by
        constructor
        · intro he
          rw [← he]
          exact (tsub_add_cancel_of_le hle).symm
        · intro he
          rw [he, add_tsub_cancel_right]
      simp only [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, heq]
      split_ifs with he
      · subst a
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
        ring
      · simp

theorem kernel_factor {m : ℕ} (L : Matrix (Fin 4) (Fin 4) K)
    (hL : L.det ≠ 0) (i p : Fin 4) (hp : L i p ≠ 0)
    (Q : MvPolynomial (Vars4 m) K) :
    MvPolynomial.eval₂Hom MvPolynomial.C (kernelImage L i)
      (kernelRestriction4 (L i) (fun _ => p) Q) =
      zeroCoordinate i (substitution L⁻¹ Q) := by
  have he : (MvPolynomial.eval₂Hom MvPolynomial.C (kernelImage (m := m) L i)).comp
      (kernelRestriction4 (L i) (fun _ => p)) =
      (zeroCoordinate i).comp (substitution L⁻¹) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [kernelRestriction4, substitution, zeroCoordinate]
    · intro u
      simp only [RingHom.comp_apply, kernelRestriction4, substitution, MvPolynomial.eval₂Hom_X']
      exact kernel_factor_variable L hL i p hp u
  exact congrArg (fun f => f Q) he

theorem index_zero_slice {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 4) (Fin 4) K) (hL : L.det ≠ 0)
    (i p : Fin 4) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars4 m) ℤ)
    (hindex : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < T →
      kernelRestriction4 (L i) (fun _ => p) (derivative4 J (P.map (Int.castRingHom K))) = 0)
    (J : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J < T) :
    zeroCoordinate i (expansion L J P) = 0 := by
  rw [expansion, ← kernel_factor L hL i p hp, hindex J hJ, map_zero]

theorem expansion_chain {m : ℕ} (L : Matrix (Fin 4) (Fin 4) K)
    (h : Fin m) (i : Fin 4) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) :
    MvPolynomial.pderiv (h,i) (expansion L J P) =
      ∑ j : Fin 4, MvPolynomial.C (L⁻¹ j i) *
        (J (h,j) + 1) • expansion L (J + Finsupp.single (h,j) 1) P := by
  rw [expansion, substitution_chain]
  simp only [source4_pderiv_hasse, map_nsmul, expansion]

noncomputable def coordinateWeight {m : ℕ} (r : Fin m → ℕ) (i : Fin 4)
    (b : Vars4 m →₀ ℕ) : ℝ := ∑ h, (b (h,i) : ℝ) / r h

theorem coordinate_weight_add {m : ℕ} (r : Fin m → ℕ) (i : Fin 4)
    (b c : Vars4 m →₀ ℕ) :
    coordinateWeight r i (b + c) =
      coordinateWeight r i b + coordinateWeight r i c := by
  simp [coordinateWeight, Finsupp.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]

theorem coordinate_weight_single {m : ℕ} (r : Fin m → ℕ)
    (i : Fin 4) (h : Fin m) :
    coordinateWeight r i (Finsupp.single (h,i) 1) = 1 / (r h : ℝ) := by
  simp [coordinateWeight, Finsupp.single_apply, Prod.mk.injEq,
    ite_div, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem coeff_zero_below_index {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 4) (Fin 4) K) (hL : (L).det ≠ 0)
    (i p : Fin 4) (hp : L i p ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars4 m) ℤ)
    (hindex : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < T →
      kernelRestriction4 (L i) (fun _ => p) (derivative4 J (P.map (Int.castRingHom K))) = 0)
    (J b : Vars4 m →₀ ℕ)
    (hbad : rothSourceDerivativeWeight r J + coordinateWeight r i b < T) :
    (expansion L J P).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : Vars4 m →₀ ℕ,
      (∑ h : Fin m, b (h,i)) = n →
      rothSourceDerivativeWeight r J + coordinateWeight r i b < T →
      (expansion L J P).coeff b = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J b hn hw
      by_cases hnzero : n = 0
      · have hbzero : ∀ h, b (h,i) = 0 := by
          intro h
          have hle : b (h,i) ≤ ∑ g : Fin m, b (g,i) :=
            Finset.single_le_sum (f := fun g : Fin m => b (g,i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
          omega
        have hnonneg : 0 ≤ coordinateWeight r i b := by
          unfold coordinateWeight
          positivity
        have hJ : rothSourceDerivativeWeight r J < T := by linarith
        have hz := index_zero_slice r L hL i p hp T P hindex J hJ
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [zero_coeff, if_pos hbzero, MvPolynomial.coeff_zero] at he
        exact he
      · have hex : ∃ h : Fin m, b (h,i) ≠ 0 := by
          by_contra hzero
          push_neg at hzero
          have hs : (∑ h : Fin m, b (h,i)) = 0 := Finset.sum_eq_zero (fun h _ => hzero h)
          omega
        obtain ⟨h, hh⟩ := hex
        let c := b - Finsupp.single (h,i) 1
        have hle : Finsupp.single (h,i) 1 ≤ b := by rw [Finsupp.single_le_iff]; omega
        have hceq : c + Finsupp.single (h,i) 1 = b := tsub_add_cancel_of_le hle
        have hcount : (∑ g : Fin m, c (g,i)) + 1 = n := by
          have hs := congrArg (fun d : Vars4 m →₀ ℕ => ∑ g : Fin m, d (g,i)) hceq
          simpa [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
            Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', hn] using hs
        have hcoord : coordinateWeight r i c + 1 / (r h : ℝ) =
            coordinateWeight r i b := by
          rw [← coordinate_weight_single r i h, ← coordinate_weight_add, hceq]
        have hz (j : Fin 4) : (expansion L (J + Finsupp.single (h,j) 1) P).coeff c = 0 := by
          apply ih (∑ g : Fin m, c (g,i)) (by omega) _ c rfl
          rw [rothSource_weight_add, rothSource_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,i) (expansion L J P)).coeff c = 0 := by
          rw [expansion_chain, MvPolynomial.coeff_sum]
          apply Finset.sum_eq_zero
          intro j hj
          rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_smul, hz j, smul_zero, mul_zero]
        rw [pderiv_coeff, hceq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad




end CompoundFeasibility.Auxiliary4Literal176.SourceSupport4

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176.SourceBalance4
open SourceMultiblock4 SourceExpansion4 SourceSupport4

variable {K : Type*} [Field K] [CharZero K]
theorem chart_block_weight {m : ℕ} (B : Matrix (Fin 4) (Fin 4) K)
    (h : Fin m) (u : Vars4 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.1 = h then 1 else 0)
      (linearChart B u) (if u.1 = h then 1 else 0) := by
  unfold linearChart
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  simpa only [zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C _ (B u.2 j)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (fun v : Vars4 m => if v.1 = h then 1 else 0) (u.1,j))

theorem expansion_block_weight {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.1 = h then 1 else 0)
      (expansion L J P) (r h - ∑ j : Fin 4, J (h,j)) := by
  classical
  let Q := derivative4 J (P.map (Int.castRingHom K))
  let w := fun v : Vars4 m => if v.1 = h then 1 else 0
  have hdegree (d : Vars4 m →₀ ℕ) (hd : d ∈ Q.support) :
      (∑ j : Fin 4, d (h,j)) = r h - ∑ j : Fin 4, J (h,j) := by
    have hcoeff : P.coeff (d + J) ≠ 0 := by
      intro hz
      have hn := MvPolynomial.mem_support_iff.mp hd
      rw [derivative4_coeff, MvPolynomial.coeff_map, hz, map_zero, zero_mul] at hn
      exact hn rfl
    have hh := hP (d + J) (MvPolynomial.mem_support_iff.mpr hcoeff) h
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hh
    omega
  change MvPolynomial.IsWeightedHomogeneous w
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (linearChart (L)⁻¹) Q) _
  conv_lhs => arg 2; rw [MvPolynomial.as_sum Q]
  rw [map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have hw : (∑ u : Vars4 m, d u * w u) = ∑ j : Fin 4, d (h,j) := by
    have he := rothAux_weight_block d h
    rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
    simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars4 m => linearChart (L)⁻¹ u ^ d u)
    (fun u => d u * w u)
    (fun u _ => by simpa only [nsmul_eq_mul] using
      (chart_block_weight (L)⁻¹ h u).pow (d u))
  simpa only [zero_add, hw, hdegree d hd] using
    (MvPolynomial.isWeightedHomogeneous_C w (Q.coeff d)).mul hprod

theorem expansion_block_degree {m : ℕ} (r : Fin m → ℕ)
    (L : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (b : Vars4 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) (h : Fin m) :
    (∑ j : Fin 4, b (h,j)) = r h - ∑ j : Fin 4, J (h,j) := by
  have hw := expansion_block_weight r L J P hP h hb
  rwa [rothAux_weight_block] at hw

theorem total_coordinate_weight_le {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (L : Matrix (Fin 4) (Fin 4) K) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (b : Vars4 m →₀ ℕ) (hb : (expansion L J P).coeff b ≠ 0) :
    (∑ i : Fin 4, coordinateWeight r i b) ≤ (m : ℝ) := by
  unfold coordinateWeight
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ h : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [← Finset.sum_div]
      have hrh : (0 : ℝ) < r h := by exact_mod_cast hr h
      apply (div_le_one hrh).mpr
      have hdeg := expansion_block_degree r L J P hP b hb h
      exact_mod_cast (show (∑ i : Fin 4, b (h,i)) ≤ r h by omega)
    _ = _ := by simp




theorem balance_from_weights (m : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (x : Fin 4 → ℝ) (hsum : (∑ i, x i) ≤ m)
    (hlower : ∀ i, (m : ℝ)/4 - 3*eta*m ≤ x i) :
    ∀ i, |x i - (m : ℝ)/4| ≤ 18*eta*m := by
  intro i
  have hc : (Finset.univ.erase i : Finset (Fin 4)).card = 3 := by simp
  have ho := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hlower j)
  have ho' : 3*((m : ℝ)/4 - 3*eta*m) ≤ ∑ j ∈ Finset.univ.erase i, x j := by
    simpa only [Finset.sum_const, hc, nsmul_eq_mul] using ho
  have ht : (∑ j ∈ Finset.univ.erase i, x j) + x i ≤ m := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsum
  have hn : 0 ≤ eta*(m : ℝ) := mul_nonneg heta (Nat.cast_nonneg _)
  exact abs_le.mpr ⟨by nlinarith [hlower i], by nlinarith⟩

theorem balanced_of_vanishing {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 4) (Fin 4) K)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (hz : ∀ (i : Fin 4) (J b : Vars4 m →₀ ℕ),
      rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/4-eta)*m →
      (expansion A J P).coeff b = 0)
    (J b : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hb : (expansion A J P).coeff b ≠ 0) :
    ∀ i, |coordinateWeight r i b - (m : ℝ)/4| ≤ 18*eta*m := by
  have hlower (i : Fin 4) : (m : ℝ)/4 - 3*eta*m ≤ coordinateWeight r i b := by
    have ht : (1/4-eta)*m ≤ rothSourceDerivativeWeight r J + coordinateWeight r i b := by
      by_contra! hbad
      exact hb (hz i J b hbad)
    nlinarith
  exact balance_from_weights m eta heta.le (fun i => coordinateWeight r i b)
    (total_coordinate_weight_le r hr A J P hP b hb) hlower

def Claims {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (A : Matrix (Fin 4) (Fin 4) K) (P : MvPolynomial (Vars4 m) ℤ) : Prop :=
  (∀ J, substitution A (expansion A J P) = derivative4 J (P.map (Int.castRingHom K))) ∧
  (∀ (i : Fin 4) (J b : Vars4 m →₀ ℕ),
    rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/4-eta)*m →
    (expansion A J P).coeff b = 0) ∧
  (∀ (J b : Vars4 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    ∀ h, (∑ j : Fin 4, b (h,j)) = r h - ∑ j : Fin 4, J (h,j)) ∧
  (∀ (J b : Vars4 m →₀ ℕ), (expansion A J P).coeff b ≠ 0 →
    (∑ i : Fin 4, coordinateWeight r i b) ≤ m) ∧
  (∀ (J b : Vars4 m →₀ ℕ), rothSourceDerivativeWeight r J ≤ 2*eta*m →
    (expansion A J P).coeff b ≠ 0 →
    ∀ i, |coordinateWeight r i b - (m : ℝ)/4| ≤ 18*eta*m)

theorem claims_of_charts {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (hindex : ∀ (i : Fin 4) (J : Vars4 m →₀ ℕ),
      rothSourceDerivativeWeight r J < (1/4-eta)*m →
      ∀ p : Fin 4, A i p ≠ 0 → kernelRestriction4 (A i) (fun _ => p)
        (derivative4 J (P.map (Int.castRingHom K))) = 0) : Claims r eta A P := by
  have hz (i : Fin 4) (J b : Vars4 m →₀ ℕ)
      (hb : rothSourceDerivativeWeight r J + coordinateWeight r i b < (1/4-eta)*m) :
      (expansion A J P).coeff b = 0 := by
    have hn : ∃ p, A i p ≠ 0 := by
      by_contra! hh
      exact hA (Matrix.det_eq_zero_of_row_eq_zero i hh)
    obtain ⟨p,hp⟩ := hn
    apply coeff_zero_below_index r A hA i p hp ((1/4-eta)*m) P
    · intro D hD
      exact hindex i D hD p hp
    · exact hb
  exact ⟨fun J => reconstruct A hA J P, hz,
    fun J b hb h => expansion_block_degree r A J P hP b hb h,
    fun J b hb => total_coordinate_weight_le r hr A J P hP b hb,
    fun J b hJ hb => balanced_of_vanishing r hr eta heta A P hP hz J b hJ hb⟩



theorem claims_of_matrix_index4 {F : Type*} [Field F] [CharZero F]
    {m : ℕ} (B : Matrix (Fin 4) (Fin 4) F) (hB : B.det = 1)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (P : MvPolynomial (Vars4 m) ℤ) (hhom : homogeneous4 r P)
    (hi : matrixIndex4 B r eta P) : Claims r eta B P := by
  apply claims_of_charts r hr eta heta B (by rw [hB]; exact one_ne_zero) P hhom
  intro i J hJ k hk
  exact hi i J hJ (fun _ => k) (fun _ => hk)

theorem source_auxiliary4_balanced (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms4Literal176.forms4 A2 A3 L tau i j ∈ K,
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
      (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex4 (fun i j => (⟨SourceForms4Literal176.forms4 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex4 (SourceForms4Literal176.forms4 A2 A3 L tau) r eta P) ∧
      matrixIndex4 (SourceForms4Literal176.finiteMatrix4 2 A2) r eta P ∧
      matrixIndex4 (SourceForms4Literal176.finiteMatrix4 3 A3) r eta P ∧
      (Claims r eta L P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 2 A2) P ∧
        Claims r eta (SourceForms4Literal176.finiteMatrix4 3 A3) P) ∧
      (∀ J b : Vars4 m →₀ ℕ,
        ‖(expansion L J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) := by
  obtain ⟨K,hK,hmem,D,hD,hconstruction⟩ := source_auxiliary4_all_places A2 A3 L h2 h3 hL ha
  obtain ⟨E,hE,hbound⟩ := source_coefficient_bounds A2 A3 L D hD
  refine ⟨K,hK,hmem,D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,?_,hbound m r hr P hhom hheight⟩
  constructor
  · exact claims_of_matrix_index4 L hL r hr eta heta P hhom (hreal 0)
  · constructor
    · exact claims_of_matrix_index4 _ (SourceForms4Literal176.finite_det_one4 2 A2 h2) r hr eta heta P hhom hp2
    · exact claims_of_matrix_index4 _ (SourceForms4Literal176.finite_det_one4 3 A3 h3) r hr eta heta P hhom hp3

end CompoundFeasibility.Auxiliary4Literal176.SourceBalance4

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4
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

end CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176.SourceGrid4
open SourceMultiblock4 SourceExpansion4 SourceSupport4 SourceBalance4 SourceEvaluation4

theorem evaluation_upper {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0)
    (r : Fin m → ℕ) (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ)
    (hP : homogeneous4 r P) (v : Fin m → Fin 4 → ℤ)
    (E T : ℝ) (hE : 0 ≤ E) (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 4 → ℝ)
    (hv : ∀ h i, ‖(A *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i))
    (hc : ∀ b, ‖(expansion A J P).coeff b‖ ≤ E^(∑ h, r h))
    (ht : ∀ b ∈ (expansion A J P).support, (∑ i, c i * logWeight Q b i) ≤ T) :
    ‖(integerValue J P v : K)‖ ≤ (16*E)^(∑ h, r h)*Real.exp T := by
  rw [evaluation_identity A hA J P v]
  calc
    _ ≤ ∑ b ∈ (expansion A J P).support, ‖(expansion A J P).coeff b *
        ∏ u : Vars4 m, ((A *ᵥ (fun i => (v u.1 i : K))) u.2)^b u‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ (expansion A J P).support, E^(∑ h, r h)*Real.exp T := by
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul]
      exact (mul_le_mul (hc b) (monomial_bound A v Q hQ c hv b)
        (norm_nonneg _) (pow_nonneg hE _)).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (ht b hb)) (pow_nonneg hE _))
    _ = ((expansion A J P).support.card : ℝ)*(E^(∑ h, r h)*Real.exp T) := by simp
    _ ≤ (16 : ℝ)^(∑ h, r h)*(E^(∑ h, r h)*Real.exp T) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast expansion_support_card r A J P hP
    _ = _ := by rw [← mul_assoc, ← mul_pow]

def gridPoint {m : ℕ} (w : Fin m → Fin 3 → Fin 4 → ℤ)
    (a : Fin m → Fin 3 → ℕ) : Fin m → Fin 4 → ℤ :=
  fun h i => ∑ j, (a h j : ℤ)*w h j i

theorem matrix_grid {K : Type*} [CommRing K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (w : Fin m → Fin 3 → Fin 4 → ℤ)
    (a : Fin m → Fin 3 → ℕ) (h : Fin m) (i : Fin 4) :
    (A *ᵥ (fun k => (gridPoint w a h k : K))) i =
      ∑ j : Fin 3, (a h j : K)*(A *ᵥ (fun k => (w h j k : K))) i := by
  simp only [gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast,
    Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem grid_form_norm {K : Type*} [NormedField K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (w : Fin m → Fin 3 → Fin 4 → ℤ)
    (a : Fin m → Fin 3 → ℕ) (h : Fin m) (i : Fin 4) (U B : ℝ)
    (hU : 0 ≤ U) (ha : ∀ j, ‖(a h j : K)‖ ≤ U)
    (hw : ∀ j, ‖(A *ᵥ (fun k => (w h j k : K))) i‖ ≤ B) :
    ‖(A *ᵥ (fun k => (gridPoint w a h k : K))) i‖ ≤ 3*U*B := by
  rw [matrix_grid]
  calc
    _ ≤ ∑ j : Fin 3, ‖(a h j : K)*(A *ᵥ (fun k => (w h j k : K))) i‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, U*B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (ha j) (hw j) (norm_nonneg _) hU
    _ = _ := by simp; ring

theorem real_multiplier {m : ℕ} (a : Fin m → Fin 3 → ℕ) (eta : ℝ) (heta : 0 < eta)
    (ha : ∀ h j, a h j ≤ Nat.floor eta⁻¹+1) (h : Fin m) (j : Fin 3) :
    ‖(a h j : ℝ)‖ ≤ eta⁻¹+1 := by
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hh : (a h j : ℝ) ≤ (Nat.floor eta⁻¹ : ℝ)+1 := by exact_mod_cast ha h j
  exact hh.trans (add_le_add_right (Nat.floor_le (inv_nonneg.mpr heta.le)) 1)

theorem padic_multiplier (p : ℕ) [Fact p.Prime] (a : ℕ) : ‖(a : ℚ_[p])‖ ≤ 1 := by
  have hh : (padicNorm p (a : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast padicNorm.of_int (p := p) (a : ℤ)
  simpa only [← Auxiliary6.SourceExpansion.finite_norm p,map_natCast] using hh

theorem grid_form_rpow {K : Type*} [NormedField K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K) (w : Fin m → Fin 3 → Fin 4 → ℤ)
    (a : Fin m → Fin 3 → ℕ) (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 4 → ℝ) (eta U : ℝ) (hU : 0 ≤ U)
    (ha : ∀ h j, ‖(a h j : K)‖ ≤ U) (hg : ∀ h, 3*U ≤ (Q h)^eta)
    (hw : ∀ h j i, ‖(A *ᵥ (fun k => (w h j k : K))) i‖ ≤ (Q h)^(c i)) :
    ∀ h i, ‖(A *ᵥ (fun k => (gridPoint w a h k : K))) i‖ ≤ (Q h)^(c i+eta) := by
  intro h i
  calc
    _ ≤ 3*U*(Q h)^(c i) := grid_form_norm A w a h i U _ hU (ha h) (fun j => hw h j i)
    _ ≤ (Q h)^eta*(Q h)^(c i) := mul_le_mul_of_nonneg_right (hg h) (Real.rpow_pos_of_pos (hQ h) _).le
    _ = _ := by rw [← Real.rpow_add (hQ h)]; congr 1; ring

theorem log_total_bounds {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (eta A : ℝ) (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (J b : Vars4 m →₀ ℕ)
    (hdegree : ∀ h, (∑ i : Fin 4, b (h,i)) = r h - ∑ i : Fin 4, J (h,i))
    (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m) :
    A*m*(1-2*eta) ≤ ∑ i : Fin 4, logWeight Q b i ∧
      (∑ i : Fin 4, logWeight Q b i) ≤ (1+eta)*A*m := by
  have hdeg (h : Fin m) : (∑ i : Fin 4, b (h,i)) ≤ r h := by rw [hdegree h]; exact Nat.sub_le _ _
  have hweights : (m : ℝ) ≤ (∑ i : Fin 4, coordinateWeight r i b) + rothSourceDerivativeWeight r J := by
    unfold coordinateWeight rothSourceDerivativeWeight
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _h : Fin m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro h hh
        rw [← Finset.sum_div, ← add_div]
        apply (le_div_iff₀ (by exact_mod_cast hr h)).mpr
        simp only [one_mul]
        have hn : r h ≤ (∑ i : Fin 4, b (h,i)) + ∑ i : Fin 4, J (h,i) := by
          rw [hdegree h]
          omega
        exact_mod_cast hn
  have hlo : A*(∑ i : Fin 4, coordinateWeight r i b) ≤ ∑ i : Fin 4, logWeight Q b i := by
    unfold coordinateWeight logWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have ht := mul_le_mul_of_nonneg_left (hlog h).1
      (show 0 ≤ (b (h,i) : ℝ)/(r h : ℝ) from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hn : (r h : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr h)
    convert ht using 1 <;> field_simp [hn] <;> ring
  constructor
  · have hs := mul_le_mul_of_nonneg_left (show (m : ℝ)-2*eta*m ≤ ∑ i : Fin 4, coordinateWeight r i b by linarith) hA
    nlinarith
  · unfold logWeight
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ h : Fin m, (1+eta)*A := by
        apply Finset.sum_le_sum
        intro h hh
        rw [← Finset.sum_mul]
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg h) (Real.log_pos (hQ h)).le).trans (hlog h).2
      _ = _ := by simp; ring

theorem weighted_log_upper {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (eta A : ℝ) (heta : 0 ≤ eta) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (b : Vars4 m →₀ ℕ) (hdegree : ∀ h, (∑ i : Fin 4, b (h,i)) ≤ r h)
    (hbalance : ∀ i, |coordinateWeight r i b - (m : ℝ)/4| ≤ 18*eta*m)
    (c : Fin 4 → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    (∑ i : Fin 4, c i * logWeight Q b i) ≤ A*m/4*(∑ i, c i)+114*A*m*eta := by
  have ht := log_weight_transport r hr Q eta A heta hA hlog b hdegree hbalance
  have hterm (i : Fin 4) : c i*logWeight Q b i ≤ c i*(A*m/4)+19*A*m*eta := by
    have hh : |c i*(logWeight Q b i-A*m/4)| ≤ 19*A*m*eta := by
      rw [abs_mul]
      exact (mul_le_mul (hc i) (ht i) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have hh' := (le_abs_self _).trans hh
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hterm i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  nlinarith [mul_nonneg (mul_nonneg hA (Nat.cast_nonneg m)) heta]

theorem source_exponents {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (eta delta A : ℝ)
    (heta : 0 < eta) (hd : 1728*eta < delta) (hd1 : delta < 1) (hA : 0 ≤ A)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (J b : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m)
    (hdegree : ∀ h, (∑ i : Fin 4, b (h,i)) = r h - ∑ i : Fin 4, J (h,i))
    (hbalance : ∀ i, |coordinateWeight r i b - (m : ℝ)/4| ≤ 18*eta*m)
    (c : Fin 4 → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    (∑ i : Fin 4, (c i-delta+eta)*logWeight Q b i) ≤ A*m*((∑ i,c i)/4-1116*eta) ∧
    (∑ i : Fin 4, (c i+eta)*logWeight Q b i) ≤ A*m*((∑ i,c i)/4+504*eta) := by
  have hdeg (h : Fin m) : (∑ i : Fin 4, b (h,i)) ≤ r h := by rw [hdegree h]; exact Nat.sub_le _ _
  have hw := weighted_log_upper r hr Q eta A heta.le hA hlog b hdeg hbalance c hc
  have ht := log_total_bounds r hr Q hQ eta A heta.le hA hlog J b hdegree hJ
  have heta1 : eta < 1 := by linarith
  have hdeta : 0 ≤ delta-eta := by linarith
  have he : delta*eta < eta := by nlinarith
  have hbudget : 1230*eta ≤ (delta-eta)*(1-2*eta) := by nlinarith [sq_nonneg eta]
  have hs := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ A*(m : ℝ) by positivity)
  have hn := mul_le_mul_of_nonneg_left ht.1 hdeta
  have hp := mul_le_mul_of_nonneg_left ht.2 heta.le
  have he2 : eta*(1+eta) ≤ 2*eta := by nlinarith
  have hs2 := mul_le_mul_of_nonneg_left he2 (show 0 ≤ A*(m : ℝ) by positivity)
  constructor
  · simp only [sub_add,sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith
  · simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
    nlinarith

theorem local_upper {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) K) (hB : B.det ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (eta delta A E : ℝ) (heta : 0 < eta) (hd : 1728*eta < delta) (hd1 : delta < 1)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (hclaims : Claims r eta B P)
    (hcfs : ∀ J b, ‖(expansion B J P).coeff b‖ ≤ E^(∑ h, r h))
    (c : Fin 4 → ℝ) (hc : ∀ i, |c i| ≤ 1) (arch : Bool)
    (v : Fin m → Fin 4 → ℤ)
    (hv : ∀ h i, ‖(B *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i-(if arch then delta else 0)+eta))
    (J : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m) :
    ‖(integerValue J P v : K)‖ ≤ (16*E)^(∑ h, r h)*
      Real.exp (A*m*((∑ i,c i)/4+(if arch then -1116*eta else 504*eta))) := by
  apply evaluation_upper B hB r J P hP v E _ hE Q (fun h => lt_trans zero_lt_one (hQ h))
    (fun i => c i-(if arch then delta else 0)+eta) hv (hcfs J)
  intro b hb
  have hn := MvPolynomial.mem_support_iff.mp hb
  have he := source_exponents r hr Q hQ eta delta A heta hd hd1 hA hlog J b hJ
    (hclaims.2.2.1 J b hn) (hclaims.2.2.2.2 J b hJ hn) c hc
  cases arch
  · simpa using he.2
  · simpa using he.1

theorem strict_product_bound {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (h0 : Fin m) (eta E : ℝ)
    (heta : 0 < eta) (heta1 : eta < 1) (hE : 1 ≤ E)
    (hg : ∀ h, 16*E < (Q h)^eta)
    (hlog : ∀ h, (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*((r h0 : ℝ)*Real.log (Q h0))) :
    (16*E)^(3*(∑ h,r h))*Real.exp (-108*((r h0 : ℝ)*Real.log (Q h0))*m*eta) < 1 := by
  let A := (r h0 : ℝ)*Real.log (Q h0)
  let R := ∑ h,r h
  have hA : 0 < A := mul_pos (by exact_mod_cast hr h0) (Real.log_pos (hQ h0))
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by have := h0.isLt; omega)
  have hbase : 0 < 16*E := by positivity
  have ht (h : Fin m) : (r h : ℝ)*Real.log (16*E) < (r h : ℝ)*(eta*Real.log (Q h)) := by
    apply mul_lt_mul_of_pos_left _ (by exact_mod_cast hr h)
    have hh := Real.log_lt_log hbase (hg h)
    simpa only [Real.rpow_eq_pow,Real.log_rpow (lt_trans zero_lt_one (hQ h))] using hh
  have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (⟨h0,Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin m)).Nonempty) (fun h _ => ht h)
  have hs' : (R : ℝ)*Real.log (16*E) < eta*(∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) := by
    simpa only [← Finset.sum_mul,mul_left_comm,← Finset.mul_sum,← Nat.cast_sum,R] using hs
  have hb : (∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) ≤ (1+eta)*A*m := by
    have hh := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin m))) => hlog h)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,A,
      mul_assoc,mul_comm,mul_left_comm] using hh
  have hs3 := mul_lt_mul_of_pos_left hs' (by norm_num : (0 : ℝ) < 3)
  have hb3 := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3*eta by positivity)
  have hgap := mul_lt_mul_of_pos_right (show 3*(1+eta) < (108 : ℝ) by linarith)
    (show 0 < A*m*eta by positivity)
  have hexp : (3*(R : ℝ))*Real.log (16*E)-108*A*m*eta < 0 := by nlinarith
  calc
    _ = Real.exp ((3*(R : ℝ))*Real.log (16*E)-108*A*m*eta) := by
      rw [Real.exp_sub,show 3*(R : ℝ) = (3*R : ℕ) by push_cast; rfl,
        Real.exp_nat_mul,Real.exp_log hbase]
      change (16*E)^(3*R)*Real.exp (-108*A*m*eta) = (16*E)^(3*R)/Real.exp (108*A*m*eta)
      rw [div_eq_mul_inv,← Real.exp_neg]
      congr 2
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hexp

theorem real_grid_bounds {m : ℕ} (B : Matrix (Fin 4) (Fin 4) ℝ)
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (a : Fin m → Fin 3 → ℕ)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h) (c : Fin 4 → ℝ) (eta delta : ℝ)
    (heta : 0 < eta) (ha : ∀ h j, a h j ≤ Nat.floor eta⁻¹+1)
    (hg : ∀ h, 4*(eta⁻¹+1) < (Q h)^eta)
    (hw : ∀ h j i, ‖(B *ᵥ (fun k => (w h j k : ℝ))) i‖ ≤ (Q h)^(c i-delta)) :
    ∀ h i, ‖(B *ᵥ (fun k => (gridPoint w a h k : ℝ))) i‖ ≤ (Q h)^(c i-delta+eta) := by
  apply grid_form_rpow B w a Q hQ (fun i => c i-delta) eta (eta⁻¹+1)
  · positivity
  · exact real_multiplier a eta heta ha
  · intro h
    exact (by have hh : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le; linarith : 3*(eta⁻¹+1) ≤ 4*(eta⁻¹+1)).trans (hg h).le
  · exact hw

theorem padic_grid_bounds (p : ℕ) [Fact p.Prime] {m : ℕ} (B : Matrix (Fin 4) (Fin 4) ℚ_[p])
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (a : Fin m → Fin 3 → ℕ)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h) (c : Fin 4 → ℝ) (eta : ℝ) (heta : 0 < eta)
    (hg : ∀ h, 4*(eta⁻¹+1) < (Q h)^eta)
    (hw : ∀ h j i, ‖(B *ᵥ (fun k => (w h j k : ℚ_[p]))) i‖ ≤ (Q h)^(c i)) :
    ∀ h i, ‖(B *ᵥ (fun k => (gridPoint w a h k : ℚ_[p]))) i‖ ≤ (Q h)^(c i+eta) := by
  apply grid_form_rpow B w a Q hQ c eta 1 (by norm_num)
  · intro h j; exact padic_multiplier p (a h j)
  · intro h
    have hh : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
    have ht := hg h
    linarith
  · exact hw

def sourceBound {m : ℕ} (r : Fin m → ℕ) (E eta : ℝ) (Q : Fin m → ℝ)
    (h0 : Fin m) (c : Fin 3 → Fin 4 → ℝ) (tau : Fin 3) : ℝ :=
  (16*E)^(∑ h,r h)*Real.exp (((r h0 : ℝ)*Real.log (Q h0))*m*
    ((∑ i,c tau i)/4+(if tau=0 then -1116*eta else 504*eta)))

end CompoundFeasibility.Auxiliary4Literal176.SourceGrid4

end

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4
open SourceMultiblock4 SourceExpansion4 SourceSupport4 SourceBalance4 SourceEvaluation4 SourceGrid4

theorem evaluation_identity_of_reconstruction {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K)
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ) (v : Fin m → Fin 4 → ℤ)
    (hrec : substitution A (expansion A J P) = derivative4 J (P.map (Int.castRingHom K))) :
    (integerValue J P v : K) = ∑ b ∈ (expansion A J P).support,
      (expansion A J P).coeff b * ∏ u : Vars4 m,
        ((A *ᵥ (fun i => (v u.1 i : K))) u.2) ^ b u := by
  rw [integerValue_cast, ← hrec]
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
theorem evaluation_upper_of_reconstruction {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) K)
    (r : Fin m → ℕ) (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ)
    (hP : homogeneous4 r P)
    (hrec : substitution A (expansion A J P) = derivative4 J (P.map (Int.castRingHom K))) (v : Fin m → Fin 4 → ℤ)
    (E T : ℝ) (hE : 0 ≤ E) (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (c : Fin 4 → ℝ)
    (hv : ∀ h i, ‖(A *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i))
    (hc : ∀ b, ‖(expansion A J P).coeff b‖ ≤ E^(∑ h, r h))
    (ht : ∀ b ∈ (expansion A J P).support, (∑ i, c i * logWeight Q b i) ≤ T) :
    ‖(integerValue J P v : K)‖ ≤ (16*E)^(∑ h, r h)*Real.exp T := by
  rw [evaluation_identity_of_reconstruction A J P v hrec]
  calc
    _ ≤ ∑ b ∈ (expansion A J P).support, ‖(expansion A J P).coeff b *
        ∏ u : Vars4 m, ((A *ᵥ (fun i => (v u.1 i : K))) u.2)^b u‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ (expansion A J P).support, E^(∑ h, r h)*Real.exp T := by
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul]
      exact (mul_le_mul (hc b) (monomial_bound A v Q hQ c hv b)
        (norm_nonneg _) (pow_nonneg hE _)).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (ht b hb)) (pow_nonneg hE _))
    _ = ((expansion A J P).support.card : ℝ)*(E^(∑ h, r h)*Real.exp T) := by simp
    _ ≤ (16 : ℝ)^(∑ h, r h)*(E^(∑ h, r h)*Real.exp T) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast expansion_support_card r A J P hP
    _ = _ := by rw [← mul_assoc, ← mul_pow]
theorem local_upper_from_claims {K : Type*} [NormedField K] [CharZero K] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) K)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (eta delta A E : ℝ) (heta : 0 < eta) (hd : 1728*eta < delta) (hd1 : delta < 1)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hlog : ∀ h, A ≤ (r h : ℝ)*Real.log (Q h) ∧ (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*A)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (hclaims : Claims r eta B P)
    (hcfs : ∀ J b, ‖(expansion B J P).coeff b‖ ≤ E^(∑ h, r h))
    (c : Fin 4 → ℝ) (hc : ∀ i, |c i| ≤ 1) (arch : Bool)
    (v : Fin m → Fin 4 → ℤ)
    (hv : ∀ h i, ‖(B *ᵥ (fun j => (v h j : K))) i‖ ≤ (Q h)^(c i-(if arch then delta else 0)+eta))
    (J : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J ≤ 2*eta*m) :
    ‖(integerValue J P v : K)‖ ≤ (16*E)^(∑ h, r h)*
      Real.exp (A*m*((∑ i,c i)/4+(if arch then -1116*eta else 504*eta))) := by
  apply evaluation_upper_of_reconstruction B r J P hP (hclaims.1 J) v E _ hE Q (fun h => lt_trans zero_lt_one (hQ h))
    (fun i => c i-(if arch then delta else 0)+eta) hv (hcfs J)
  intro b hb
  have hn := MvPolynomial.mem_support_iff.mp hb
  have he := source_exponents r hr Q hQ eta delta A heta hd hd1 hA hlog J b hJ
    (hclaims.2.2.1 J b hn) (hclaims.2.2.2.2 J b hJ hn) c hc
  cases arch
  · simpa using he.2
  · simpa using he.1

theorem three_place_upper {m : ℕ} (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (r : Fin m → ℕ) (hr : ∀ h,0<r h) (Q : Fin m → ℝ) (hQ : ∀ h,1<Q h) (h0 : Fin m)
    (eta delta E : ℝ) (heta : 0<eta) (hd : 1728*eta<delta) (hd1 : delta<1) (hE : 1≤E)
    (hg : ∀ h,4*(eta⁻¹+1)<(Q h)^eta)
    (hlog : ∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0)))
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (hclaims : Claims r eta (L) P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 2 A2) P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 3 A3) P)
    (hcfs : ∀ J b, ‖(expansion (L) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖≤E^(∑ h,r h))
    (c : Fin 3 → Fin 4 → ℝ) (hc : ∀ tau i,|c tau i|≤1)
    (w : Fin m → Fin 3 → Fin 4 → ℤ)
    (hw0 : ∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta))
    (hw2 : ∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i))
    (hw3 : ∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i))
    (a : Fin m → Fin 3 → ℕ) (ha : ∀ h j,a h j≤Nat.floor eta⁻¹+1)
    (J : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J≤2*eta*m) :
    ‖(integerValue J P (gridPoint w a) : ℝ)‖≤sourceBound r E eta Q h0 c 0 ∧
    ‖(integerValue J P (gridPoint w a) : ℚ_[2])‖≤sourceBound r E eta Q h0 c 1 ∧
    ‖(integerValue J P (gridPoint w a) : ℚ_[3])‖≤sourceBound r E eta Q h0 c 2 := by
  have hA : 0≤(r h0 : ℝ)*Real.log (Q h0) := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (hQ h0)).le
  have hEp : 0≤E := by linarith
  have hQp : ∀ h,0<Q h := fun h => lt_trans zero_lt_one (hQ h)
  have hv0 := real_grid_bounds (L) w a Q hQp (c 0) eta delta heta ha hg hw0
  have hv2 := padic_grid_bounds 2 (SourceForms4Literal176.finiteMatrix4 2 A2) w a Q hQp (c 1) eta heta hg hw2
  have hv3 := padic_grid_bounds 3 (SourceForms4Literal176.finiteMatrix4 3 A3) w a Q hQp (c 2) eta heta hg hw3
  constructor
  · simpa only [sourceBound,if_pos rfl,Bool.true_eq] using
      (local_upper_from_claims (L) r hr Q hQ eta delta
        ((r h0 : ℝ)*Real.log (Q h0)) E heta hd hd1 hA hEp hlog P hP hclaims.1
        (fun J b => (hcfs J b).1) (c 0) (hc 0) true (gridPoint w a) hv0 J hJ)
  · constructor
    · simpa [sourceBound] using
        (local_upper_from_claims (SourceForms4Literal176.finiteMatrix4 2 A2) r hr Q hQ eta delta
          ((r h0 : ℝ)*Real.log (Q h0)) E heta hd hd1 hA hEp hlog P hP hclaims.2.1
          (fun J b => (hcfs J b).2.1) (c 1) (hc 1) false (gridPoint w a) (by simpa using hv2) J hJ)
    · simpa [sourceBound] using
        (local_upper_from_claims (SourceForms4Literal176.finiteMatrix4 3 A3) r hr Q hQ eta delta
          ((r h0 : ℝ)*Real.log (Q h0)) E heta hd hd1 hA hEp hlog P hP hclaims.2.2
          (fun J b => (hcfs J b).2.2) (c 2) (hc 2) false (gridPoint w a) (by simpa using hv3) J hJ)


theorem sourceBound_product {m : ℕ} (r : Fin m → ℕ) (E eta : ℝ) (Q : Fin m → ℝ)
    (h0 : Fin m) (c : Fin 3 → Fin 4 → ℝ) (hc : (∑ tau, ∑ i, c tau i) = 0) :
    sourceBound r E eta Q h0 c 0 * sourceBound r E eta Q h0 c 1 *
      sourceBound r E eta Q h0 c 2 =
      (16*E)^(3*(∑ h,r h))*Real.exp (-108*((r h0 : ℝ)*Real.log (Q h0))*m*eta) := by
  have hs : (∑ i,c 0 i)+(∑ i,c 1 i)+(∑ i,c 2 i)=0 := by
    simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,
      Fin.val_one,Fin.val_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,add_zero,add_assoc] using hc
  let F : ℝ := (16*E)^(∑ h,r h)
  let T : Fin 3 → ℝ := fun tau => ((r h0 : ℝ)*Real.log (Q h0))*m*
    ((∑ i,c tau i)/4+(if tau=0 then -1116*eta else 504*eta))
  have ht : T 0+T 1+T 2 = -108*((r h0 : ℝ)*Real.log (Q h0))*m*eta := by
    dsimp [T]
    linear_combination ((r h0 : ℝ)*Real.log (Q h0)*(m : ℝ)/4)*hs
  have hf : F*F*F = (16*E)^(3*(∑ h,r h)) := by
    dsimp [F]
    rw [← pow_add,← pow_add]
    congr 1
    omega
  change (F*Real.exp (T 0))*(F*Real.exp (T 1))*(F*Real.exp (T 2)) = _
  calc
    _ = (F*F*F)*Real.exp (T 0+T 1+T 2) := by rw [Real.exp_add,Real.exp_add]; ring
    _ = _ := by rw [hf,ht]

theorem three_place_product_lt_one {m : ℕ} (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (r : Fin m → ℕ) (hr : ∀ h,0<r h) (Q : Fin m → ℝ) (hQ : ∀ h,1<Q h) (h0 : Fin m)
    (eta delta E : ℝ) (heta : 0<eta) (hd : 1728*eta<delta) (hd1 : delta<1) (hE : 1≤E)
    (hg64 : ∀ h,16*E<(Q h)^eta)
    (hg : ∀ h,4*(eta⁻¹+1)<(Q h)^eta)
    (hlog : ∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0)))
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (hclaims : Claims r eta (L) P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 2 A2) P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 3 A3) P)
    (hcfs : ∀ J b, ‖(expansion (L) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖≤E^(∑ h,r h))
    (c : Fin 3 → Fin 4 → ℝ) (hc : ∀ tau i,|c tau i|≤1)
    (hbalance : (∑ tau,∑ i,c tau i)=0)
    (w : Fin m → Fin 3 → Fin 4 → ℤ)
    (hw0 : ∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta))
    (hw2 : ∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i))
    (hw3 : ∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i))
    (a : Fin m → Fin 3 → ℕ) (ha : ∀ h j,a h j≤Nat.floor eta⁻¹+1)
    (J : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J≤2*eta*m) :
    ‖(integerValue J P (gridPoint w a) : ℝ)‖ *
      ‖(integerValue J P (gridPoint w a) : ℚ_[2])‖ *
      ‖(integerValue J P (gridPoint w a) : ℚ_[3])‖ < 1 := by
  have hu := three_place_upper A2 A3 L h2 h3 hL r hr Q hQ h0 eta delta E heta hd hd1 hE hg hlog P hP hclaims hcfs c hc w hw0 hw2 hw3 a ha J hJ
  have hEp : 0≤E := by linarith
  have hn (tau : Fin 3) : 0≤sourceBound r E eta Q h0 c tau := by
    unfold sourceBound
    positivity
  have hu01 := mul_le_mul hu.1 hu.2.1 (norm_nonneg _) (hn 0)
  have hu012 := mul_le_mul hu01 hu.2.2 (norm_nonneg _) (mul_nonneg (hn 0) (hn 1))
  rw [sourceBound_product r E eta Q h0 c hbalance] at hu012
  exact hu012.trans_lt (strict_product_bound r hr Q hQ h0 eta E heta (by linarith)
    hE hg64 (fun h => (hlog h).2))
theorem grid_derivative_vanishes {m : ℕ} (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (r : Fin m → ℕ) (hr : ∀ h,0<r h) (Q : Fin m → ℝ) (hQ : ∀ h,1<Q h) (h0 : Fin m)
    (eta delta E : ℝ) (heta : 0<eta) (hd : 1728*eta<delta) (hd1 : delta<1) (hE : 1≤E)
    (hg64 : ∀ h,16*E<(Q h)^eta)
    (hg : ∀ h,4*(eta⁻¹+1)<(Q h)^eta)
    (hlog : ∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0)))
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (hclaims : Claims r eta (L) P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 2 A2) P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 3 A3) P)
    (hcfs : ∀ J b, ‖(expansion (L) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖≤E^(∑ h,r h) ∧
      ‖(expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖≤E^(∑ h,r h))
    (c : Fin 3 → Fin 4 → ℝ) (hc : ∀ tau i,|c tau i|≤1)
    (hbalance : (∑ tau,∑ i,c tau i)=0)
    (w : Fin m → Fin 3 → Fin 4 → ℤ)
    (hw0 : ∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta))
    (hw2 : ∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i))
    (hw3 : ∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i))
    (a : Fin m → Fin 3 → ℕ) (ha : ∀ h j,a h j≤Nat.floor eta⁻¹+1)
    (J : Vars4 m →₀ ℕ) (hJ : rothSourceDerivativeWeight r J≤2*eta*m) :
    integerValue J P (gridPoint w a) = 0 := by
  by_contra hz
  have hl := integerValue_lower J P (gridPoint w a) hz
  have hu := three_place_product_lt_one A2 A3 L h2 h3 hL r hr Q hQ h0 eta delta E heta hd hd1 hE hg64 hg hlog P hP hclaims hcfs c hc hbalance w hw0 hw2 hw3 a ha J hJ
  linarith


theorem source_auxiliary4_grid_vanishing (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms4Literal176.forms4 A2 A3 L tau i j ∈ K,
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
      (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex4 (fun i j => (⟨SourceForms4Literal176.forms4 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex4 (SourceForms4Literal176.forms4 A2 A3 L tau) r eta P) ∧
      matrixIndex4 (SourceForms4Literal176.finiteMatrix4 2 A2) r eta P ∧
      matrixIndex4 (SourceForms4Literal176.finiteMatrix4 3 A3) r eta P ∧
      (Claims r eta L P ∧ Claims r eta (SourceForms4Literal176.finiteMatrix4 2 A2) P ∧
        Claims r eta (SourceForms4Literal176.finiteMatrix4 3 A3) P) ∧
      (∀ J b : Vars4 m →₀ ℕ,
        ‖(expansion L J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
        ‖(expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) ∧
        (∀ (Q : Fin m → ℝ), (∀ h,1<Q h) → ∀ h0 : Fin m,
          ∀ delta : ℝ, 1728*eta<delta → delta<1 →
          (∀ h,16*E<(Q h)^eta) → (∀ h,4*(eta⁻¹+1)<(Q h)^eta) →
          (∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0))) →
          ∀ c : Fin 3 → Fin 4 → ℝ, (∀ tau i,|c tau i|≤1) → (∑ tau,∑ i,c tau i)=0 →
          ∀ w : Fin m → Fin 3 → Fin 4 → ℤ,
          (∀ h j i,‖(L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta)) →
          (∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i)) →
          (∀ h j i,‖(SourceForms4Literal176.finiteMatrix4 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i)) →
          ∀ a : Fin m → Fin 3 → ℕ, (∀ h j,1≤a h j ∧ a h j≤Nat.floor eta⁻¹+1) →
          ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J<2*eta*m →
          integerValue J P (gridPoint w a)=0) := by
  obtain ⟨K,hK,hmem,D,E,hD,hE,hconstruction⟩ := source_auxiliary4_balanced A2 A3 L h2 h3 hL ha
  refine ⟨K,hK,hmem,D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,?_⟩
  intro Q hQ h0 delta hd hd1 hg16 hg hlog c hc hbalance w hw0 hw2 hw3 a haGrid J hJ
  exact grid_derivative_vanishes A2 A3 L h2 h3 hL r hr Q hQ h0 eta delta E heta hd hd1 hE
    hg16 hg hlog P hhom hclaims hcfs c hc hbalance w hw0 hw2 hw3 a
    (fun h j => (haGrid h j).2) J hJ.le

end CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceWeights4Literal176
open OriginalDeformation4 OriginalDeformedSource4 OriginalSelectedSystem4

theorem select_unbounded_weights (U : Set ℝ) (hU : ¬ BddAbove U)
    (alpha : ℝ → Fin 4 → ℝ) (hb : ∀ q ∈ U, ∀ i, |alpha q i| ≤ 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ V : Set ℝ, V ⊆ U ∧ ¬ BddAbove V ∧ ∃ q0 ∈ V,
      ∀ q ∈ V, ∀ i, |alpha q i-alpha q0 i| < epsilon := by
  let B : Set (Fin 4 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨S,hSB,hS,hcover⟩ := hB.finite_cover_balls (show 0 < epsilon/2 by positivity)
  let F : (Fin 4 → ℝ) → Set ℝ := fun x => {q | q ∈ U ∧ alpha q ∈ Metric.ball x (epsilon/2)}
  have hUF : U ⊆ ⋃ x ∈ S, F x := by
    intro q hq
    have ha : alpha q ∈ B := by
      intro i hi
      exact abs_le.mp (hb q hq i)
    obtain ⟨x,hx,hqx⟩ := Set.mem_iUnion₂.mp (hcover ha)
    exact Set.mem_iUnion₂.mpr ⟨x,hx,hq,hqx⟩
  have hex : ∃ x ∈ S, ¬ BddAbove (F x) := by
    by_contra hn
    push_neg at hn
    exact hU (((hS.bddAbove_biUnion).mpr hn).mono hUF)
  obtain ⟨x,hx,hF⟩ := hex
  obtain ⟨q0,h0,_⟩ := not_bddAbove_iff.mp hF 0
  refine ⟨F x,fun q hq => hq.1,hF,q0,h0,?_⟩
  intro q hq i
  have hqi := (dist_pi_lt_iff (show 0 < epsilon/2 by positivity)).mp hq.2 i
  have h0i := (dist_pi_lt_iff (show 0 < epsilon/2 by positivity)).mp h0.2 i
  rw [Real.dist_eq] at hqi h0i
  calc
    |alpha q i-alpha q0 i| ≤ |alpha q i-x i|+|x i-alpha q0 i| := abs_sub_le _ _ _
    _ < epsilon/2+epsilon/2 := add_lt_add hqi (by simpa only [abs_sub_comm] using h0i)
    _ = epsilon := by ring


def logWeight (Q a : ℝ) : ℝ := Real.log a / Real.log Q

theorem logWeight_bounds (Q a : ℝ) (hQ : 1 < Q) (ha : 0 < a)
    (hau : a < Q) (hai : a⁻¹ < Q) : -1 < logWeight Q a ∧ logWeight Q a < 1 := by
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have h1 := Real.log_lt_log ha hau
  have h2 := Real.log_lt_log (inv_pos.mpr ha) hai
  rw [Real.log_inv] at h2
  constructor
  · apply (lt_div_iff₀ hlog).mpr
    linarith
  · apply (div_lt_iff₀ hlog).mpr
    linarith

theorem logWeight_power (Q a : ℝ) (hQ : 1 < Q) (ha : 0 < a) : Q^(logWeight Q a)=a := by
  rw [logWeight,Real.rpow_def_of_pos (lt_trans zero_lt_one hQ)]
  have he : Real.log Q*(Real.log a/Real.log Q)=Real.log a := by
    field_simp [(Real.log_pos hQ).ne']
  rw [he,Real.exp_log ha]

theorem logWeight_balance (Q : ℝ) (hQ : 1 < Q) (a b2 b3 : Fin 4 → ℝ)
    (ha : ∀ i,0<a i) (hp : (∏ i,a i*Q^(b2 i)*Q^(b3 i))=1) :
    (∑ i,logWeight Q (a i))+(∑ i,b2 i)+(∑ i,b3 i)=0 := by
  have hq := lt_trans zero_lt_one hQ
  have hpow : Q^(∑ i : Fin 4,(logWeight Q (a i)+b2 i+b3 i))=1 := by
    rw [Real.rpow_sum_of_pos hq]
    calc
      _ = ∏ i : Fin 4,a i*Q^(b2 i)*Q^(b3 i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Real.rpow_add hq,Real.rpow_add hq,logWeight_power Q (a i) hQ (ha i)]
      _ = 1 := hp
  have hs := (Real.rpow_right_inj hq (ne_of_gt hQ)).mp (hpow.trans (Real.rpow_zero Q).symm)
  simpa only [Finset.sum_add_distrib] using hs

def fixedWeights (a b2 b3 : Fin 4 → ℝ) (tau : Fin 3) (i : Fin 4) : ℝ :=
  if tau=0 then a i else if tau=1 then b2 i else b3 i

theorem fixedWeights_bounds_balance (a b2 b3 : Fin 4 → ℝ)
    (ha : ∀ i,-1<a i ∧ a i<1) (h2 : ∀ i,-1≤b2 i ∧ b2 i≤0)
    (h3 : ∀ i,-1≤b3 i ∧ b3 i≤0)
    (hb : (∑ i,a i)+(∑ i,b2 i)+(∑ i,b3 i)=0) :
    (∀ tau i,|fixedWeights a b2 b3 tau i|≤1) ∧ (∑ tau,∑ i,fixedWeights a b2 b3 tau i)=0 := by
  constructor
  · intro tau i
    fin_cases tau <;> simp only [fixedWeights,Fin.reduceFinMk,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
    · exact abs_le.mpr ⟨(ha i).1.le,(ha i).2.le⟩
    · exact abs_le.mpr ⟨(h2 i).1,(h2 i).2.trans (by norm_num)⟩
    · exact abs_le.mpr ⟨(h3 i).1,(h3 i).2.trans (by norm_num)⟩
  · simpa [Fin.sum_univ_three,fixedWeights,add_assoc] using hb

theorem finite_form_bounds (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (q : ℝ) (hq : 1 < q) (c2 c3 : Fin 4 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (z : originalSourceGroup4 A2 A3 q c2 c3) :
    (∀ i, ‖(SourceForms4Literal176.finiteMatrix4 2 A2 *ᵥ (fun j => ((z : Fin 4 → ℤ) j : ℚ_[2]))) i‖ ≤
      (q^(5 : ℕ))^(c2 i/5)) ∧
    (∀ i, ‖(SourceForms4Literal176.finiteMatrix4 3 A3 *ᵥ (fun j => ((z : Fin 4 → ℤ) j : ℚ_[3]))) i‖ ≤
      (q^(5 : ℕ))^(c3 i/5)) := by
  have hm := z.property
  change _ ∈ sourceLattice4 A2 A3 _ _ at hm
  constructor
  · intro i
    rw [rescaled_power4 q _ (zero_lt_one.trans hq),SourceForms4Literal176.finiteMatrix4,OriginalAuxiliaryDual4.finite_form_norm4]
    apply (padic_rpow_ceil42 2 q (c2 i) hq (hc2 i) _).mpr
    simpa only [zpow_neg,zpow_natCast] using (lattice4_spec 2 A2 _ _).mp hm.1 i
  · intro i
    rw [rescaled_power4 q _ (zero_lt_one.trans hq),SourceForms4Literal176.finiteMatrix4,OriginalAuxiliaryDual4.finite_form_norm4]
    apply (padic_rpow_ceil42 3 q (c3 i) hq (hc3 i) _).mpr
    simpa only [zpow_neg,zpow_natCast] using (lattice4_spec 3 A3 _ _).mp hm.2 i


variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

def frameWidths (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
    (hQU q.val q.property) c0 c2 c3 delta (u q)) (q : U) : Fin 4 → ℝ :=
  deformedWidths4 q.val c0
    (gapDeformation4 (sourceMinima4 A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3)) (F q).sigma

theorem fixed_weights_same_frame4
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ V : Set ℝ, V ⊆ U ∧ ¬ BddAbove V ∧
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧
    ∃ c : Fin 3 → Fin 4 → ℝ, (∀ tau i, |c tau i| ≤ 1) ∧
      (∑ tau, ∑ i, c tau i) = 0 ∧
      (∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5) ∧
      ∀ (q : U), q.val ∈ V →
        (∀ (j : Fin 3) i, ‖(L *ᵥ integerReal ((F q).w j.castSucc : Fin 4 → ℤ)) i‖ ≤
          (q.val^(5 : ℕ))^(c 0 i-d)) ∧
        (∀ (j : Fin 3) i, ‖(SourceForms4Literal176.finiteMatrix4 2 A2 *ᵥ
          (fun k => (((F q).w j.castSucc : Fin 4 → ℤ) k : ℚ_[2]))) i‖ ≤ (q.val^(5 : ℕ))^(c 1 i)) ∧
        (∀ (j : Fin 3) i, ‖(SourceForms4Literal176.finiteMatrix4 3 A3 *ᵥ
          (fun k => (((F q).w j.castSucc : Fin 4 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^(5 : ℕ))^(c 2 i)) := by
  let eps : ℝ := min (delta/96) (1/4)
  have he : 0 < eps := lt_min (by positivity) (by norm_num)
  have he1 : eps < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hslack : eps+eps < delta/24 := by
    have hh : eps ≤ delta/96 := min_le_left _ _
    linarith
  have hqp (q : U) : 1 < q.val^(5 : ℕ) := one_lt_pow₀ (hQU q.val q.property) (by decide)
  have hab (q : U) (i : Fin 4) :
      -1 < logWeight (q.val^(5 : ℕ)) (frameWidths F q i) ∧
      logWeight (q.val^(5 : ℕ)) (frameWidths F q i) < 1 :=
    logWeight_bounds _ _ (hqp q) ((F q).widths_pos i) ((F q).sizes i).1 ((F q).sizes i).2.1
  let alpha : ℝ → Fin 4 → ℝ := fun q => if h : q ∈ U then
    fun i => logWeight (q^(5 : ℕ)) (frameWidths F ⟨q,h⟩ i) else 0
  have hb : ∀ q ∈ U, ∀ i, |alpha q i| ≤ 1 := by
    intro q hq i
    simp only [alpha,dif_pos hq]
    exact abs_le.mpr ⟨(hab ⟨q,hq⟩ i).1.le,(hab ⟨q,hq⟩ i).2.le⟩
  obtain ⟨V,hVU,hV,q0,hq0,hclose⟩ := select_unbounded_weights U hU alpha hb eps he
  let u0 : U := ⟨q0,hVU hq0⟩
  let a0 : Fin 4 → ℝ := fun i => logWeight (q0^(5 : ℕ)) (frameWidths F u0 i)
  let c := fixedWeights a0 (fun i => c2 i/5) (fun i => c3 i/5)
  have hp : (∏ i, frameWidths F u0 i*(q0^(5 : ℕ))^(c2 i/5)*(q0^(5 : ℕ))^(c3 i/5)) = 1 := by
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    have hpow (i : Fin 4) :
        (q0^(5 : ℕ))^(c2 i/5)*(q0^(5 : ℕ))^(c3 i/5) = q0^(c2 i+c3 i) := by
      rw [rescaled_power4 _ _ (zero_lt_one.trans (hQU q0 (hVU hq0))),
        rescaled_power4 _ _ (zero_lt_one.trans (hQU q0 (hVU hq0))),
        ← Real.rpow_add (zero_lt_one.trans (hQU q0 (hVU hq0)))]
    rw [mul_assoc,← Finset.prod_mul_distrib]
    simp_rw [hpow]
    exact (F u0).balance
  have hcb := fixedWeights_bounds_balance a0 (fun i => c2 i/5) (fun i => c3 i/5)
    (hab u0) (rescaled_finite_weights4 c2 hc2) (rescaled_finite_weights4 c3 hc3)
    (logWeight_balance _ (hqp u0) (frameWidths F u0) _ _ (F u0).widths_pos hp)
  refine ⟨V,hVU,hV,eps,he,he1,c,hcb.1,hcb.2,by intro i; exact ⟨rfl,rfl⟩,?_⟩
  intro q hq
  have happrox (i : Fin 4) :
      |logWeight (q.val^(5 : ℕ)) (frameWidths F q i)-a0 i| < eps := by
    have hh := hclose q.val hq i
    simpa only [alpha,dif_pos q.property,dif_pos (hVU hq0),a0,u0] using hh
  refine ⟨?_,?_,?_⟩
  · intro j i
    have heq : (q.val^(5 : ℕ))^(logWeight (q.val^(5 : ℕ)) (frameWidths F q i)) = frameWidths F q i :=
      logWeight_power _ _ (hqp q) ((F q).widths_pos i)
    have hexp : -delta/24+logWeight (q.val^(5 : ℕ)) (frameWidths F q i) ≤ a0 i-eps := by
      have hh := (abs_lt.mp (happrox i)).2
      linarith
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (q.val^(5 : ℕ))^(-(delta/24))*frameWidths F q i := attaining_first_three4 (F q) j i
      _ = (q.val^(5 : ℕ))^(-delta/24+logWeight (q.val^(5 : ℕ)) (frameWidths F q i)) := by
        rw [Real.rpow_add (zero_lt_one.trans (hqp q)),heq]
        congr 1 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hqp q).le hexp
  · intro j i
    exact (finite_form_bounds A2 A3 q.val (hQU q.val q.property) c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) ((F q).w j.castSucc)).1 i
  · intro j i
    exact (finite_form_bounds A2 A3 q.val (hQU q.val q.property) c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) ((F q).w j.castSucc)).2 i

end CompoundFeasibility.SourceWeights4Literal176

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceBlocks4Literal176
open SourceWeights4Literal176 SourceMultiblock4 Auxiliary4Literal176 Auxiliary4Literal176.SourceBalance4
  Auxiliary4Literal176.SourceVanishing4 Auxiliary4Literal176.SourceGrid4 Auxiliary4Literal176.SourceEvaluation4
open OriginalDeformedSource4

theorem original_blocks4 (V : Set ℝ) (hV : ¬ BddAbove V)
    (eta E rho : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho) (m : ℕ) :
    ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧
      Set.Finite (Set.range t) ∧
      (∀ h, 1 < (t h).val^(5 : ℕ) ∧
        16*E < ((t h).val^(5 : ℕ))^eta ∧
        4*(eta⁻¹+1) < ((t h).val^(5 : ℕ))^eta) ∧
      ∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log ((t h).val^(5 : ℕ)) ≤
          rho*Real.log ((t ⟨h.val+1,hh⟩).val^(5 : ℕ)) := by
  let B := max (Real.log (16*E)/eta) (Real.log (4*(eta⁻¹+1))/eta)
  obtain ⟨q,hq,hmono,hsep⟩ := JSP000334.parameter_sparse_Q V hV (Real.exp B)
    ((1+eta)/rho) m
  let t : Fin m → V := fun h => ⟨q h,(hq h).1⟩
  have hlog (h) : B < Real.log (q h) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) (hq h).2.1
  have hQ (h) : 1 < (q h)^(5 : ℕ) := one_lt_pow₀ (hq h).2.2 (by decide)
  have hlogpow (h) : B < Real.log ((q h)^(5 : ℕ)) := by
    rw [Real.log_pow]
    have hl := Real.log_pos (hq h).2.2
    norm_num only [Nat.cast_ofNat]
    linarith [hlog h]
  refine ⟨t,hmono,Set.finite_range t,?_,?_⟩
  · intro h
    refine ⟨hQ h,?_,?_⟩
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by linarith)
        (lt_of_le_of_lt (le_max_left _ _) (hlogpow h))
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by positivity)
        (lt_of_le_of_lt (le_max_right _ _) (hlogpow h))
  · intro h hh
    have hs0 := hsep h hh
    rw [div_mul_eq_mul_div] at hs0
    have hs := (div_lt_iff₀ hp).mp hs0
    dsimp [t]
    rw [Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

theorem same_selected_frame_grid4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ m : ℕ, 0 < m ∧
      ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau i j, SourceForms4Literal176.forms4 A2 A3 L tau i j ∈ K) ∧
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ rho : ℝ, 0 < rho → ∃ t : Fin m → U,
        StrictMono (fun h => (t h).val) ∧
        ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
        (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
        ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
          (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
          matrixIndex4 L r eta P ∧ matrixIndex4 (SourceForms4Literal176.finiteMatrix4 2 A2) r eta P ∧
          matrixIndex4 (SourceForms4Literal176.finiteMatrix4 3 A3) r eta P ∧
          (∀ J b : Vars4 m →₀ ℕ,
            ‖(Auxiliary4Literal176.SourceExpansion4.expansion L J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4Literal176.SourceExpansion4.expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4Literal176.SourceExpansion4.expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h,r h)) ∧
          ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
          ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
            integerValue J P (gridPoint (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) a) = 0 := by
  obtain ⟨V,hVU,hV,d,hdp,hd1,c,hc,hbal,hfin,hframe⟩ := fixed_weights_same_frame4 F hU hd hc2 hc3
  obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ := source_auxiliary4_grid_vanishing A2 A3 L h2 h3 hLdet ha
  let eta := d/3456
  have he : 0 < eta := by dsimp [eta]; positivity
  have he1 : eta < 1 := by dsimp [eta]; linarith
  have hde : 1728*eta < d := by dsimp [eta]; linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ))))
  have hmp : 0 < m := by
    have h1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast (lt_trans zero_lt_one h1)
  have hcut := (lt_of_le_of_lt (le_max_right _ _) hm).le
  refine ⟨eta,he,he1,m,hmp,K,hK,hmem,D,E,hD,hE,?_⟩
  intro rho hp
  obtain ⟨t,ht,hfinite,hgrowth,hsep⟩ := original_blocks4 V hV eta E rho he hE hp m
  let lift : V → U := fun q => ⟨q.val,hVU q.property⟩
  let Q : Fin m → ℝ := fun h => (t h).val^(5 : ℕ)
  have hQ : ∀ h, 1 < Q h := fun h => (hgrowth h).1
  obtain ⟨h0,r,hr,hlogs,hA,hrsep,hrbal⟩ := SourceBlocks.positive_degrees m hmp eta rho he hp Q hQ hsep
  obtain ⟨P,hP,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,hvan⟩ := haux eta he m hcut r hr
  refine ⟨fun h => lift (t h),ht,r,hr,hrsep,P,hP,hhom,hheight,hreal 0,hp2,hp3,hcfs,?_⟩
  apply hvan Q hQ h0 d hde hd1 (fun h => (hgrowth h).2.1)
    (fun h => (hgrowth h).2.2) hrbal c hc hbal
    (fun h j => ((F (lift (t h))).w j.castSucc : Fin 4 → ℤ))
  · intro h j i
    exact (hframe (lift (t h)) (t h).property).1 j i
  · intro h j i
    exact (hframe (lift (t h)) (t h).property).2.1 j i
  · intro h j i
    exact (hframe (lift (t h)) (t h).property).2.2 j i

end CompoundFeasibility.SourceBlocks4Literal176

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalIndex4Literal176
open SourceMultiblock4 OriginalLastDual4 OriginalAuxiliaryDual4 OriginalDeformedSource4
open Auxiliary4Literal176 Auxiliary4Literal176.SourceEvaluation4 Auxiliary4Literal176.SourceGrid4 Auxiliary4Literal176.SourceSupport4
variable {K : Type*} [Field K]

theorem primitive_integer4 (z : Fin 4 → ℤ) (hz : z ≠ 0) :
    ∃ (g : ℤ) (M a : Fin 4 → ℤ), g ≠ 0 ∧ M ≠ 0 ∧
      (∀ i, z i = g*M i) ∧ (∑ i, a i*M i) = 1 ∧ Ideal.span (Set.range M) = ⊤ := by
  let I : Ideal ℤ := Ideal.span (Set.range z)
  let g := Submodule.IsPrincipal.generator I
  have hdiv (i : Fin 4) : g ∣ z i :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_range_self i))
  choose M hM using hdiv
  have hg : g ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hM i,he,zero_mul]
    rfl
  have hgm : g ∈ Submodule.span ℤ (Set.range z) := by
    rw [Ideal.submodule_span_eq]
    exact Submodule.IsPrincipal.generator_mem I
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hgm
  simp only [smul_eq_mul] at ha
  have hsum : ∑ i, a i*M i = 1 := by
    apply mul_left_cancel₀ hg
    calc
      g*(∑ i, a i*M i) = ∑ i, a i*z i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hM i]
        ring
      _ = g*1 := by simpa using ha
  have hspan : Ideal.span (Set.range M) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hsum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  have hMn : M ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hM i,he]
    simp
  exact ⟨g,M,a,hg,hMn,hM,hsum,hspan⟩

def realNormalForm4 (M : Fin 4 → ℤ) : Module.Dual ℝ (Fin 4 → ℝ) :=
  ∑ i, (M i : ℝ) • LinearMap.proj i

theorem realNormalForm4_apply (M : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    realNormalForm4 M x = ∑ i, (M i : ℝ)*x i := by
  simp [realNormalForm4]

theorem real_normal_kernel4 (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ)))
    (M : Fin 4 → ℤ) (hM : M ≠ 0)
    (hann : ∀ j : Fin 3, (∑ i, M i*v j.castSucc i) = 0) :
    LinearMap.ker (realNormalForm4 M) =
      Submodule.span ℝ (Set.range (fun j : Fin 3 => fun i => (v j.castSucc i : ℝ))) := by
  let u : Fin 4 → Fin 4 → ℝ := fun j i => (v j i : ℝ)
  let b := basisOfPiSpaceOfLinearIndependent hv
  have hb (i : Fin 4) : b i = u i := congrFun (coe_basisOfPiSpaceOfLinearIndependent hv) i
  have hf (j : Fin 3) : realNormalForm4 M (u j.castSucc) = 0 := by
    rw [realNormalForm4_apply]
    change (∑ i, (M i : ℝ)*(v j.castSucc i : ℝ)) = 0
    exact_mod_cast hann j
  have hfn : realNormalForm4 M ≠ 0 := by
    intro hz
    apply hM
    funext i
    have he := congrArg (fun f : Module.Dual ℝ (Fin 4 → ℝ) => f (Pi.single i 1)) hz
    have hi : (M i : ℝ) = 0 := by simpa [realNormalForm4,Pi.single_apply] using he
    exact_mod_cast hi
  have hlast : realNormalForm4 M (u 3) ≠ 0 := by
    intro hz
    apply hfn
    apply b.ext
    intro j
    rw [hb]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hz
    · exact hf i
  have hvalue (x : Fin 4 → ℝ) :
      realNormalForm4 M x = b.repr x 3 * realNormalForm4 M (u 3) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum,Fin.sum_univ_castSucc]
    simp only [map_smul,hb,hf,smul_zero,Finset.sum_const_zero,zero_add]
    rfl
  apply le_antisymm
  · intro x hx
    have hz : b.repr x 3 = 0 := (mul_eq_zero.mp ((hvalue x).symm.trans hx)).resolve_right hlast
    have he := b.sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 3 = (3 : Fin 4) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [hb]
    exact Submodule.subset_span ⟨j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hf j

theorem hermite_sizes4 (eta : ℝ) (heta : 0 < eta) (r : ℕ) (hr : 0 < r) :
    eta⁻¹ < (Nat.floor eta⁻¹+1 : ℕ) ∧
    (r : ℝ)*eta < (Nat.floor ((r : ℝ)*eta)+1 : ℕ) ∧
    (r : ℝ) < (Nat.floor eta⁻¹+1 : ℕ)*(Nat.floor ((r : ℝ)*eta)+1 : ℕ) := by
  have hs := Nat.lt_floor_add_one eta⁻¹
  have ht := Nat.lt_floor_add_one ((r : ℝ)*eta)
  have hs' : eta⁻¹ < ((Nat.floor eta⁻¹+1 : ℕ) : ℝ) := by exact_mod_cast hs
  have ht' : (r : ℝ)*eta < ((Nat.floor ((r : ℝ)*eta)+1 : ℕ) : ℝ) := by exact_mod_cast ht
  refine ⟨hs',ht',?_⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have he : eta⁻¹*((r : ℝ)*eta) = r := by field_simp
  calc
    (r : ℝ) = eta⁻¹*((r : ℝ)*eta) := he.symm
    _ < _ := mul_lt_mul hs' ht'.le (mul_pos hr' heta) (by positivity)

theorem additional_weight4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (K : Vars4 m →₀ ℕ)
    (hK : ∀ h, (∑ i : Fin 4, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r K ≤ (m : ℝ)*eta := by
  unfold rothSourceDerivativeWeight
  calc
    _ ≤ ∑ h : Fin m, eta := by
      apply Finset.sum_le_sum
      intro h _
      apply (div_le_iff₀ (show (0 : ℝ) < r h by exact_mod_cast hr h)).mpr
      have hk : (∑ i : Fin 4, (K (h,i) : ℝ)) ≤ (Nat.floor ((r h : ℝ)*eta) : ℝ) := by
        exact_mod_cast hK h
      exact hk.trans (by simpa [mul_comm] using Nat.floor_le (le_of_lt (mul_pos (by exact_mod_cast hr h) heta)))
    _ = _ := by simp

theorem additional_cutoff4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (J K : Vars4 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (m : ℝ)*eta)
    (hK : ∀ h, (∑ i : Fin 4, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r (K+J) < 2*eta*m := by
  rw [rothSource_weight_add]
  have hk := additional_weight4 r hr eta heta K hK
  nlinarith

theorem hasse_grid_composition4 {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ)
    (J K : Vars4 m →₀ ℕ) (x : Fin m → Fin 4 → ℤ)
    (hz : integerValue (K+J) P x = 0) :
    integerValue K (derivative4 J P) x = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_zero,integerValue_cast,derivative4_map,source4_derivative_comp]
  rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,← integerValue_cast, hz]
  simp


def normalPolynomial4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    MvPolynomial (Vars4 m) ℝ := ∑ i, MvPolynomial.C (M h i : ℝ)*MvPolynomial.X (h,i)

def sourceNormalIdeal4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    Ideal (MvPolynomial (Vars4 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, (normalPolynomial4 M h)^(i h)}

theorem homogeneous4_map {R : Type*} [CommRing R] (f : R →+* K) {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) R) (hP : homogeneous4 r P) :
    homogeneous4 r (P.map f) := by
  intro d hd h
  have hn : P.coeff d ≠ 0 := by
    intro hz
    have hn := MvPolynomial.mem_support_iff.mp hd
    apply hn
    rw [MvPolynomial.coeff_map,hz,map_zero]
  exact hP d (MvPolynomial.mem_support_iff.mpr hn) h

theorem integer_grid_rational_restriction4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (J : Vars4 m →₀ ℕ)
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative4 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 4 → ℚ,
      (∀ h, y h ∈ Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0 := by
  classical
  let N := Nat.floor eta⁻¹+1
  let S : Fin m → Fin 3 → Finset ℚ := fun _ _ => (Finset.Icc 1 N).image (fun n : ℕ => (n : ℚ))
  have hcard : ∀ h j, (S h j).card = N := by
    intro h j
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Nat.cast_injective)]
    simp
  have hdeg : ∀ d ∈ (derivative4 J (P.map (Int.castRingHom ℚ))).support, ∀ h,
      (∑ i : Fin 4, d (h,i)) ≤ r h :=
    derivative4_block_degree_bound r _ (fun d hd h => (homogeneous4_map _ r P hP d hd h).le) J
  have hsize : ∀ h, r h < N*(Nat.floor ((r h : ℝ)*eta)+1) := by
    intro h
    have he := (hermite_sizes4 eta heta (r h) (hr h)).2.2
    exact_mod_cast he
  apply multiblock_span_hermite4 _ (fun h j i => (w h j i : ℚ)) S (fun _ => N)
    (fun h => Nat.floor ((r h : ℝ)*eta)) r hcard hdeg hsize
  intro a ha B hB
  have hex : ∀ h j, ∃ n : ℕ, n ∈ Finset.Icc 1 N ∧ (n : ℚ) = a h j := by
    intro h j
    exact Finset.mem_image.mp (ha h j)
  choose n hn hna using hex
  have hn' : ∀ h j, 1 ≤ n h j ∧ n h j ≤ Nat.floor eta⁻¹+1 := by
    intro h j
    exact Finset.mem_Icc.mp (hn h j)
  have hz := congrArg (fun z : ℤ => (z : ℚ)) (hgrid n hn' B hB)
  change (integerValue B (derivative4 J P) (gridPoint w n) : ℚ) = 0 at hz
  rw [integerValue_cast,derivative4_map] at hz
  have he : blockFramePoint4 (fun h j i => (w h j i : ℚ)) a =
      (fun u : Vars4 m => (gridPoint w n u.1 u.2 : ℚ)) := by
    funext u
    rcases u with ⟨h,i⟩
    simp only [blockFramePoint4,gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hna h j]
  rw [he]
  exact hz


theorem integer_grid_real_restriction4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (J : Vars4 m →₀ ℕ)
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative4 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 4 → ℝ,
      (∀ h, y h ∈ Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0 := by
  classical
  let N := Nat.floor eta⁻¹+1
  let S : Fin m → Fin 3 → Finset ℝ := fun _ _ => (Finset.Icc 1 N).image (fun n : ℕ => (n : ℝ))
  have hcard : ∀ h j, (S h j).card = N := by
    intro h j
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Nat.cast_injective)]
    simp
  have hdeg : ∀ d ∈ (derivative4 J (P.map (Int.castRingHom ℝ))).support, ∀ h,
      (∑ i : Fin 4, d (h,i)) ≤ r h :=
    derivative4_block_degree_bound r _ (fun d hd h => (homogeneous4_map _ r P hP d hd h).le) J
  have hsize : ∀ h, r h < N*(Nat.floor ((r h : ℝ)*eta)+1) := by
    intro h
    have he := (hermite_sizes4 eta heta (r h) (hr h)).2.2
    exact_mod_cast he
  apply multiblock_span_hermite4 _ (fun h j i => (w h j i : ℝ)) S (fun _ => N)
    (fun h => Nat.floor ((r h : ℝ)*eta)) r hcard hdeg hsize
  intro a ha B hB
  have hex : ∀ h j, ∃ n : ℕ, n ∈ Finset.Icc 1 N ∧ (n : ℝ) = a h j := by
    intro h j
    exact Finset.mem_image.mp (ha h j)
  choose n hn hna using hex
  have hn' : ∀ h j, 1 ≤ n h j ∧ n h j ≤ Nat.floor eta⁻¹+1 := by
    intro h j
    exact Finset.mem_Icc.mp (hn h j)
  have hz := congrArg (fun z : ℤ => (z : ℝ)) (hgrid n hn' B hB)
  have hz0 : ((0 : ℤ) : ℝ) = (0 : ℝ) := by norm_num
  change (integerValue B (derivative4 J P) (gridPoint w n) : ℝ) = ((0 : ℤ) : ℝ) at hz
  rw [hz0] at hz
  rw [integerValue_cast,derivative4_map] at hz
  have he : blockFramePoint4 (fun h j i => (w h j i : ℝ)) a =
      (fun u : Vars4 m => (gridPoint w n u.1 u.2 : ℝ)) := by
    funext u
    rcases u with ⟨h,i⟩
    simp only [blockFramePoint4,gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hna h j]
  rw [he]
  exact hz


def normalForward4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) ℝ →+* MvPolynomial (Vars4 m) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = k u.1 then normalPolynomial4 M u.1 else MvPolynomial.X u)

def normalInverse4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) ℝ →+* MvPolynomial (Vars4 m) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then
    MvPolynomial.C ((M u.1 (k u.1) : ℝ)⁻¹) *
      (MvPolynomial.X u - ∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (M u.1 j : ℝ) * MvPolynomial.X (u.1,j))
    else MvPolynomial.X u)

theorem normalForward6_inverse4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars4 m) ℝ) :
    normalForward4 M k (normalInverse4 M k P) = P := by
  classical
  have he : (normalForward4 M k).comp (normalInverse4 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [normalForward4,normalInverse4]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C ((M h (k h) : ℝ)⁻¹) : MvPolynomial (Vars4 m) ℝ) *
            MvPolynomial.C (M h (k h) : ℝ) = 1 := by
          rw [← MvPolynomial.C_mul,inv_mul_cancel₀ (by exact_mod_cast hk h),map_one]
        have hs : normalPolynomial4 M h =
            (∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j)) +
              MvPolynomial.C (M h (k h) : ℝ) * MvPolynomial.X (h,k h) := by
          exact (Finset.sum_erase_add _ _ (Finset.mem_univ (k h))).symm
        simp only [RingHom.comp_apply,normalInverse4,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,map_mul,map_sub,map_sum,normalForward4,
          MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',RingHom.id_apply]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) *
              (if j = k h then normalPolynomial4 M h else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,hs,add_sub_cancel_left,← mul_assoc,hc,one_mul]
      · simp [normalForward4,normalInverse4,hi]
  exact congrArg (fun f => f P) he

theorem normalInverse6_forward4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars4 m) ℝ) :
    normalInverse4 M k (normalForward4 M k P) = P := by
  classical
  have he : (normalInverse4 M k).comp (normalForward4 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [normalForward4,normalInverse4]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C (M h (k h) : ℝ) : MvPolynomial (Vars4 m) ℝ) *
            MvPolynomial.C ((M h (k h) : ℝ)⁻¹) = 1 := by
          rw [← MvPolynomial.C_mul,mul_inv_cancel₀ (by exact_mod_cast hk h),map_one]
        simp only [RingHom.comp_apply,normalForward4,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,RingHom.id_apply]
        change normalInverse4 M k (normalPolynomial4 M h) = MvPolynomial.X (h,k h)
        rw [normalPolynomial4,← Finset.sum_erase_add _ _ (Finset.mem_univ (k h))]
        simp only [map_add,map_sum,map_mul,normalInverse4,MvPolynomial.eval₂Hom_C,
          MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) *
              (if j = k h then MvPolynomial.C ((M h (k h) : ℝ)⁻¹) *
                (MvPolynomial.X (h,j) - ∑ l ∈ Finset.univ.erase (k h),
                  MvPolynomial.C (M h l : ℝ) * MvPolynomial.X (h,l))
               else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,← mul_assoc,hc,one_mul]
        ring
      · simp [normalForward4,normalInverse4,hi]
  exact congrArg (fun f => f P) he

noncomputable def zeroNormalCoordinates4 {m : ℕ} (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) K →+* MvPolynomial (Vars4 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then 0 else MvPolynomial.X u)

theorem zeroNormalCoordinates4_monomial {m : ℕ} (k : Fin m → Fin 4)
    (b : Vars4 m →₀ ℕ) (c : K) :
    zeroNormalCoordinates4 k (MvPolynomial.monomial b c) =
      if (∀ h, b (h,k h) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [zeroNormalCoordinates4, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  by_cases hb : ∀ h, b (h,k h) = 0
  · rw [if_pos hb, MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    apply Finset.prod_congr rfl
    intro u _
    by_cases hu : u.2 = k u.1
    · have he : u = (u.1,k u.1) := Prod.ext rfl hu
      have hz : b u = 0 := (congrArg b he).trans (hb u.1)
      simp [hu, hz]
    · simp [hu]
  · rw [if_neg hb]
    push_neg at hb
    obtain ⟨h, hh⟩ := hb
    have hz : (∏ u : Vars4 m, (if u.2 = k u.1 then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (Vars4 m) K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,k h))
      simp [hh]
    rw [hz, mul_zero]

theorem zeroNormalCoordinates4_coeff {m : ℕ} (k : Fin m → Fin 4)
    (Q : MvPolynomial (Vars4 m) K) (b : Vars4 m →₀ ℕ) :
    (zeroNormalCoordinates4 k Q).coeff b = if (∀ h, b (h,k h) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [zeroNormalCoordinates4_monomial]
    by_cases ha : ∀ h, a (h,k h) = 0
    · rw [if_pos ha]
      by_cases hb : ∀ h, b (h,k h) = 0
      · simp [hb]
      · have hab : a ≠ b := by intro he; subst a; exact hb ha
        simp [hb, hab]
    · rw [if_neg ha]
      by_cases hb : ∀ h, b (h,k h) = 0
      · have hab : a ≠ b := by intro he; subst a; exact ha hb
        simp [hb, hab]
      · simp [hb]
  | add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, hP, hQ, MvPolynomial.coeff_add]
    split_ifs <;> simp


theorem normal_zero_restriction4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars4 m) ℝ)
    (hzero : ∀ y : Fin m → Fin 4 → ℝ,
      (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0) :
    zeroNormalCoordinates4 k (normalInverse4 M k P) = 0 := by
  classical
  apply MvPolynomial.funext
  intro z
  let H := (zeroNormalCoordinates4 (K := ℝ) k).comp (normalInverse4 M k)
  let y : Fin m → Fin 4 → ℝ := fun h i => MvPolynomial.eval z (H (MvPolynomial.X (h,i)))
  have he : (MvPolynomial.eval z).comp H = MvPolynomial.eval (fun u => y u.1 u.2) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [H,normalInverse4,zeroNormalCoordinates4]
    · intro u
      simp [y]
  have hker : ∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h)) := by
    intro h
    have hn := normalInverse6_forward4 M k hk (MvPolynomial.X (h,k h))
    simp only [normalForward4,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true] at hn
    have hz := congrArg (fun Q => MvPolynomial.eval z (zeroNormalCoordinates4 k Q)) hn
    simp only [zeroNormalCoordinates4,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,
      ite_true,map_zero] at hz
    have hp := congrArg (fun f : MvPolynomial (Vars4 m) ℝ →+* ℝ => f (normalPolynomial4 M h)) he
    change MvPolynomial.eval z (H (normalPolynomial4 M h)) = _ at hp
    change MvPolynomial.eval z (H (normalPolynomial4 M h)) = 0 at hz
    rw [hp] at hz
    simpa [LinearMap.mem_ker,realNormalForm4,normalPolynomial4,map_sum,map_mul,y] using hz
  have hp := congrArg (fun f : MvPolynomial (Vars4 m) ℝ →+* ℝ => f P) he
  change MvPolynomial.eval z (zeroNormalCoordinates4 k (normalInverse4 M k P)) =
    MvPolynomial.eval (fun u => y u.1 u.2) P at hp
  rw [hp,hzero y hker,map_zero]

theorem normalInverse4_pderiv_X {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (h : Fin m) (u : Vars4 m) :
    MvPolynomial.pderiv (h,k h) (normalInverse4 M k (MvPolynomial.X u)) =
      MvPolynomial.C ((M h (k h) : ℝ)⁻¹) * (if (h,k h) = u then 1 else 0) := by
  classical
  rcases u with ⟨g,i⟩
  by_cases hg : g = h
  · subst g
    by_cases hi : i = k h
    · subst i
      have hs : MvPolynomial.pderiv (h,k h)
          (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j)) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        simp [MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply,
          Prod.mk.injEq,Ne.symm (Finset.mem_erase.mp hj).1]
      simp only [normalInverse4,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true,
        MvPolynomial.pderiv_C_mul,map_sub,hs,MvPolynomial.pderiv_X,Pi.single_eq_same]
      simp
    · simp [normalInverse4,hi,MvPolynomial.pderiv_X,Pi.single_apply,Prod.mk.injEq,Ne.symm hi]
  · by_cases hi : i = k g <;>
      simp [normalInverse4,hi,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,map_sum,
        Pi.single_apply,Prod.mk.injEq,hg,Ne.symm hg]

theorem normalInverse4_chain {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (h : Fin m) (P : MvPolynomial (Vars4 m) ℝ) :
    MvPolynomial.pderiv (h,k h) (normalInverse4 M k P) =
      MvPolynomial.C ((M h (k h) : ℝ)⁻¹) * normalInverse4 M k (MvPolynomial.pderiv (h,k h) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [normalInverse4]
  | add P Q hP hQ => simp only [map_add,hP,hQ,mul_add]
  | mul_X P u hP =>
    rw [map_mul,MvPolynomial.pderiv_mul,hP,normalInverse4_pderiv_X,
      MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.pderiv_X]
    simp only [Pi.single_apply,apply_ite,map_one,map_zero]
    by_cases hu : u = (h,k h)
    · subst u
      simp
      ring
    · simp [hu,Ne.symm hu]
      ring

def normalCoordinateWeight4 {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 4)
    (b : Vars4 m →₀ ℕ) : ℝ := ∑ h, (b (h,k h) : ℝ) / r h

theorem normalCoordinateWeight4_add {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 4)
    (b c : Vars4 m →₀ ℕ) :
    normalCoordinateWeight4 r k (b+c) = normalCoordinateWeight4 r k b + normalCoordinateWeight4 r k c := by
  simp [normalCoordinateWeight4,Finsupp.add_apply,Nat.cast_add,add_div,Finset.sum_add_distrib]

theorem normalCoordinateWeight4_single {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 4) (h : Fin m) :
    normalCoordinateWeight4 r k (Finsupp.single (h,k h) 1) = 1/(r h : ℝ) := by
  have he (g : Fin m) : (Finsupp.single (h,k h) 1 : Vars4 m →₀ ℕ) (g,k g) =
      if g = h then 1 else 0 := by
    by_cases hg : g = h
    · subst g; simp
    · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
  simp only [normalCoordinateWeight4]
  simp_rw [he]
  simp [ite_div,Finset.sum_ite_eq,Finset.sum_ite_eq']

theorem normalInverse4_coeff_zero {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars4 m) ℝ)
    (hindex : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J P) = 0)
    (J b : Vars4 m →₀ ℕ)
    (hbad : rothSourceDerivativeWeight r J + normalCoordinateWeight4 r k b < c) :
    (normalInverse4 M k (derivative4 J P)).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : Vars4 m →₀ ℕ,
      (∑ h : Fin m, b (h,k h)) = n →
      rothSourceDerivativeWeight r J + normalCoordinateWeight4 r k b < c →
      (normalInverse4 M k (derivative4 J P)).coeff b = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J b hn hw
      by_cases hnzero : n = 0
      · have hbzero : ∀ h, b (h,k h) = 0 := by
          intro h
          have hle : b (h,k h) ≤ ∑ g : Fin m, b (g,k g) :=
            Finset.single_le_sum (f := fun g : Fin m => b (g,k g)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
          omega
        have hnonneg : 0 ≤ normalCoordinateWeight4 r k b := by
          unfold normalCoordinateWeight4
          positivity
        have hJ : rothSourceDerivativeWeight r J < c := by linarith
        have hz := normal_zero_restriction4 M k hk (derivative4 J P) (hindex J hJ)
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [zeroNormalCoordinates4_coeff,if_pos hbzero,MvPolynomial.coeff_zero] at he
        exact he
      · have hex : ∃ h : Fin m, b (h,k h) ≠ 0 := by
          by_contra! hzero
          have hs : (∑ h : Fin m, b (h,k h)) = 0 := Finset.sum_eq_zero (fun h _ => hzero h)
          omega
        obtain ⟨h,hh⟩ := hex
        let d := b - Finsupp.single (h,k h) 1
        have hle : Finsupp.single (h,k h) 1 ≤ b := by rw [Finsupp.single_le_iff]; omega
        have hdeq : d + Finsupp.single (h,k h) 1 = b := tsub_add_cancel_of_le hle
        have hcount : (∑ g : Fin m, d (g,k g)) + 1 = n := by
          have hs := congrArg (fun b : Vars4 m →₀ ℕ => ∑ g : Fin m, b (g,k g)) hdeq
          have he (g : Fin m) : (Finsupp.single (h,k h) 1 : Vars4 m →₀ ℕ) (g,k g) =
              if g = h then 1 else 0 := by
            by_cases hg : g = h
            · subst g; simp
            · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
          simp_rw [Finsupp.add_apply,he] at hs
          simpa [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',hn] using hs
        have hcoord : normalCoordinateWeight4 r k d + 1/(r h : ℝ) = normalCoordinateWeight4 r k b := by
          rw [← normalCoordinateWeight4_single r k h,← normalCoordinateWeight4_add,hdeq]
        have hz : (normalInverse4 M k (derivative4 (J+Finsupp.single (h,k h) 1) P)).coeff d = 0 := by
          apply ih (∑ g : Fin m, d (g,k g)) (by omega) _ d rfl
          rw [rothSource_weight_add,rothSource_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,k h) (normalInverse4 M k (derivative4 J P))).coeff d = 0 := by
          rw [normalInverse4_chain,source4_pderiv_hasse,map_nsmul,
            MvPolynomial.coeff_C_mul,MvPolynomial.coeff_smul,hz,smul_zero,mul_zero]
        rw [SourceSupport4.pderiv_coeff,hdeq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad

theorem normalForward4_monomial {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (b : Vars4 m →₀ ℕ) (a : ℝ) :
    normalForward4 M k (MvPolynomial.monomial b a) =
      MvPolynomial.C a * ((∏ h, (normalPolynomial4 M h) ^ b (h,k h)) *
        (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) := by
  classical
  rw [normalForward4,MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp),Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro h hh
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (k h))]
  simp only [Prod.fst,Prod.snd,ite_true]
  have he : (∏ i ∈ Finset.univ.erase (k h),
      (if i = k h then normalPolynomial4 M h else MvPolynomial.X (h,i)) ^ b (h,i)) =
      ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_erase.mp hi).1]
  rw [he]
  ring

theorem normalForward4_monomial_mem {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (r : Fin m → ℕ) (c : ℝ)
    (b : Vars4 m →₀ ℕ) (a : ℝ) (hb : c ≤ normalCoordinateWeight4 r k b) :
    normalForward4 M k (MvPolynomial.monomial b a) ∈ sourceNormalIdeal4 M r c := by
  have hg : (∏ h, (normalPolynomial4 M h) ^ b (h,k h)) ∈ sourceNormalIdeal4 M r c :=
    Ideal.subset_span ⟨fun h => b (h,k h),hb,rfl⟩
  rw [normalForward4_monomial]
  have hm := Ideal.mul_mem_left (sourceNormalIdeal4 M r c)
    (MvPolynomial.C a * (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) hg
  convert hm using 1
  ring

theorem sourceNormalIdeal4_of_derivative_restrictions {m : ℕ}
    (M : Fin m → Fin 4 → ℤ) (hM : ∀ h, M h ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars4 m) ℝ)
    (hindex : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J P) = 0) :
    P ∈ sourceNormalIdeal4 M r c := by
  classical
  have hex (h : Fin m) : ∃ i : Fin 4, M h i ≠ 0 := by
    by_contra! hz
    exact hM h (funext hz)
  choose k hk using hex
  have hcoeff (b : Vars4 m →₀ ℕ) (hb : normalCoordinateWeight4 r k b < c) :
      (normalInverse4 M k P).coeff b = 0 := by
    have hz := normalInverse4_coeff_zero M k hk r c P hindex 0 b
      (by simpa [rothSourceDerivativeWeight] using hb)
    simpa only [derivative4_zero_index] using hz
  have hsupport (b) (hb : b ∈ (normalInverse4 M k P).support) :
      c ≤ normalCoordinateWeight4 r k b := by
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp hb) (hcoeff b hlt)
  have hsum := congrArg (normalForward4 M k) (normalInverse4 M k P).as_sum
  rw [normalForward6_inverse4 M k hk P,map_sum] at hsum
  rw [hsum]
  apply Ideal.sum_mem
  intro b hb
  exact normalForward4_monomial_mem M k r c b _ (hsupport b hb)

theorem integer_grid_high_normal_index4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h ≠ 0)
    (hQ : ∀ h, LinearMap.ker (normalForm4 (M h)) =
      Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ))))
    (hR : ∀ h, LinearMap.ker (realNormalForm4 (M h)) =
      Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ))))
    (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
        integerValue J P (gridPoint w a) = 0) :
    (∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 4 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r ((m : ℝ)*eta) := by
  have hrestr : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 4 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0) := by
    intro J hJ
    have hc : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ B : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
          integerValue B (derivative4 J P) (gridPoint w a) = 0 := by
      intro a ha B hB
      exact hasse_grid_composition4 P J B _
        (hgrid a ha (B+J) (additional_cutoff4 r hr eta heta J B hJ hB))
    constructor
    · intro y hy
      apply integer_grid_rational_restriction4 r hr P hP J w eta heta hc y
      intro h
      rw [← hQ h]
      exact hy h
    · intro y hy
      exact integer_grid_real_restriction4 r hr P hP J w eta heta hc y
        (fun h => (hR h) ▸ hy h)

  exact ⟨hrestr,sourceNormalIdeal4_of_derivative_restrictions M hM r ((m : ℝ)*eta)
    (P.map (Int.castRingHom ℝ)) (fun J hJ => (hrestr J hJ).2)⟩



theorem primitive_cofactor_normal4 (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j))) :
    ∃ (g : ℤ) (M a : Fin 4 → ℤ), g ≠ 0 ∧ M ≠ 0 ∧
      (∀ i, integerLastDual4 v i = g*M i) ∧ (∑ i, a i*M i) = 1 ∧
      Ideal.span (Set.range M) = ⊤ ∧
      (∀ j : Fin 3, (∑ i, M i*v j.castSucc i) = 0) ∧
      LinearMap.ker (normalForm4 M) =
        Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (v j.castSucc i : ℚ))) ∧
      LinearMap.ker (realNormalForm4 M) =
        Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (v j.castSucc))) := by
  have hrat := integral_frame_rational_independent v hv
  obtain ⟨g,M,a,hg,hMn,hscale,ha,hspan⟩ :=
    primitive_integer4 (integerLastDual4 v) (integerLastDual4_nonzero v hrat)
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hscaleQ : normalForm4 (integerLastDual4 v) = (g : ℚ) • normalForm4 M := by
    apply LinearMap.ext
    intro x
    rw [normalForm4_apply,LinearMap.smul_apply,normalForm4_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i]
    push_cast
    ring
  have hk : LinearMap.ker (normalForm4 M) = firstThreeSpan4 (fun j i => (v j i : ℚ)) := by
    calc
      _ = LinearMap.ker (normalForm4 (integerLastDual4 v)) := by rw [hscaleQ,LinearMap.ker_smul _ _ hgQ]
      _ = _ := by
        rw [integerLastDual4_form v hrat,LinearMap.ker_smul _ _
          (show ((Matrix.det v : ℤ) : ℚ) ≠ 0 by exact_mod_cast integerFrame4_det_ne_zero v hrat),
          lastDual4_kernel]
  have hann (j : Fin 3) : (∑ i, M i*v j.castSucc i) = 0 := by
    have hm : (fun i => (v j.castSucc i : ℚ)) ∈ LinearMap.ker (normalForm4 M) := by
      rw [hk]
      exact Submodule.subset_span (Set.mem_range_self j)
    have hmQ := (normalForm4_apply M (fun i => (v j.castSucc i : ℚ))).symm.trans hm
    exact_mod_cast hmQ
  exact ⟨g,M,a,hg,hMn,hscale,ha,hspan,hann,hk,real_normal_kernel4 v hv M hMn hann⟩

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

def sourceFrameHighIndex4
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q)) : Prop :=

    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ m : ℕ, 0 < m ∧
      ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau i j, SourceForms4Literal176.forms4 A2 A3 L tau i j ∈ K) ∧
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ rho : ℝ, 0 < rho → ∃ t : Fin m → U,
        StrictMono (fun h => (t h).val) ∧
        ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
        (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
        ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
          (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
          matrixIndex4 L r eta P ∧ matrixIndex4 (SourceForms4Literal176.finiteMatrix4 2 A2) r eta P ∧
          matrixIndex4 (SourceForms4Literal176.finiteMatrix4 3 A3) r eta P ∧
          (∀ J b : Vars4 m →₀ ℕ,
            ‖(Auxiliary4Literal176.SourceExpansion4.expansion L J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4Literal176.SourceExpansion4.expansion (SourceForms4Literal176.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4Literal176.SourceExpansion4.expansion (SourceForms4Literal176.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h,r h)) ∧
          (∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
          ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
            integerValue J P (gridPoint (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) a) = 0) ∧
          ∃ (g : Fin m → ℤ) (M a : Fin m → Fin 4 → ℤ),
            (∀ h, g h ≠ 0 ∧ M h ≠ 0 ∧
              (∀ i, integerLastDual4 (fun j => ((F (t h)).w j : Fin 4 → ℤ)) i = g h*M h i) ∧
              (∑ i, a h i*M h i) = 1 ∧ Ideal.span (Set.range (M h)) = ⊤ ∧
              LinearMap.ker (normalForm4 (M h)) =
                Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (((F (t h)).w j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
              LinearMap.ker (realNormalForm4 (M h)) =
                Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal ((F (t h)).w j.castSucc : Fin 4 → ℤ)))) ∧
            (∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
              (∀ y : Fin m → Fin 4 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm4 (M h))) →
                MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0) ∧
              (∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
                MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
            P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r ((m : ℝ)*eta)

theorem same_selected_frame_high_index4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) : sourceFrameHighIndex4 F := by
  obtain ⟨eta,he,he1,m,hm,K,hK,hmem,D,E,hD,hE,hblocks⟩ :=
    SourceBlocks4Literal176.same_selected_frame_grid4 h2 h3 hLdet ha F hU hd hc2 hc3
  refine ⟨eta,he,he1,m,hm,K,hK,hmem,D,E,hD,hE,?_⟩
  intro rho hp
  obtain ⟨t,ht,r,hr,hrsep,P,hP,hhom,hheight,hi0,hi2,hi3,hcfs,hgrid⟩ := hblocks rho hp
  have hex (h : Fin m) := primitive_cofactor_normal4
    (fun j => ((F (t h)).w j : Fin 4 → ℤ)) (F (t h)).real_independent
  choose g M a hg hM hscale ha hspan hann hQ hR using hex
  refine ⟨t,ht,r,hr,hrsep,P,hP,hhom,hheight,hi0,hi2,hi3,hcfs,hgrid,g,M,a,?_,?_⟩
  · intro h
    exact ⟨hg h,hM h,hscale h,ha h,hspan h,hQ h,hR h⟩
  · exact integer_grid_high_normal_index4 r hr P hhom
      (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) M hM hQ hR eta he hgrid


end CompoundFeasibility.SourceNormalIndex4Literal176
end

#check CompoundFeasibility.SourceForms4Literal176.forms4
#print CompoundFeasibility.SourceForms4Literal176.forms4
#print axioms CompoundFeasibility.SourceForms4Literal176.forms4
#check CompoundFeasibility.SourceForms4Literal176.finiteMatrix4
#print CompoundFeasibility.SourceForms4Literal176.finiteMatrix4
#print axioms CompoundFeasibility.SourceForms4Literal176.finiteMatrix4
#check CompoundFeasibility.SourceForms4Literal176.source_det_one4
#print CompoundFeasibility.SourceForms4Literal176.source_det_one4
#print axioms CompoundFeasibility.SourceForms4Literal176.source_det_one4
#check CompoundFeasibility.SourceForms4Literal176.source_unit4
#print CompoundFeasibility.SourceForms4Literal176.source_unit4
#print axioms CompoundFeasibility.SourceForms4Literal176.source_unit4
#check CompoundFeasibility.SourceForms4Literal176.finite_det_one4
#print CompoundFeasibility.SourceForms4Literal176.finite_det_one4
#print axioms CompoundFeasibility.SourceForms4Literal176.finite_det_one4
#check CompoundFeasibility.SourceForms4Literal176.source_algebraic4
#print CompoundFeasibility.SourceForms4Literal176.source_algebraic4
#print axioms CompoundFeasibility.SourceForms4Literal176.source_algebraic4
#check CompoundFeasibility.SourceForms4Literal176.common_source_field4
#print CompoundFeasibility.SourceForms4Literal176.common_source_field4
#print axioms CompoundFeasibility.SourceForms4Literal176.common_source_field4
#check CompoundFeasibility.SourceForms4Literal176.source_rows_nonzero4
#print CompoundFeasibility.SourceForms4Literal176.source_rows_nonzero4
#print axioms CompoundFeasibility.SourceForms4Literal176.source_rows_nonzero4
#check CompoundFeasibility.Auxiliary4Literal176.Block4
#print CompoundFeasibility.Auxiliary4Literal176.Block4
#print axioms CompoundFeasibility.Auxiliary4Literal176.Block4
#check CompoundFeasibility.Auxiliary4Literal176.blockNatEquiv4
#print CompoundFeasibility.Auxiliary4Literal176.blockNatEquiv4
#print axioms CompoundFeasibility.Auxiliary4Literal176.blockNatEquiv4
#check CompoundFeasibility.Auxiliary4Literal176.block4_card
#print CompoundFeasibility.Auxiliary4Literal176.block4_card
#print axioms CompoundFeasibility.Auxiliary4Literal176.block4_card
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxBlockPerm
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxBlockPerm
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxBlockPerm
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_coordinate_sum
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_coordinate_sum
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_coordinate_sum
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_center_sum
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_center_sum
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_center_sum
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_center_bound
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_center_bound
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_center_bound
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_exp_sum
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_exp_sum
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxBlock_exp_sum
#check CompoundFeasibility.Auxiliary4Literal176.RothAuxCoefficients
#print CompoundFeasibility.Auxiliary4Literal176.RothAuxCoefficients
#print axioms CompoundFeasibility.Auxiliary4Literal176.RothAuxCoefficients
#check CompoundFeasibility.Auxiliary4Literal176.RothAuxPivots
#print CompoundFeasibility.Auxiliary4Literal176.RothAuxPivots
#print axioms CompoundFeasibility.Auxiliary4Literal176.RothAuxPivots
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxDimension
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxDimension
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxDimension
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxDimension_eq
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxDimension_eq
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxDimension_eq
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxCentered
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxCentered
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxCentered
#check CompoundFeasibility.Auxiliary4Literal176.RothAuxBad
#print CompoundFeasibility.Auxiliary4Literal176.RothAuxBad
#print axioms CompoundFeasibility.Auxiliary4Literal176.RothAuxBad
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxPivotCondition
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxPivotCondition
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxPivotCondition
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_exp_moment
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_exp_moment
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_exp_moment
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_exp_tail_parameter
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_exp_tail_parameter
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_exp_tail_parameter
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxBad_card_zero
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxBad_card_zero
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxBad_card_zero
#check CompoundFeasibility.Auxiliary4Literal176.rothAuxBad_exp_bound
#print CompoundFeasibility.Auxiliary4Literal176.rothAuxBad_exp_bound
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAuxBad_exp_bound
#check CompoundFeasibility.Auxiliary4Literal176.Equations4
#print CompoundFeasibility.Auxiliary4Literal176.Equations4
#print axioms CompoundFeasibility.Auxiliary4Literal176.Equations4
#check CompoundFeasibility.Auxiliary4Literal176.dimension4_pos
#print CompoundFeasibility.Auxiliary4Literal176.dimension4_pos
#print axioms CompoundFeasibility.Auxiliary4Literal176.dimension4_pos
#check CompoundFeasibility.Auxiliary4Literal176.coordinate_rows4_le_half
#print CompoundFeasibility.Auxiliary4Literal176.coordinate_rows4_le_half
#print axioms CompoundFeasibility.Auxiliary4Literal176.coordinate_rows4_le_half
#check CompoundFeasibility.Auxiliary4Literal176.coordinate_rows4_lt
#print CompoundFeasibility.Auxiliary4Literal176.coordinate_rows4_lt
#print axioms CompoundFeasibility.Auxiliary4Literal176.coordinate_rows4_lt
#check CompoundFeasibility.Auxiliary4Literal176.Block3
#print CompoundFeasibility.Auxiliary4Literal176.Block3
#print axioms CompoundFeasibility.Auxiliary4Literal176.Block3
#check CompoundFeasibility.Auxiliary4Literal176.blockNatEquiv3
#print CompoundFeasibility.Auxiliary4Literal176.blockNatEquiv3
#print axioms CompoundFeasibility.Auxiliary4Literal176.blockNatEquiv3
#check CompoundFeasibility.Auxiliary4Literal176.block3_card
#print CompoundFeasibility.Auxiliary4Literal176.block3_card
#print axioms CompoundFeasibility.Auxiliary4Literal176.block3_card
#check CompoundFeasibility.Auxiliary4Literal176.blockPivotEquiv4
#print CompoundFeasibility.Auxiliary4Literal176.blockPivotEquiv4
#print axioms CompoundFeasibility.Auxiliary4Literal176.blockPivotEquiv4
#check CompoundFeasibility.Auxiliary4Literal176.bad_iff_pivot6
#print CompoundFeasibility.Auxiliary4Literal176.bad_iff_pivot6
#print axioms CompoundFeasibility.Auxiliary4Literal176.bad_iff_pivot6
#check CompoundFeasibility.Auxiliary4Literal176.badPivotEquiv4
#print CompoundFeasibility.Auxiliary4Literal176.badPivotEquiv4
#print axioms CompoundFeasibility.Auxiliary4Literal176.badPivotEquiv4
#check CompoundFeasibility.Auxiliary4Literal176.bad_count_source4
#print CompoundFeasibility.Auxiliary4Literal176.bad_count_source4
#print axioms CompoundFeasibility.Auxiliary4Literal176.bad_count_source4
#check CompoundFeasibility.Auxiliary4Literal176.constraint_count_source4
#print CompoundFeasibility.Auxiliary4Literal176.constraint_count_source4
#print axioms CompoundFeasibility.Auxiliary4Literal176.constraint_count_source4
#check CompoundFeasibility.Auxiliary4Literal176.rothSourceDerivativeWeight
#print CompoundFeasibility.Auxiliary4Literal176.rothSourceDerivativeWeight
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSourceDerivativeWeight
#check CompoundFeasibility.Auxiliary4Literal176.exponent4
#print CompoundFeasibility.Auxiliary4Literal176.exponent4
#print axioms CompoundFeasibility.Auxiliary4Literal176.exponent4
#check CompoundFeasibility.Auxiliary4Literal176.exponent4_injective
#print CompoundFeasibility.Auxiliary4Literal176.exponent4_injective
#print axioms CompoundFeasibility.Auxiliary4Literal176.exponent4_injective
#check CompoundFeasibility.Auxiliary4Literal176.polynomial4
#print CompoundFeasibility.Auxiliary4Literal176.polynomial4
#print axioms CompoundFeasibility.Auxiliary4Literal176.polynomial4
#check CompoundFeasibility.Auxiliary4Literal176.polynomial4_coeff
#print CompoundFeasibility.Auxiliary4Literal176.polynomial4_coeff
#print axioms CompoundFeasibility.Auxiliary4Literal176.polynomial4_coeff
#check CompoundFeasibility.Auxiliary4Literal176.homogeneous4
#print CompoundFeasibility.Auxiliary4Literal176.homogeneous4
#print axioms CompoundFeasibility.Auxiliary4Literal176.homogeneous4
#check CompoundFeasibility.Auxiliary4Literal176.polynomial4_homogeneous
#print CompoundFeasibility.Auxiliary4Literal176.polynomial4_homogeneous
#print axioms CompoundFeasibility.Auxiliary4Literal176.polynomial4_homogeneous
#check CompoundFeasibility.Auxiliary4Literal176.chart4
#print CompoundFeasibility.Auxiliary4Literal176.chart4
#print axioms CompoundFeasibility.Auxiliary4Literal176.chart4
#check CompoundFeasibility.Auxiliary4Literal176.substitute4
#print CompoundFeasibility.Auxiliary4Literal176.substitute4
#print axioms CompoundFeasibility.Auxiliary4Literal176.substitute4
#check CompoundFeasibility.Auxiliary4Literal176.pivotDerivative4
#print CompoundFeasibility.Auxiliary4Literal176.pivotDerivative4
#print axioms CompoundFeasibility.Auxiliary4Literal176.pivotDerivative4
#check CompoundFeasibility.Auxiliary4Literal176.transformed_monomial4
#print CompoundFeasibility.Auxiliary4Literal176.transformed_monomial4
#print axioms CompoundFeasibility.Auxiliary4Literal176.transformed_monomial4
#check CompoundFeasibility.Auxiliary4Literal176.exponent4_sum
#print CompoundFeasibility.Auxiliary4Literal176.exponent4_sum
#print axioms CompoundFeasibility.Auxiliary4Literal176.exponent4_sum
#check CompoundFeasibility.Auxiliary4Literal176.transformed_coeff_sum4
#print CompoundFeasibility.Auxiliary4Literal176.transformed_coeff_sum4
#print axioms CompoundFeasibility.Auxiliary4Literal176.transformed_coeff_sum4
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_weight_block
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_weight_block
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_weight_block
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_weight_pivot
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_weight_pivot
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_weight_pivot
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_weighted_neg
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_weighted_neg
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_weighted_neg
#check CompoundFeasibility.Auxiliary4Literal176.chart4_block_weight
#print CompoundFeasibility.Auxiliary4Literal176.chart4_block_weight
#print axioms CompoundFeasibility.Auxiliary4Literal176.chart4_block_weight
#check CompoundFeasibility.Auxiliary4Literal176.chart4_pivot_weight
#print CompoundFeasibility.Auxiliary4Literal176.chart4_pivot_weight
#print axioms CompoundFeasibility.Auxiliary4Literal176.chart4_pivot_weight
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_scaled_monomial_weighted
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_scaled_monomial_weighted
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_scaled_monomial_weighted
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_polynomial
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_polynomial
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_polynomial
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_pivot_monomial_block_weight
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_pivot_monomial_block_weight
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_pivot_monomial_block_weight
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_block_weight
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_block_weight
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_block_weight
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_block_homogeneous
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_block_homogeneous
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_block_homogeneous
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_pivot_weight
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_pivot_weight
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_pivot_weight
#check CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_pivot_zero
#print CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_pivot_zero
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothAux_transformed_pivot_zero
#check CompoundFeasibility.Auxiliary4Literal176.freeExponent4
#print CompoundFeasibility.Auxiliary4Literal176.freeExponent4
#print axioms CompoundFeasibility.Auxiliary4Literal176.freeExponent4
#check CompoundFeasibility.Auxiliary4Literal176.freeExponent4_reconstruct
#print CompoundFeasibility.Auxiliary4Literal176.freeExponent4_reconstruct
#print axioms CompoundFeasibility.Auxiliary4Literal176.freeExponent4_reconstruct
#check Aux4HeightLiteral176.chart_mass4
#print Aux4HeightLiteral176.chart_mass4
#print axioms Aux4HeightLiteral176.chart_mass4
#check Aux4HeightLiteral176.binomial_norm4
#print Aux4HeightLiteral176.binomial_norm4
#print axioms Aux4HeightLiteral176.binomial_norm4
#check Aux4HeightLiteral176.transformed_entry_norm4
#print Aux4HeightLiteral176.transformed_entry_norm4
#print axioms Aux4HeightLiteral176.transformed_entry_norm4
#check CompoundFeasibility.Auxiliary4Literal176.formEquiv4
#print CompoundFeasibility.Auxiliary4Literal176.formEquiv4
#print axioms CompoundFeasibility.Auxiliary4Literal176.formEquiv4
#check CompoundFeasibility.Auxiliary4Literal176.equation4
#print CompoundFeasibility.Auxiliary4Literal176.equation4
#print axioms CompoundFeasibility.Auxiliary4Literal176.equation4
#check CompoundFeasibility.Auxiliary4Literal176.matrix4
#print CompoundFeasibility.Auxiliary4Literal176.matrix4
#print axioms CompoundFeasibility.Auxiliary4Literal176.matrix4
#check CompoundFeasibility.Auxiliary4Literal176.matrix4_mulVec
#print CompoundFeasibility.Auxiliary4Literal176.matrix4_mulVec
#print axioms CompoundFeasibility.Auxiliary4Literal176.matrix4_mulVec
#check CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_iff_coefficients
#print CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_iff_coefficients
#print axioms CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_iff_coefficients
#check CompoundFeasibility.Auxiliary4Literal176.restriction4_zero_iff_coefficients
#print CompoundFeasibility.Auxiliary4Literal176.restriction4_zero_iff_coefficients
#print axioms CompoundFeasibility.Auxiliary4Literal176.restriction4_zero_iff_coefficients
#check CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_iff_restrictions
#print CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_iff_restrictions
#print axioms CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_iff_restrictions
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_chart_pderiv
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_chart_pderiv
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_chart_pderiv
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_chain
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_chain
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_chain
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_add
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_add
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_add
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_mono
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_mono
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_mono
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_single
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_single
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_single
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_pivot
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_pivot
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_weight_pivot
#check CompoundFeasibility.Auxiliary4Literal176.rothSourceFreeOrder
#print CompoundFeasibility.Auxiliary4Literal176.rothSourceFreeOrder
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSourceFreeOrder
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_free_add
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_free_add
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_free_add
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_free_single
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_free_single
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_free_single
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_free_zero_pivot
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_free_zero_pivot
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_free_zero_pivot
#check CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_mixed_vanishing
#print CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_mixed_vanishing
#print axioms CompoundFeasibility.Auxiliary4Literal176.rothSource_scaled_mixed_vanishing
#check CompoundFeasibility.Auxiliary4Literal176.kernelChart4
#print CompoundFeasibility.Auxiliary4Literal176.kernelChart4
#print axioms CompoundFeasibility.Auxiliary4Literal176.kernelChart4
#check CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4
#print CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4
#print axioms CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4
#check CompoundFeasibility.Auxiliary4Literal176.kernelChart4_form
#print CompoundFeasibility.Auxiliary4Literal176.kernelChart4_form
#print axioms CompoundFeasibility.Auxiliary4Literal176.kernelChart4_form
#check CompoundFeasibility.Auxiliary4Literal176.chartTransport4
#print CompoundFeasibility.Auxiliary4Literal176.chartTransport4
#print axioms CompoundFeasibility.Auxiliary4Literal176.chartTransport4
#check CompoundFeasibility.Auxiliary4Literal176.chartTransport4_variable
#print CompoundFeasibility.Auxiliary4Literal176.chartTransport4_variable
#print axioms CompoundFeasibility.Auxiliary4Literal176.chartTransport4_variable
#check CompoundFeasibility.Auxiliary4Literal176.chartTransport4_substitute
#print CompoundFeasibility.Auxiliary4Literal176.chartTransport4_substitute
#print axioms CompoundFeasibility.Auxiliary4Literal176.chartTransport4_substitute
#check CompoundFeasibility.Auxiliary4Literal176.derivative4_zero_of_block_excess
#print CompoundFeasibility.Auxiliary4Literal176.derivative4_zero_of_block_excess
#print axioms CompoundFeasibility.Auxiliary4Literal176.derivative4_zero_of_block_excess
#check CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_all_derivatives
#print CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_all_derivatives
#print axioms CompoundFeasibility.Auxiliary4Literal176.matrix4_kernel_all_derivatives
#check CompoundFeasibility.Auxiliary4Literal176.derivative4_map
#print CompoundFeasibility.Auxiliary4Literal176.derivative4_map
#print axioms CompoundFeasibility.Auxiliary4Literal176.derivative4_map
#check CompoundFeasibility.Auxiliary4Literal176.chart4_map
#print CompoundFeasibility.Auxiliary4Literal176.chart4_map
#print axioms CompoundFeasibility.Auxiliary4Literal176.chart4_map
#check CompoundFeasibility.Auxiliary4Literal176.substitute4_map
#print CompoundFeasibility.Auxiliary4Literal176.substitute4_map
#print axioms CompoundFeasibility.Auxiliary4Literal176.substitute4_map
#check CompoundFeasibility.Auxiliary4Literal176.polynomial4_map
#print CompoundFeasibility.Auxiliary4Literal176.polynomial4_map
#print axioms CompoundFeasibility.Auxiliary4Literal176.polynomial4_map
#check CompoundFeasibility.Auxiliary4Literal176.matrix4_map
#print CompoundFeasibility.Auxiliary4Literal176.matrix4_map
#print axioms CompoundFeasibility.Auxiliary4Literal176.matrix4_map
#check CompoundFeasibility.Auxiliary4Literal176.integralMatrix4
#print CompoundFeasibility.Auxiliary4Literal176.integralMatrix4
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralMatrix4
#check CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_kernel
#print CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_kernel
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_kernel
#check CompoundFeasibility.Auxiliary4Literal176.integralHeightBase4
#print CompoundFeasibility.Auxiliary4Literal176.integralHeightBase4
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralHeightBase4
#check CompoundFeasibility.Auxiliary4Literal176.integralCoordinateConstant4
#print CompoundFeasibility.Auxiliary4Literal176.integralCoordinateConstant4
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralCoordinateConstant4
#check CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_entry_bound
#print CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_entry_bound
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_entry_bound
#check CompoundFeasibility.Auxiliary4Literal176.dimension4_le_pow
#print CompoundFeasibility.Auxiliary4Literal176.dimension4_le_pow
#print axioms CompoundFeasibility.Auxiliary4Literal176.dimension4_le_pow
#check CompoundFeasibility.Auxiliary4Literal176.integralSiegelConstant4
#print CompoundFeasibility.Auxiliary4Literal176.integralSiegelConstant4
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralSiegelConstant4
#check CompoundFeasibility.Auxiliary4Literal176.integralSiegelConstant4_ge_one
#print CompoundFeasibility.Auxiliary4Literal176.integralSiegelConstant4_ge_one
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralSiegelConstant4_ge_one
#check CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_uniform_bound
#print CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_uniform_bound
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_uniform_bound
#check CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_bounded_kernel
#print CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_bounded_kernel
#print axioms CompoundFeasibility.Auxiliary4Literal176.integralMatrix4_bounded_kernel
#check CompoundFeasibility.Auxiliary4Literal176.height4
#print CompoundFeasibility.Auxiliary4Literal176.height4
#print axioms CompoundFeasibility.Auxiliary4Literal176.height4
#check CompoundFeasibility.Auxiliary4Literal176.polynomial4_ne_zero
#print CompoundFeasibility.Auxiliary4Literal176.polynomial4_ne_zero
#print axioms CompoundFeasibility.Auxiliary4Literal176.polynomial4_ne_zero
#check CompoundFeasibility.Auxiliary4Literal176.polynomial4_height_le
#print CompoundFeasibility.Auxiliary4Literal176.polynomial4_height_le
#print axioms CompoundFeasibility.Auxiliary4Literal176.polynomial4_height_le
#check CompoundFeasibility.Auxiliary4Literal176.kernelChart4_scale
#print CompoundFeasibility.Auxiliary4Literal176.kernelChart4_scale
#print axioms CompoundFeasibility.Auxiliary4Literal176.kernelChart4_scale
#check CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4_scale
#print CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4_scale
#print axioms CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4_scale
#check CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4_map
#print CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4_map
#print axioms CompoundFeasibility.Auxiliary4Literal176.kernelRestriction4_map
#check CompoundFeasibility.Auxiliary4Literal176.integral_auxiliary4
#print CompoundFeasibility.Auxiliary4Literal176.integral_auxiliary4
#print axioms CompoundFeasibility.Auxiliary4Literal176.integral_auxiliary4
#check CompoundFeasibility.Auxiliary4Literal176.source_integral_scaling4
#print CompoundFeasibility.Auxiliary4Literal176.source_integral_scaling4
#print axioms CompoundFeasibility.Auxiliary4Literal176.source_integral_scaling4
#check CompoundFeasibility.Auxiliary4Literal176.algebraic_auxiliary4
#print CompoundFeasibility.Auxiliary4Literal176.algebraic_auxiliary4
#print axioms CompoundFeasibility.Auxiliary4Literal176.algebraic_auxiliary4
#check CompoundFeasibility.Auxiliary4Literal176.source_restriction4_real
#print CompoundFeasibility.Auxiliary4Literal176.source_restriction4_real
#print axioms CompoundFeasibility.Auxiliary4Literal176.source_restriction4_real
#check CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4_field
#print CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4_field
#print axioms CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4_field
#check CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4
#print CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4
#print axioms CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4
#check CompoundFeasibility.Auxiliary4Literal176.matrixIndex4
#print CompoundFeasibility.Auxiliary4Literal176.matrixIndex4
#print axioms CompoundFeasibility.Auxiliary4Literal176.matrixIndex4
#check CompoundFeasibility.Auxiliary4Literal176.restriction4_map_int
#print CompoundFeasibility.Auxiliary4Literal176.restriction4_map_int
#print axioms CompoundFeasibility.Auxiliary4Literal176.restriction4_map_int
#check CompoundFeasibility.Auxiliary4Literal176.padic_restriction4_zero
#print CompoundFeasibility.Auxiliary4Literal176.padic_restriction4_zero
#print axioms CompoundFeasibility.Auxiliary4Literal176.padic_restriction4_zero
#check CompoundFeasibility.Auxiliary4Literal176.finite_matrix_index4
#print CompoundFeasibility.Auxiliary4Literal176.finite_matrix_index4
#print axioms CompoundFeasibility.Auxiliary4Literal176.finite_matrix_index4
#check CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4_all_places
#print CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4_all_places
#print axioms CompoundFeasibility.Auxiliary4Literal176.source_auxiliary4_all_places
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.linearChart
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.linearChart
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.linearChart
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.expansion
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.expansion
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.expansion
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_one
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_one
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_one
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_comp
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_comp
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_comp
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution_comp
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution_comp
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution_comp
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution_one
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution_one
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.substitution_one
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.reconstruct
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.reconstruct
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.reconstruct
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.unique
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.unique
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.unique
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_mass
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_mass
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.chart_mass
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.monomial_mass
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.monomial_mass
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.monomial_mass
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.support_index
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.support_index
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.support_index
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.support_card
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.support_card
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.support_card
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.expansion_sum
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.expansion_sum
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.expansion_sum
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.coefficient_bound
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.coefficient_bound
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.coefficient_bound
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget_one
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget_one
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget_one
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget_entry
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget_entry
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.inverseBudget_entry
#check CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.source_coefficient_bounds
#print CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.source_coefficient_bounds
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceExpansion4.source_coefficient_bounds
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.chart_pderiv
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.chart_pderiv
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.chart_pderiv
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.substitution_chain
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.substitution_chain
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.substitution_chain
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zeroCoordinate
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zeroCoordinate
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zeroCoordinate
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernelImage
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernelImage
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernelImage
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_image_form
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_image_form
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_image_form
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_factor_variable
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_factor_variable
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_factor_variable
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zero_monomial
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zero_monomial
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zero_monomial
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zero_coeff
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zero_coeff
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.zero_coeff
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.pderiv_coeff
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.pderiv_coeff
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.pderiv_coeff
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_factor
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_factor
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.kernel_factor
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.index_zero_slice
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.index_zero_slice
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.index_zero_slice
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.expansion_chain
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.expansion_chain
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.expansion_chain
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinateWeight
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinateWeight
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinateWeight
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinate_weight_add
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinate_weight_add
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinate_weight_add
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinate_weight_single
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinate_weight_single
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coordinate_weight_single
#check CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coeff_zero_below_index
#print CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coeff_zero_below_index
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceSupport4.coeff_zero_below_index
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.chart_block_weight
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.chart_block_weight
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.chart_block_weight
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.expansion_block_weight
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.expansion_block_weight
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.expansion_block_weight
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.expansion_block_degree
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.expansion_block_degree
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.expansion_block_degree
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.total_coordinate_weight_le
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.total_coordinate_weight_le
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.total_coordinate_weight_le
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.balance_from_weights
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.balance_from_weights
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.balance_from_weights
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.balanced_of_vanishing
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.balanced_of_vanishing
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.balanced_of_vanishing
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.Claims
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.Claims
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.Claims
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.claims_of_charts
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.claims_of_charts
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.claims_of_charts
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.claims_of_matrix_index4
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.claims_of_matrix_index4
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.claims_of_matrix_index4
#check CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.source_auxiliary4_balanced
#print CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.source_auxiliary4_balanced
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceBalance4.source_auxiliary4_balanced
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_cast
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_cast
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_cast
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_lower
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_lower
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_lower
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_finite_le_one
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_finite_le_one
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.integerValue_finite_le_one
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.evaluation_identity
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.evaluation_identity
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.evaluation_identity
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.logWeight
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.logWeight
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.logWeight
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.log_weight_transport
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.log_weight_transport
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.log_weight_transport
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.monomial_bound
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.monomial_bound
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.monomial_bound
#check CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.expansion_support_card
#print CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.expansion_support_card
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceEvaluation4.expansion_support_card
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.evaluation_upper
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.evaluation_upper
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.evaluation_upper
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.gridPoint
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.gridPoint
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.gridPoint
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.matrix_grid
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.matrix_grid
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.matrix_grid
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.grid_form_norm
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.grid_form_norm
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.grid_form_norm
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.real_multiplier
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.real_multiplier
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.real_multiplier
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.padic_multiplier
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.padic_multiplier
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.padic_multiplier
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.grid_form_rpow
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.grid_form_rpow
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.grid_form_rpow
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.log_total_bounds
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.log_total_bounds
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.log_total_bounds
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.weighted_log_upper
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.weighted_log_upper
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.weighted_log_upper
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.source_exponents
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.source_exponents
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.source_exponents
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.local_upper
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.local_upper
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.local_upper
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.strict_product_bound
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.strict_product_bound
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.strict_product_bound
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.real_grid_bounds
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.real_grid_bounds
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.real_grid_bounds
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.padic_grid_bounds
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.padic_grid_bounds
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.padic_grid_bounds
#check CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.sourceBound
#print CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.sourceBound
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceGrid4.sourceBound
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.evaluation_identity_of_reconstruction
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.evaluation_identity_of_reconstruction
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.evaluation_identity_of_reconstruction
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.evaluation_upper_of_reconstruction
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.evaluation_upper_of_reconstruction
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.evaluation_upper_of_reconstruction
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.local_upper_from_claims
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.local_upper_from_claims
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.local_upper_from_claims
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.three_place_upper
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.three_place_upper
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.three_place_upper
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.sourceBound_product
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.sourceBound_product
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.sourceBound_product
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.three_place_product_lt_one
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.three_place_product_lt_one
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.three_place_product_lt_one
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.grid_derivative_vanishes
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.grid_derivative_vanishes
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.grid_derivative_vanishes
#check CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.source_auxiliary4_grid_vanishing
#print CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.source_auxiliary4_grid_vanishing
#print axioms CompoundFeasibility.Auxiliary4Literal176.SourceVanishing4.source_auxiliary4_grid_vanishing
#check CompoundFeasibility.SourceWeights4Literal176.select_unbounded_weights
#print CompoundFeasibility.SourceWeights4Literal176.select_unbounded_weights
#print axioms CompoundFeasibility.SourceWeights4Literal176.select_unbounded_weights
#check CompoundFeasibility.SourceWeights4Literal176.logWeight
#print CompoundFeasibility.SourceWeights4Literal176.logWeight
#print axioms CompoundFeasibility.SourceWeights4Literal176.logWeight
#check CompoundFeasibility.SourceWeights4Literal176.logWeight_bounds
#print CompoundFeasibility.SourceWeights4Literal176.logWeight_bounds
#print axioms CompoundFeasibility.SourceWeights4Literal176.logWeight_bounds
#check CompoundFeasibility.SourceWeights4Literal176.logWeight_power
#print CompoundFeasibility.SourceWeights4Literal176.logWeight_power
#print axioms CompoundFeasibility.SourceWeights4Literal176.logWeight_power
#check CompoundFeasibility.SourceWeights4Literal176.logWeight_balance
#print CompoundFeasibility.SourceWeights4Literal176.logWeight_balance
#print axioms CompoundFeasibility.SourceWeights4Literal176.logWeight_balance
#check CompoundFeasibility.SourceWeights4Literal176.fixedWeights
#print CompoundFeasibility.SourceWeights4Literal176.fixedWeights
#print axioms CompoundFeasibility.SourceWeights4Literal176.fixedWeights
#check CompoundFeasibility.SourceWeights4Literal176.fixedWeights_bounds_balance
#print CompoundFeasibility.SourceWeights4Literal176.fixedWeights_bounds_balance
#print axioms CompoundFeasibility.SourceWeights4Literal176.fixedWeights_bounds_balance
#check CompoundFeasibility.SourceWeights4Literal176.finite_form_bounds
#print CompoundFeasibility.SourceWeights4Literal176.finite_form_bounds
#print axioms CompoundFeasibility.SourceWeights4Literal176.finite_form_bounds
#check CompoundFeasibility.SourceWeights4Literal176.frameWidths
#print CompoundFeasibility.SourceWeights4Literal176.frameWidths
#print axioms CompoundFeasibility.SourceWeights4Literal176.frameWidths
#check CompoundFeasibility.SourceWeights4Literal176.fixed_weights_same_frame4
#print CompoundFeasibility.SourceWeights4Literal176.fixed_weights_same_frame4
#print axioms CompoundFeasibility.SourceWeights4Literal176.fixed_weights_same_frame4
#check CompoundFeasibility.SourceBlocks4Literal176.original_blocks4
#print CompoundFeasibility.SourceBlocks4Literal176.original_blocks4
#print axioms CompoundFeasibility.SourceBlocks4Literal176.original_blocks4
#check CompoundFeasibility.SourceBlocks4Literal176.same_selected_frame_grid4
#print CompoundFeasibility.SourceBlocks4Literal176.same_selected_frame_grid4
#print axioms CompoundFeasibility.SourceBlocks4Literal176.same_selected_frame_grid4
#check CompoundFeasibility.SourceNormalIndex4Literal176.primitive_integer4
#print CompoundFeasibility.SourceNormalIndex4Literal176.primitive_integer4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.primitive_integer4
#check CompoundFeasibility.SourceNormalIndex4Literal176.realNormalForm4
#print CompoundFeasibility.SourceNormalIndex4Literal176.realNormalForm4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.realNormalForm4
#check CompoundFeasibility.SourceNormalIndex4Literal176.realNormalForm4_apply
#print CompoundFeasibility.SourceNormalIndex4Literal176.realNormalForm4_apply
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.realNormalForm4_apply
#check CompoundFeasibility.SourceNormalIndex4Literal176.real_normal_kernel4
#print CompoundFeasibility.SourceNormalIndex4Literal176.real_normal_kernel4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.real_normal_kernel4
#check CompoundFeasibility.SourceNormalIndex4Literal176.hermite_sizes4
#print CompoundFeasibility.SourceNormalIndex4Literal176.hermite_sizes4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.hermite_sizes4
#check CompoundFeasibility.SourceNormalIndex4Literal176.additional_weight4
#print CompoundFeasibility.SourceNormalIndex4Literal176.additional_weight4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.additional_weight4
#check CompoundFeasibility.SourceNormalIndex4Literal176.additional_cutoff4
#print CompoundFeasibility.SourceNormalIndex4Literal176.additional_cutoff4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.additional_cutoff4
#check CompoundFeasibility.SourceNormalIndex4Literal176.hasse_grid_composition4
#print CompoundFeasibility.SourceNormalIndex4Literal176.hasse_grid_composition4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.hasse_grid_composition4
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalPolynomial4
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalPolynomial4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalPolynomial4
#check CompoundFeasibility.SourceNormalIndex4Literal176.sourceNormalIdeal4
#print CompoundFeasibility.SourceNormalIndex4Literal176.sourceNormalIdeal4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.sourceNormalIdeal4
#check CompoundFeasibility.SourceNormalIndex4Literal176.homogeneous4_map
#print CompoundFeasibility.SourceNormalIndex4Literal176.homogeneous4_map
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.homogeneous4_map
#check CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_rational_restriction4
#print CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_rational_restriction4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_rational_restriction4
#check CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_real_restriction4
#print CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_real_restriction4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_real_restriction4
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalForward6_inverse4
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalForward6_inverse4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalForward6_inverse4
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse6_forward4
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse6_forward4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse6_forward4
#check CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4
#print CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4
#check CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4_monomial
#print CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4_monomial
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4_monomial
#check CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4_coeff
#print CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4_coeff
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.zeroNormalCoordinates4_coeff
#check CompoundFeasibility.SourceNormalIndex4Literal176.normal_zero_restriction4
#print CompoundFeasibility.SourceNormalIndex4Literal176.normal_zero_restriction4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normal_zero_restriction4
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_pderiv_X
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_pderiv_X
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_pderiv_X
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_chain
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_chain
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_chain
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4_add
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4_add
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4_add
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4_single
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4_single
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalCoordinateWeight4_single
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_coeff_zero
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_coeff_zero
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalInverse4_coeff_zero
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4_monomial
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4_monomial
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4_monomial
#check CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4_monomial_mem
#print CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4_monomial_mem
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.normalForward4_monomial_mem
#check CompoundFeasibility.SourceNormalIndex4Literal176.sourceNormalIdeal4_of_derivative_restrictions
#print CompoundFeasibility.SourceNormalIndex4Literal176.sourceNormalIdeal4_of_derivative_restrictions
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.sourceNormalIdeal4_of_derivative_restrictions
#check CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_high_normal_index4
#print CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_high_normal_index4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.integer_grid_high_normal_index4
#check CompoundFeasibility.SourceNormalIndex4Literal176.primitive_cofactor_normal4
#print CompoundFeasibility.SourceNormalIndex4Literal176.primitive_cofactor_normal4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.primitive_cofactor_normal4
#check CompoundFeasibility.SourceNormalIndex4Literal176.sourceFrameHighIndex4
#print CompoundFeasibility.SourceNormalIndex4Literal176.sourceFrameHighIndex4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.sourceFrameHighIndex4
#check CompoundFeasibility.SourceNormalIndex4Literal176.same_selected_frame_high_index4
#print CompoundFeasibility.SourceNormalIndex4Literal176.same_selected_frame_high_index4
#print axioms CompoundFeasibility.SourceNormalIndex4Literal176.same_selected_frame_high_index4
