import FixedReference
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Pi

namespace JSP000334

open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def threePlaceProduct (q : ℚ) : ℚ := |q| * padicNorm 2 q * padicNorm 3 q

theorem threePlaceProduct_mul (q r : ℚ) :
    threePlaceProduct (q * r) = threePlaceProduct q * threePlaceProduct r := by
  simp only [threePlaceProduct, abs_mul, padicNorm.mul]
  ring

theorem threePlaceProduct_inv (q : ℚ) :
    threePlaceProduct q⁻¹ = (threePlaceProduct q)⁻¹ := by
  have h2 : padicNorm 2 q⁻¹ = (padicNorm 2 q)⁻¹ := by
    rw [inv_eq_one_div, padicNorm.div, padicNorm.one, one_div]
  have h3 : padicNorm 3 q⁻¹ = (padicNorm 3 q)⁻¹ := by
    rw [inv_eq_one_div, padicNorm.div, padicNorm.one, one_div]
  simp only [threePlaceProduct, h2, h3, abs_inv, mul_inv_rev]
  ring

theorem fixed_sunit_product_formula (u : fixedSUnitGroup) :
    threePlaceProduct ((u : ℚˣ) : ℚ) = 1 := by
  have h : ∀ (a : ℚˣ), a ∈ fixedSUnitGroup → threePlaceProduct (a : ℚ) = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · norm_num [threePlaceProduct, padicNorm.one]
        · change threePlaceProduct 2 = 1
          unfold threePlaceProduct
          have h22 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := by
            convert padicNorm.padicNorm_p (p := 2) (by decide) using 1
          have h32 : padicNorm 3 (2 : ℚ) = 1 := by
            convert padicNorm.padicNorm_of_prime_of_ne (p := 3) (q := 2) (by decide) using 1
          rw [h22, h32]
          norm_num
        · change threePlaceProduct 3 = 1
          unfold threePlaceProduct
          have h33 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ := by
            convert padicNorm.padicNorm_p (p := 3) (by decide) using 1
          have h23 : padicNorm 2 (3 : ℚ) = 1 := by
            convert padicNorm.padicNorm_of_prime_of_ne (p := 2) (q := 3) (by decide) using 1
          rw [h33, h23]
          norm_num
    | one => simp [threePlaceProduct, padicNorm.one]
    | mul a b _ _ ha hb => simp [threePlaceProduct_mul, ha, hb]
    | inv a _ ha => simp [threePlaceProduct_inv, ha]
  exact h u u.property

def rationalPlaceNorm (v : Fin 3) (q : ℚ) : ℚ := ![|q|, padicNorm 2 q, padicNorm 3 q] v

def localPairHeight (v : Fin 3) (u w : ℚ) : ℚ :=
  max (rationalPlaceNorm v u) (rationalPlaceNorm v w)

def pairHeight (u w : ℚ) : ℚ := ∏ v : Fin 3, localPairHeight v u w

def retainedFormsProduct (u w : ℚ) : ℚ :=
  ∏ v : Fin 3, min (rationalPlaceNorm v u) (rationalPlaceNorm v w) *
    rationalPlaceNorm v (u + w)

def normalizedFormsProduct (u w : ℚ) : ℚ :=
  ∏ v : Fin 3,
    (min (rationalPlaceNorm v u) (rationalPlaceNorm v w) /
      localPairHeight v u w) *
    (rationalPlaceNorm v (u + w) / localPairHeight v u w)

theorem rationalPlaceNorm_product (q : ℚ) :
    (∏ v : Fin 3, rationalPlaceNorm v q) = threePlaceProduct q := by
  simp [rationalPlaceNorm, Fin.prod_univ_succ, threePlaceProduct, mul_assoc]

theorem rationalPlaceNorm_pos (v : Fin 3) {q : ℚ} (hq : q ≠ 0) :
    0 < rationalPlaceNorm v q := by
  fin_cases v
  · exact abs_pos.mpr hq
  · exact lt_of_le_of_ne (padicNorm.nonneg q) (Ne.symm (padicNorm.nonzero hq))
  · exact lt_of_le_of_ne (padicNorm.nonneg q) (Ne.symm (padicNorm.nonzero hq))

theorem rationalPlaceNorm_one (v : Fin 3) : rationalPlaceNorm v 1 = 1 := by
  fin_cases v <;> simp [rationalPlaceNorm, padicNorm.one]

theorem three_term_height_one_le {x : Fin 3 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 2) : 1 ≤ pairHeight (x 0) (x 1) := by
  have h (v : Fin 3) : 1 ≤ localPairHeight v (x 0) (x 1) := by
    unfold localPairHeight
    rw [hx.1, rationalPlaceNorm_one]
    exact le_max_left _ _
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h01 : 1 ≤ localPairHeight 0 (x 0) (x 1) * localPairHeight 1 (x 0) (x 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  simp only [pairHeight, Fin.prod_univ_succ]
  norm_num only [Fin.prod_univ_zero, mul_one]
  change 1 ≤ localPairHeight 0 (x 0) (x 1) *
    (localPairHeight 1 (x 0) (x 1) * localPairHeight 2 (x 0) (x 1))
  nlinarith [mul_nonneg (sub_nonneg.mpr h01) (sub_nonneg.mpr h2)]

theorem pairHeight_pos {u w : ℚ} (hu : u ≠ 0) : 0 < pairHeight u w := by
  apply Finset.prod_pos
  intro v _
  exact (rationalPlaceNorm_pos v hu).trans_le (le_max_left _ _)

theorem three_term_forms_full_product {x : Fin 3 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 2) :
    threePlaceProduct (x 0) * threePlaceProduct (x 1) *
      threePlaceProduct (x 0 + x 1) = 1 := by
  have hu (i : Fin 3) : threePlaceProduct (x i) = 1 := by
    obtain ⟨u, he⟩ := hx.2.1 i
    rw [← he]
    exact fixed_sunit_product_formula u
  have hs : x 0 + x 1 = -x 2 := by
    have hsum := hx.2.2.1
    simp [Fin.sum_univ_succ] at hsum
    linarith
  have hneg : threePlaceProduct (-x 2) = threePlaceProduct (x 2) := by
    simp [threePlaceProduct]
  rw [hs, hneg, hu 0, hu 1, hu 2]
  norm_num

theorem three_term_retained_product_height {x : Fin 3 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 2) :
    retainedFormsProduct (x 0) (x 1) * pairHeight (x 0) (x 1) = 1 := by
  have hlocal (v : Fin 3) :
      (min (rationalPlaceNorm v (x 0)) (rationalPlaceNorm v (x 1)) *
        rationalPlaceNorm v (x 0 + x 1)) * localPairHeight v (x 0) (x 1) =
      rationalPlaceNorm v (x 0) * rationalPlaceNorm v (x 1) *
        rationalPlaceNorm v (x 0 + x 1) := by
    dsimp [localPairHeight]
    rw [mul_right_comm, min_mul_max]
  unfold retainedFormsProduct pairHeight
  rw [← Finset.prod_mul_distrib]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [rationalPlaceNorm_product]
  exact three_term_forms_full_product hx

theorem three_term_normalized_product_height {x : Fin 3 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 2) :
    normalizedFormsProduct (x 0) (x 1) = (pairHeight (x 0) (x 1))⁻¹ ^ 3 := by
  have hpos : 0 < pairHeight (x 0) (x 1) := pairHeight_pos (by simp [hx.1])
  have hret := three_term_retained_product_height hx
  have hnorm : normalizedFormsProduct (x 0) (x 1) =
      retainedFormsProduct (x 0) (x 1) / pairHeight (x 0) (x 1) ^ 2 := by
    unfold normalizedFormsProduct retainedFormsProduct pairHeight
    simp only [div_mul_div_comm, ← pow_two]
    rw [Finset.prod_div_distrib, Finset.prod_pow]
  rw [hnorm]
  have hne := ne_of_gt hpos
  field_simp
  nlinarith [hret]


def coordinateSumForms (i : Fin 2) : Fin 2 → ((Fin 2 → ℚ) →ₗ[ℚ] ℚ) :=
  ![LinearMap.proj i,
    LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 0 +
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 1]

theorem coordinateSumForms_independent (i : Fin 2) :
    LinearIndependent ℚ (coordinateSumForms i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h (z : Fin 2 → ℚ) : c 0 * z i + c 1 * (z 0 + z 1) = 0 := by
    simpa [coordinateSumForms, Fin.sum_univ_succ, mul_add] using LinearMap.congr_fun hc z
  have h0 := h ![1, 0]
  have h1 := h ![0, 1]
  fin_cases i
  · simp at h0 h1
    have hc0 : c 0 = 0 := by linarith
    fin_cases j <;> assumption
  · simp at h0 h1
    have hc0 : c 0 = 0 := by linarith
    fin_cases j <;> assumption

theorem exists_retained_coordinate (v : Fin 3) (u w : ℚ) :
    ∃ i : Fin 2, rationalPlaceNorm v (![u, w] i) =
      min (rationalPlaceNorm v u) (rationalPlaceNorm v w) := by
  by_cases h : rationalPlaceNorm v u ≤ rationalPlaceNorm v w
  · exact ⟨0, by simp [min_eq_left h]⟩
  · exact ⟨1, by simp [min_eq_right (le_of_not_ge h)]⟩


theorem fixed_sunit_norm_outside (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (u : fixedSUnitGroup) :
    padicNorm p ((u : ℚˣ) : ℚ) = 1 := by
  have h : ∀ (a : ℚˣ), a ∈ fixedSUnitGroup → padicNorm p (a : ℚ) = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · simp [padicNorm.one]
        · change padicNorm p (2 : ℚ) = 1
          convert padicNorm.padicNorm_of_prime_of_ne (q := 2) hp2 using 1
        · change padicNorm p (3 : ℚ) = 1
          convert padicNorm.padicNorm_of_prime_of_ne (q := 3) hp3 using 1
    | one => simp [padicNorm.one]
    | mul a b _ _ ha hb => simp only [Units.val_mul, padicNorm.mul, ha, hb, one_mul]
    | inv a _ ha =>
        rw [Units.val_inv_eq_inv_val]
        rw [inv_eq_one_div, padicNorm.div, padicNorm.one, ha]
        norm_num
  exact h u u.property

theorem pairHeight_sunit_scale (s : fixedSUnitGroup) (u w : ℚ) :
    pairHeight (((s : ℚˣ) : ℚ) * u) (((s : ℚˣ) : ℚ) * w) = pairHeight u w := by
  have hmul (v : Fin 3) (q : ℚ) :
      rationalPlaceNorm v (((s : ℚˣ) : ℚ) * q) =
        rationalPlaceNorm v ((s : ℚˣ) : ℚ) * rationalPlaceNorm v q := by
    fin_cases v <;> simp [rationalPlaceNorm, abs_mul]
  have hlocal (v : Fin 3) :
      localPairHeight v (((s : ℚˣ) : ℚ) * u) (((s : ℚˣ) : ℚ) * w) =
        rationalPlaceNorm v ((s : ℚˣ) : ℚ) * localPairHeight v u w := by
    simp only [localPairHeight, hmul]
    exact (mul_max_of_nonneg _ _ (le_of_lt (rationalPlaceNorm_pos v (Units.ne_zero _)))).symm
  unfold pairHeight
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, rationalPlaceNorm_product, fixed_sunit_product_formula, one_mul]

end JSP000334
