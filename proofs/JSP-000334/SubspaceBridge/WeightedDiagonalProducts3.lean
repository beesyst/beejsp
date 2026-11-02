import SubspaceBridge.WeightedDiagonalReduction3
import SubspaceBridge.WeightedDiagonalWeights3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_scaled_product3 (q : ℚ) (s u : fixedSUnitGroup) :
    threePlaceProduct (q*((s : ℚˣ) : ℚ)*((u : ℚˣ) : ℚ))=threePlaceProduct q := by
  rw [threePlaceProduct_mul,threePlaceProduct_mul,fixed_sunit_product_formula,fixed_sunit_product_formula,mul_one,mul_one]

theorem weighted_three_place_pos3 {q : ℚ} (hq : q≠0) : 0<threePlaceProduct q := by
  rw [← rationalPlaceNorm_product]
  exact Finset.prod_pos (fun v _ => rationalPlaceNorm_pos v hq)

def weightedDiagonalK3 (t : Fin 3 → ℤ) (L A : ℚ) (g : ℕ) : ℚ :=
  threePlaceProduct ((t 0 : ℚ)/g)*threePlaceProduct ((t 1 : ℚ)/g)*
    threePlaceProduct ((t 2 : ℚ)/g)*threePlaceProduct (L*A/g)

theorem weighted_diagonal_K_pos3 (t : Fin 3 → ℤ) (ht : ∀ i,t i≠0)
    (L A : ℚ) (hL : L≠0) (hA : A≠0) (g : ℕ) (hg : 0<g) :
    0<weightedDiagonalK3 t L A g := by
  have hgn : (g : ℚ)≠0 := by exact_mod_cast ne_of_gt hg
  have hp (i : Fin 3) : 0<threePlaceProduct ((t i : ℚ)/g) :=
    weighted_three_place_pos3 (div_ne_zero (by exact_mod_cast ht i) hgn)
  exact mul_pos (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2))
    (weighted_three_place_pos3 (div_ne_zero (mul_ne_zero hL hA) hgn))

theorem weighted_diagonal_products3 (t : Fin 3 → ℤ) (L A : ℚ) (g : ℕ)
    (u : Fin 3 → fixedSUnitGroup) (s : fixedSUnitGroup) (y : Fin 3 → ℤ)
    (hy : PrimitiveTriple y)
    (hcoord : ∀ i,(y i : ℚ)=((t i : ℚ)/g)*((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ))
    (hsum : (y 0 : ℚ)+y 1+y 2=-(L*A/g)*((s : ℚˣ) : ℚ)) :
    (∀ i,threePlaceProduct (y i : ℚ)=threePlaceProduct ((t i : ℚ)/g)) ∧
    threePlaceProduct ((y 0 : ℚ)+y 1+y 2)=threePlaceProduct (L*A/g) ∧
    ∃ choice : Fin 3 → Fin 3,
      tripleChoiceFormsProduct choice (fun i => (y i : ℚ))*archTripleHeight y=weightedDiagonalK3 t L A g := by
  have hc (i : Fin 3) : threePlaceProduct (y i : ℚ)=threePlaceProduct ((t i : ℚ)/g) := by
    rw [hcoord]
    exact weighted_scaled_product3 _ _ _
  have hs : threePlaceProduct ((y 0 : ℚ)+y 1+y 2)=threePlaceProduct (L*A/g) := by
    rw [hsum,threePlaceProduct_mul,fixed_sunit_product_formula,mul_one]
    simp [threePlaceProduct]
  exact ⟨hc,hs,weighted_fixed_product_height3 y hy (fun i => (t i : ℚ)/g) (L*A/g) hc hs⟩

theorem weighted_integer_local_inverse3 (m : ℤ) {p : ℚ} (hp : 0<p)
    (hprod : threePlaceProduct (m : ℚ)=p) (tau : Fin 3) :
    0<rationalPlaceNorm tau (m : ℚ) ∧
    (rationalPlaceNorm tau (m : ℚ))⁻¹≤max 1 p⁻¹*|(m : ℚ)| ∧
    (tau≠0 → rationalPlaceNorm tau (m : ℚ)≤1) := by
  have hm : m≠0 := by intro h;subst m;simp [threePlaceProduct] at hprod;linarith
  have hmq : (m : ℚ)≠0 := by exact_mod_cast hm
  have hpos := rationalPlaceNorm_pos tau hmq
  have h2 := padicNorm.of_int (p:=2) m
  have h3 := padicNorm.of_int (p:=3) m
  have hp2 : 0<padicNorm 2 (m : ℚ) := by simpa [rationalPlaceNorm] using rationalPlaceNorm_pos 1 hmq
  have hp3 : 0<padicNorm 3 (m : ℚ) := by simpa [rationalPlaceNorm] using rationalPlaceNorm_pos 2 hmq
  have ha1 : (1 : ℚ)≤|(m : ℚ)| := by exact_mod_cast (Int.one_le_abs hm)
  have ha : 0 < |(m : ℚ)| := abs_pos.mpr hmq
  have hmax : p⁻¹*|(m : ℚ)|≤max 1 p⁻¹*|(m : ℚ)| := mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le
  have harch : |(m : ℚ)|≤max 1 p⁻¹*|(m : ℚ)| := by nlinarith [mul_le_mul_of_nonneg_right (le_max_left (1 : ℚ) p⁻¹) ha.le]
  change |(m : ℚ)| *padicNorm 2 (m : ℚ)*padicNorm 3 (m : ℚ)=p at hprod
  refine ⟨hpos,?_,?_⟩
  · fin_cases tau
    · change |(m : ℚ)|⁻¹≤_
      exact (by apply (inv_le_iff_one_le_mul₀ ha).mpr;nlinarith : |(m : ℚ)|⁻¹≤|(m : ℚ)|).trans harch
    · change (padicNorm 2 (m : ℚ))⁻¹≤_
      apply le_trans _ hmax
      apply (inv_le_iff_one_le_mul₀ hp2).mpr
      have hb : p≤|(m : ℚ)| *padicNorm 2 (m : ℚ) := by nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos ha hp2).le]
      have hh := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hp).le
      rw [inv_mul_cancel₀ hp.ne'] at hh
      nlinarith
    · change (padicNorm 3 (m : ℚ))⁻¹≤_
      apply le_trans _ hmax
      apply (inv_le_iff_one_le_mul₀ hp3).mpr
      have hb : p≤|(m : ℚ)| *padicNorm 3 (m : ℚ) := by nlinarith [mul_le_mul_of_nonneg_left h2 (mul_pos ha hp3).le]
      have hh := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hp).le
      rw [inv_mul_cancel₀ hp.ne'] at hh
      nlinarith
  · intro ht
    fin_cases tau
    · exact (ht rfl).elim
    · exact h2
    · exact h3

end JSP000334
