import SubspaceBridge.WeightedFourTermSource3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_diagonal_gcd_divides3 (t z : Fin 3 → ℤ) (hz : PrimitiveTriple z)
    (g : ℤ) (hg : ∀ i,g∣t i*z i) : g∣t 0*t 1*t 2 := by
  obtain ⟨c,hc⟩ := hz
  have hd (i : Fin 3) : g∣(t 0*t 1*t 2)*z i := by
    have h0 : g∣(t 0*t 1*t 2)*z 0 := by
      have hh := dvd_mul_of_dvd_right (hg 0) (t 1*t 2)
      convert hh using 1 <;> ring
    have h1 : g∣(t 0*t 1*t 2)*z 1 := by
      have hh := dvd_mul_of_dvd_right (hg 1) (t 0*t 2)
      convert hh using 1 <;> ring
    have h2 : g∣(t 0*t 1*t 2)*z 2 := by
      have hh := dvd_mul_of_dvd_right (hg 2) (t 0*t 1)
      convert hh using 1 <;> ring
    fin_cases i <;> assumption
  have hs : g∣∑ i,c i*((t 0*t 1*t 2)*z i) :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hd i) (c i))
  have he : (∑ i,c i*((t 0*t 1*t 2)*z i))=t 0*t 1*t 2 := by
    calc
      _=(t 0*t 1*t 2)*(∑ i,c i*z i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=_ := by rw [hc,mul_one]
  rwa [he] at hs

theorem weighted_diagonal_gcd_values_finite3 (t : Fin 3 → ℤ) (ht : ∀ i,t i≠0) :
    {g : ℕ | 0<g ∧ (g : ℤ)∣t 0*t 1*t 2}.Finite := by
  have hn : t 0*t 1*t 2≠0 := mul_ne_zero (mul_ne_zero (ht 0) (ht 1)) (ht 2)
  apply (Set.finite_Iic (t 0*t 1*t 2).natAbs).subset
  intro g hg
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natCast_dvd.mp hg.2)

def weightedIntegerDiagonal3 (t : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.diagonal (fun i => (t i : ℚ))

theorem weighted_diagonal_invertible3 (t : Fin 3 → ℤ) (ht : ∀ i,t i≠0) :
    IsUnit (weightedIntegerDiagonal3 t) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit (Matrix.diagonal (fun i => (t i : ℚ))).det
  rw [Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast ht i)

theorem weighted_fixed_product_height3 (y : Fin 3 → ℤ) (hy : PrimitiveTriple y)
    (k : Fin 3 → ℚ) (a : ℚ)
    (hk : ∀ i,threePlaceProduct (y i : ℚ)=threePlaceProduct (k i))
    (ha : threePlaceProduct ((y 0 : ℚ)+y 1+y 2)=threePlaceProduct a) :
    ∃ choice : Fin 3 → Fin 3,
      tripleChoiceFormsProduct choice (fun i => (y i : ℚ))*archTripleHeight y=
        threePlaceProduct (k 0)*threePlaceProduct (k 1)*threePlaceProduct (k 2)*threePlaceProduct a := by
  choose choice hc using fun v : Fin 3 => exists_maximal_triple_coordinate v (fun i => (y i : ℚ))
  refine ⟨choice,?_⟩
  have hh := triple_retained_product_height choice (fun i => (y i : ℚ)) hc
  rw [primitive_triple_height y hy] at hh
  rw [hk 0,hk 1,hk 2,ha] at hh
  exact hh

end JSP000334
