import SubspaceBridge.WeightedPrimitiveInput4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_diagonal_gcd_divides4 (t z : Fin 4 → ℤ) (hz : PrimitiveFour z)
    (g : ℤ) (hg : ∀ i,g∣t i*z i) : g∣∏ i,t i := by
  classical
  obtain ⟨c,hc⟩ := hz
  have hd (i : Fin 4) : g∣(∏ j,t j)*z i := by
    obtain ⟨r,hr⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
    rw [hr]
    have hh := dvd_mul_of_dvd_right (hg i) r
    convert hh using 1 <;> ring
  have hs : g∣∑ i,c i*((∏ j,t j)*z i) :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hd i) (c i))
  have he : (∑ i,c i*((∏ j,t j)*z i))=(∏ j,t j) := by
    calc
      _=(∏ j,t j)*(∑ i,c i*z i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=_ := by rw [hc,mul_one]
  rwa [he] at hs

theorem weighted_diagonal_gcd_values_finite4 (t : Fin 4 → ℤ) (ht : ∀ i,t i≠0) :
    {g : ℕ | 0<g ∧ (g : ℤ)∣∏ i,t i}.Finite := by
  have hn : (∏ i,t i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ht i)
  apply (Set.finite_Iic (∏ i,t i).natAbs).subset
  intro g hg
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natCast_dvd.mp hg.2)

def weightedIntegerDiagonal4 (t : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.diagonal (fun i => (t i : ℚ))

theorem weighted_diagonal_invertible4 (t : Fin 4 → ℤ) (ht : ∀ i,t i≠0) :
    IsUnit (weightedIntegerDiagonal4 t) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit (Matrix.diagonal (fun i => (t i : ℚ))).det
  rw [Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast ht i)

theorem weighted_diagonal_primitive4 (t z : Fin 4 → ℤ) (ht : ∀ i,t i≠0)
    (hz : PrimitiveFour z) (hzn : ∀ i,z i≠0) :
    ∃ g : ℕ,0<g ∧ (g : ℤ)∣(∏ i,t i) ∧ ∃ y : Fin 4 → ℤ,
      PrimitiveFour y ∧ (∀ i,y i≠0) ∧ ∀ i,t i*z i=(g : ℤ)*y i := by
  obtain ⟨g,hg,_,y,hy,he⟩ := primitive_four_integer_reduction (fun i => t i*z i) (mul_ne_zero (ht 0) (hzn 0))
  refine ⟨g,hg,weighted_diagonal_gcd_divides4 t z hz (g : ℤ) (fun i => ⟨y i,he i⟩),y,hy,?_,he⟩
  intro i hi
  have hh := he i
  rw [hi,mul_zero] at hh
  exact (mul_ne_zero (ht i) (hzn i)) hh

end JSP000334
