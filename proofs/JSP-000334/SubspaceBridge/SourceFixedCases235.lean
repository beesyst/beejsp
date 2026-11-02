import SubspaceBridge.SourceFixedReference234
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedGeometry235
open SourceFixedArithmetic234 SourceSelectedUpper10 SourceGlobalSelected10 SourceSatz51Entry218

theorem supported_padic_nonzero235 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A) (v : Fin 10 → ℤ)
    (j : Fin 10) (hj : j ∈ dualSupport234 A v) :
    ((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ (fun k => (v k : ℚ_[p]))) j ≠ 0 := by
  rw [rational_padic_coordinates234 p A hA v j]
  exact (map_ne_zero_iff _ (algebraMap ℚ ℚ_[p]).injective).mpr (Finset.mem_filter.mp hj).2

theorem selected_coordinate_zero235
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (h2 : IsUnit A2) (h3 : IsUnit A3)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (v : Fin 10 → ℤ)
    (S : Finset (Fin 3 → Fin 10)) (hz : ∀ s ∈ S, mixedProduct10 A2 A3 L v s = 0)
    (i : Fin 10) (hs : ∃ j2 ∈ dualSupport234 A2 v, ∃ j3 ∈ dualSupport234 A3 v,
      ![i,j2,j3] ∈ S) : (L⁻¹.transpose *ᵥ integerReal v) i = 0 := by
  obtain ⟨j2,hj2,j3,hj3,hs⟩ := hs
  have h2p := supported_padic_nonzero235 2 A2 h2 v j2 hj2
  have h3p := supported_padic_nonzero235 3 A3 h3 v j3 hj3
  by_contra hn
  have hh := (mixedProduct10_ne_zero_iff A2 A3 L v ![i,j2,j3]).mpr
    (by simpa using And.intro hn (And.intro h2p h3p))
  exact hh (hz _ hs)

theorem source_complement235 (q delta : ℝ) (hq : 1 < q) (A c2 c3 : Fin 10 → ℝ)
    (hA : ∀ i, 0 < A i) (S : Finset (Fin 3 → Fin 10))
    (hS : sourceSet218 q delta A c2 c3 = S) (i j2 j3 : Fin 10)
    (hs : ![i,j2,j3] ∉ S) :
    A i*q^(c2 j2+c3 j3)*q^(delta/4) < 1 ∧
      q^(c2 j2+c3 j3) < 1/(A i*q^(delta/4)) := by
  have hh : A i*q^(c2 j2)*q^(c3 j3)*q^(delta/4) < 1 := by
    apply lt_of_not_ge
    intro he
    apply hs
    rw [← hS]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using he⟩
  have he : A i*q^(c2 j2+c3 j3)*q^(delta/4) < 1 := by
    rwa [Real.rpow_add (zero_lt_one.trans hq),← mul_assoc]
  refine ⟨he,?_⟩
  apply (lt_div_iff₀ (mul_pos (hA i) (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _))).mpr
  nlinarith only [he]

theorem width_product235 (q : ℝ) (hq : 1 < q) (A c2 c3 : Fin 10 → ℝ)
    (hb : (∏ i, A i*q^(c2 i)*q^(c3 i)) = 1) :
    (∏ i, A i) = q^(-(∑ i, c2 i)-(∑ i, c3 i)) := by
  have hp := zero_lt_one.trans hq
  have he : (∏ i, q^(c2 i)*q^(c3 i)) = q^((∑ i, c2 i)+(∑ i, c3 i)) := by
    simp_rw [← Real.rpow_add hp]
    rw [← Real.rpow_sum_of_pos hp,Finset.sum_add_distrib]
  have hm : (∏ i, A i)*q^((∑ i, c2 i)+(∑ i, c3 i)) = 1 := by
    rw [← he]
    simpa only [Finset.prod_mul_distrib,mul_assoc] using hb
  apply mul_right_cancel₀ (Real.rpow_pos_of_pos hp ((∑ i, c2 i)+(∑ i, c3 i))).ne'
  rw [hm,← Real.rpow_add hp]
  convert (Real.rpow_zero q).symm using 1 <;> congr 1 <;> ring

theorem complement_coordinate_bound235 (q : ℝ) (hq : 1 < q) (delta : ℝ)
    (A c2 c3 : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (hb : (∏ i, A i*q^(c2 i)*q^(c3 i)) = 1) (d : ℝ)
    (hcov : (∏ i, A i) ≤ d) (K a t : ℝ) (hK : 0 ≤ K) (i j2 j3 : Fin 10)
    (ht : t ≤ K*q^(-(∑ k, c2 k)-(∑ k, c3 k)+c2 j2+c3 j3))
    (hs : A i*q^(c2 j2+c3 j3)*q^(delta/4) < 1) :
    t* |a| ≤ K* |a| *q^(-delta/4)*d/A i := by
  have hp := zero_lt_one.trans hq
  have hd : 0 ≤ d := (Finset.prod_pos (fun j _ => hA j)).le.trans hcov
  have he : q^(-(∑ k, c2 k)-(∑ k, c3 k)+c2 j2+c3 j3) =
      (∏ k, A k)*q^(c2 j2+c3 j3) := by
    rw [width_product235 q hq A c2 c3 hb,← Real.rpow_add hp]
    congr 1
    ring
  rw [he] at ht
  have hr : q^(delta/4)*q^(-delta/4) = 1 := by
    rw [← Real.rpow_add hp]
    convert Real.rpow_zero q using 1 <;> congr 1 <;> ring
  have hAu : A i*q^(c2 j2+c3 j3) ≤ q^(-delta/4) := by
    calc
      _ = (A i*q^(c2 j2+c3 j3)*q^(delta/4))*q^(-delta/4) := by
        rw [mul_assoc,hr,mul_one]
      _ ≤ 1*q^(-delta/4) := mul_le_mul_of_nonneg_right hs.le (Real.rpow_pos_of_pos hp _).le
      _ = _ := one_mul _
  have hu : q^(c2 j2+c3 j3) ≤ q^(-delta/4)/A i :=
    (le_div_iff₀ (hA i)).mpr (by nlinarith only [hAu])
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul hcov hu (Real.rpow_pos_of_pos hp _).le hd) hK) (abs_nonneg a)
  calc
    _ ≤ (K*((∏ k, A k)*q^(c2 j2+c3 j3)))* |a| := mul_le_mul_of_nonneg_right ht (abs_nonneg a)
    _ ≤ (K*(d*(q^(-delta/4)/A i)))* |a| := hh
    _ = _ := by ring

theorem coefficient_bound235 (a : Fin 10 → ℝ) :
    0 < 1+∑ i, |a i| ∧ ∀ i, |a i| ≤ 1+∑ j, |a j| := by
  have hs : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨by linarith,?_⟩
  intro i
  have hi : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum (f := fun j => |a j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

theorem fixed_cutoff235 (delta : ℝ) (hd : 0 < delta) (K : ℝ) (hK : 0 < K) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : ℝ, T < q → K*q^(-delta/4) ≤ 1 := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_neg_atTop (show 0 < delta/4 by linarith)).eventually
      (gt_mem_nhds (one_div_pos.mpr hK)))
  refine ⟨max B 2,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro q hq
  have hh := (lt_div_iff₀ hK).mp (hB q ((le_max_left B 2).trans hq.le))
  rw [show -delta/4 = -(delta/4) by ring]
  nlinarith


end CompoundFeasibility.SourceFixedGeometry235
