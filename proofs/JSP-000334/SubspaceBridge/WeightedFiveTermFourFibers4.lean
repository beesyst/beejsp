import SubspaceBridge.WeightedFiveTermThreeFibers4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_nondegenerate_scale4 {n : ℕ} (x : Fin n → ℚ) (hx : Nondegenerate x)
    (c : ℚ) (hc : c≠0) : Nondegenerate (fun i => c*x i) := by
  intro I hI hproper hz
  rw [← Finset.mul_sum] at hz
  exact hx I hI hproper ((mul_eq_zero.mp hz).resolve_left hc)

def weightedFiveCoefficientFiber4 (A : ℚ) (B b : Fin 4 → ℚ) : Set (Fin 4 → fixedSUnitGroup) :=
  {u∈WeightedFiveTermSolutions A B | ∑ i,b i*((u i : ℚˣ) : ℚ)=0}

theorem weighted_five_good_four_finite4 (A : ℚ) (B b : Fin 4 → ℚ)
    (hA : A≠0) (hb : ∀ i,b i≠0) :
    {u∈weightedFiveCoefficientFiber4 A B b |
      Nondegenerate (fun i => b i*((u i : ℚˣ) : ℚ))}.Finite := by
  let S := {u∈weightedFiveCoefficientFiber4 A B b |
      Nondegenerate (fun i => b i*((u i : ℚˣ) : ℚ))}
  let f (u : Fin 4 → fixedSUnitGroup) := (u 1/u 0,u 2/u 0,u 3/u 0)
  have himage : (f '' S).Finite := by
    apply (weighted_four_term_finite (b 0) (b 1) (b 2) (b 3) (hb 0) (hb 1) (hb 2) (hb 3)).subset
    rintro _ ⟨u,hu,rfl⟩
    have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    constructor
    · change b 0+b 1*(((u 1/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)+b 2*(((u 2/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)+b 3*(((u 3/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)=0
      simp only [Subgroup.coe_div,Units.val_div_eq_div_val]
      field_simp
      have hs := hu.1.2
      simp only [Fin.sum_univ_four] at hs
      nlinarith only [hs]
    · have hh := weighted_nondegenerate_scale4 _ hu.2 (((u 0 : ℚˣ) : ℚ))⁻¹ (inv_ne_zero hn)
      convert hh using 1
      ext i
      fin_cases i <;> simp [f,Subgroup.coe_div,Units.val_div_eq_div_val,div_eq_mul_inv,hn] <;> field_simp
  apply himage.of_finite_image
  intro u hu v hv he
  have hr1 : u 1/u 0=v 1/v 0 := congrArg Prod.fst he
  have hr2 : u 2/u 0=v 2/v 0 := congrArg (fun p => p.2.1) he
  have hr3 : u 3/u 0=v 3/v 0 := congrArg (fun p => p.2.2) he
  have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
  have hm : ((v 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
  have he1 : ((u 1 : ℚˣ) : ℚ)*((v 0 : ℚˣ) : ℚ)=((v 1 : ℚˣ) : ℚ)*((u 0 : ℚˣ) : ℚ) := by
    have hh := congrArg (fun q : fixedSUnitGroup => ((q : ℚˣ) : ℚ)) hr1
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val] at hh
    exact (div_eq_div_iff hn hm).mp hh
  have he2 : ((u 2 : ℚˣ) : ℚ)*((v 0 : ℚˣ) : ℚ)=((v 2 : ℚˣ) : ℚ)*((u 0 : ℚˣ) : ℚ) := by
    have hh := congrArg (fun q : fixedSUnitGroup => ((q : ℚˣ) : ℚ)) hr2
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val] at hh
    exact (div_eq_div_iff hn hm).mp hh
  have he3 : ((u 3 : ℚˣ) : ℚ)*((v 0 : ℚˣ) : ℚ)=((v 3 : ℚˣ) : ℚ)*((u 0 : ℚˣ) : ℚ) := by
    have hh := congrArg (fun q : fixedSUnitGroup => ((q : ℚˣ) : ℚ)) hr3
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val] at hh
    exact (div_eq_div_iff hn hm).mp hh
  have hsu := hu.1.1.1
  have hsv := hv.1.1.1
  simp only [Fin.sum_univ_four] at hsu hsv
  have hz : A*(((v 0 : ℚˣ) : ℚ)-((u 0 : ℚˣ) : ℚ))=0 := by
    linear_combination ((v 0 : ℚˣ) : ℚ)*hsu-((u 0 : ℚˣ) : ℚ)*hsv-B 1*he1-B 2*he2-B 3*he3
  have h0 : u 0=v 0 := weighted_unit_injective4 (by
    have hh := (mul_eq_zero.mp hz).resolve_left hA
    linarith)
  funext i
  fin_cases i
  · exact h0
  · calc
      u 1=(u 1/u 0)*u 0 := (div_mul_cancel _ _).symm
      _=(v 1/v 0)*v 0 := by rw [hr1,h0]
      _=v 1 := div_mul_cancel _ _
  · calc
      u 2=(u 2/u 0)*u 0 := (div_mul_cancel _ _).symm
      _=(v 2/v 0)*v 0 := by rw [hr2,h0]
      _=v 2 := div_mul_cancel _ _
  · calc
      u 3=(u 3/u 0)*u 0 := (div_mul_cancel _ _).symm
      _=(v 3/v 0)*v 0 := by rw [hr3,h0]
      _=v 3 := div_mul_cancel _ _

theorem weighted_five_four_finite4 (A : ℚ) (B b : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (hb : ∀ i,b i≠0) :
    (weightedFiveCoefficientFiber4 A B b).Finite := by
  have hgood := weighted_five_good_four_finite4 A B b hA hb
  have hU := ((hgood.union (weighted_five_pair_01_finite4 A B hA hB (-b 0/b 1))).union
    (weighted_five_pair_02_finite4 A B hA hB (-b 0/b 2))).union
    (weighted_five_pair_03_finite4 A B hA hB (-b 0/b 3))
  apply hU.subset
  intro u hu
  by_cases hn : Nondegenerate (fun i => b i*((u i : ℚˣ) : ℚ))
  · exact Or.inl (Or.inl (Or.inl ⟨hu,hn⟩))
  · have hs := hu.2
    simp only [Fin.sum_univ_four] at hs
    have hn' : ¬Nondegenerate (![b 0*((u 0 : ℚˣ) : ℚ),b 1*((u 1 : ℚˣ) : ℚ),b 2*((u 2 : ℚˣ) : ℚ),b 3*((u 3 : ℚˣ) : ℚ)] : Fin 4 → ℚ) := by
      have he : (![b 0*((u 0 : ℚˣ) : ℚ),b 1*((u 1 : ℚˣ) : ℚ),b 2*((u 2 : ℚˣ) : ℚ),b 3*((u 3 : ℚˣ) : ℚ)] : Fin 4 → ℚ)=(fun i => b i*((u i : ℚˣ) : ℚ)) := by
        ext i
        fin_cases i <;> rfl
      rwa [he]
    obtain hp|hp|hp := five_term_weighted_degenerate_pair4 _ _ _ _
      (mul_ne_zero (hb 0) (Units.ne_zero _)) (mul_ne_zero (hb 1) (Units.ne_zero _))
      (mul_ne_zero (hb 2) (Units.ne_zero _)) (mul_ne_zero (hb 3) (Units.ne_zero _)) hs hn'
    · refine Or.inl (Or.inl (Or.inr ?_))
      refine ⟨hu.1,?_⟩
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (hb 1)).mpr
      nlinarith only [hp]
    · refine Or.inl (Or.inr ?_)
      refine ⟨hu.1,?_⟩
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (hb 2)).mpr
      nlinarith only [hp]
    · refine Or.inr ?_
      refine ⟨hu.1,?_⟩
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (hb 3)).mpr
      nlinarith only [hp]

end JSP000334
