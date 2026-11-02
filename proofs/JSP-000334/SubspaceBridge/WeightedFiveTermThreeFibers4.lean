import SubspaceBridge.WeightedFiveTermPairFibers4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_five_ratios_012_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r t : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 1 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ) ∧
      ((u 2 : ℚˣ) : ℚ)=t*((u 0 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 1 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ) ∧
      ((u 2 : ℚˣ) : ℚ)=t*((u 0 : ℚˣ) : ℚ)}
  let C := B 0+B 1*r+B 2*t
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hu.1.2 ({1,2,3} : Finset (Fin 5)) (by decide) (by decide)
    apply False.elim
    apply hh
    have hz : B 0*((u 0 : ℚˣ) : ℚ)+B 1*((u 1 : ℚˣ) : ℚ)+B 2*((u 2 : ℚˣ) : ℚ)=0 := by
      rw [hu.2.1,hu.2.2]
      change B 0*_+B 1*(_*_)+B 2*(_*_)=0
      dsimp [C] at hC
      linear_combination ((u 0 : ℚˣ) : ℚ)*hC
    simpa [weightedFiveTerms4,Finset.sum_insert,add_assoc] using hz
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 0,u 3)
    have himage : (f '' S).Finite := by
      apply (weighted_fixed_sunit_pair_finite A C (B 3) hA hC (hB 3)).subset
      rintro _ ⟨u,hu,rfl⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      change A+C*((u 0 : ℚˣ) : ℚ)+B 3*((u 3 : ℚˣ) : ℚ)=0
      rw [hu.2.1,hu.2.2] at hs
      dsimp [C]
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 0=v 0 := congrArg Prod.fst he
    have h1 : u 3=v 3 := congrArg Prod.snd he
    have h2 : u 1=v 1 := weighted_unit_injective4 (by rw [hu.2.1,hv.2.1,h0])
    have h3 : u 2=v 2 := weighted_unit_injective4 (by rw [hu.2.2,hv.2.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_three_012_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (b c d : ℚ) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {u∈WeightedFiveTermSolutions A B | b*((u 0 : ℚˣ) : ℚ)+c*((u 1 : ℚˣ) : ℚ)+d*((u 2 : ℚˣ) : ℚ)=0}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | b*((u 0 : ℚˣ) : ℚ)+c*((u 1 : ℚˣ) : ℚ)+d*((u 2 : ℚˣ) : ℚ)=0}
  let f (u : Fin 4 → fixedSUnitGroup) := (u 1/u 0,u 2/u 0)
  have hf (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) : f u∈weightedFixedSUnitPairs b c d := by
    change b+c*(((u 1/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)+d*(((u 2/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)=0
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val]
    have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    field_simp
    nlinarith only [hu.2]
  have hU : (⋃ p∈weightedFixedSUnitPairs b c d,{u∈S | f u=p}).Finite := by
    apply (weighted_fixed_sunit_pair_finite b c d hb hc hd).biUnion
    intro p hp
    apply (weighted_five_ratios_012_finite4 A B hA hB ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro u hu
    have he1 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.1 : ℚˣ) : ℚ)) hu.2
    have he2 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.2 : ℚˣ) : ℚ)) hu.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val] at he1 he2
    have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    refine ⟨hu.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm
  apply hU.subset
  intro u hu
  exact Set.mem_iUnion.mpr ⟨f u,Set.mem_iUnion.mpr ⟨hf u hu,hu,rfl⟩⟩

theorem weighted_five_ratios_013_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r t : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 1 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ) ∧
      ((u 3 : ℚˣ) : ℚ)=t*((u 0 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 1 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ) ∧
      ((u 3 : ℚˣ) : ℚ)=t*((u 0 : ℚˣ) : ℚ)}
  let C := B 0+B 1*r+B 3*t
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hu.1.2 ({1,2,4} : Finset (Fin 5)) (by decide) (by decide)
    apply False.elim
    apply hh
    have hz : B 0*((u 0 : ℚˣ) : ℚ)+B 1*((u 1 : ℚˣ) : ℚ)+B 3*((u 3 : ℚˣ) : ℚ)=0 := by
      rw [hu.2.1,hu.2.2]
      change B 0*_+B 1*(_*_)+B 3*(_*_)=0
      dsimp [C] at hC
      linear_combination ((u 0 : ℚˣ) : ℚ)*hC
    simpa [weightedFiveTerms4,Finset.sum_insert,add_assoc] using hz
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 0,u 2)
    have himage : (f '' S).Finite := by
      apply (weighted_fixed_sunit_pair_finite A C (B 2) hA hC (hB 2)).subset
      rintro _ ⟨u,hu,rfl⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      change A+C*((u 0 : ℚˣ) : ℚ)+B 2*((u 2 : ℚˣ) : ℚ)=0
      rw [hu.2.1,hu.2.2] at hs
      dsimp [C]
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 0=v 0 := congrArg Prod.fst he
    have h1 : u 2=v 2 := congrArg Prod.snd he
    have h2 : u 1=v 1 := weighted_unit_injective4 (by rw [hu.2.1,hv.2.1,h0])
    have h3 : u 3=v 3 := weighted_unit_injective4 (by rw [hu.2.2,hv.2.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_three_013_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (b c d : ℚ) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {u∈WeightedFiveTermSolutions A B | b*((u 0 : ℚˣ) : ℚ)+c*((u 1 : ℚˣ) : ℚ)+d*((u 3 : ℚˣ) : ℚ)=0}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | b*((u 0 : ℚˣ) : ℚ)+c*((u 1 : ℚˣ) : ℚ)+d*((u 3 : ℚˣ) : ℚ)=0}
  let f (u : Fin 4 → fixedSUnitGroup) := (u 1/u 0,u 3/u 0)
  have hf (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) : f u∈weightedFixedSUnitPairs b c d := by
    change b+c*(((u 1/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)+d*(((u 3/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)=0
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val]
    have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    field_simp
    nlinarith only [hu.2]
  have hU : (⋃ p∈weightedFixedSUnitPairs b c d,{u∈S | f u=p}).Finite := by
    apply (weighted_fixed_sunit_pair_finite b c d hb hc hd).biUnion
    intro p hp
    apply (weighted_five_ratios_013_finite4 A B hA hB ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro u hu
    have he1 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.1 : ℚˣ) : ℚ)) hu.2
    have he2 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.2 : ℚˣ) : ℚ)) hu.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val] at he1 he2
    have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    refine ⟨hu.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm
  apply hU.subset
  intro u hu
  exact Set.mem_iUnion.mpr ⟨f u,Set.mem_iUnion.mpr ⟨hf u hu,hu,rfl⟩⟩

theorem weighted_five_ratios_023_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r t : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ) ∧
      ((u 3 : ℚˣ) : ℚ)=t*((u 0 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ) ∧
      ((u 3 : ℚˣ) : ℚ)=t*((u 0 : ℚˣ) : ℚ)}
  let C := B 0+B 2*r+B 3*t
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hu.1.2 ({1,3,4} : Finset (Fin 5)) (by decide) (by decide)
    apply False.elim
    apply hh
    have hz : B 0*((u 0 : ℚˣ) : ℚ)+B 2*((u 2 : ℚˣ) : ℚ)+B 3*((u 3 : ℚˣ) : ℚ)=0 := by
      rw [hu.2.1,hu.2.2]
      change B 0*_+B 2*(_*_)+B 3*(_*_)=0
      dsimp [C] at hC
      linear_combination ((u 0 : ℚˣ) : ℚ)*hC
    simpa [weightedFiveTerms4,Finset.sum_insert,add_assoc] using hz
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 0,u 1)
    have himage : (f '' S).Finite := by
      apply (weighted_fixed_sunit_pair_finite A C (B 1) hA hC (hB 1)).subset
      rintro _ ⟨u,hu,rfl⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      change A+C*((u 0 : ℚˣ) : ℚ)+B 1*((u 1 : ℚˣ) : ℚ)=0
      rw [hu.2.1,hu.2.2] at hs
      dsimp [C]
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 0=v 0 := congrArg Prod.fst he
    have h1 : u 1=v 1 := congrArg Prod.snd he
    have h2 : u 2=v 2 := weighted_unit_injective4 (by rw [hu.2.1,hv.2.1,h0])
    have h3 : u 3=v 3 := weighted_unit_injective4 (by rw [hu.2.2,hv.2.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_three_023_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (b c d : ℚ) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {u∈WeightedFiveTermSolutions A B | b*((u 0 : ℚˣ) : ℚ)+c*((u 2 : ℚˣ) : ℚ)+d*((u 3 : ℚˣ) : ℚ)=0}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | b*((u 0 : ℚˣ) : ℚ)+c*((u 2 : ℚˣ) : ℚ)+d*((u 3 : ℚˣ) : ℚ)=0}
  let f (u : Fin 4 → fixedSUnitGroup) := (u 2/u 0,u 3/u 0)
  have hf (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) : f u∈weightedFixedSUnitPairs b c d := by
    change b+c*(((u 2/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)+d*(((u 3/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)=0
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val]
    have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    field_simp
    nlinarith only [hu.2]
  have hU : (⋃ p∈weightedFixedSUnitPairs b c d,{u∈S | f u=p}).Finite := by
    apply (weighted_fixed_sunit_pair_finite b c d hb hc hd).biUnion
    intro p hp
    apply (weighted_five_ratios_023_finite4 A B hA hB ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro u hu
    have he1 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.1 : ℚˣ) : ℚ)) hu.2
    have he2 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.2 : ℚˣ) : ℚ)) hu.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val] at he1 he2
    have hn : ((u 0 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    refine ⟨hu.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm
  apply hU.subset
  intro u hu
  exact Set.mem_iUnion.mpr ⟨f u,Set.mem_iUnion.mpr ⟨hf u hu,hu,rfl⟩⟩

theorem weighted_five_ratios_123_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r t : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 1 : ℚˣ) : ℚ) ∧
      ((u 3 : ℚˣ) : ℚ)=t*((u 1 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 1 : ℚˣ) : ℚ) ∧
      ((u 3 : ℚˣ) : ℚ)=t*((u 1 : ℚˣ) : ℚ)}
  let C := B 1+B 2*r+B 3*t
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hu.1.2 ({2,3,4} : Finset (Fin 5)) (by decide) (by decide)
    apply False.elim
    apply hh
    have hz : B 1*((u 1 : ℚˣ) : ℚ)+B 2*((u 2 : ℚˣ) : ℚ)+B 3*((u 3 : ℚˣ) : ℚ)=0 := by
      rw [hu.2.1,hu.2.2]
      change B 1*_+B 2*(_*_)+B 3*(_*_)=0
      dsimp [C] at hC
      linear_combination ((u 1 : ℚˣ) : ℚ)*hC
    simpa [weightedFiveTerms4,Finset.sum_insert,add_assoc] using hz
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 1,u 0)
    have himage : (f '' S).Finite := by
      apply (weighted_fixed_sunit_pair_finite A C (B 0) hA hC (hB 0)).subset
      rintro _ ⟨u,hu,rfl⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      change A+C*((u 1 : ℚˣ) : ℚ)+B 0*((u 0 : ℚˣ) : ℚ)=0
      rw [hu.2.1,hu.2.2] at hs
      dsimp [C]
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 1=v 1 := congrArg Prod.fst he
    have h1 : u 0=v 0 := congrArg Prod.snd he
    have h2 : u 2=v 2 := weighted_unit_injective4 (by rw [hu.2.1,hv.2.1,h0])
    have h3 : u 3=v 3 := weighted_unit_injective4 (by rw [hu.2.2,hv.2.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_three_123_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (b c d : ℚ) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {u∈WeightedFiveTermSolutions A B | b*((u 1 : ℚˣ) : ℚ)+c*((u 2 : ℚˣ) : ℚ)+d*((u 3 : ℚˣ) : ℚ)=0}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | b*((u 1 : ℚˣ) : ℚ)+c*((u 2 : ℚˣ) : ℚ)+d*((u 3 : ℚˣ) : ℚ)=0}
  let f (u : Fin 4 → fixedSUnitGroup) := (u 2/u 1,u 3/u 1)
  have hf (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) : f u∈weightedFixedSUnitPairs b c d := by
    change b+c*(((u 2/u 1 : fixedSUnitGroup) : ℚˣ) : ℚ)+d*(((u 3/u 1 : fixedSUnitGroup) : ℚˣ) : ℚ)=0
    simp only [Subgroup.coe_div,Units.val_div_eq_div_val]
    have hn : ((u 1 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    field_simp
    nlinarith only [hu.2]
  have hU : (⋃ p∈weightedFixedSUnitPairs b c d,{u∈S | f u=p}).Finite := by
    apply (weighted_fixed_sunit_pair_finite b c d hb hc hd).biUnion
    intro p hp
    apply (weighted_five_ratios_123_finite4 A B hA hB ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)).subset
    intro u hu
    have he1 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.1 : ℚˣ) : ℚ)) hu.2
    have he2 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.2 : ℚˣ) : ℚ)) hu.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val] at he1 he2
    have hn : ((u 1 : ℚˣ) : ℚ)≠0 := Units.ne_zero _
    refine ⟨hu.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm
  apply hU.subset
  intro u hu
  exact Set.mem_iUnion.mpr ⟨f u,Set.mem_iUnion.mpr ⟨hf u hu,hu,rfl⟩⟩

end JSP000334
