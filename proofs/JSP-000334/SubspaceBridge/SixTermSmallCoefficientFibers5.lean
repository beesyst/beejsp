import SubspaceBridge.SixTermRatioFibers5
namespace JSP000334
open scoped BigOperators Matrix

theorem six_term_constant_12_good5 (a b c : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 1,sixTermUnit5 x 2)
  have hU : (⋃ q∈weightedFixedSUnitPairs a b c,{x∈S | f x=q}).Finite := by
    apply (weighted_fixed_sunit_pair_finite a b c ha hb hc).biUnion
    intro q hq
    apply (six_term_fixed_12_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 1 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 2 : ℚˣ) : ℚ)=0
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_13_good5 (a b c : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 3=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 3=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 1,sixTermUnit5 x 3)
  have hU : (⋃ q∈weightedFixedSUnitPairs a b c,{x∈S | f x=q}).Finite := by
    apply (weighted_fixed_sunit_pair_finite a b c ha hb hc).biUnion
    intro q hq
    apply (six_term_fixed_13_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 1 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 3 : ℚˣ) : ℚ)=0
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_14_good5 (a b c : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 4=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 4=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 1,sixTermUnit5 x 4)
  have hU : (⋃ q∈weightedFixedSUnitPairs a b c,{x∈S | f x=q}).Finite := by
    apply (weighted_fixed_sunit_pair_finite a b c ha hb hc).biUnion
    intro q hq
    apply (six_term_fixed_14_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 1 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 4 : ℚˣ) : ℚ)=0
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_23_good5 (a b c : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 2+c*x 3=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 2+c*x 3=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 2,sixTermUnit5 x 3)
  have hU : (⋃ q∈weightedFixedSUnitPairs a b c,{x∈S | f x=q}).Finite := by
    apply (weighted_fixed_sunit_pair_finite a b c ha hb hc).biUnion
    intro q hq
    apply (six_term_fixed_23_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 2 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 3 : ℚˣ) : ℚ)=0
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_24_good5 (a b c : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 2+c*x 4=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 2+c*x 4=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 2,sixTermUnit5 x 4)
  have hU : (⋃ q∈weightedFixedSUnitPairs a b c,{x∈S | f x=q}).Finite := by
    apply (weighted_fixed_sunit_pair_finite a b c ha hb hc).biUnion
    intro q hq
    apply (six_term_fixed_24_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 2 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 4 : ℚˣ) : ℚ)=0
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_34_good5 (a b c : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 3+c*x 4=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 3+c*x 4=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 3,sixTermUnit5 x 4)
  have hU : (⋃ q∈weightedFixedSUnitPairs a b c,{x∈S | f x=q}).Finite := by
    apply (weighted_fixed_sunit_pair_finite a b c ha hb hc).biUnion
    intro q hq
    apply (six_term_fixed_34_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 3 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 4 : ℚˣ) : ℚ)=0
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_123_good5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2+d*x 3=0 ∧ Nondegenerate (![a,b*x 1,c*x 2,d*x 3] : Fin 4 → ℚ)}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2+d*x 3=0 ∧ Nondegenerate (![a,b*x 1,c*x 2,d*x 3] : Fin 4 → ℚ)}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 1,sixTermUnit5 x 2,sixTermUnit5 x 3)
  have hU : (⋃ q∈WeightedFourTermSolutions a b c d,{x∈S | f x=q}).Finite := by
    apply (weighted_four_term_finite a b c d ha hb hc hd).biUnion
    intro q hq
    apply (six_term_fixed_123_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2.1 : ℚˣ) : ℚ) ((q.2.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1,by simpa only [f,six_term_unit_value5 hx.1.1] using he2⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 1 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 2 : ℚˣ) : ℚ)+d*((sixTermUnit5 x 3 : ℚˣ) : ℚ)=0 ∧ Nondegenerate (![a,b*((sixTermUnit5 x 1 : ℚˣ) : ℚ),c*((sixTermUnit5 x 2 : ℚˣ) : ℚ),d*((sixTermUnit5 x 3 : ℚˣ) : ℚ)] : Fin 4 → ℚ)
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_123_finite5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2+d*x 3=0}.Finite := by
  have hg := six_term_constant_123_good5 a b c d ha hb hc hd
  have hU := (((hg.union (six_term_fixed_1_finite5 (-a/b))).union (six_term_fixed_2_finite5 (-a/c))).union (six_term_fixed_3_finite5 (-a/d)))
  apply hU.subset
  intro x hx
  by_cases hn : Nondegenerate (![a,b*x 1,c*x 2,d*x 3] : Fin 4 → ℚ)
  · exact Or.inl (Or.inl (Or.inl ⟨hx.1,hx.2,hn⟩))
  · have hxn := (six_term_relation_facts5 hx.1).2.2
    obtain hp|hp|hp := five_term_weighted_degenerate_pair4 _ _ _ _ ha
      (mul_ne_zero hb (hxn 1))
      (mul_ne_zero hc (hxn 2))
      (mul_ne_zero hd (hxn 3))
      hx.2 hn
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact ⟨hx.1,(eq_div_iff hb).mpr (by nlinarith only [hp])⟩
    · refine Or.inl (Or.inr ?_)
      exact ⟨hx.1,(eq_div_iff hc).mpr (by nlinarith only [hp])⟩
    · refine Or.inr ?_
      exact ⟨hx.1,(eq_div_iff hd).mpr (by nlinarith only [hp])⟩

theorem six_term_constant_124_good5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2+d*x 4=0 ∧ Nondegenerate (![a,b*x 1,c*x 2,d*x 4] : Fin 4 → ℚ)}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2+d*x 4=0 ∧ Nondegenerate (![a,b*x 1,c*x 2,d*x 4] : Fin 4 → ℚ)}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 1,sixTermUnit5 x 2,sixTermUnit5 x 4)
  have hU : (⋃ q∈WeightedFourTermSolutions a b c d,{x∈S | f x=q}).Finite := by
    apply (weighted_four_term_finite a b c d ha hb hc hd).biUnion
    intro q hq
    apply (six_term_fixed_124_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2.1 : ℚˣ) : ℚ) ((q.2.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1,by simpa only [f,six_term_unit_value5 hx.1.1] using he2⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 1 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 2 : ℚˣ) : ℚ)+d*((sixTermUnit5 x 4 : ℚˣ) : ℚ)=0 ∧ Nondegenerate (![a,b*((sixTermUnit5 x 1 : ℚˣ) : ℚ),c*((sixTermUnit5 x 2 : ℚˣ) : ℚ),d*((sixTermUnit5 x 4 : ℚˣ) : ℚ)] : Fin 4 → ℚ)
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_124_finite5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 2+d*x 4=0}.Finite := by
  have hg := six_term_constant_124_good5 a b c d ha hb hc hd
  have hU := (((hg.union (six_term_fixed_1_finite5 (-a/b))).union (six_term_fixed_2_finite5 (-a/c))).union (six_term_fixed_4_finite5 (-a/d)))
  apply hU.subset
  intro x hx
  by_cases hn : Nondegenerate (![a,b*x 1,c*x 2,d*x 4] : Fin 4 → ℚ)
  · exact Or.inl (Or.inl (Or.inl ⟨hx.1,hx.2,hn⟩))
  · have hxn := (six_term_relation_facts5 hx.1).2.2
    obtain hp|hp|hp := five_term_weighted_degenerate_pair4 _ _ _ _ ha
      (mul_ne_zero hb (hxn 1))
      (mul_ne_zero hc (hxn 2))
      (mul_ne_zero hd (hxn 4))
      hx.2 hn
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact ⟨hx.1,(eq_div_iff hb).mpr (by nlinarith only [hp])⟩
    · refine Or.inl (Or.inr ?_)
      exact ⟨hx.1,(eq_div_iff hc).mpr (by nlinarith only [hp])⟩
    · refine Or.inr ?_
      exact ⟨hx.1,(eq_div_iff hd).mpr (by nlinarith only [hp])⟩

theorem six_term_constant_134_good5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 3+d*x 4=0 ∧ Nondegenerate (![a,b*x 1,c*x 3,d*x 4] : Fin 4 → ℚ)}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 3+d*x 4=0 ∧ Nondegenerate (![a,b*x 1,c*x 3,d*x 4] : Fin 4 → ℚ)}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 1,sixTermUnit5 x 3,sixTermUnit5 x 4)
  have hU : (⋃ q∈WeightedFourTermSolutions a b c d,{x∈S | f x=q}).Finite := by
    apply (weighted_four_term_finite a b c d ha hb hc hd).biUnion
    intro q hq
    apply (six_term_fixed_134_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2.1 : ℚˣ) : ℚ) ((q.2.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1,by simpa only [f,six_term_unit_value5 hx.1.1] using he2⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 1 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 3 : ℚˣ) : ℚ)+d*((sixTermUnit5 x 4 : ℚˣ) : ℚ)=0 ∧ Nondegenerate (![a,b*((sixTermUnit5 x 1 : ℚˣ) : ℚ),c*((sixTermUnit5 x 3 : ℚˣ) : ℚ),d*((sixTermUnit5 x 4 : ℚˣ) : ℚ)] : Fin 4 → ℚ)
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_134_finite5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 1+c*x 3+d*x 4=0}.Finite := by
  have hg := six_term_constant_134_good5 a b c d ha hb hc hd
  have hU := (((hg.union (six_term_fixed_1_finite5 (-a/b))).union (six_term_fixed_3_finite5 (-a/c))).union (six_term_fixed_4_finite5 (-a/d)))
  apply hU.subset
  intro x hx
  by_cases hn : Nondegenerate (![a,b*x 1,c*x 3,d*x 4] : Fin 4 → ℚ)
  · exact Or.inl (Or.inl (Or.inl ⟨hx.1,hx.2,hn⟩))
  · have hxn := (six_term_relation_facts5 hx.1).2.2
    obtain hp|hp|hp := five_term_weighted_degenerate_pair4 _ _ _ _ ha
      (mul_ne_zero hb (hxn 1))
      (mul_ne_zero hc (hxn 3))
      (mul_ne_zero hd (hxn 4))
      hx.2 hn
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact ⟨hx.1,(eq_div_iff hb).mpr (by nlinarith only [hp])⟩
    · refine Or.inl (Or.inr ?_)
      exact ⟨hx.1,(eq_div_iff hc).mpr (by nlinarith only [hp])⟩
    · refine Or.inr ?_
      exact ⟨hx.1,(eq_div_iff hd).mpr (by nlinarith only [hp])⟩

theorem six_term_constant_234_good5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 2+c*x 3+d*x 4=0 ∧ Nondegenerate (![a,b*x 2,c*x 3,d*x 4] : Fin 4 → ℚ)}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 2+c*x 3+d*x 4=0 ∧ Nondegenerate (![a,b*x 2,c*x 3,d*x 4] : Fin 4 → ℚ)}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 2,sixTermUnit5 x 3,sixTermUnit5 x 4)
  have hU : (⋃ q∈WeightedFourTermSolutions a b c d,{x∈S | f x=q}).Finite := by
    apply (weighted_four_term_finite a b c d ha hb hc hd).biUnion
    intro q hq
    apply (six_term_fixed_234_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2.1 : ℚˣ) : ℚ) ((q.2.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he0 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup× fixedSUnitGroup => ((p.2.2 : ℚˣ) : ℚ)) hx.2
    refine ⟨hx.1.1,by simpa only [f,six_term_unit_value5 hx.1.1] using he0,by simpa only [f,six_term_unit_value5 hx.1.1] using he1,by simpa only [f,six_term_unit_value5 hx.1.1] using he2⟩
  apply hU.subset
  intro x hx
  refine Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨?_,hx,rfl⟩⟩
  change a+b*((sixTermUnit5 x 2 : ℚˣ) : ℚ)+c*((sixTermUnit5 x 3 : ℚˣ) : ℚ)+d*((sixTermUnit5 x 4 : ℚˣ) : ℚ)=0 ∧ Nondegenerate (![a,b*((sixTermUnit5 x 2 : ℚˣ) : ℚ),c*((sixTermUnit5 x 3 : ℚˣ) : ℚ),d*((sixTermUnit5 x 4 : ℚˣ) : ℚ)] : Fin 4 → ℚ)
  simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
  exact hx.2

theorem six_term_constant_234_finite5 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a+b*x 2+c*x 3+d*x 4=0}.Finite := by
  have hg := six_term_constant_234_good5 a b c d ha hb hc hd
  have hU := (((hg.union (six_term_fixed_2_finite5 (-a/b))).union (six_term_fixed_3_finite5 (-a/c))).union (six_term_fixed_4_finite5 (-a/d)))
  apply hU.subset
  intro x hx
  by_cases hn : Nondegenerate (![a,b*x 2,c*x 3,d*x 4] : Fin 4 → ℚ)
  · exact Or.inl (Or.inl (Or.inl ⟨hx.1,hx.2,hn⟩))
  · have hxn := (six_term_relation_facts5 hx.1).2.2
    obtain hp|hp|hp := five_term_weighted_degenerate_pair4 _ _ _ _ ha
      (mul_ne_zero hb (hxn 2))
      (mul_ne_zero hc (hxn 3))
      (mul_ne_zero hd (hxn 4))
      hx.2 hn
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact ⟨hx.1,(eq_div_iff hb).mpr (by nlinarith only [hp])⟩
    · refine Or.inl (Or.inr ?_)
      exact ⟨hx.1,(eq_div_iff hc).mpr (by nlinarith only [hp])⟩
    · refine Or.inr ?_
      exact ⟨hx.1,(eq_div_iff hd).mpr (by nlinarith only [hp])⟩

theorem six_term_homogeneous_123_finite5 (a b c : ℚ) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 2+c*x 3=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 2+c*x 3=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 2/sixTermUnit5 x 1,sixTermUnit5 x 3/sixTermUnit5 x 1)
  apply six_term_finite_over_pairs5 S f a b c ha hb hc
  · intro x hx
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
    have hn := (six_term_relation_facts5 hx.1).2.2 1
    field_simp
    nlinarith only [hx.2]
  · intro q hq
    apply (six_term_ratios_123_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1.1] at he1 he2
    have hn := (six_term_relation_facts5 hx.1.1).2.2 1
    refine ⟨hx.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm

theorem six_term_homogeneous_124_finite5 (a b c : ℚ) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 2+c*x 4=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 2+c*x 4=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 2/sixTermUnit5 x 1,sixTermUnit5 x 4/sixTermUnit5 x 1)
  apply six_term_finite_over_pairs5 S f a b c ha hb hc
  · intro x hx
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
    have hn := (six_term_relation_facts5 hx.1).2.2 1
    field_simp
    nlinarith only [hx.2]
  · intro q hq
    apply (six_term_ratios_124_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1.1] at he1 he2
    have hn := (six_term_relation_facts5 hx.1.1).2.2 1
    refine ⟨hx.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm

theorem six_term_homogeneous_134_finite5 (a b c : ℚ) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 3+c*x 4=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a*x 1+b*x 3+c*x 4=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 3/sixTermUnit5 x 1,sixTermUnit5 x 4/sixTermUnit5 x 1)
  apply six_term_finite_over_pairs5 S f a b c ha hb hc
  · intro x hx
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
    have hn := (six_term_relation_facts5 hx.1).2.2 1
    field_simp
    nlinarith only [hx.2]
  · intro q hq
    apply (six_term_ratios_134_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1.1] at he1 he2
    have hn := (six_term_relation_facts5 hx.1.1).2.2 1
    refine ⟨hx.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm

theorem six_term_homogeneous_234_finite5 (a b c : ℚ) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    {x∈normalizedRelations fixedSUnitGroup 5 | a*x 2+b*x 3+c*x 4=0}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | a*x 2+b*x 3+c*x 4=0}
  let f (x : Fin 6 → ℚ) := (sixTermUnit5 x 3/sixTermUnit5 x 2,sixTermUnit5 x 4/sixTermUnit5 x 2)
  apply six_term_finite_over_pairs5 S f a b c ha hb hc
  · intro x hx
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1]
    have hn := (six_term_relation_facts5 hx.1).2.2 2
    field_simp
    nlinarith only [hx.2]
  · intro q hq
    apply (six_term_ratios_234_finite5 ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ)).subset
    intro x hx
    have he1 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.1 : ℚˣ) : ℚ)) hx.2
    have he2 := congrArg (fun p : fixedSUnitGroup × fixedSUnitGroup => ((p.2 : ℚˣ) : ℚ)) hx.2
    simp only [f,Subgroup.coe_div,Units.val_div_eq_div_val,six_term_unit_value5 hx.1.1] at he1 he2
    have hn := (six_term_relation_facts5 hx.1.1).2.2 2
    refine ⟨hx.1.1,?_,?_⟩
    · rw [← he1]
      exact (div_mul_cancel₀ _ hn).symm
    · rw [← he2]
      exact (div_mul_cancel₀ _ hn).symm

end JSP000334
