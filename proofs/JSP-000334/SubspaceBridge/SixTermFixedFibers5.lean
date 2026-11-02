import SubspaceBridge.SixTermSource5
namespace JSP000334
open scoped BigOperators Matrix

theorem six_term_fixed_1_finite5 (a : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a}
  by_cases hC : 1+a=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) (1+a) (fun _ => 1) hC (by intro i;norm_num)
      ![2,3,4,5] (fun u => ![1,a,u 0,u 1,u 2,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,0,1,2,3,4]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen5 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · exact hx.2.symm
      · rfl
      · rfl
      · rfl
      · rfl

theorem six_term_fixed_2_finite5 (a : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a}
  by_cases hC : 1+a=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,2} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) (1+a) (fun _ => 1) hC (by intro i;norm_num)
      ![1,3,4,5] (fun u => ![1,u 0,a,u 1,u 2,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,1,0,2,3,4]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen5 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.symm
      · rfl
      · rfl
      · rfl

theorem six_term_fixed_3_finite5 (a : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 3=a}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 3=a}
  by_cases hC : 1+a=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,3} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) (1+a) (fun _ => 1) hC (by intro i;norm_num)
      ![1,2,4,5] (fun u => ![1,u 0,u 1,a,u 2,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,1,2,0,3,4]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen5 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl
      · rfl

theorem six_term_fixed_4_finite5 (a : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 4=a}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 4=a}
  by_cases hC : 1+a=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) (1+a) (fun _ => 1) hC (by intro i;norm_num)
      ![1,2,3,5] (fun u => ![1,u 0,u 1,u 2,a,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,1,2,3,0,4]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen5 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl

theorem six_term_fixed_12_finite5 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 2=b}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 2=b}
  by_cases hC : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,2} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) (1+a+b) 1 1 1 hC one_ne_zero one_ne_zero one_ne_zero
      3 4 5 (fun u v w => ![1,a,b,u,v,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,0,0,1,2,3]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen4 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl
      · rfl
      · rfl

theorem six_term_fixed_13_finite5 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 3=b}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 3=b}
  by_cases hC : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,3} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) (1+a+b) 1 1 1 hC one_ne_zero one_ne_zero one_ne_zero
      2 4 5 (fun u v w => ![1,a,u,b,v,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,0,1,0,2,3]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen4 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · rfl
      · exact hx.2.2.symm
      · rfl
      · rfl

theorem six_term_fixed_14_finite5 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 4=b}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 4=b}
  by_cases hC : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) (1+a+b) 1 1 1 hC one_ne_zero one_ne_zero one_ne_zero
      2 3 5 (fun u v w => ![1,a,u,v,b,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,0,1,2,0,3]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen4 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · rfl
      · rfl
      · exact hx.2.2.symm
      · rfl

theorem six_term_fixed_23_finite5 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a ∧ x 3=b}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a ∧ x 3=b}
  by_cases hC : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,2,3} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) (1+a+b) 1 1 1 hC one_ne_zero one_ne_zero one_ne_zero
      1 4 5 (fun u v w => ![1,u,a,b,v,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,1,0,0,2,3]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen4 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl
      · rfl

theorem six_term_fixed_24_finite5 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a ∧ x 4=b}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a ∧ x 4=b}
  by_cases hC : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,2,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) (1+a+b) 1 1 1 hC one_ne_zero one_ne_zero one_ne_zero
      1 3 5 (fun u v w => ![1,u,a,v,b,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,1,0,2,0,3]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen4 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.1.symm
      · rfl
      · exact hx.2.2.symm
      · rfl

theorem six_term_fixed_34_finite5 (a b : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 3=a ∧ x 4=b}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 3=a ∧ x 4=b}
  by_cases hC : 1+a+b=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,3,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) (1+a+b) 1 1 1 hC one_ne_zero one_ne_zero one_ne_zero
      1 2 5 (fun u v w => ![1,u,v,a,b,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,1,2,0,0,3]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen4 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2,add_comm,add_left_comm,add_assoc] <;> rfl
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl

theorem six_term_fixed_123_finite5 (a b c : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 2=b ∧ x 3=c}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 2=b ∧ x 3=c}
  by_cases hC : 1+a+b+c=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,2,3} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_pair_projection5 S (fun _ hx => hx.1) (1+a+b+c) 1 1 hC one_ne_zero one_ne_zero
      4 5 (fun u v => ![1,a,b,c,u,v])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · exact hx.2.2.1.symm
      · exact hx.2.2.2.symm
      · rfl
      · rfl

theorem six_term_fixed_124_finite5 (a b c : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 2=b ∧ x 4=c}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 2=b ∧ x 4=c}
  by_cases hC : 1+a+b+c=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,2,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_pair_projection5 S (fun _ hx => hx.1) (1+a+b+c) 1 1 hC one_ne_zero one_ne_zero
      3 5 (fun u v => ![1,a,b,u,c,v])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · exact hx.2.2.1.symm
      · rfl
      · exact hx.2.2.2.symm
      · rfl

theorem six_term_fixed_134_finite5 (a b c : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 3=b ∧ x 4=c}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 1=a ∧ x 3=b ∧ x 4=c}
  by_cases hC : 1+a+b+c=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1,3,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_pair_projection5 S (fun _ hx => hx.1) (1+a+b+c) 1 1 hC one_ne_zero one_ne_zero
      2 5 (fun u v => ![1,a,u,b,c,v])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · exact hx.2.1.symm
      · rfl
      · exact hx.2.2.1.symm
      · exact hx.2.2.2.symm
      · rfl

theorem six_term_fixed_234_finite5 (a b c : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a ∧ x 3=b ∧ x 4=c}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=a ∧ x 3=b ∧ x 4=c}
  by_cases hC : 1+a+b+c=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,2,3,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    simpa [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2,add_comm,add_left_comm,add_assoc] using hC
  ·
    apply six_term_weighted_pair_projection5 S (fun _ hx => hx.1) (1+a+b+c) 1 1 hC one_ne_zero one_ne_zero
      1 5 (fun u v => ![1,u,a,b,c,v])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2] at hs
      simpa [Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc] using hs
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.1.symm
      · exact hx.2.2.2.symm
      · rfl

end JSP000334
