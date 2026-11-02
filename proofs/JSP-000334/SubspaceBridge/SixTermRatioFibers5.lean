import SubspaceBridge.SixTermFixedFibers5
namespace JSP000334
open scoped BigOperators Matrix

theorem six_term_ratios_12_finite5 (r : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1}
  by_cases hC : 1+r=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,2} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 1+x 2=0 := by
      rw [hx.2]
      linear_combination x 1*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) 1 ![1+r,1,1,1] one_ne_zero
      (by intro i;fin_cases i <;> simp_all) ![1,3,4,5]
      (fun u => ![1,u 0,r*u 0,u 1,u 2,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,1,1,2,3,4]
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
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.symm
      · rfl
      · rfl
      · rfl

theorem six_term_ratios_13_finite5 (r : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 1}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 1}
  by_cases hC : 1+r=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,3} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 1+x 3=0 := by
      rw [hx.2]
      linear_combination x 1*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) 1 ![1+r,1,1,1] one_ne_zero
      (by intro i;fin_cases i <;> simp_all) ![1,2,4,5]
      (fun u => ![1,u 0,u 1,r*u 0,u 2,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,1,2,1,3,4]
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
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl
      · rfl

theorem six_term_ratios_14_finite5 (r : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 4=r*x 1}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 4=r*x 1}
  by_cases hC : 1+r=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 1+x 4=0 := by
      rw [hx.2]
      linear_combination x 1*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) 1 ![1+r,1,1,1] one_ne_zero
      (by intro i;fin_cases i <;> simp_all) ![1,2,3,5]
      (fun u => ![1,u 0,u 1,u 2,r*u 0,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,1,2,3,1,4]
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
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl

theorem six_term_ratios_23_finite5 (r : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 2}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 2}
  by_cases hC : 1+r=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({2,3} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 2+x 3=0 := by
      rw [hx.2]
      linear_combination x 2*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) 1 ![1+r,1,1,1] one_ne_zero
      (by intro i;fin_cases i <;> simp_all) ![2,1,4,5]
      (fun u => ![1,u 1,u 0,r*u 0,u 2,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,2,1,1,3,4]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen5 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl
      · rfl

theorem six_term_ratios_24_finite5 (r : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 4=r*x 2}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 4=r*x 2}
  by_cases hC : 1+r=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({2,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 2+x 4=0 := by
      rw [hx.2]
      linear_combination x 2*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) 1 ![1+r,1,1,1] one_ne_zero
      (by intro i;fin_cases i <;> simp_all) ![2,1,3,5]
      (fun u => ![1,u 1,u 0,u 2,r*u 0,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,2,1,3,1,4]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen5 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl

theorem six_term_ratios_34_finite5 (r : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 4=r*x 3}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 4=r*x 3}
  by_cases hC : 1+r=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({3,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 3+x 4=0 := by
      rw [hx.2]
      linear_combination x 3*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_quad_projection5 S (fun _ hx => hx.1) 1 ![1+r,1,1,1] one_ne_zero
      (by intro i;fin_cases i <;> simp_all) ![3,1,2,5]
      (fun u => ![1,u 1,u 2,u 0,r*u 0,u 3])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 5 := ![0,2,3,1,1,4]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen5 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl

theorem six_term_ratios_123_finite5 (r s : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1 ∧ x 3=s*x 1}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1 ∧ x 3=s*x 1}
  by_cases hC : 1+r+s=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,2,3} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 1+x 2+x 3=0 := by
      rw [hx.2.1,hx.2.2]
      linear_combination x 1*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) 1 (1+r+s) 1 1 one_ne_zero hC one_ne_zero one_ne_zero
      1 4 5 (fun u v w => ![1,u,r*u,s*u,v,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,1,1,1,2,3]
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
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl
      · rfl

theorem six_term_ratios_124_finite5 (r s : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1 ∧ x 4=s*x 1}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1 ∧ x 4=s*x 1}
  by_cases hC : 1+r+s=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,2,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 1+x 2+x 4=0 := by
      rw [hx.2.1,hx.2.2]
      linear_combination x 1*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) 1 (1+r+s) 1 1 one_ne_zero hC one_ne_zero one_ne_zero
      1 3 5 (fun u v w => ![1,u,r*u,v,s*u,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,1,1,2,1,3]
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
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.1.symm
      · rfl
      · exact hx.2.2.symm
      · rfl

theorem six_term_ratios_134_finite5 (r s : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 1 ∧ x 4=s*x 1}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 1 ∧ x 4=s*x 1}
  by_cases hC : 1+r+s=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,3,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 1+x 3+x 4=0 := by
      rw [hx.2.1,hx.2.2]
      linear_combination x 1*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) 1 (1+r+s) 1 1 one_ne_zero hC one_ne_zero one_ne_zero
      1 2 5 (fun u v w => ![1,u,v,r*u,s*u,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,1,2,1,1,3]
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
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl

theorem six_term_ratios_234_finite5 (r s : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 2 ∧ x 4=s*x 2}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 3=r*x 2 ∧ x 4=s*x 2}
  by_cases hC : 1+r+s=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({2,3,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 2+x 3+x 4=0 := by
      rw [hx.2.1,hx.2.2]
      linear_combination x 2*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_triple_projection5 S (fun _ hx => hx.1) 1 (1+r+s) 1 1 one_ne_zero hC one_ne_zero one_ne_zero
      2 1 5 (fun u v w => ![1,v,u,r*u,s*u,w])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
    · intro x hx
      let f : Fin 6 → Fin 4 := ![0,2,1,1,1,3]
      have hf : Function.Surjective f := by
        intro j
        fin_cases j
        · exact ⟨0,rfl⟩
        · exact ⟨2,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨5,rfl⟩
      have hh := six_term_nondegenerate_coarsen4 x hx.1.2.2.2 f hf
      convert hh using 1
      ext j
      fin_cases j <;> simp [f,Fin.sum_univ_succ,hx.1.1,hx.2.1,hx.2.2] <;> first | (change (1 : ℚ)*_=_;exact one_mul _) | ring
    · intro x hx
      ext j
      fin_cases j
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.1.symm
      · exact hx.2.2.symm
      · rfl

theorem six_term_ratios_1234_finite5 (r s t : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1 ∧ x 3=s*x 1 ∧ x 4=t*x 1}.Finite := by
  let S := {x∈normalizedRelations fixedSUnitGroup 5 | x 2=r*x 1 ∧ x 3=s*x 1 ∧ x 4=t*x 1}
  by_cases hC : 1+r+s+t=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,2,3,4} : Finset (Fin 6)) (by decide) (by decide)
    apply False.elim
    apply hn
    have he : x 1+x 2+x 3+x 4=0 := by
      rw [hx.2.1,hx.2.2.1,hx.2.2.2]
      linear_combination x 1*hC
    simpa [add_assoc] using he
  ·
    apply six_term_weighted_pair_projection5 S (fun _ hx => hx.1) 1 (1+r+s+t) 1 one_ne_zero hC one_ne_zero
      1 5 (fun u v => ![1,u,r*u,s*u,t*u,v])
    · intro x hx
      have hs := (six_term_relation_facts5 hx.1).2.1
      rw [hx.1.1,hx.2.1,hx.2.2.1,hx.2.2.2] at hs
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      nlinarith only [hs]
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
