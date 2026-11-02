import SubspaceBridge.FiveTermSource4
import SubspaceBridge.FiveTermProjection4
import SubspaceBridge.FiveTermMerge4
namespace JSP000334
open scoped BigOperators Matrix

theorem five_term_fixed_coordinate_14 (k : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 1=k}.Finite := by
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,1} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 0+x 1=0 := by rw [hx.1.1,hx.2];exact hk
    exact False.elim (hn (by simpa using he))
  · apply five_term_weighted_triple_projection4 _ (fun _ hx => hx.1) (1+k) 1 1 1 hk
      one_ne_zero one_ne_zero one_ne_zero 2 3 4 (fun u v w => ![1,k,u,v,w])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [one_mul]
      linarith only [hs]
    · intro x hx
      have hn := five_term_merge_first14 x hx.1.2.2.2
      simpa only [hx.1.1,hx.2,one_mul] using hn
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · exact hx.2.symm
      · rfl
      · rfl
      · rfl

theorem five_term_fixed_coordinate_24 (k : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 2=k}.Finite := by
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,2} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 0+x 2=0 := by rw [hx.1.1,hx.2];exact hk
    exact False.elim (hn (by simpa using he))
  · apply five_term_weighted_triple_projection4 _ (fun _ hx => hx.1) (1+k) 1 1 1 hk
      one_ne_zero one_ne_zero one_ne_zero 1 3 4 (fun u v w => ![1,u,k,v,w])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [one_mul]
      linarith only [hs]
    · intro x hx
      have hn := five_term_merge_first24 x hx.1.2.2.2
      simpa only [hx.1.1,hx.2,one_mul] using hn
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.symm
      · rfl
      · rfl

theorem five_term_fixed_coordinate_34 (k : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 3=k}.Finite := by
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({0,3} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 0+x 3=0 := by rw [hx.1.1,hx.2];exact hk
    exact False.elim (hn (by simpa using he))
  · apply five_term_weighted_triple_projection4 _ (fun _ hx => hx.1) (1+k) 1 1 1 hk
      one_ne_zero one_ne_zero one_ne_zero 1 2 4 (fun u v w => ![1,u,v,k,w])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [one_mul]
      linarith only [hs]
    · intro x hx
      have hn := five_term_merge_first34 x hx.1.2.2.2
      simpa only [hx.1.1,hx.2,one_mul] using hn
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl

theorem five_term_ratio_coordinate_124 (k : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 2=k*x 1}.Finite := by
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,2} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 1+x 2=(1+k)*x 1 := by rw [hx.2];ring
    rw [hk,zero_mul] at he
    exact False.elim (hn (by simpa using he))
  · apply five_term_weighted_triple_projection4 _ (fun _ hx => hx.1) 1 (1+k) 1 1
      one_ne_zero hk one_ne_zero one_ne_zero 1 3 4 (fun u v w => ![1,u,k*u,v,w])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [one_mul]
      nlinarith only [hs]
    · intro x hx
      have hn := five_term_merge_pair124 x hx.1.2.2.2
      have he : x 1+x 2=(1+k)*x 1 := by rw [hx.2];ring
      simpa only [hx.1.1,he,one_mul] using hn
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · rfl
      · exact hx.2.symm
      · rfl
      · rfl

theorem five_term_ratio_coordinate_134 (k : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 3=k*x 1}.Finite := by
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({1,3} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 1+x 3=(1+k)*x 1 := by rw [hx.2];ring
    rw [hk,zero_mul] at he
    exact False.elim (hn (by simpa using he))
  · apply five_term_weighted_triple_projection4 _ (fun _ hx => hx.1) 1 (1+k) 1 1
      one_ne_zero hk one_ne_zero one_ne_zero 1 2 4 (fun u v w => ![1,u,v,k*u,w])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [one_mul]
      nlinarith only [hs]
    · intro x hx
      have hn := five_term_merge_pair134 x hx.1.2.2.2
      have he : x 1+x 3=(1+k)*x 1 := by rw [hx.2];ring
      simpa only [hx.1.1,he,one_mul] using hn
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl

theorem five_term_ratio_coordinate_234 (k : ℚ) :
    {x∈normalizedRelations fixedSUnitGroup 4 | x 3=k*x 2}.Finite := by
  by_cases hk : 1+k=0
  · apply Set.finite_empty.subset
    intro x hx
    have hn := hx.1.2.2.2 ({2,3} : Finset (Fin 5)) (by decide) (by decide)
    have he : x 2+x 3=(1+k)*x 2 := by rw [hx.2];ring
    rw [hk,zero_mul] at he
    exact False.elim (hn (by simpa using he))
  · apply five_term_weighted_triple_projection4 _ (fun _ hx => hx.1) 1 (1+k) 1 1
      one_ne_zero hk one_ne_zero one_ne_zero 2 1 4 (fun u v w => ![1,v,u,k*u,w])
    · intro x hx
      have hs := (five_term_relation_facts4 hx.1).2.1
      rw [hx.1.1,hx.2] at hs
      simp only [one_mul]
      nlinarith only [hs]
    · intro x hx
      have hn := five_term_merge_pair234 x hx.1.2.2.2
      have he : x 2+x 3=(1+k)*x 2 := by rw [hx.2];ring
      simpa only [hx.1.1,he,one_mul] using hn
    · intro x hx
      ext n
      fin_cases n
      · exact hx.1.1.symm
      · rfl
      · rfl
      · exact hx.2.symm
      · rfl

end JSP000334
