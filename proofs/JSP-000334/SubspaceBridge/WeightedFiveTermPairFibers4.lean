import SubspaceBridge.WeightedFiveTermCover4
import SubspaceBridge.WeightedFourTermFiniteness3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_unit_injective4 {u v : fixedSUnitGroup} (h : ((u : ℚˣ) : ℚ)=((v : ℚˣ) : ℚ)) : u=v := by
  apply Subtype.ext
  exact Units.ext h

theorem weighted_five_pair_01_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 1 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 1 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ)}
  let C := B 0+B 1*r
  have hmerged (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) :
      Nondegenerate (![A,C*((u 0 : ℚˣ) : ℚ),B 2*((u 2 : ℚˣ) : ℚ),B 3*((u 3 : ℚˣ) : ℚ)] : Fin 4 → ℚ) := by
    let f : Fin 5 → Fin 4 := ![0,1,1,2,3]
    have hf : Function.Surjective f := by
      intro j
      fin_cases j
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨4,rfl⟩
    have hh := five_term_nondegenerate_coarsen4 (weightedFiveTerms4 A B u) hu.1.2 f hf
    convert hh using 1
    ext n
    fin_cases n <;> simp [f,weightedFiveTerms4,Fin.sum_univ_succ,hu.2,C] <;> ring
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hmerged u hu ({1} : Finset (Fin 4)) (by decide) (by decide)
    exact False.elim (hh (by simp [hC]))
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 0,u 2,u 3)
    have himage : (f '' S).Finite := by
      apply (weighted_four_term_finite A C (B 2) (B 3) hA hC (hB 2) (hB 3)).subset
      rintro _ ⟨u,hu,rfl⟩
      refine ⟨?_,hmerged u hu⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      have hr := hu.2
      change A+C*((u 0 : ℚˣ) : ℚ)+B 2*((u 2 : ℚˣ) : ℚ)+B 3*((u 3 : ℚˣ) : ℚ)=0
      dsimp [C]
      rw [hr] at hs
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 0=v 0 := congrArg Prod.fst he
    have h1 : u 2=v 2 := congrArg (fun p => p.2.1) he
    have h2 : u 3=v 3 := congrArg (fun p => p.2.2) he
    have h3 : u 1=v 1 := weighted_unit_injective4 (by rw [hu.2,hv.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_pair_02_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ)}
  let C := B 0+B 2*r
  have hmerged (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) :
      Nondegenerate (![A,C*((u 0 : ℚˣ) : ℚ),B 1*((u 1 : ℚˣ) : ℚ),B 3*((u 3 : ℚˣ) : ℚ)] : Fin 4 → ℚ) := by
    let f : Fin 5 → Fin 4 := ![0,1,2,1,3]
    have hf : Function.Surjective f := by
      intro j
      fin_cases j
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨4,rfl⟩
    have hh := five_term_nondegenerate_coarsen4 (weightedFiveTerms4 A B u) hu.1.2 f hf
    convert hh using 1
    ext n
    fin_cases n <;> simp [f,weightedFiveTerms4,Fin.sum_univ_succ,hu.2,C] <;> ring
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hmerged u hu ({1} : Finset (Fin 4)) (by decide) (by decide)
    exact False.elim (hh (by simp [hC]))
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 0,u 1,u 3)
    have himage : (f '' S).Finite := by
      apply (weighted_four_term_finite A C (B 1) (B 3) hA hC (hB 1) (hB 3)).subset
      rintro _ ⟨u,hu,rfl⟩
      refine ⟨?_,hmerged u hu⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      have hr := hu.2
      change A+C*((u 0 : ℚˣ) : ℚ)+B 1*((u 1 : ℚˣ) : ℚ)+B 3*((u 3 : ℚˣ) : ℚ)=0
      dsimp [C]
      rw [hr] at hs
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 0=v 0 := congrArg Prod.fst he
    have h1 : u 1=v 1 := congrArg (fun p => p.2.1) he
    have h2 : u 3=v 3 := congrArg (fun p => p.2.2) he
    have h3 : u 2=v 2 := weighted_unit_injective4 (by rw [hu.2,hv.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_pair_03_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 3 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 3 : ℚˣ) : ℚ)=r*((u 0 : ℚˣ) : ℚ)}
  let C := B 0+B 3*r
  have hmerged (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) :
      Nondegenerate (![A,C*((u 0 : ℚˣ) : ℚ),B 1*((u 1 : ℚˣ) : ℚ),B 2*((u 2 : ℚˣ) : ℚ)] : Fin 4 → ℚ) := by
    let f : Fin 5 → Fin 4 := ![0,1,2,3,1]
    have hf : Function.Surjective f := by
      intro j
      fin_cases j
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨3,rfl⟩
    have hh := five_term_nondegenerate_coarsen4 (weightedFiveTerms4 A B u) hu.1.2 f hf
    convert hh using 1
    ext n
    fin_cases n <;> simp [f,weightedFiveTerms4,Fin.sum_univ_succ,hu.2,C] <;> ring
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hmerged u hu ({1} : Finset (Fin 4)) (by decide) (by decide)
    exact False.elim (hh (by simp [hC]))
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 0,u 1,u 2)
    have himage : (f '' S).Finite := by
      apply (weighted_four_term_finite A C (B 1) (B 2) hA hC (hB 1) (hB 2)).subset
      rintro _ ⟨u,hu,rfl⟩
      refine ⟨?_,hmerged u hu⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      have hr := hu.2
      change A+C*((u 0 : ℚˣ) : ℚ)+B 1*((u 1 : ℚˣ) : ℚ)+B 2*((u 2 : ℚˣ) : ℚ)=0
      dsimp [C]
      rw [hr] at hs
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 0=v 0 := congrArg Prod.fst he
    have h1 : u 1=v 1 := congrArg (fun p => p.2.1) he
    have h2 : u 2=v 2 := congrArg (fun p => p.2.2) he
    have h3 : u 3=v 3 := weighted_unit_injective4 (by rw [hu.2,hv.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_pair_12_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 1 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 2 : ℚˣ) : ℚ)=r*((u 1 : ℚˣ) : ℚ)}
  let C := B 1+B 2*r
  have hmerged (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) :
      Nondegenerate (![A,C*((u 1 : ℚˣ) : ℚ),B 0*((u 0 : ℚˣ) : ℚ),B 3*((u 3 : ℚˣ) : ℚ)] : Fin 4 → ℚ) := by
    let f : Fin 5 → Fin 4 := ![0,2,1,1,3]
    have hf : Function.Surjective f := by
      intro j
      fin_cases j
      · exact ⟨0,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨4,rfl⟩
    have hh := five_term_nondegenerate_coarsen4 (weightedFiveTerms4 A B u) hu.1.2 f hf
    convert hh using 1
    ext n
    fin_cases n <;> simp [f,weightedFiveTerms4,Fin.sum_univ_succ,hu.2,C] <;> ring
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hmerged u hu ({1} : Finset (Fin 4)) (by decide) (by decide)
    exact False.elim (hh (by simp [hC]))
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 1,u 0,u 3)
    have himage : (f '' S).Finite := by
      apply (weighted_four_term_finite A C (B 0) (B 3) hA hC (hB 0) (hB 3)).subset
      rintro _ ⟨u,hu,rfl⟩
      refine ⟨?_,hmerged u hu⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      have hr := hu.2
      change A+C*((u 1 : ℚˣ) : ℚ)+B 0*((u 0 : ℚˣ) : ℚ)+B 3*((u 3 : ℚˣ) : ℚ)=0
      dsimp [C]
      rw [hr] at hs
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 1=v 1 := congrArg Prod.fst he
    have h1 : u 0=v 0 := congrArg (fun p => p.2.1) he
    have h2 : u 3=v 3 := congrArg (fun p => p.2.2) he
    have h3 : u 2=v 2 := weighted_unit_injective4 (by rw [hu.2,hv.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_pair_13_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 3 : ℚˣ) : ℚ)=r*((u 1 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 3 : ℚˣ) : ℚ)=r*((u 1 : ℚˣ) : ℚ)}
  let C := B 1+B 3*r
  have hmerged (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) :
      Nondegenerate (![A,C*((u 1 : ℚˣ) : ℚ),B 0*((u 0 : ℚˣ) : ℚ),B 2*((u 2 : ℚˣ) : ℚ)] : Fin 4 → ℚ) := by
    let f : Fin 5 → Fin 4 := ![0,2,1,3,1]
    have hf : Function.Surjective f := by
      intro j
      fin_cases j
      · exact ⟨0,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨3,rfl⟩
    have hh := five_term_nondegenerate_coarsen4 (weightedFiveTerms4 A B u) hu.1.2 f hf
    convert hh using 1
    ext n
    fin_cases n <;> simp [f,weightedFiveTerms4,Fin.sum_univ_succ,hu.2,C] <;> ring
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hmerged u hu ({1} : Finset (Fin 4)) (by decide) (by decide)
    exact False.elim (hh (by simp [hC]))
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 1,u 0,u 2)
    have himage : (f '' S).Finite := by
      apply (weighted_four_term_finite A C (B 0) (B 2) hA hC (hB 0) (hB 2)).subset
      rintro _ ⟨u,hu,rfl⟩
      refine ⟨?_,hmerged u hu⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      have hr := hu.2
      change A+C*((u 1 : ℚˣ) : ℚ)+B 0*((u 0 : ℚˣ) : ℚ)+B 2*((u 2 : ℚˣ) : ℚ)=0
      dsimp [C]
      rw [hr] at hs
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 1=v 1 := congrArg Prod.fst he
    have h1 : u 0=v 0 := congrArg (fun p => p.2.1) he
    have h2 : u 2=v 2 := congrArg (fun p => p.2.2) he
    have h3 : u 3=v 3 := weighted_unit_injective4 (by rw [hu.2,hv.2,h0])
    funext n
    fin_cases n <;> assumption

theorem weighted_five_pair_23_finite4 (A : ℚ) (B : Fin 4 → ℚ)
    (hA : A≠0) (hB : ∀ i,B i≠0) (r : ℚ) :
    {u∈WeightedFiveTermSolutions A B | ((u 3 : ℚˣ) : ℚ)=r*((u 2 : ℚˣ) : ℚ)}.Finite := by
  let S := {u∈WeightedFiveTermSolutions A B | ((u 3 : ℚˣ) : ℚ)=r*((u 2 : ℚˣ) : ℚ)}
  let C := B 2+B 3*r
  have hmerged (u : Fin 4 → fixedSUnitGroup) (hu : u∈S) :
      Nondegenerate (![A,C*((u 2 : ℚˣ) : ℚ),B 0*((u 0 : ℚˣ) : ℚ),B 1*((u 1 : ℚˣ) : ℚ)] : Fin 4 → ℚ) := by
    let f : Fin 5 → Fin 4 := ![0,2,3,1,1]
    have hf : Function.Surjective f := by
      intro j
      fin_cases j
      · exact ⟨0,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    have hh := five_term_nondegenerate_coarsen4 (weightedFiveTerms4 A B u) hu.1.2 f hf
    convert hh using 1
    ext n
    fin_cases n <;> simp [f,weightedFiveTerms4,Fin.sum_univ_succ,hu.2,C] <;> ring
  by_cases hC : C=0
  · apply Set.finite_empty.subset
    intro u hu
    have hh := hmerged u hu ({1} : Finset (Fin 4)) (by decide) (by decide)
    exact False.elim (hh (by simp [hC]))
  · let f (u : Fin 4 → fixedSUnitGroup) := (u 2,u 0,u 1)
    have himage : (f '' S).Finite := by
      apply (weighted_four_term_finite A C (B 0) (B 1) hA hC (hB 0) (hB 1)).subset
      rintro _ ⟨u,hu,rfl⟩
      refine ⟨?_,hmerged u hu⟩
      have hs := hu.1.1
      simp only [Fin.sum_univ_four] at hs
      have hr := hu.2
      change A+C*((u 2 : ℚˣ) : ℚ)+B 0*((u 0 : ℚˣ) : ℚ)+B 1*((u 1 : ℚˣ) : ℚ)=0
      dsimp [C]
      rw [hr] at hs
      nlinarith only [hs]
    apply himage.of_finite_image
    intro u hu v hv he
    have h0 : u 2=v 2 := congrArg Prod.fst he
    have h1 : u 0=v 0 := congrArg (fun p => p.2.1) he
    have h2 : u 1=v 1 := congrArg (fun p => p.2.2) he
    have h3 : u 3=v 3 := weighted_unit_injective4 (by rw [hu.2,hv.2,h0])
    funext n
    fin_cases n <;> assumption

end JSP000334
