import SubspaceBridge.FiveTermDegeneracy4
namespace JSP000334
open scoped BigOperators Matrix

def fiveTermCoefficientFiber4 (b0 b1 b2 b3 : ℚ) : Set (Fin 5 → ℚ) :=
  {x | x∈normalizedRelations fixedSUnitGroup 4 ∧ b0*x 0+b1*x 1+b2*x 2+b3*x 3=0}

theorem five_term_weighted_triple_projection4 (S : Set (Fin 5 → ℚ))
    (hs : S⊆normalizedRelations fixedSUnitGroup 4)
    (A B C D : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0)
    (i j k : Fin 5) (recover : ℚ → ℚ → ℚ → Fin 5 → ℚ)
    (he : ∀ x∈S,A+B*x i+C*x j+D*x k=0)
    (hn : ∀ x∈S,Nondegenerate (![A,B*x i,C*x j,D*x k] : Fin 4 → ℚ))
    (hr : ∀ x∈S,recover (x i) (x j) (x k)=x) : S.Finite := by
  let f : (fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup) → Fin 5 → ℚ :=
    fun p => recover ((p.1 : ℚˣ) : ℚ) ((p.2.1 : ℚˣ) : ℚ) ((p.2.2 : ℚˣ) : ℚ)
  apply ((weighted_four_term_finite A B C D hA hB hC hD).image f).subset
  intro x hx
  obtain ⟨u,hu⟩ := (hs hx).2.1 i
  obtain ⟨v,hv⟩ := (hs hx).2.1 j
  obtain ⟨w,hw⟩ := (hs hx).2.1 k
  refine ⟨(u,v,w),?_,?_⟩
  · change A+B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ)+D*((w : ℚˣ) : ℚ)=0 ∧ _
    rw [hu,hv,hw]
    exact ⟨he x hx,hn x hx⟩
  · change recover ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ) ((w : ℚˣ) : ℚ)=x
    rw [hu,hv,hw]
    exact hr x hx

theorem five_term_weighted_pair_projection4 (S : Set (Fin 5 → ℚ))
    (hs : S⊆normalizedRelations fixedSUnitGroup 4)
    (A B C : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (i j : Fin 5) (recover : ℚ → ℚ → Fin 5 → ℚ)
    (he : ∀ x∈S,A+B*x i+C*x j=0)
    (hr : ∀ x∈S,recover (x i) (x j)=x) : S.Finite := by
  let f : (fixedSUnitGroup × fixedSUnitGroup) → Fin 5 → ℚ :=
    fun p => recover ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)
  apply ((weighted_fixed_sunit_pair_finite A B C hA hB hC).image f).subset
  intro x hx
  obtain ⟨u,hu⟩ := (hs hx).2.1 i
  obtain ⟨v,hv⟩ := (hs hx).2.1 j
  refine ⟨(u,v),?_,?_⟩
  · change A+B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ)=0
    rw [hu,hv]
    exact he x hx
  · change recover ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ)=x
    rw [hu,hv]
    exact hr x hx

theorem five_term_finite_over_pairs4 (S : Set (Fin 5 → ℚ))
    (f : (Fin 5 → ℚ) → fixedSUnitGroup × fixedSUnitGroup)
    (A B C : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (he : ∀ x∈S,A+B*(((f x).1 : ℚˣ) : ℚ)+C*(((f x).2 : ℚˣ) : ℚ)=0)
    (hf : ∀ p∈weightedFixedSUnitPairs A B C,{x∈S | f x=p}.Finite) : S.Finite := by
  have hU : (⋃ p∈weightedFixedSUnitPairs A B C,{x∈S | f x=p}).Finite :=
    (weighted_fixed_sunit_pair_finite A B C hA hB hC).biUnion hf
  apply hU.subset
  intro x hx
  exact Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨he x hx,hx,rfl⟩⟩

end JSP000334
