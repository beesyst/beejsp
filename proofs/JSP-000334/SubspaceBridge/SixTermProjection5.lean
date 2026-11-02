import SubspaceBridge.SixTermDegeneracy5
namespace JSP000334
open scoped BigOperators Matrix

noncomputable def sixTermUnit5 (x : Fin 6 → ℚ) (i : Fin 6) : fixedSUnitGroup := by
  classical
  exact if h : x∈normalizedRelations fixedSUnitGroup 5 then (h.2.1 i).choose else 1

theorem six_term_unit_value5 {x : Fin 6 → ℚ} (hx : x∈normalizedRelations fixedSUnitGroup 5) (i : Fin 6) :
    ((sixTermUnit5 x i : ℚˣ) : ℚ)=x i := by
  simp only [sixTermUnit5,dif_pos hx]
  exact (hx.2.1 i).choose_spec

theorem six_term_relation_facts5 {x : Fin 6 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 5) :
    x 0=1 ∧ x 0+x 1+x 2+x 3+x 4+x 5=0 ∧ (∀ i,x i≠0) := by
  refine ⟨hx.1,?_,?_⟩
  · simpa [Fin.sum_univ_succ,add_assoc] using hx.2.2.1
  · intro i
    obtain ⟨u,hu⟩ := hx.2.1 i
    rw [← hu]
    exact Units.ne_zero _

def sixTermCoefficientFiber5 (b : Fin 5 → ℚ) : Set (Fin 6 → ℚ) :=
  {x∈normalizedRelations fixedSUnitGroup 5 | ∑ i,b i*x i.castSucc=0}

theorem six_term_weighted_triple_projection5 (S : Set (Fin 6 → ℚ))
    (hs : S⊆normalizedRelations fixedSUnitGroup 5)
    (A B C D : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0)
    (i j k : Fin 6) (recover : ℚ → ℚ → ℚ → Fin 6 → ℚ)
    (he : ∀ x∈S,A+B*x i+C*x j+D*x k=0)
    (hn : ∀ x∈S,Nondegenerate (![A,B*x i,C*x j,D*x k] : Fin 4 → ℚ))
    (hr : ∀ x∈S,recover (x i) (x j) (x k)=x) : S.Finite := by
  let f : (fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup) → Fin 6 → ℚ :=
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

theorem six_term_weighted_pair_projection5 (S : Set (Fin 6 → ℚ))
    (hs : S⊆normalizedRelations fixedSUnitGroup 5)
    (A B C : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (i j : Fin 6) (recover : ℚ → ℚ → Fin 6 → ℚ)
    (he : ∀ x∈S,A+B*x i+C*x j=0)
    (hr : ∀ x∈S,recover (x i) (x j)=x) : S.Finite := by
  let f : (fixedSUnitGroup × fixedSUnitGroup) → Fin 6 → ℚ :=
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

theorem six_term_finite_over_pairs5 (S : Set (Fin 6 → ℚ))
    (f : (Fin 6 → ℚ) → fixedSUnitGroup × fixedSUnitGroup)
    (A B C : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (he : ∀ x∈S,A+B*(((f x).1 : ℚˣ) : ℚ)+C*(((f x).2 : ℚˣ) : ℚ)=0)
    (hf : ∀ p∈weightedFixedSUnitPairs A B C,{x∈S | f x=p}.Finite) : S.Finite := by
  have hU : (⋃ p∈weightedFixedSUnitPairs A B C,{x∈S | f x=p}).Finite :=
    (weighted_fixed_sunit_pair_finite A B C hA hB hC).biUnion hf
  apply hU.subset
  intro x hx
  exact Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨he x hx,hx,rfl⟩⟩


theorem six_term_weighted_quad_projection5 (S : Set (Fin 6 → ℚ))
    (hs : S⊆normalizedRelations fixedSUnitGroup 5)
    (A : ℚ) (B : Fin 4 → ℚ) (hA : A≠0) (hB : ∀ i,B i≠0)
    (idx : Fin 4 → Fin 6) (recover : (Fin 4 → ℚ) → Fin 6 → ℚ)
    (he : ∀ x∈S,A+∑ i,B i*x (idx i)=0)
    (hn : ∀ x∈S,Nondegenerate (Fin.cons A (fun i => B i*x (idx i))))
    (hr : ∀ x∈S,recover (fun i => x (idx i))=x) : S.Finite := by
  let f (u : Fin 4 → fixedSUnitGroup) := recover (fun i => ((u i : ℚˣ) : ℚ))
  apply ((weighted_five_term_finite A B hA hB).image f).subset
  intro x hx
  let u (i : Fin 4) := sixTermUnit5 x (idx i)
  have hu (i : Fin 4) : ((u i : ℚˣ) : ℚ)=x (idx i) := six_term_unit_value5 (hs hx) _
  refine ⟨u,?_,?_⟩
  · change A+∑ i,B i*((u i : ℚˣ) : ℚ)=0 ∧ _
    change A+∑ i,B i*((u i : ℚˣ) : ℚ)=0 ∧ Nondegenerate (Fin.cons A (fun i => B i*((u i : ℚˣ) : ℚ)))
    simp_rw [hu]
    exact ⟨he x hx,hn x hx⟩
  · change recover (fun i => ((u i : ℚˣ) : ℚ))=x
    simp_rw [hu]
    exact hr x hx

end JSP000334
