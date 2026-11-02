import SubspaceBridge.WeightedPairFiniteness2
namespace JSP000334

def fourTermCoefficientFiber (a0 a1 a2 : ℚ) : Set (Fin 4 → ℚ) :=
  {x | x ∈ normalizedRelations fixedSUnitGroup 3 ∧ a0*x 0+a1*x 1+a2*x 2=0}

theorem four_term_weighted_projection_finite (S : Set (Fin 4 → ℚ))
    (hs : S ⊆ normalizedRelations fixedSUnitGroup 3)
    (A B C : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (i j : Fin 4) (recover : ℚ → ℚ → (Fin 4 → ℚ))
    (heq : ∀ x∈S,A+B*x i+C*x j=0)
    (hrec : ∀ x∈S,recover (x i) (x j)=x) : S.Finite := by
  let f : (fixedSUnitGroup × fixedSUnitGroup) → (Fin 4 → ℚ) :=
    fun p => recover ((p.1 : ℚˣ) : ℚ) ((p.2 : ℚˣ) : ℚ)
  apply ((weighted_fixed_sunit_pair_finite A B C hA hB hC).image f).subset
  intro x hx
  obtain ⟨u,hu⟩ := (hs hx).2.1 i
  obtain ⟨v,hv⟩ := (hs hx).2.1 j
  refine ⟨(u,v),?_,?_⟩
  · change A+B*((u : ℚˣ) : ℚ)+C*((v : ℚˣ) : ℚ)=0
    rw [hu,hv]
    exact heq x hx
  · change recover ((u : ℚˣ) : ℚ) ((v : ℚˣ) : ℚ)=x
    rw [hu,hv]
    exact hrec x hx

theorem four_term_coordinate_reconstruction (x : Fin 4 → ℚ) (h0 : x 0=1)
    (hs : x 0+x 1+x 2+x 3=0) : ![1,x 1,x 2,-1-x 1-x 2]=x := by
  ext i
  fin_cases i
  · exact h0.symm
  · rfl
  · rfl
  · change -1-x 1-x 2=x 3
    linarith

end JSP000334
