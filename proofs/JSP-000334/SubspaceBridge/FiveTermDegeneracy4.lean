import SubspaceBridge.WeightedFourTermFiniteness3
namespace JSP000334
open scoped BigOperators Matrix

theorem five_term_weighted_degenerate_pair4 (a b c d : ℚ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0)
    (hs : a+b+c+d=0) (hn : ¬Nondegenerate (![a,b,c,d] : Fin 4 → ℚ)) :
    a+b=0 ∨ a+c=0 ∨ a+d=0 := by
  classical
  unfold Nondegenerate at hn
  push_neg at hn
  obtain ⟨I,hI,hproper,hzero⟩ := hn
  fin_cases I <;> norm_num [Finset.sum_insert,Matrix.cons_val_succ,Matrix.cons_val_zero] at hzero hI
  all_goals first
    | exact False.elim (ha (by linarith))
    | exact False.elim (hb (by linarith))
    | exact False.elim (hc (by linarith))
    | exact False.elim (hd (by linarith))
    | exact Or.inl (by linarith)
    | exact Or.inr (Or.inl (by linarith))
    | exact Or.inr (Or.inr (by linarith))
    | exact False.elim (hproper (by decide))

theorem five_term_nondegenerate_coarsen4 (x : Fin 5 → ℚ) (hx : Nondegenerate x)
    (f : Fin 5 → Fin 4) (hf : Function.Surjective f) :
    Nondegenerate (fun j => ∑ i : Fin 5,if f i=j then x i else 0) := by
  classical
  intro I hI hproper
  let J : Finset (Fin 5) := Finset.univ.filter (fun i => f i∈I)
  have hJ : J.Nonempty := by
    obtain ⟨j,hj⟩ := hI
    obtain ⟨i,rfl⟩ := hf j
    exact ⟨i,by simpa [J] using hj⟩
  have hJproper : J≠Finset.univ := by
    intro he
    apply hproper
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨i,rfl⟩ := hf j
    have hi : i∈J := by rw [he];exact Finset.mem_univ i
    simpa [J] using hi
  have heq : (∑ j∈I,∑ i : Fin 5,if f i=j then x i else 0)=∑ i∈J,x i := by
    rw [Finset.sum_comm]
    simp [J,Finset.sum_filter,Finset.sum_ite_eq']
  rw [heq]
  exact hx J hJ hJproper

end JSP000334
