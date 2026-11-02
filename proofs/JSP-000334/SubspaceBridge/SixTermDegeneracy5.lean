import SubspaceBridge.WeightedFiveTermFiniteness4
import SubspaceBridge.FiveTermFiniteness4
import SubspaceBridge.AllPointFiniteCover5
namespace JSP000334
open scoped BigOperators Matrix

theorem six_term_annihilator_degenerate5 (x : Fin 5 → ℚ)
    (hx : ∀ i,x i≠0) (hs : ∑ i,x i=0) (hn : ¬Nondegenerate x) :
    x 0+x 1=0 ∨ x 0+x 2=0 ∨ x 0+x 3=0 ∨ x 0+x 4=0 ∨ x 0+x 1+x 2=0 ∨ x 0+x 1+x 3=0 ∨ x 0+x 1+x 4=0 ∨ x 0+x 2+x 3=0 ∨ x 0+x 2+x 4=0 ∨ x 0+x 3+x 4=0 := by
  classical
  unfold Nondegenerate at hn
  push_neg at hn
  obtain ⟨I,hI,hproper,hzero⟩ := hn
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  have hs' : x 0+x 1+x 2+x 3+x 4=0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hs
  clear hs
  have he : x=![x 0,x 1,x 2,x 3,x 4] := by
    ext i
    fin_cases i <;> rfl
  rw [he] at hzero
  fin_cases I <;> norm_num [Finset.sum_insert,Matrix.cons_val_succ,Matrix.cons_val_zero] at hzero hI
  all_goals first
    | exact False.elim (h0 (by linarith))
    | exact False.elim (h1 (by linarith))
    | exact False.elim (h2 (by linarith))
    | exact False.elim (h3 (by linarith))
    | exact False.elim (h4 (by linarith))
    | exact Or.inl (by linarith)
    | exact Or.inr (Or.inl (by linarith))
    | exact Or.inr (Or.inr (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by linarith))))))))))
    | exact False.elim (hproper (by decide))

theorem six_term_nondegenerate_coarsen5 (x : Fin 6 → ℚ) (hx : Nondegenerate x)
    (f : Fin 6 → Fin 5) (hf : Function.Surjective f) :
    Nondegenerate (fun j => ∑ i : Fin 6,if f i=j then x i else 0) := by
  classical
  intro I hI hproper
  let J : Finset (Fin 6) := Finset.univ.filter (fun i => f i∈I)
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
  have heq : (∑ j∈I,∑ i : Fin 6,if f i=j then x i else 0)=∑ i∈J,x i := by
    rw [Finset.sum_comm]
    simp [J,Finset.sum_filter,Finset.sum_ite_eq']
  rw [heq]
  exact hx J hJ hJproper


theorem six_term_nondegenerate_coarsen4 (x : Fin 6 → ℚ) (hx : Nondegenerate x)
    (f : Fin 6 → Fin 4) (hf : Function.Surjective f) :
    Nondegenerate (fun j => ∑ i : Fin 6,if f i=j then x i else 0) := by
  classical
  intro I hI hproper
  let J : Finset (Fin 6) := Finset.univ.filter (fun i => f i∈I)
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
  have heq : (∑ j∈I,∑ i : Fin 6,if f i=j then x i else 0)=∑ i∈J,x i := by
    rw [Finset.sum_comm]
    simp [J,Finset.sum_filter,Finset.sum_ite_eq']
  rw [heq]
  exact hx J hJ hJproper


end JSP000334
