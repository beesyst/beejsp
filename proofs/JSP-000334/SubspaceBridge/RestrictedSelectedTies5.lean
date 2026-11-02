import SubspaceBridge.RestrictedGreedyRanks5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.RestrictedSelectedTies5
open RestrictedWeightOrder5 RestrictedGreedyRows5 RestrictedGreedyRanks5 SelectedRestriction5

def weightedRowSet5 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ) (t : ℝ) : Set (Fin d → K) :=
  M.row '' {i | c i ≤ t}

theorem selected_weight_le_iff_rank5 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) (k : Fin d) (t : ℝ) :
    c (weightOrder5 c (selectedIndex5 M c hfull k)) ≤ t ↔
      k.val < Module.finrank K (Submodule.span K (weightedRowSet5 M c t)) := by
  let E := selectedIndex5 M c hfull
  let rows := sortedRows5 M c
  have hpre := greedyIndex5_prefix_rank rows (sortedRows5_span M c hfull) d (by simp) k
  have hstep := (greedyIndex5_first_rank_increase rows (sortedRows5_span M c hfull) d (by simp) k).1
  constructor
  · intro h
    have hs : rowPrefix5 rows ((E k).val+1) ⊆ weightedRowSet5 M c t := by
      rintro _ ⟨i,hi,rfl⟩
      change i.val < (E k).val+1 at hi
      refine ⟨weightOrder5 c i,?_,rfl⟩
      exact ((weightOrder5_monotone c) (show i ≤ E k by change i.val ≤ (E k).val; omega)).trans h
    have hd := Submodule.finrank_mono (Submodule.span_mono (R := K) hs)
    change Module.finrank K (Submodule.span K (rowPrefix5 rows ((E k).val+1))) = k.val+1 at hstep
    rw [hstep] at hd
    omega
  · intro h
    by_contra hn
    have hs : weightedRowSet5 M c t ⊆ rowPrefix5 rows (E k).val := by
      rintro _ ⟨i,hi,rfl⟩
      let a := (weightOrder5 c).symm i
      have ha : a < E k := by
        apply lt_of_not_ge
        intro hna
        have hm := weightOrder5_monotone c hna
        have hv : c (weightOrder5 c a) = c i := by simp [a]
        change c (weightOrder5 c (E k)) ≤ c (weightOrder5 c a) at hm
        rw [hv] at hm
        exact hn (hm.trans hi)
      exact ⟨a,ha,by simp [rows,sortedRows5,a,Matrix.row_def]⟩
    have hd := Submodule.finrank_mono (Submodule.span_mono (R := K) hs)
    change Module.finrank K (Submodule.span K (rowPrefix5 rows (E k).val)) = k.val at hpre
    rw [hpre] at hd
    omega

theorem selected_weights_permutation5 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) (sigma : Equiv.Perm (Fin 5))
    (hfull' : Submodule.span K (Set.range (fun i => M (sigma i))) = ⊤) :
    (fun k : Fin d => c (weightOrder5 c (selectedIndex5 M c hfull k))) =
      (fun k : Fin d => (c ∘ sigma) (weightOrder5 (c ∘ sigma)
        (selectedIndex5 (fun i => M (sigma i)) (c ∘ sigma) hfull' k))) := by
  have hset (t : ℝ) : weightedRowSet5 (fun i => M (sigma i)) (c ∘ sigma) t = weightedRowSet5 M c t := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨sigma i,hi,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨sigma.symm i,by simpa [Function.comp_apply,Set.mem_setOf_eq] using hi,by simp [Matrix.row_def]⟩
  funext k
  apply le_antisymm
  · apply (selected_weight_le_iff_rank5 M c hfull k _).mpr
    rw [← hset]
    exact (selected_weight_le_iff_rank5 _ _ hfull' k _).mp le_rfl
  · apply (selected_weight_le_iff_rank5 _ _ hfull' k _).mpr
    rw [hset]
    exact (selected_weight_le_iff_rank5 M c hfull k _).mp le_rfl

theorem selected_weight_sum_permutation5 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 5) (Fin d) K) (c : Fin 5 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) (sigma : Equiv.Perm (Fin 5))
    (hfull' : Submodule.span K (Set.range (fun i => M (sigma i))) = ⊤) :
    (∑ k, c (weightOrder5 c (selectedIndex5 M c hfull k))) =
      ∑ k, (c ∘ sigma) (weightOrder5 (c ∘ sigma)
        (selectedIndex5 (fun i => M (sigma i)) (c ∘ sigma) hfull' k)) := by
  exact congrArg (fun v : Fin d → ℝ => ∑ k, v k) (selected_weights_permutation5 M c hfull sigma hfull')

end CompoundFeasibility.RestrictedSelectedTies5
