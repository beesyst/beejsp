import SubspaceBridge.SelectedRestriction5
open scoped BigOperators Classical
namespace CompoundFeasibility.RestrictedGreedyRanks5
open RestrictedGreedyRows5
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem greedyIndex5_prefix_set (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    greedyPrefix5 (K := K) rows (greedyIndex5 rows hfull d hdim k).val =
      Set.range (fun a : Fin k.val => greedyIndex5 rows hfull d hdim (Fin.castLE (by omega) a)) := by
  let E := greedyIndex5 rows hfull d hdim
  have hrange : Set.range E = (greedyFinset5 (K := K) rows : Set (Fin 5)) :=
    (greedyFinset5 (K := K) rows).range_orderEmbOfFin ((greedyFinset5_card (K := K) rows hfull).trans hdim)
  ext i
  constructor
  · intro hi
    have himem : i ∈ (greedyFinset5 (K := K) rows : Set (Fin 5)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.2⟩
    rw [← hrange] at himem
    obtain ⟨a,rfl⟩ := himem
    have ha : a < k := E.lt_iff_lt.mp hi.1
    refine ⟨⟨a.val,ha⟩,?_⟩
    congr 1
  · rintro ⟨a,rfl⟩
    exact ⟨E.strictMono (show Fin.castLE (by omega) a < k from a.isLt),
      greedyIndex5_pivot rows hfull d hdim _⟩

theorem greedyIndex5_prefix_rank (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    Module.finrank K (Submodule.span K (rowPrefix5 rows (greedyIndex5 rows hfull d hdim k).val)) = k.val := by
  have hs := (greedyPrefix5_independent_span (K := K) rows
    (greedyIndex5 rows hfull d hdim k).val (by omega)).2
  rw [← hs,greedyIndex5_prefix_set rows hfull d hdim k,← Set.range_comp]
  have hli := (greedyIndex5_independent rows hfull d hdim).comp
    (fun a : Fin k.val => Fin.castLE (by omega) a) (Fin.castLE_injective (by omega))
  simpa only [Fintype.card_fin] using finrank_span_eq_card hli

theorem greedyIndex5_first_rank_increase (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    Module.finrank K (Submodule.span K (rowPrefix5 rows
      ((greedyIndex5 rows hfull d hdim k).val+1))) = k.val+1 ∧
    ∀ i : Fin 5, i < greedyIndex5 rows hfull d hdim k →
      Module.finrank K (Submodule.span K (rowPrefix5 rows (i.val+1))) ≤ k.val := by
  let E := greedyIndex5 rows hfull d hdim
  have hp := greedyIndex5_pivot rows hfull d hdim k
  have hprev := greedyIndex5_prefix_rank rows hfull d hdim k
  have hnonzero : rows (E k) ≠ 0 := by
    intro hz
    apply hp
    rw [hz]
    exact Submodule.zero_mem _
  have hdisjoint := Submodule.disjoint_span_singleton_of_not_mem hp
  have hdimstep := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K (rowPrefix5 rows (E k).val)) (K ∙ rows (E k))
  rw [hdisjoint.eq_bot,finrank_bot,add_zero,finrank_span_singleton hnonzero,hprev] at hdimstep
  constructor
  · rw [rowPrefix5_succ rows (E k).val (E k).isLt,Submodule.span_insert,sup_comm]
    exact hdimstep
  · intro i hi
    calc
      _ ≤ Module.finrank K (Submodule.span K (rowPrefix5 rows (E k).val)) := by
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro x ⟨a,ha,rfl⟩
        have hle : i.val+1 ≤ (E k).val := by
          change i.val < (E k).val at hi
          omega
        exact ⟨a,lt_of_lt_of_le ha hle,rfl⟩
      _ = _ := hprev

end
end CompoundFeasibility.RestrictedGreedyRanks5
