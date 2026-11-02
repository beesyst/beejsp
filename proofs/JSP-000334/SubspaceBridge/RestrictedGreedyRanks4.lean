import SubspaceBridge.SelectedRestriction4
open scoped BigOperators Classical
namespace CompoundFeasibility.RestrictedGreedyRanks4
open RestrictedGreedyRows4
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem greedyIndex4_prefix_set (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    greedyPrefix4 (K := K) rows (greedyIndex4 rows hfull d hdim k).val =
      Set.range (fun a : Fin k.val => greedyIndex4 rows hfull d hdim (Fin.castLE (by omega) a)) := by
  let E := greedyIndex4 rows hfull d hdim
  have hrange : Set.range E = (greedyFinset4 (K := K) rows : Set (Fin 4)) :=
    (greedyFinset4 (K := K) rows).range_orderEmbOfFin ((greedyFinset4_card (K := K) rows hfull).trans hdim)
  ext i
  constructor
  · intro hi
    have himem : i ∈ (greedyFinset4 (K := K) rows : Set (Fin 4)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.2⟩
    rw [← hrange] at himem
    obtain ⟨a,rfl⟩ := himem
    have ha : a < k := E.lt_iff_lt.mp hi.1
    refine ⟨⟨a.val,ha⟩,?_⟩
    congr 1
  · rintro ⟨a,rfl⟩
    exact ⟨E.strictMono (show Fin.castLE (by omega) a < k from a.isLt),
      greedyIndex4_pivot rows hfull d hdim _⟩

theorem greedyIndex4_prefix_rank (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    Module.finrank K (Submodule.span K (rowPrefix4 rows (greedyIndex4 rows hfull d hdim k).val)) = k.val := by
  have hs := (greedyPrefix4_independent_span (K := K) rows
    (greedyIndex4 rows hfull d hdim k).val (by omega)).2
  rw [← hs,greedyIndex4_prefix_set rows hfull d hdim k,← Set.range_comp]
  have hli := (greedyIndex4_independent rows hfull d hdim).comp
    (fun a : Fin k.val => Fin.castLE (by omega) a) (Fin.castLE_injective (by omega))
  simpa only [Fintype.card_fin] using finrank_span_eq_card hli

theorem greedyIndex4_first_rank_increase (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    Module.finrank K (Submodule.span K (rowPrefix4 rows
      ((greedyIndex4 rows hfull d hdim k).val+1))) = k.val+1 ∧
    ∀ i : Fin 4, i < greedyIndex4 rows hfull d hdim k →
      Module.finrank K (Submodule.span K (rowPrefix4 rows (i.val+1))) ≤ k.val := by
  let E := greedyIndex4 rows hfull d hdim
  have hp := greedyIndex4_pivot rows hfull d hdim k
  have hprev := greedyIndex4_prefix_rank rows hfull d hdim k
  have hnonzero : rows (E k) ≠ 0 := by
    intro hz
    apply hp
    rw [hz]
    exact Submodule.zero_mem _
  have hdisjoint := Submodule.disjoint_span_singleton_of_not_mem hp
  have hdimstep := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K (rowPrefix4 rows (E k).val)) (K ∙ rows (E k))
  rw [hdisjoint.eq_bot,finrank_bot,add_zero,finrank_span_singleton hnonzero,hprev] at hdimstep
  constructor
  · rw [rowPrefix4_succ rows (E k).val (E k).isLt,Submodule.span_insert,sup_comm]
    exact hdimstep
  · intro i hi
    calc
      _ ≤ Module.finrank K (Submodule.span K (rowPrefix4 rows (E k).val)) := by
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro x ⟨a,ha,rfl⟩
        have hle : i.val+1 ≤ (E k).val := by
          change i.val < (E k).val at hi
          omega
        exact ⟨a,lt_of_lt_of_le ha hle,rfl⟩
      _ = _ := hprev

end
end CompoundFeasibility.RestrictedGreedyRanks4
