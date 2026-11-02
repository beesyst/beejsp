import SubspaceBridge.DetNormalization4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.RowScaleSelection4
open RestrictedGreedyRows4 RestrictedRows4 SelectedRestriction4 RestrictedWeightOrder4
noncomputable section

theorem rowPrefix4_span_scale {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rows rows' : Fin 4 → V) (lambda : Fin 4 → K) (hn : ∀ i, lambda i ≠ 0)
    (hr : ∀ i, rows' i = lambda i • rows i) (n : ℕ) :
    Submodule.span K (rowPrefix4 rows' n) = Submodule.span K (rowPrefix4 rows n) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    rw [hr i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    have h : rows' i ∈ Submodule.span K (rowPrefix4 rows' n) :=
      Submodule.subset_span ⟨i,hi,rfl⟩
    rw [hr i] at h
    exact (Submodule.smul_mem_iff _ (hn i)).mp h

theorem greedyPivot4_scale_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rows rows' : Fin 4 → V) (lambda : Fin 4 → K) (hn : ∀ i, lambda i ≠ 0)
    (hr : ∀ i, rows' i = lambda i • rows i) (i : Fin 4) :
    greedyPivot4 (K := K) rows' i ↔ greedyPivot4 (K := K) rows i := by
  unfold greedyPivot4
  rw [rowPrefix4_span_scale rows rows' lambda hn hr,hr i]
  exact not_congr (Submodule.smul_mem_iff _ (hn i))

theorem greedyFinset4_scale {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rows rows' : Fin 4 → V) (lambda : Fin 4 → K) (hn : ∀ i, lambda i ≠ 0)
    (hr : ∀ i, rows' i = lambda i • rows i) :
    greedyFinset4 (K := K) rows' = greedyFinset4 (K := K) rows := by
  ext i
  simp only [greedyFinset4,Finset.mem_filter,Finset.mem_univ,true_and]
  exact greedyPivot4_scale_iff rows rows' lambda hn hr i

theorem greedyIndex4_scale {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (rows rows' : Fin 4 → V) (lambda : Fin 4 → K)
    (hn : ∀ i, lambda i ≠ 0) (hr : ∀ i, rows' i = lambda i • rows i)
    (hf : Submodule.span K (Set.range rows) = ⊤)
    (hf' : Submodule.span K (Set.range rows') = ⊤)
    (d : ℕ) (hd : Module.finrank K V = d) :
    greedyIndex4 rows' hf' d hd = greedyIndex4 rows hf d hd := by
  have hs := greedyFinset4_scale rows rows' lambda hn hr
  simp only [greedyIndex4,hs]

theorem selectedIndex4_scale {K : Type*} [Field K] {d : ℕ}
    (M N : Matrix (Fin 4) (Fin d) K) (lambda : Fin 4 → K)
    (hn : ∀ i, lambda i ≠ 0) (hr : ∀ i, N i = lambda i • M i)
    (c : Fin 4 → ℝ) (hf : Submodule.span K (Set.range M.row) = ⊤)
    (hf' : Submodule.span K (Set.range N.row) = ⊤) :
    selectedIndex4 N c hf' = selectedIndex4 M c hf := by
  exact greedyIndex4_scale (sortedRows4 M c) (sortedRows4 N c)
    (fun i => lambda (weightOrder4 c i)) (fun i => hn _) (fun i => hr _)
    (sortedRows4_span M c hf) (sortedRows4_span N c hf') d (by simp)

theorem rowCoordinates4_normalized {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    rowCoordinates4 P b (DetNormalization4.normalizedDet4 A) i =
      DetNormalization4.detRowMultiplier4 A i • rowCoordinates4 P b A i := by
  ext k
  exact DetNormalization4.normalizedDet4_mulVec A (b k) i

end
end CompoundFeasibility.RowScaleSelection4
