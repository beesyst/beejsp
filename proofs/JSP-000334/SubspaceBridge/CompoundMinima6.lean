import SubspaceBridge.CompoundMinima42
open scoped BigOperators Matrix
namespace CompoundFeasibility
abbrev lattice6Span (b : Basis (Fin 6) ℝ (Fin 6 → ℝ)) : Submodule ℤ (Fin 6 → ℝ) :=
  Submodule.span ℤ (Set.range b)
def coordinateGauge6 (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (x : Fin 6 → ℝ) : ℝ := ‖e x‖
theorem lattice6Span_gauge_ball_finite (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (r : ℝ) :
    ({x : (Fin 6 → ℝ) | coordinateGauge6 e x ≤ r} ∩ (lattice6Span b : Set (Fin 6 → ℝ))).Finite := by
  have hf := ZSpan.setFinite_inter (b.map e) (Metric.isBounded_closedBall (x := 0) (r := r))
  apply (hf.preimage e.injective.injOn).subset
  intro x hx
  refine ⟨?_, ?_⟩
  · simpa [coordinateGauge6, Metric.mem_closedBall, dist_zero_right] using hx.1
  · have hm := Submodule.mem_map_of_mem (f := (e.restrictScalars ℤ).toLinearMap) hx.2
    simpa only [lattice6Span, Submodule.map_span, Set.range_comp,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Basis.coe_map] using hm

theorem exists_shortest_lattice6Span_vector_outside (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (W : Submodule ℝ (Fin 6 → ℝ)) (hW : W ≠ ⊤) :
    ∃ x ∈ lattice6Span b, x ∉ W ∧ 0 < coordinateGauge6 e x ∧
      ∀ y ∈ lattice6Span b, y ∉ W → coordinateGauge6 e x ≤ coordinateGauge6 e y := by
  classical
  have hex : ∃ i, b i ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  obtain ⟨i, hi⟩ := hex
  let s : Set (Fin 6 → ℝ) :=
    {x | coordinateGauge6 e x ≤ coordinateGauge6 e (b i)} ∩
      (lattice6Span b : Set (Fin 6 → ℝ)) ∩ {x | x ∉ W}
  have hs : s.Finite := (lattice6Span_gauge_ball_finite b e _).inter_of_left _
  have hbi : b i ∈ lattice6Span b := Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image s (coordinateGauge6 e) hs
    ⟨b i, ⟨⟨show coordinateGauge6 e (b i) ≤ coordinateGauge6 e (b i) from le_rfl, hbi⟩, hi⟩⟩
  refine ⟨x, hx.1.2, hx.2, ?_, ?_⟩
  · apply norm_pos_iff.mpr
    intro h0
    have : x = 0 := e.injective (h0.trans e.map_zero.symm)
    exact hx.2 (this ▸ W.zero_mem)
  · intro y hy hyW
    by_cases hle : coordinateGauge6 e y ≤ coordinateGauge6 e (b i)
    · exact hmin y ⟨⟨hle, hy⟩, hyW⟩
    · exact hx.1.1.trans (le_of_not_ge hle)

noncomputable def successiveRadius6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (k : Fin 6) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val + 1) → (Fin 6 → ℝ),
    LinearIndependent ℝ u ∧ (∀ i, u i ∈ lattice6Span b) ∧
      ∀ i, coordinateGauge6 e (u i) ≤ r}

theorem independent_family_escapes_subspace6 {n : ℕ} (u : Fin n → (Fin 6 → ℝ))
    (hu : LinearIndependent ℝ u) (W : Submodule ℝ (Fin 6 → ℝ))
    (hW : Module.finrank ℝ W < n) : ∃ i, u i ∉ W := by
  by_contra! h
  have hs : Submodule.span ℝ (Set.range u) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  have hd := Submodule.finrank_mono hs
  rw [finrank_span_eq_card hu, Fintype.card_fin] at hd
  omega


theorem exists_successive_minima6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) :
    ∃ v : Fin 6 → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ lattice6Span b) ∧
      (∀ i, 0 < successiveRadius6 b e i) ∧
      Monotone (successiveRadius6 b e) ∧
      ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i := by
  classical
  let W0 : Submodule ℝ (Fin 6 → ℝ) := ⊥
  have hdim0 : Module.finrank ℝ W0 = 0 := by simp [W0]
  have hW0 : W0 ≠ ⊤ := bot_ne_top
  obtain ⟨x0, hx0L, hx0W, hx0pos, hx0min⟩ :=
    exists_shortest_lattice6Span_vector_outside b e W0 hW0
  let u1 : Fin 1 → (Fin 6 → ℝ) := ![x0]
  have hu1 : LinearIndependent ℝ u1 := linearIndependent_unique u1 (by simpa [W0] using hx0W)
  let W1 := Submodule.span ℝ (Set.range u1)
  have hdim1 : Module.finrank ℝ W1 = 1 := by
    simpa [W1] using finrank_span_eq_card hu1
  have hW1 : W1 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W1 = 6 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x1, hx1L, hx1W, hx1pos, hx1min⟩ :=
    exists_shortest_lattice6Span_vector_outside b e W1 hW1
  let u2 : Fin 2 → (Fin 6 → ℝ) := Fin.snoc u1 x1
  have hu2 : LinearIndependent ℝ u2 := linearIndependent_fin_snoc.mpr ⟨hu1,hx1W⟩
  let W2 := Submodule.span ℝ (Set.range u2)
  have hdim2 : Module.finrank ℝ W2 = 2 := by
    simpa [W2] using finrank_span_eq_card hu2
  have hW2 : W2 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W2 = 6 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x2, hx2L, hx2W, hx2pos, hx2min⟩ :=
    exists_shortest_lattice6Span_vector_outside b e W2 hW2
  let u3 : Fin 3 → (Fin 6 → ℝ) := Fin.snoc u2 x2
  have hu3 : LinearIndependent ℝ u3 := linearIndependent_fin_snoc.mpr ⟨hu2,hx2W⟩
  let W3 := Submodule.span ℝ (Set.range u3)
  have hdim3 : Module.finrank ℝ W3 = 3 := by
    simpa [W3] using finrank_span_eq_card hu3
  have hW3 : W3 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W3 = 6 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x3, hx3L, hx3W, hx3pos, hx3min⟩ :=
    exists_shortest_lattice6Span_vector_outside b e W3 hW3
  let u4 : Fin 4 → (Fin 6 → ℝ) := Fin.snoc u3 x3
  have hu4 : LinearIndependent ℝ u4 := linearIndependent_fin_snoc.mpr ⟨hu3,hx3W⟩
  let W4 := Submodule.span ℝ (Set.range u4)
  have hdim4 : Module.finrank ℝ W4 = 4 := by
    simpa [W4] using finrank_span_eq_card hu4
  have hW4 : W4 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W4 = 6 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x4, hx4L, hx4W, hx4pos, hx4min⟩ :=
    exists_shortest_lattice6Span_vector_outside b e W4 hW4
  let u5 : Fin 5 → (Fin 6 → ℝ) := Fin.snoc u4 x4
  have hu5 : LinearIndependent ℝ u5 := linearIndependent_fin_snoc.mpr ⟨hu4,hx4W⟩
  let W5 := Submodule.span ℝ (Set.range u5)
  have hdim5 : Module.finrank ℝ W5 = 5 := by
    simpa [W5] using finrank_span_eq_card hu5
  have hW5 : W5 ≠ ⊤ := by
    intro h
    have hd : Module.finrank ℝ W5 = 6 := by rw [h]; simp [Module.finrank_pi]
    omega
  obtain ⟨x5, hx5L, hx5W, hx5pos, hx5min⟩ :=
    exists_shortest_lattice6Span_vector_outside b e W5 hW5
  let u6 : Fin 6 → (Fin 6 → ℝ) := Fin.snoc u5 x5
  have hu6 : LinearIndependent ℝ u6 := linearIndependent_fin_snoc.mpr ⟨hu5,hx5W⟩
  have hle0 : coordinateGauge6 e x0 ≤ coordinateGauge6 e x1 := by
    apply hx0min x1 hx1L
    intro h
    exact hx1W (show x1 ∈ W1 from (show W0 ≤ W1 from bot_le) h)
  have hle1 : coordinateGauge6 e x1 ≤ coordinateGauge6 e x2 := by
    apply hx1min x2 hx2L
    intro h
    apply hx2W
    apply (Submodule.span_mono (show Set.range u1 ⊆ Set.range u2 from ?_)) h
    rintro _ ⟨j,rfl⟩
    exact ⟨j.castSucc,by simp [u2]⟩
  have hle2 : coordinateGauge6 e x2 ≤ coordinateGauge6 e x3 := by
    apply hx2min x3 hx3L
    intro h
    apply hx3W
    apply (Submodule.span_mono (show Set.range u2 ⊆ Set.range u3 from ?_)) h
    rintro _ ⟨j,rfl⟩
    exact ⟨j.castSucc,by simp [u3]⟩
  have hle3 : coordinateGauge6 e x3 ≤ coordinateGauge6 e x4 := by
    apply hx3min x4 hx4L
    intro h
    apply hx4W
    apply (Submodule.span_mono (show Set.range u3 ⊆ Set.range u4 from ?_)) h
    rintro _ ⟨j,rfl⟩
    exact ⟨j.castSucc,by simp [u4]⟩
  have hle4 : coordinateGauge6 e x4 ≤ coordinateGauge6 e x5 := by
    apply hx4min x5 hx5L
    intro h
    apply hx5W
    apply (Submodule.span_mono (show Set.range u4 ⊆ Set.range u5 from ?_)) h
    rintro _ ⟨j,rfl⟩
    exact ⟨j.castSucc,by simp [u5]⟩
  have hrad0 : successiveRadius6 b e 0 = coordinateGauge6 e x0 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u1,hu1,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, u5, u6, Fin.snoc,hx0L,hx1L,hx2L,hx3L,hx4L,hx5L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x0 ≤ coordinateGauge6 e x0 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace6 u hu W0 (by omega)
      exact (hx0min (u j) (huL j) hj).trans (hur j)
  have hrad1 : successiveRadius6 b e 1 = coordinateGauge6 e x1 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u2,hu2,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, u5, u6, Fin.snoc,hx0L,hx1L,hx2L,hx3L,hx4L,hx5L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x0 ≤ coordinateGauge6 e x1 from hle0)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x1 ≤ coordinateGauge6 e x1 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace6 u hu W1 (by omega)
      exact (hx1min (u j) (huL j) hj).trans (hur j)
  have hrad2 : successiveRadius6 b e 2 = coordinateGauge6 e x2 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u3,hu3,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, u5, u6, Fin.snoc,hx0L,hx1L,hx2L,hx3L,hx4L,hx5L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x0 ≤ coordinateGauge6 e x2 from (hle0).trans hle1)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x1 ≤ coordinateGauge6 e x2 from hle1)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x2 ≤ coordinateGauge6 e x2 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace6 u hu W2 (by omega)
      exact (hx2min (u j) (huL j) hj).trans (hur j)
  have hrad3 : successiveRadius6 b e 3 = coordinateGauge6 e x3 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u4,hu4,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, u5, u6, Fin.snoc,hx0L,hx1L,hx2L,hx3L,hx4L,hx5L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x0 ≤ coordinateGauge6 e x3 from ((hle0).trans hle1).trans hle2)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x1 ≤ coordinateGauge6 e x3 from (hle1).trans hle2)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x2 ≤ coordinateGauge6 e x3 from hle2)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x3 ≤ coordinateGauge6 e x3 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace6 u hu W3 (by omega)
      exact (hx3min (u j) (huL j) hj).trans (hur j)
  have hrad4 : successiveRadius6 b e 4 = coordinateGauge6 e x4 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u5,hu5,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, u5, u6, Fin.snoc,hx0L,hx1L,hx2L,hx3L,hx4L,hx5L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x0 ≤ coordinateGauge6 e x4 from (((hle0).trans hle1).trans hle2).trans hle3)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x1 ≤ coordinateGauge6 e x4 from ((hle1).trans hle2).trans hle3)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x2 ≤ coordinateGauge6 e x4 from (hle2).trans hle3)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x3 ≤ coordinateGauge6 e x4 from hle3)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x4 ≤ coordinateGauge6 e x4 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace6 u hu W4 (by omega)
      exact (hx4min (u j) (huL j) hj).trans (hur j)
  have hrad5 : successiveRadius6 b e 5 = coordinateGauge6 e x5 := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨u6,hu6,?_,?_⟩
      · intro j
        fin_cases j <;> norm_num [u1, u2, u3, u4, u5, u6, Fin.snoc,hx0L,hx1L,hx2L,hx3L,hx4L,hx5L]
      · intro j
        fin_cases j
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x0 ≤ coordinateGauge6 e x5 from ((((hle0).trans hle1).trans hle2).trans hle3).trans hle4)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x1 ≤ coordinateGauge6 e x5 from (((hle1).trans hle2).trans hle3).trans hle4)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x2 ≤ coordinateGauge6 e x5 from ((hle2).trans hle3).trans hle4)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x3 ≤ coordinateGauge6 e x5 from (hle3).trans hle4)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x4 ≤ coordinateGauge6 e x5 from hle4)
        · simpa [u1, u2, u3, u4, u5, u6, Fin.snoc] using (show coordinateGauge6 e x5 ≤ coordinateGauge6 e x5 from le_rfl)
    · rintro r ⟨u,hu,huL,hur⟩
      obtain ⟨j,hj⟩ := independent_family_escapes_subspace6 u hu W5 (by omega)
      exact (hx5min (u j) (huL j) hj).trans (hur j)
  refine ⟨u6,hu6,?_,?_,?_,?_⟩
  · intro j
    fin_cases j <;> norm_num [u1, u2, u3, u4, u5, u6, Fin.snoc,hx0L,hx1L,hx2L,hx3L,hx4L,hx5L]
  · intro j
    fin_cases j
    · simpa [hrad0] using hx0pos
    · simpa [hrad1] using hx1pos
    · simpa [hrad2] using hx2pos
    · simpa [hrad3] using hx3pos
    · simpa [hrad4] using hx4pos
    · simpa [hrad5] using hx5pos
  · apply Fin.monotone_iff_le_succ.mpr
    intro j
    fin_cases j
    · change successiveRadius6 b e 0 ≤ successiveRadius6 b e 1
      rw [hrad0,hrad1]
      exact hle0
    · change successiveRadius6 b e 1 ≤ successiveRadius6 b e 2
      rw [hrad1,hrad2]
      exact hle1
    · change successiveRadius6 b e 2 ≤ successiveRadius6 b e 3
      rw [hrad2,hrad3]
      exact hle2
    · change successiveRadius6 b e 3 ≤ successiveRadius6 b e 4
      rw [hrad3,hrad4]
      exact hle3
    · change successiveRadius6 b e 4 ≤ successiveRadius6 b e 5
      rw [hrad4,hrad5]
      exact hle4
  · intro j
    fin_cases j
    · change coordinateGauge6 e (u6 0) = successiveRadius6 b e 0
      rw [hrad0]
      norm_num [u1,u2,u3,u4,u5,u6,Fin.snoc]
    · change coordinateGauge6 e (u6 1) = successiveRadius6 b e 1
      rw [hrad1]
      norm_num [u1,u2,u3,u4,u5,u6,Fin.snoc]
    · change coordinateGauge6 e (u6 2) = successiveRadius6 b e 2
      rw [hrad2]
      norm_num [u1,u2,u3,u4,u5,u6,Fin.snoc]
    · change coordinateGauge6 e (u6 3) = successiveRadius6 b e 3
      rw [hrad3]
      have hv3 : u6 (3 : Fin 6) = x3 := by
        calc
          u6 (3 : Fin 6) = u5 (3 : Fin 5) := by rfl
          _ = u4 (3 : Fin 4) := by rfl
          _ = x3 := by rfl
      exact congrArg (coordinateGauge6 e) hv3
    · change coordinateGauge6 e (u6 4) = successiveRadius6 b e 4
      rw [hrad4]
      have hv4 : u6 (4 : Fin 6) = x4 := by
        calc
          u6 (4 : Fin 6) = u5 (4 : Fin 5) := by rfl
          _ = x4 := by rfl
      exact congrArg (coordinateGauge6 e) hv4
    · change coordinateGauge6 e (u6 5) = successiveRadius6 b e 5
      rw [hrad5]
      have hv5 : u6 (5 : Fin 6) = x5 := by
        rfl
      exact congrArg (coordinateGauge6 e) hv5

end CompoundFeasibility

namespace CompoundFeasibility

noncomputable def weightedCoordinates6 (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (w : Fin 6 → ℝ) (hw : ∀ i, 0 < w i) : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) where
  toFun x i := e x i / w i
  invFun y := e.symm (fun i => y i * w i)
  map_add' x y := by ext i; simp [add_div]
  map_smul' r x := by ext i; simp [smul_eq_mul,mul_div_assoc]
  left_inv x := by
    change e.symm (fun i => (e x i / w i) * w i) = x
    have h : (fun i => (e x i / w i) * w i) = e x :=
      funext (fun i => div_mul_cancel₀ _ (hw i).ne')
    rw [h,e.symm_apply_apply]
  right_inv y := by
    change (fun i => e (e.symm (fun j => y j * w j)) i / w i) = y
    rw [e.apply_symm_apply]
    exact funext (fun i => mul_div_cancel_right₀ _ (hw i).ne')

noncomputable def compoundFormEquiv42 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (compound L)) (by
    have hu := compound_unit L hL
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem compoundFormEquiv42_apply (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (x : Fin 6 → ℝ) : compoundFormEquiv42 L hL x = compound L *ᵥ x := rfl

noncomputable def compoundCoordinates42 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  weightedCoordinates6 (compoundFormEquiv42 L hL)
    (fun s => Q ^ c₀ (lo s) * Q ^ c₀ (hi s))
    (fun s => mul_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _))

def compoundBody42 (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ : Fin 4 → ℝ) : Set (Fin 6 → ℝ) :=
  {x | ∀ s, |(compound L *ᵥ x) s| ≤ Q ^ c₀ (lo s) * Q ^ c₀ (hi s)}

theorem compoundCoordinates42_bounds (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) (r : ℝ) :
    ‖compoundCoordinates42 L hL Q hQ c₀ x‖ ≤ r ↔
      ∀ s, |(compound L *ᵥ x) s| ≤ r * (Q ^ c₀ (lo s) * Q ^ c₀ (hi s)) := by
  rw [pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro s
  have hw : 0 < Q ^ c₀ (lo s) * Q ^ c₀ (hi s) := mul_pos
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  change ‖(compound L *ᵥ x) s / (Q ^ c₀ (lo s) * Q ^ c₀ (hi s))‖ ≤ r ↔ _
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hw,div_le_iff₀ hw]

theorem compoundBody42_mem_iff (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) :
    x ∈ compoundBody42 L Q c₀ ↔ ‖compoundCoordinates42 L hL Q hQ c₀ x‖ ≤ 1 := by
  rw [compoundCoordinates42_bounds]
  simp only [one_mul,compoundBody42,Set.mem_setOf_eq]


noncomputable def sourceRealBasis6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : Basis (Fin 6) ℝ (Fin 6 → ℝ) :=
  (integerRealImageBasis (sourceLattice6 A₂ A₃ e₂ e₃)
    (sourceLattice6_has_basis A₂ A₃ e₂ e₃).some).ofZLatticeBasis ℝ
      (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃))

theorem sourceRealBasis6_span (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) :
    lattice6Span (sourceRealBasis6 A₂ A₃ e₂ e₃) = integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃) :=
  Basis.ofZLatticeBasis_span ℝ (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃))
    (integerRealImageBasis (sourceLattice6 A₂ A₃ e₂ e₃) (sourceLattice6_has_basis A₂ A₃ e₂ e₃).some)

noncomputable def compoundSourceGroup6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : AddSubgroup (Fin 6 → ℤ) :=
  sourceLattice6 A₂ A₃ (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))

noncomputable def sourceMinima6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ u ∧
    (∀ i, u i ∈ integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃)) ∧
    ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (u i) ≤ r}

theorem sourceMinima6_eq_radius (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j =
      successiveRadius6 (sourceRealBasis6 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))
        (compoundCoordinates42 L hL Q hQ c₀) j := by
  simp only [sourceMinima6,successiveRadius6,sourceRealBasis6_span,compoundSourceGroup6]

theorem exists_sourceMinima6_attaining (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ u : Fin 6 → compoundSourceGroup6 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 6 → ℤ)) ∧
      (∀ j, 0 < sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀)
        (integerReal (u j : Fin 6 → ℤ)) = sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      ∀ j s, |(compound L *ᵥ integerReal (u j : Fin 6 → ℤ)) s| ≤
        sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j * (Q ^ c₀ (lo s) * Q ^ c₀ (hi s)) := by
  classical
  let e₂ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))
  let e₃ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))
  let b := sourceRealBasis6 A₂ A₃ e₂ e₃
  let e := compoundCoordinates42 L hL Q hQ c₀
  obtain ⟨v,hv,hvL,hpos,hmono,hatt⟩ := exists_successive_minima6 b e
  have hrad (j : Fin 6) : sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = successiveRadius6 b e j :=
    sourceMinima6_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hvImage (j : Fin 6) : v j ∈ integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃) := by
    change v j ∈ integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)
    rw [← sourceRealBasis6_span A₂ A₃ e₂ e₃]
    exact hvL j
  have hlift (j : Fin 6) : ∃ x : compoundSourceGroup6 A₂ A₃ Q c₂ c₃,
      integerReal (x : Fin 6 → ℤ) = v j := by
    obtain ⟨x,hx,he⟩ := hvImage j
    exact ⟨⟨x,hx⟩,he⟩
  choose u hu using hlift
  have hfun : (fun j => integerReal (u j : Fin 6 → ℤ)) = v := funext hu
  refine ⟨u,?_,?_,?_,?_,?_⟩
  · rw [hfun]
    exact hv
  · intro j
    rw [hrad]
    exact hpos j
  · intro i j hij
    rw [hrad,hrad]
    exact hmono hij
  · intro j
    rw [hu j,hrad]
    exact hatt j
  · intro j
    apply (compoundCoordinates42_bounds L hL Q hQ c₀ _ _).mp
    change coordinateGauge6 e (integerReal (u j : Fin 6 → ℤ)) ≤ _
    rw [hu j,hrad,hatt j]


theorem sourceMinima6_admissible (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤
        sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima6_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let f : Fin (j.val+1) → Fin 6 := Fin.castLE (by omega)
  refine ⟨fun i => integerReal (u (f i) : Fin 6 → ℤ),
    hu.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    exact ⟨(u (f i) : Fin 6 → ℤ),(u (f i)).property,rfl⟩
  · intro i
    rw [hatt]
    exact hmono (show f i ≤ j from (by change i.val ≤ j.val; omega))

theorem sourceMinima6_radius_set_properties (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    let S := {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤ r}
    S.Nonempty ∧ BddBelow S ∧ IsLeast S (sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) := by
  dsimp only
  have hm := sourceMinima6_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hne : ({r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤ r}).Nonempty := ⟨_,hm⟩
  have hb : BddBelow {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (v i) ≤ r} := by
    refine ⟨0,?_⟩
    rintro r ⟨v,_,_,hv⟩
    exact (norm_nonneg _).trans (hv 0)
  refine ⟨hne,hb,hm,?_⟩
  intro r hr
  exact csInf_le hb hr

theorem sourceMinima6_pos_mono (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∀ j, 0 < sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima6_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨hpos,hmono⟩

theorem source_compound_uniform_minima_lower6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c₆ : ℝ, 0 < c₆ ∧ c₆ = |(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        c₆ ≤ ∏ j : Fin 6, sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨c₆,hpos,hval,hframe⟩ := source_compound_uniform_frame_lower42 A₂ A₃ L h₂ h₃ hL
  refine ⟨c₆,hpos,hval,?_⟩
  intro Q hQ c₀ c₂ c₃ hb
  obtain ⟨u,hu,_,_,hatt,hpoint⟩ := exists_sourceMinima6_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact hframe Q hQ c₀ c₂ c₃ hb u hu (sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃) hpoint

theorem sourceMinima6_product_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    0 < |(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720 ∧
      |(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720 ≤
        ∏ j : Fin 6, sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨c₆,hpos,hval,hbound⟩ := source_compound_uniform_minima_lower6 A₂ A₃ L h₂ h₃ hL
  rw [← hval]
  exact ⟨hpos,hbound Q hQ c₀ c₂ c₃ hb⟩

end CompoundFeasibility
