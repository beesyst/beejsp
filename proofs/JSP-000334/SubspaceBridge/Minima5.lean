import SubspaceBridge.InvertibleCriterion4
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section
abbrev lattice5Span (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) : Submodule ℤ (Fin 5 → ℝ) :=
  Submodule.span ℤ (Set.range b)
def coordinateGauge5 (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (x : Fin 5 → ℝ) : ℝ := ‖e x‖
theorem lattice5Span_gauge_ball_finite (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (r : ℝ) :
    ({x : (Fin 5 → ℝ) | coordinateGauge5 e x ≤ r} ∩ (lattice5Span b : Set (Fin 5 → ℝ))).Finite := by
  have hf := ZSpan.setFinite_inter (b.map e) (Metric.isBounded_closedBall (x := 0) (r := r))
  apply (hf.preimage e.injective.injOn).subset
  intro x hx
  refine ⟨?_, ?_⟩
  · simpa [coordinateGauge5, Metric.mem_closedBall, dist_zero_right] using hx.1
  · have hm := Submodule.mem_map_of_mem (f := (e.restrictScalars ℤ).toLinearMap) hx.2
    simpa only [lattice5Span, Submodule.map_span, Set.range_comp,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Basis.coe_map] using hm

theorem exists_shortest_lattice5Span_vector_outside (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (W : Submodule ℝ (Fin 5 → ℝ)) (hW : W ≠ ⊤) :
    ∃ x ∈ lattice5Span b, x ∉ W ∧ 0 < coordinateGauge5 e x ∧
      ∀ y ∈ lattice5Span b, y ∉ W → coordinateGauge5 e x ≤ coordinateGauge5 e y := by
  classical
  have hex : ∃ i, b i ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  obtain ⟨i, hi⟩ := hex
  let s : Set (Fin 5 → ℝ) :=
    {x | coordinateGauge5 e x ≤ coordinateGauge5 e (b i)} ∩
      (lattice5Span b : Set (Fin 5 → ℝ)) ∩ {x | x ∉ W}
  have hs : s.Finite := (lattice5Span_gauge_ball_finite b e _).inter_of_left _
  have hbi : b i ∈ lattice5Span b := Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image s (coordinateGauge5 e) hs
    ⟨b i, ⟨⟨show coordinateGauge5 e (b i) ≤ coordinateGauge5 e (b i) from le_rfl, hbi⟩, hi⟩⟩
  refine ⟨x, hx.1.2, hx.2, ?_, ?_⟩
  · apply norm_pos_iff.mpr
    intro h0
    have : x = 0 := e.injective (h0.trans e.map_zero.symm)
    exact hx.2 (this ▸ W.zero_mem)
  · intro y hy hyW
    by_cases hle : coordinateGauge5 e y ≤ coordinateGauge5 e (b i)
    · exact hmin y ⟨⟨hle, hy⟩, hyW⟩
    · exact hx.1.1.trans (le_of_not_ge hle)

noncomputable def successiveRadius5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (k : Fin 5) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val + 1) → (Fin 5 → ℝ),
    LinearIndependent ℝ u ∧ (∀ i, u i ∈ lattice5Span b) ∧
      ∀ i, coordinateGauge5 e (u i) ≤ r}

theorem independent_family_escapes_subspace5 {n : ℕ} (u : Fin n → (Fin 5 → ℝ))
    (hu : LinearIndependent ℝ u) (W : Submodule ℝ (Fin 5 → ℝ))
    (hW : Module.finrank ℝ W < n) : ∃ i, u i ∉ W := by
  by_contra! h
  have hs : Submodule.span ℝ (Set.range u) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  have hd := Submodule.finrank_mono hs
  rw [finrank_span_eq_card hu, Fintype.card_fin] at hd
  omega



def minimaPrefix5 {n : ℕ} (v : Fin n → Fin 5 → ℝ) (i : Fin n) : Submodule ℝ (Fin 5 → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : Fin i.val => v (Fin.castLE (by omega) j)))

theorem minimaPrefix5_snoc_castSucc {n : ℕ} (v : Fin n → Fin 5 → ℝ)
    (x : Fin 5 → ℝ) (i : Fin n) :
    minimaPrefix5 (Fin.snoc v x) i.castSucc = minimaPrefix5 v i := by
  unfold minimaPrefix5
  apply congrArg (fun u : Fin i.val → Fin 5 → ℝ => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) =
      (Fin.castLE (Nat.le_of_lt i.isLt) j).castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]

theorem minimaPrefix5_snoc_last {n : ℕ} (v : Fin n → Fin 5 → ℝ) (x : Fin 5 → ℝ) :
    minimaPrefix5 (Fin.snoc v x) (Fin.last n) = Submodule.span ℝ (Set.range v) := by
  unfold minimaPrefix5
  apply congrArg (fun u : Fin n → Fin 5 → ℝ => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) = j.castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]

theorem exists_greedy_prefix5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) :
    ∀ n ≤ 5, ∃ v : Fin n → Fin 5 → ℝ,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ lattice5Span b) ∧
      ∀ i, ∀ y ∈ lattice5Span b, y ∉ minimaPrefix5 v i →
        coordinateGauge5 e (v i) ≤ coordinateGauge5 e y := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨Fin.elim0,linearIndependent_empty_type,(fun i => Fin.elim0 i),fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro hn
    obtain ⟨v,hv,hvL,hmin⟩ := ih (by omega)
    let W := Submodule.span ℝ (Set.range v)
    have hW : W ≠ ⊤ := by
      intro h
      have hd := finrank_span_eq_card hv
      simp only [Fintype.card_fin] at hd
      change Module.finrank ℝ W = n at hd
      rw [h,finrank_top,Module.finrank_pi,Fintype.card_fin] at hd
      omega
    obtain ⟨x,hxL,hxW,hxpos,hxmin⟩ := exists_shortest_lattice5Span_vector_outside b e W hW
    refine ⟨Fin.snoc v x,linearIndependent_fin_snoc.mpr ⟨hv,hxW⟩,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hxL
      · simpa only [Fin.snoc_castSucc] using hvL j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [minimaPrefix5_snoc_last]
        simpa only [Fin.snoc_last] using hxmin
      · rw [minimaPrefix5_snoc_castSucc]
        simpa only [Fin.snoc_castSucc] using hmin j

theorem minimaPrefix5_not_mem {n : ℕ} (v : Fin n → Fin 5 → ℝ)
    (hv : LinearIndependent ℝ v) (i j : Fin n) (hij : i ≤ j) : v j ∉ minimaPrefix5 v i := by
  have hle : minimaPrefix5 v i ≤ Submodule.span ℝ (v '' {t | t < i}) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact Submodule.subset_span ⟨Fin.castLE (by omega) a,by change a.val < i.val; exact a.isLt,rfl⟩
  exact fun h => hv.not_mem_span_image (s := {t | t < i}) (x := j) (not_lt_of_ge hij) (hle h)

theorem minimaPrefix5_finrank {n : ℕ} (v : Fin n → Fin 5 → ℝ)
    (hv : LinearIndependent ℝ v) (i : Fin n) : Module.finrank ℝ (minimaPrefix5 v i) = i.val := by
  exact (finrank_span_eq_card (hv.comp (Fin.castLE (by omega) : Fin i.val → Fin n)
    (Fin.castLE_injective _))).trans (Fintype.card_fin i.val)

theorem exists_successive_minima5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) :
    ∃ v : Fin 5 → Fin 5 → ℝ, LinearIndependent ℝ v ∧
      (∀ i, v i ∈ lattice5Span b) ∧ (∀ i, 0 < successiveRadius5 b e i) ∧
      Monotone (successiveRadius5 b e) ∧
      (∀ i, coordinateGauge5 e (v i) = successiveRadius5 b e i) ∧
      ∀ i, ∀ y ∈ lattice5Span b, y ∉ minimaPrefix5 v i → coordinateGauge5 e (v i) ≤ coordinateGauge5 e y := by
  obtain ⟨v,hv,hvL,hmin⟩ := exists_greedy_prefix5 b e 5 le_rfl
  let f := coordinateGauge5 e
  have hmono : Monotone (fun i => f (v i)) := by
    intro i j hij
    exact hmin i (v j) (hvL j) (minimaPrefix5_not_mem v hv i j hij)
  have heq (k : Fin 5) : successiveRadius5 b e k = f (v k) := by
    apply IsLeast.csInf_eq
    constructor
    · let emb : Fin (k.val+1) → Fin 5 := Fin.castLE (by omega)
      refine ⟨fun i => v (emb i),hv.comp emb (Fin.castLE_injective _),fun i => hvL (emb i),?_⟩
      intro i
      exact hmono (show emb i ≤ k by change i.val ≤ k.val; omega)
    · rintro r ⟨a,ha,haL,har⟩
      obtain ⟨i,hi⟩ := independent_family_escapes_subspace5 a ha (minimaPrefix5 v k)
        (by rw [minimaPrefix5_finrank v hv k]; omega)
      exact (hmin k (a i) (haL i) hi).trans (har i)
  refine ⟨v,hv,hvL,?_,?_,?_,hmin⟩
  · intro i
    rw [heq]
    exact norm_pos_iff.mpr (fun h => hv.ne_zero i (e.injective (h.trans e.map_zero.symm)))
  · intro i j hij
    rw [heq,heq]
    exact hmono hij
  · intro i
    exact (heq i).symm

end
end CompoundFeasibility
