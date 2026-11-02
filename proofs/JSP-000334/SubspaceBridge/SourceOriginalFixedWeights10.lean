import SubspaceBridge.SourceOriginalWeightSelection10
import SubspaceBridge.SourceOriginalWeightBalance10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
noncomputable section

theorem select_original_balanced_weights10 (U : Set ℝ) (hU : ¬ BddAbove U)
    (a : U → Fin 3 → Fin 10 → ℝ) (ha : ∀ q tau i, |a q tau i| ≤ 1/5)
    (ha1 : ∀ q i, a q 1 i ≤ 0) (ha2 : ∀ q i, a q 2 i ≤ 0)
    (hbal : ∀ q, (∑ tau, ∑ i, a q tau i) = 0) (delta : ℝ) (hd : 0 < delta) :
    ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
      ∃ e : ℝ, 0 < e ∧ e < 1 ∧ ∃ c : Fin 3 → Fin 10 → ℝ,
        (∀ tau i, |c tau i| ≤ 1) ∧ (∑ tau, ∑ i, c tau i) = 0 ∧
        (∀ i, c 1 i ≤ 0 ∧ c 2 i ≤ 0) ∧
        ∀ q : V, ∀ i, a ⟨q.val,hVU q.property⟩ 0 i-delta/5 ≤ c 0 i-e ∧
          a ⟨q.val,hVU q.property⟩ 1 i ≤ c 1 i ∧ a ⟨q.val,hVU q.property⟩ 2 i ≤ c 2 i := by
  let e := min (delta/40) (1/40 : ℝ)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e ≤ 1/40 := min_le_right _ _
  have hed : 4*e ≤ delta/5 := by have := min_le_left (delta/40) (1/40 : ℝ); linarith
  let alpha : ℝ → (Fin 3 × Fin 10) → ℝ := fun q i => if hq : q ∈ U then a ⟨q,hq⟩ i.1 i.2 else 0
  have halpha (q : U) (tau : Fin 3) (i : Fin 10) : alpha q.val (tau,i) = a q tau i := by simp only [alpha,dif_pos q.property]
  obtain ⟨V,hVU,hV,q0,hq0,hclose⟩ := select_unbounded_original_weights10 U hU alpha
    (fun q hq i => by rw [halpha ⟨q,hq⟩ i.1 i.2]; exact (ha ⟨q,hq⟩ i.1 i.2).trans (by norm_num)) e he
  let x := a ⟨q0,hVU hq0⟩
  have hc := fixed_original_weights10 x e he he1 (ha ⟨q0,hVU hq0⟩) (ha1 ⟨q0,hVU hq0⟩)
    (ha2 ⟨q0,hVU hq0⟩) (hbal ⟨q0,hVU hq0⟩)
  refine ⟨V,hVU,hV,e,he,by linarith,fixedOriginalWeights10 x e,hc.1,hc.2.1,hc.2.2.1,?_⟩
  intro q i
  have hnear (tau : Fin 3) : a ⟨q.val,hVU q.property⟩ tau i ≤ x tau i+e := by
    have h := (abs_lt.mp (hclose q.val q.property (tau,i))).2
    rw [halpha ⟨q.val,hVU q.property⟩ tau i,halpha ⟨q0,hVU hq0⟩ tau i] at h
    linarith
  refine ⟨?_,?_,?_⟩
  · linarith [(hc.2.2.2.1 i),hnear 0]
  · change a ⟨q.val,hVU q.property⟩ 1 i ≤ min 0 (x 1 i+e)
    exact le_min (ha1 _ i) (hnear 1)
  · change a ⟨q.val,hVU q.property⟩ 2 i ≤ min 0 (x 2 i+e)
    exact le_min (ha2 _ i) (hnear 2)

end
end CompoundFeasibility.SourceOriginalVariable10
