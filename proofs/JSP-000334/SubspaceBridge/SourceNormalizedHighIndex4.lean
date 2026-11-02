import SubspaceBridge.SourceNormalIndex4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalIndex4
open OriginalDeformedSource4

theorem source_normalized_selected_high_index4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ U : Set ℝ, ∃ hUV : U ⊆ V, ¬ BddAbove U ∧
      ∃ u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ∃ F : (q : U) → DeformedAttaining4 A2 A3 L (sourceUnit42 L hLdet) q.val
        (hQV q.val (hUV q.property)) c0 c2 c3 delta (u q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ W : Set ℝ, ∃ hWU : W ⊆ U, ¬ BddAbove W ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
        (∀ q : U, q.val ∈ W →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
            (OriginalDeformation4.deformedWidths4 q.val c0
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q.val
                  (hQV q.val (hUV q.property)) c0 c2 c3)) (F q).sigma) (fun i => c2 i/5) (fun i => c3 i/5) = S) ∧
        ∀ B : Set ℝ, ∀ hBW : B ⊆ W, ¬ BddAbove B →
          sourceFrameHighIndex4 (A2 := A2) (A3 := A3) (L := L)
            (hL := sourceUnit42 L hLdet) (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta)
            (hQU := fun q hq => hQV q (hUV (hWU (hBW hq))))
            (u := fun q : B => u ⟨q.val,hWU (hBW q.property)⟩)
            (fun q : B => F ⟨q.val,hWU (hBW q.property)⟩) := by
  obtain ⟨T,hT,u0,_,hU,_,hframes,hready⟩ :=
    OriginalDeformation4.source_normalized_unbounded_deformation4 A2 A3 L h2 h3 hLdet hAlg
      delta hd c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap
  let U : Set ℝ := {q | q ∈ V ∧ T < q}
  let hUV : U ⊆ V := fun _ hq => hq.1
  let hQU : ∀ q ∈ U, 1 < q := fun q hq => hQV q hq.1
  let u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3 :=
    fun q => u0 ⟨q.val,q.property.1⟩
  have hr (q : U) : OriginalDeformation4.deformationReady4 A2 A3 L (sourceUnit42 L hLdet)
      q.val (hQU q.val q.property) c0 c2 c3 delta (u q) :=
    (hready ⟨q.val,q.property.1⟩ q.property.2).2.2
  obtain ⟨F,S,hS,W,hWU,hW,hWp,hindex⟩ := OriginalSelectedSystem4.deformed_fixed_selected_system4
    A2 A3 L (sourceUnit42 L hLdet) c0 c2 c3 delta hd U hU hQU u hr
  refine ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hindex,?_⟩
  intro B hBW hB
  exact same_selected_frame_high_index4
    (A2 := A2) (A3 := A3) (L := L) (hL := sourceUnit42 L hLdet)
    (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := B)
    (hQU := fun q hq => hQV q (hUV (hWU (hBW hq))))
    (u := fun q : B => u ⟨q.val,hWU (hBW q.property)⟩)
    h2 h3 hLdet hAlg
    (fun q : B => F ⟨q.val,hWU (hBW q.property)⟩) hB hd hc2 hc3


end CompoundFeasibility.SourceNormalIndex4
