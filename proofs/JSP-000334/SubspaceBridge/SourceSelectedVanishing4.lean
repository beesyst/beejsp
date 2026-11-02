import SubspaceBridge.SchmidtSourceParameters4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedVanishing4
open SourceSelectedDual4 SourceNormalHeight4 SchmidtNormalCoordinates4 SchmidtSourceParameters4
open OriginalSelectedSystem4 OriginalDeformedSource4 OriginalLastDual4 OriginalAuxiliaryDual4
open SourceMultiblock4 SourceNormalIndex4 Auxiliary4 Auxiliary4.SourceVanishing4
open Auxiliary4.SourceExpansion4 Auxiliary4.SourceGrid4 Auxiliary4.SourceEvaluation4

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

theorem source_nonzero_branch_contradiction4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (g : U → ℤ) (M : U → Fin 4 → ℤ)
    (hnormal : ∀ q, g q ≠ 0 ∧ M q ≠ 0 ∧
      (∀ i, integerLastDual4 (fun j => ((F q).w j : Fin 4 → ℤ)) i = g q*M q i) ∧
      Ideal.span (Set.range (M q)) = ⊤ ∧
      LinearMap.ker (normalForm4 (M q)) =
        Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (((F q).w j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
      LinearMap.ker (realNormalForm4 (M q)) =
        Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal ((F q).w j.castSucc : Fin 4 → ℤ))))
    (s : MixedIndex4)
    (hselected : ∀ q : U, s ∈ publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
      (SourceWeights4.frameWidths F q) (fun i => c2 i/5) (fun i => c3 i/5))
    (hnonzero : ∀ q, mixedNonzero4 A2 A3 L (M q) s) : False := by
  obtain ⟨alpha,halpha,T,hT,henvelopes⟩ :=
    source_uniform_height_envelopes4 A2 A3 L h2 h3 hLdet ha delta hd
  obtain ⟨V,hVU,hV,d,hdp,hd1,c,hc,hbal,hfin,hframe⟩ :=
    SourceWeights4.fixed_weights_same_frame4 F hU hd hc2 hc3
  obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ := source_auxiliary4_grid_vanishing A2 A3 L h2 h3 hLdet ha
  obtain ⟨eta,theta,m,hee,hte,he,he1,hed,hm,hmb,ht,ht1,htm,ho⟩ := eta_m_theta4 d hdp hd1 K
  obtain ⟨gamma,hg,hg3,hcompat,hcompat'⟩ := positive_gamma4 alpha eta halpha he
  let omega := JSP000334.omega65 m theta
  let cut := originalCutoff4 T m eta alpha omega gamma D E
  obtain ⟨t0,ht0,hfinite,hgrowth,hsep⟩ := original_blocks_cutoff4 V hV cut eta E omega he hE ho m
  let lift : V → U := fun q => ⟨q.val,hVU q.property⟩
  let t : Fin m → U := fun h => lift (t0 h)
  let Q : Fin m → ℝ := fun h => (t h).val^(5 : ℕ)
  let H : Fin m → ℝ := fun h => (normalHeight4 (M (t h)) : ℝ)
  have hQ (h) : 1 < Q h := (hgrowth h).2.1
  have hcut (h) := cutoff_budgets4 T m eta alpha omega gamma D E (t h).val
    halpha ho hg (hgrowth h).1
  have hH (h) : max 1 (normalHeight4 (M (t h)) : ℝ) = H h := by
    apply max_eq_right
    exact_mod_cast normalHeight4_pos (M (t h)) (hnormal (t h)).2.1
  have henv (h) : (Q h)^alpha ≤ H h ∧ H h ≤ (Q h)^(4 : ℝ) := by
    have hh := henvelopes (t h).val (hcut h).1 (hQU _ (t h).property) hL c0 c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) (u (t h)) (F (t h))
      (M (t h)) (g (t h)) (hnormal (t h)).1 (hnormal (t h)).2.2.1
      s (hselected (t h)) (hnonzero (t h))
    rwa [hH h] at hh
  have hmono : Monotone Q := by
    intro i j hij
    exact pow_le_pow_left₀ (zero_lt_one.trans (hQU _ (t i).property)).le (ht0.monotone hij) 5
  obtain ⟨r,hr,hrsep,hrbal,hrsum⟩ := SchmidtParameters6.anchored_degrees6 m hm eta omega he ho Q hQ hmono hsep
  obtain ⟨P,hP,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,hvan⟩ := haux eta he m hmb r hr
  have hgrid := hvan Q hQ ⟨0,hm⟩ d hed hd1
    (fun h => (hgrowth h).2.2.1) (fun h => (hgrowth h).2.2.2) hrbal c hc hbal
    (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ))
    (fun h j i => (hframe (t h) (t0 h).property).1 j i)
    (fun h j i => (hframe (t h) (t0 h).property).2.1 j i)
    (fun h j i => (hframe (t h) (t0 h).property).2.2 j i)
  have hindex := (integer_grid_high_normal_index4 r hr P hhom
    (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) (fun h => M (t h))
    (fun h => (hnormal (t h)).2.1) (fun h => (hnormal (t h)).2.2.2.2.1)
    (fun h => (hnormal (t h)).2.2.2.2.2) eta he hgrid).2
  have hcompare := height_comparison4 m hm alpha gamma halpha hg hcompat' Q H hQ henv r
    (fun h => (hrbal h).1)
  have hbudget (h) := normal_budget4 m alpha omega gamma (Q h) (H h) ho hg (hQ h)
    (henv h).1 (hcut h).2.2.1
  have hpoly := polynomial_budget4 m (r ⟨0,hm⟩) (∑ h, r h) eta alpha omega gamma D
    (Q ⟨0,hm⟩) (H ⟨0,hm⟩) (height4 P : ℝ) ho hg hD (hQ _) (henv _).1
    (Nat.cast_nonneg _) hheight hrsum (hcut ⟨0,hm⟩).2.2.2
  exact primitive_high_index_contradiction4 m hm (fun h => M (t h))
    (fun h => (hnormal (t h)).2.2.2.1) theta gamma ((m : ℝ)*eta) ht ht1 hg hg3 htm
    r hr hrsep P hP hhom hindex hcompare hbudget hpoly


theorem same_frame_selected_vanishing4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (S : Finset MixedIndex4)
    (hselected : ∀ q : U, ∀ s ∈ S, s ∈ publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
      (SourceWeights4.frameWidths F q) (fun i => c2 i/5) (fun i => c3 i/5)) :
    ∃ T : ℝ, ∀ q : U, T < q.val → ∀ s ∈ S,
      lastDualProduct4 A2 A3 L (fun j => ((F q).w j : Fin 4 → ℤ)) (F q).rational_independent s = 0 := by
  obtain ⟨g,M,a,hn⟩ := same_frame_primitive_normals4
    (fun q : U => fun j => ((F q).w j : Fin 4 → ℤ)) (fun q => (F q).real_independent)
  have hz : ∃ T : ℝ, ∀ q : U, T < q.val → ∀ s ∈ S, mixedProduct4 A2 A3 L (M q) s = 0 := by
    by_contra hf
    obtain ⟨s,hs,hB⟩ := failure_eventual_zero_branch4 A2 A3 L U M S hf
    let B := nonzeroBranch4 A2 A3 L U M s
    let lift : B → U := fun q => ⟨q.val,(nonzeroBranch4_subset A2 A3 L U M s) q.property⟩
    refine source_nonzero_branch_contradiction4
      (A2 := A2) (A3 := A3) (L := L) (hL := hL) (c0 := c0) (c2 := c2) (c3 := c3)
      (delta := delta) (U := B)
      (hQU := fun q hq => hQU q ((nonzeroBranch4_subset A2 A3 L U M s) hq))
      (u := fun q : B => u (lift q)) h2 h3 hLdet ha (fun q : B => F (lift q)) hB hd hc2 hc3
      (fun q => g (lift q)) (fun q => M (lift q)) ?_ s ?_ ?_
    · intro q
      exact ⟨(hn (lift q)).1,(hn (lift q)).2.1,(hn (lift q)).2.2.1,
        (hn (lift q)).2.2.2.2.1,(hn (lift q)).2.2.2.2.2.2.1,
        (hn (lift q)).2.2.2.2.2.2.2.1⟩
    · intro q
      exact hselected (lift q) s hs
    · intro q
      exact (mem_nonzeroBranch4 A2 A3 L U M s (lift q)).mp q.property
  obtain ⟨T,hT⟩ := hz
  refine ⟨T,?_⟩
  intro q hq s hs
  exact (primitive_lastDualProduct4_zero A2 A3 L _ (F q).rational_independent
    (M q) (g q) (hn q).1 (hn q).2.2.1 s).mp (hT q hq s hs)

theorem source_selected_vanishing4
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
        ∃ T : ℝ, ∀ q : U, q.val ∈ W → T < q.val → ∀ s ∈ S,
          lastDualProduct4 A2 A3 L (fun j => ((F q).w j : Fin 4 → ℤ)) (F q).rational_independent s = 0 := by
  obtain ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,hhigh⟩ :=
    source_normalized_selected_high_index4 A2 A3 L h2 h3 hLdet hAlg delta hd
      c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap
  let lift : W → U := fun q => ⟨q.val,hWU q.property⟩
  obtain ⟨T,hT⟩ := same_frame_selected_vanishing4
    (A2 := A2) (A3 := A3) (L := L) (hL := sourceUnit42 L hLdet)
    (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := W)
    (hQU := fun q hq => hQV q (hUV (hWU hq))) (u := fun q : W => u (lift q)) h2 h3 hLdet hAlg
    (fun q : W => F (lift q)) hW hd hc2 hc3 S (fun q s hs => by
      have heq := hselected (lift q) q.property
      exact Eq.mpr (congrArg (fun K : Finset MixedIndex4 => s ∈ K) heq) hs)
  refine ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,T,?_⟩
  intro q hq hTq s hs
  exact hT ⟨q.val,hq⟩ hTq s hs

end CompoundFeasibility.SourceSelectedVanishing4
