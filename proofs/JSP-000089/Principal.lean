import GraphFoundations
import Construction
/-!
Final assembly of Verstraëte's Theorem 1 (Version of Record, printed page 166).
The exact statement and the existing graph and sparse-set constructions are
imported unchanged. Mathematical attribution: Jacques Verstraëte.
-/

namespace JSP000089
/-- Theorem 3's integer bound enables the exact floor threshold of source Lemma 4.3. -/
lemma sourceLemma43_theorem3_threshold {k j : ℕ} (_hk : 2 ≤ k) (hj : 1 ≤ j)
    (hpow : 2^(j-1) ≤ 2^120*k^24) :
    j * sourceLemma43BlockThreshold j ≤ k := by
  let p : ℝ := (2 : ℝ)^(((j-1 : ℕ) : ℝ)/24)
  have hp : 0 ≤ p := Real.rpow_nonneg (by norm_num) _
  have hp24 : p^24 = (2 : ℝ)^(j-1) := by
    dsimp [p]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hpower : p^24 ≤ ((32 : ℝ)*(k : ℝ))^24 := by
    rw [hp24]
    have hcast : (2 : ℝ)^(j-1) ≤ 2^120*(k : ℝ)^24 := by exact_mod_cast hpow
    calc
      (2 : ℝ)^(j-1) ≤ 2^120*(k : ℝ)^24 := hcast
      _ = ((32 : ℝ)*(k : ℝ))^24 := by ring
  have hroot : p ≤ 32*(k : ℝ) := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (24 : ℕ) ≠ 0) (by positivity) hpower
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  let x : ℝ := (1/32 : ℝ)*(j : ℝ)⁻¹*p-(j : ℝ)⁻¹
  have hdef : sourceLemma43BlockThreshold j = ⌊x⌋₊ := rfl
  rw [hdef]
  by_cases hx : x ≤ 0
  · rw [Nat.floor_eq_zero.mpr (by linarith : x < 1)]
    simp
  · have hf := Nat.floor_le (le_of_lt (lt_of_not_ge hx))
    have hmul := mul_le_mul_of_nonneg_left hf hjpos.le
    have hcancel : (j : ℝ)*x = p/32-1 := by
      dsimp [x]
      field_simp
      ring
    rw [hcancel] at hmul
    have hreal : (j : ℝ)*(⌊x⌋₊ : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast hreal
end JSP000089

namespace JSP000089
/-- The source spectrum meets the existing sparse set at large girth. -/
theorem sourceTheorem3_high_girth_unavoidable {V : Type*} [Fintype V]
    (G : SimpleGraph V) (havg : averageDegreeAtLeast G 10) (hgirth : 2^120 ≤ G.girth) :
    HasCycleLengthIn G sourceLemma43Set := by
  classical
  obtain ⟨k, hk, A, B, hAc, hBc, hAp, hBp, hcycles⟩ :=
    sourceTheorem3_complete G havg hgirth
  let N := 2^120*k^24
  have hN : 0 < N := by dsimp [N]; positivity
  obtain ⟨j, hj, hNj⟩ := sourceLemma43_exists_mem_dyadicBlock hN
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  have hArange : A ⊆ sourceLemma42Universe N := by
    intro a ha
    obtain ⟨b, hb⟩ := hBne
    have hbound := (hcycles a ha b hb).2
    have hpos := hAp a ha
    exact Finset.mem_Icc.mpr ⟨by omega, by dsimp [N]; omega⟩
  have hBrange : B ⊆ sourceLemma42Universe N := by
    intro b hb
    obtain ⟨a, ha⟩ := hAne
    have hbound := (hcycles a ha b hb).2
    have hpos := hBp b hb
    exact Finset.mem_Icc.mpr ⟨by omega, by dsimp [N]; omega⟩
  have hlow : 2^(j-1) ≤ N := (Finset.mem_Icc.mp hNj).1
  have hcard := sourceLemma43_theorem3_threshold hk hj hlow
  obtain ⟨x, hxS, hxAB⟩ := sourceLemma43_global_hitting hj hNj hArange hBrange
    (hAc.symm ▸ hcard) (hBc.symm ▸ hcard) hAne hBne
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_image₂.mp hxAB
  exact ⟨x, hab ▸ (hcycles a ha b hb).1, hxS⟩

/-- Average degree ten supplies an actual simple cycle in the original graph. -/
theorem source_averageDegree10_cycle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (havg : averageDegreeAtLeast G 10) :
    ∃ n : ℕ, IsCycleLength G n := by
  classical
  obtain ⟨W, hconn, hdegree⟩ := sourceTheorem3_mader_extraction G havg
  let H := G.induce (↑W : Set V)
  obtain ⟨r, C, hLongest⟩ := sourceTheorem3_longest_cycle H hconn
    (fun v => hdegree v inferInstance)
  exact ⟨C.length, sourceLemma24_map_cycle_length H
    (SimpleGraph.Embedding.induce (↑W : Set V)).toHom Subtype.val_injective
    ⟨r, C, hLongest.1, rfl⟩⟩

/-- The average-degree hypothesis excludes zero (acyclic) Nat girth. -/
theorem source_averageDegree10_girth_pos {V : Type*} [Fintype V]
    (G : SimpleGraph V) (havg : averageDegreeAtLeast G 10) : 0 < G.girth := by
  obtain ⟨n, r, C, hC, _⟩ := source_averageDegree10_cycle G havg
  have hnot : ¬ G.IsAcyclic := fun hac => hac _ hC
  have := SimpleGraph.three_le_girth hnot
  omega

/-- The finite source prefix handles the remaining girth case. -/
theorem source_short_girth_unavoidable {V : Type*} [Fintype V]
    (G : SimpleGraph V) (havg : averageDegreeAtLeast G 10) (hgirth : G.girth < 2^120) :
    HasCycleLengthIn G sourceShortCycleLengths :=
  hasCycleLengthIn_sourceShortCycleLengths_of_girth_le G
    (source_averageDegree10_girth_pos G havg) hgirth.le

/-- Verstraëte's Theorem 1, proving the unchanged JSP-000089 statement contract. -/
theorem jsp_000089_complete : jsp_000089_statement := by
  refine ⟨sourceLemma43Set ∪ sourceShortCycleLengths, sourceSparsity099_finalSet, ?_⟩
  intro V _ G havg
  by_cases hgirth : 2^120 ≤ G.girth
  · obtain ⟨n, hn, hmem⟩ := sourceTheorem3_high_girth_unavoidable G havg hgirth
    exact ⟨n, hn, Set.mem_union_left _ hmem⟩
  · obtain ⟨n, hn, hmem⟩ := source_short_girth_unavoidable G havg (lt_of_not_ge hgirth)
    exact ⟨n, hn, Set.mem_union_right _ hmem⟩
end JSP000089
