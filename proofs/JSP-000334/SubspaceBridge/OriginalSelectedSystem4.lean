import SubspaceBridge.AlgebraicLiouville4
import SubspaceBridge.OriginalAuxiliaryGeometry4
import SubspaceBridge.OriginalDeformedSource4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalSelectedSystem4

abbrev MixedIndex4 := Fin 3 → Fin 4

def publishedIndexSet4 (Q delta : ℝ) (A c2 c3 : Fin 4 → ℝ) : Finset MixedIndex4 :=
  Finset.univ.filter (fun s => 1 ≤ A (s 0)*Q^(c2 (s 1))*Q^(c3 (s 2))*Q^(delta/2))

def logarithmicWeights4 (Q : ℝ) (A c2 c3 : Fin 4 → ℝ) : Fin 3 → Fin 4 → ℝ :=
  ![fun i => Real.log (A i)/Real.log Q,c2,c3]

theorem logarithmic_width4 (Q : ℝ) (hQ : 1 < Q) (A : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i) (i : Fin 4) :
    Q^(Real.log (A i)/Real.log Q) = A i := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hQ)]
  have hlog : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  have he : Real.log Q*(Real.log (A i)/Real.log Q) = Real.log (A i) := by
    field_simp [hlog]
  rw [he,Real.exp_log (hA i)]

theorem logarithmic_balance4 (Q : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (∑ tau, ∑ i, logarithmicWeights4 Q A c2 c3 tau i) = 0 := by
  have hlog := congrArg Real.log hb
  rw [Real.log_mul (Finset.prod_pos (fun i _ => hA i)).ne'
    (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)).ne',
    Real.log_prod Finset.univ A (fun i _ => (hA i).ne'),Real.log_prod Finset.univ (fun i => Q^(c2 i+c3 i)) (fun i _ => (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).ne'),Real.log_one] at hlog
  simp_rw [Real.log_rpow (zero_lt_one.trans hQ)] at hlog
  simp [logarithmicWeights4,Fin.sum_univ_three,Finset.sum_div,Finset.sum_add_distrib,Finset.sum_mul] at hlog ⊢
  have hdiv := congrArg (fun x : ℝ => x/Real.log Q) hlog
  simpa only [Finset.sum_mul,Finset.sum_div,Finset.sum_add_distrib,add_div,
    mul_div_cancel_right₀ _ (Real.log_pos hQ).ne',zero_div,add_assoc] using hdiv

theorem balanced_mixed_nonnegative4 (c : Fin 3 → Fin 4 → ℝ)
    (hb : (∑ tau, ∑ i, c tau i) = 0) :
    ∃ s : MixedIndex4, 0 ≤ ∑ tau, c tau (s tau) := by
  have hm (tau : Fin 3) : ∃ i : Fin 4, ∀ j : Fin 4, c tau j ≤ c tau i := by
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (c tau) Finset.univ_nonempty
    exact ⟨i,fun j => hi j (Finset.mem_univ j)⟩
  choose s hs using hm
  refine ⟨s,?_⟩
  have hrow (tau : Fin 3) : (∑ i, c tau i) ≤ 4*c tau (s tau) := by
    calc
      _ ≤ ∑ _i : Fin 4, c tau (s tau) := Finset.sum_le_sum (fun j _ => hs tau j)
      _ = _ := by simp
  have h := Finset.sum_le_sum (fun tau (_ : tau ∈ Finset.univ) => hrow tau)
  rw [hb,← Finset.mul_sum] at h
  linarith

theorem published_index_logarithmic4 (Q delta : ℝ) (hQ : 1 < Q)
    (A c2 c3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i) (s : MixedIndex4) :
    s ∈ publishedIndexSet4 Q delta A c2 c3 ↔
      -delta/2 ≤ ∑ tau, logarithmicWeights4 Q A c2 c3 tau (s tau) := by
  simp only [publishedIndexSet4,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← logarithmic_width4 Q hQ A hA (s 0)]
  simp_rw [← Real.rpow_add (zero_lt_one.trans hQ)]
  rw [← Real.rpow_zero Q,Real.rpow_le_rpow_left_iff hQ]
  simp [logarithmicWeights4,Fin.sum_univ_three]
  constructor <;> intro h <;> linarith

theorem published_index_nonempty4 (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (A c2 c3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (publishedIndexSet4 Q delta A c2 c3).Nonempty := by
  obtain ⟨s,hs⟩ := balanced_mixed_nonnegative4 _ (logarithmic_balance4 Q hQ A c2 c3 hA hb)
  refine ⟨s,(published_index_logarithmic4 Q delta hQ A c2 c3 hA s).mpr ?_⟩
  linarith

theorem published_index_unbounded_fiber4 (V : Set ℝ) (hV : ¬ BddAbove V)
    (S : V → Finset MixedIndex4) (hS : ∀ q, (S q).Nonempty) :
    ∃ s : Finset MixedIndex4, s.Nonempty ∧
      ¬ BddAbove {q : ℝ | ∃ hq : q ∈ V, S ⟨q,hq⟩ = s} := by
  by_contra! h
  have hb (s : Finset MixedIndex4) :
      BddAbove {q : ℝ | ∃ hq : q ∈ V, S ⟨q,hq⟩ = s} := by
    by_cases hs : s.Nonempty
    · exact h s hs
    · have he : {q : ℝ | ∃ hq : q ∈ V, S ⟨q,hq⟩ = s} = ∅ := by
        ext q
        simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_exists]
        intro hq he
        exact hs (he ▸ hS ⟨q,hq⟩)
      rw [he]
      exact bddAbove_empty
  choose b hb using hb
  obtain ⟨B,hB⟩ := (Set.finite_range b).bddAbove
  apply hV
  refine ⟨B,?_⟩
  intro q hq
  exact (hb (S ⟨q,hq⟩) ⟨hq,rfl⟩).trans (hB (Set.mem_range_self _))


theorem deformed_fixed_selected_system4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ) (hd : 0 < delta)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3)
    (hready : ∀ q : V, OriginalDeformation4.deformationReady4 A2 A3 L hL q.val
      (hQV q.val q.property) c0 c2 c3 delta (u q)) :
    ∃ F : (q : V) → OriginalDeformedSource4.DeformedAttaining4 A2 A3 L hL q.val
        (hQV q.val q.property) c0 c2 c3 delta (u q),
      ∃ S : Finset MixedIndex4, S.Nonempty ∧ ∃ W : Set ℝ,
      W ⊆ V ∧ ¬ BddAbove W ∧
      ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
      ∀ q : V, q.val ∈ W →
        publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
          (OriginalDeformation4.deformedWidths4 q.val c0
            (OriginalDeformation4.gapDeformation4 (sourceMinima4 A2 A3 L hL q.val
              (hQV q.val q.property) c0 c2 c3)) (F q).sigma)
          (fun i => c2 i/5) (fun i => c3 i/5) = S := by
  let F := fun q : V => Classical.choice
    (OriginalDeformedSource4.attaining_of_ready4 A2 A3 L hL q.val (hQV q.val q.property)
      c0 c2 c3 delta (u q) (hready q))
  let A := fun (q : V) => OriginalDeformation4.deformedWidths4 q.val c0
    (OriginalDeformation4.gapDeformation4 (sourceMinima4 A2 A3 L hL q.val
      (hQV q.val q.property) c0 c2 c3)) (F q).sigma
  let index := fun (q : V) => publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
    (A q) (fun i => c2 i/5) (fun i => c3 i/5)
  have hnonempty (q : V) : (index q).Nonempty := by
    apply published_index_nonempty4 _ _ (one_lt_pow₀ (hQV q.val q.property) (by decide))
      (by positivity) _ _ _ (F q).widths_pos
    have hb := (F q).balance
    have he (i : Fin 4) : (q.val^(5 : ℕ))^(c2 i/5+c3 i/5) = q.val^(c2 i+c3 i) := by
      rw [show c2 i/5+c3 i/5 = (c2 i+c3 i)/5 by ring]
      exact OriginalDeformation4.rescaled_power4 q.val (c2 i+c3 i) (zero_lt_one.trans (hQV q.val q.property))
    simpa only [he] using hb
  obtain ⟨S,hS,hW⟩ := published_index_unbounded_fiber4 V hV index hnonempty
  let W := {q : ℝ | ∃ hq : q ∈ V, index ⟨q,hq⟩ = S}
  have hWV : W ⊆ V := by rintro q ⟨hq,_⟩; exact hq
  refine ⟨F,S,hS,W,hWV,hW,OriginalDeformation4.fifth_image_unbounded4 W hW
    (fun q hq => hQV q (hWV hq)),?_⟩
  intro q hq
  obtain ⟨hq,he⟩ := hq
  exact he

end CompoundFeasibility.OriginalSelectedSystem4
