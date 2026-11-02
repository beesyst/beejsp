import SubspaceBridge.SourceFrameWitness10
import SubspaceBridge.SourceWidthSelection10
import SubspaceBridge.SourceFiniteSampling10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open OriginalDeformation10

theorem source_original_fixed_weight_family10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (c0 c2 c3 : Fin 10 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) (delta : ℝ) (hd : 0 < delta)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (u : (q : U) → Fin 10 → originalSourceGroup10 A2 A3 q.val c2 c3)
    (hu : ∀ q : U, LinearIndependent ℝ (fun i => integerReal (u q i : Fin 10 → ℤ)))
    (hatt : ∀ (q : U) (i : Fin 10), coordinateGauge10 (originalCoordinates10 L hL q.val (hQU q.val q.property) c0)
      (integerReal (u q i : Fin 10 → ℤ)) =
        sourceMinima10 A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 i)
    (hgap : ∀ q : U, sourceMinima10 A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 9*q.val^(-delta)) :
    ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
    ∃ c : Fin 3 → Fin 10 → ℝ, (∀ tau i, |c tau i| ≤ 1) ∧
      (∑ tau, ∑ i, c tau i) = 0 ∧
      (∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5) ∧
      ∀ q : V, ∃ w : Fin 10 → originalSourceGroup10 A2 A3 q.val c2 c3,
        LinearIndependent ℝ (fun i => integerReal (w i : Fin 10 → ℤ)) ∧
        minimaFlag10 (fun i => integerReal (u ⟨q.val,hVU q.property⟩ i : Fin 10 → ℤ)) 9 =
          minimaFlag10 (fun i => integerReal (w i : Fin 10 → ℤ)) 9 ∧
        (∀ (j : Fin 9) i, ‖(L *ᵥ integerReal (w j.castSucc : Fin 10 → ℤ)) i‖ ≤
          (q.val^(5 : ℕ))^(c 0 i-epsilon)) ∧
        (∀ (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ
          (fun k => ((w j.castSucc : Fin 10 → ℤ) k : ℚ_[2]))) i‖ ≤ (q.val^(5 : ℕ))^(c 1 i)) ∧
        (∀ (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ
          (fun k => ((w j.castSucc : Fin 10 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^(5 : ℕ))^(c 2 i)) := by
  obtain ⟨T,hT,hframe⟩ := original_frame_witness10 A2 A3 L h2 h3 hL delta hd
  let U0 := {q : ℝ | q ∈ U ∧ T < q}
  have hU0 : ¬ BddAbove U0 := by
    intro h
    obtain ⟨B,hB⟩ := h
    obtain ⟨q,hq,hbig⟩ := not_bddAbove_iff.mp hU (max B T)
    have hq0 : q ∈ U0 := ⟨hq,(le_max_right _ _).trans_lt hbig⟩
    exact (not_lt_of_ge (hB hq0)) ((le_max_left _ _).trans_lt hbig)
  have hpoint (q : U) (hq : T < q.val) :
      Nonempty (OriginalFrameWitness10 A2 A3 L q.val delta c2 c3
        (fun i => (u q i : Fin 10 → ℤ))) := by
    exact hframe q.val (hQU q.val q.property) c0 c2 c3 hc0 hc2 hc3 hb hq
      (u q) (hu q) (hatt q) (hgap q)
  have hfamily (q : U0) : Nonempty (OriginalFrameWitness10 A2 A3 L q.val delta c2 c3
      (fun i => (u ⟨q.val,q.property.1⟩ i : Fin 10 → ℤ))) :=
    hpoint ⟨q.val,q.property.1⟩ q.property.2
  let F := fun q : U0 => Classical.choice (hfamily q)
  let W := fun q : U0 => (F q).W
  let w := fun q : U0 => (F q).w
  let epsilon := min (delta/240) (1/4 : ℝ)
  have he : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have he1 : epsilon < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hedelta : 2*epsilon ≤ delta/60 := by
    have hh : epsilon ≤ delta/240 := min_le_left _ _
    linarith
  obtain ⟨V,hVU0,hV,a,ha,hba,hupper⟩ := fixed_width_exponents10 U0 hU0
    (fun q hq => hQU q hq.1) W c2 c3 (fun q => (F q).positive) (fun q => (F q).sizes) (fun q => (F q).balance) epsilon he
  let c : Fin 3 → Fin 10 → ℝ := ![a,fun i => c2 i/5,fun i => c3 i/5]
  have hc (tau : Fin 3) (i : Fin 10) : |c tau i| ≤ 1 := by
    fin_cases tau
    · exact abs_le.mpr ⟨(ha i).1.le,(ha i).2.le⟩
    · change |c2 i/5| ≤ 1
      exact abs_le.mpr ⟨by linarith [(hc2 i).1],by linarith [(hc2 i).2]⟩
    · change |c3 i/5| ≤ 1
      exact abs_le.mpr ⟨by linarith [(hc3 i).1],by linarith [(hc3 i).2]⟩
  have hbalance : (∑ tau, ∑ i, c tau i) = 0 := by
    simpa only [c,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two] using hba
  refine ⟨V,fun q hq => (hVU0 hq).1,hV,epsilon,he,he1,c,hc,hbalance,fun i => ⟨rfl,rfl⟩,?_⟩
  intro q
  let q' : U0 := ⟨q.val,hVU0 q.property⟩
  refine ⟨w q',(F q').independent,(F q').flag,?_,?_,?_⟩
  · intro j i
    have hh := (F q').small j i
    have hQ5 : 1 < q.val^5 := one_lt_pow₀ (hQU q.val q'.property.1) (by decide)
    have hW := hupper q i
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (q.val^5)^(-(delta/60))*W q' i := hh
      _ ≤ (q.val^5)^(-(delta/60))*(q.val^5)^(a i+epsilon) :=
        mul_le_mul_of_nonneg_left hW (Real.rpow_pos_of_pos (zero_lt_one.trans hQ5) _).le
      _ = (q.val^5)^(a i+epsilon-delta/60) := by
        rw [← Real.rpow_add (zero_lt_one.trans hQ5)]
        congr 1
        ring
      _ ≤ (q.val^5)^(a i-epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hQ5.le (by linarith)
      _ = _ := rfl
  · intro j i
    change ‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ _) i‖ ≤ (q.val^5)^(c2 i/5)
    rw [rescaled_power10 q.val _ (zero_lt_one.trans (hQU q.val q'.property.1))]
    exact source_finite_short_bound10 2 A2 q.val (hQU q.val q'.property.1) c2 (fun i => (hc2 i).2)
      (w q' j.castSucc) (w q' j.castSucc).property.1 i
  · intro j i
    change ‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ _) i‖ ≤ (q.val^5)^(c3 i/5)
    rw [rescaled_power10 q.val _ (zero_lt_one.trans (hQU q.val q'.property.1))]
    exact source_finite_short_bound10 3 A3 q.val (hQU q.val q'.property.1) c3 (fun i => (hc3 i).2)
      (w q' j.castSucc) (w q' j.castSucc).property.2 i

end CompoundFeasibility.SourceSampling10
