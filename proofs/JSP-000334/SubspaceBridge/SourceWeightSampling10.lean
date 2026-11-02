import SubspaceBridge.SourceOriginalFrame10
import SubspaceBridge.SourceTailSampling10
import Mathlib.Topology.MetricSpace.Pseudo.Pi
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10

theorem select_unbounded_weights10 (U : Set ℝ) (hU : ¬ BddAbove U)
    (alpha : ℝ → Fin 10 → ℝ) (hb : ∀ q ∈ U, ∀ i, |alpha q i| ≤ 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ V : Set ℝ, V ⊆ U ∧ ¬ BddAbove V ∧ ∃ q0 ∈ V,
      ∀ q ∈ V, ∀ i, |alpha q i-alpha q0 i| < epsilon := by
  let B : Set (Fin 10 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨S,hSB,hS,hcover⟩ := hB.finite_cover_balls (show 0 < epsilon/2 by positivity)
  let F : (Fin 10 → ℝ) → Set ℝ := fun x => {q | q ∈ U ∧ alpha q ∈ Metric.ball x (epsilon/2)}
  have hUF : U ⊆ ⋃ x ∈ S, F x := by
    intro q hq
    have ha : alpha q ∈ B := by
      intro i hi
      exact abs_le.mp (hb q hq i)
    obtain ⟨x,hx,hqx⟩ := Set.mem_iUnion₂.mp (hcover ha)
    exact Set.mem_iUnion₂.mpr ⟨x,hx,hq,hqx⟩
  have hex : ∃ x ∈ S, ¬ BddAbove (F x) := by
    by_contra hn
    push_neg at hn
    exact hU (((hS.bddAbove_biUnion).mpr hn).mono hUF)
  obtain ⟨x,hx,hF⟩ := hex
  obtain ⟨q0,h0,_⟩ := not_bddAbove_iff.mp hF 0
  refine ⟨F x,fun q hq => hq.1,hF,q0,h0,?_⟩
  intro q hq i
  have hqi := (dist_pi_lt_iff (show 0 < epsilon/2 by positivity)).mp hq.2 i
  have h0i := (dist_pi_lt_iff (show 0 < epsilon/2 by positivity)).mp h0.2 i
  rw [Real.dist_eq] at hqi h0i
  calc
    |alpha q i-alpha q0 i| ≤ |alpha q i-x i|+|x i-alpha q0 i| := abs_sub_le _ _ _
    _ < epsilon/2+epsilon/2 := add_lt_add hqi (by simpa only [abs_sub_comm] using h0i)
    _ = epsilon := by ring


def logWeight10 (Q a : ℝ) : ℝ := Real.log a / Real.log Q

theorem logWeight10_bounds (Q a : ℝ) (hQ : 1 < Q) (ha : 0 < a)
    (hau : a < Q) (hai : a⁻¹ < Q) : -1 < logWeight10 Q a ∧ logWeight10 Q a < 1 := by
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have h1 := Real.log_lt_log ha hau
  have h2 := Real.log_lt_log (inv_pos.mpr ha) hai
  rw [Real.log_inv] at h2
  constructor
  · apply (lt_div_iff₀ hlog).mpr
    linarith
  · apply (div_lt_iff₀ hlog).mpr
    linarith

theorem logWeight10_power (Q a : ℝ) (hQ : 1 < Q) (ha : 0 < a) : Q^(logWeight10 Q a)=a := by
  rw [logWeight10,Real.rpow_def_of_pos (lt_trans zero_lt_one hQ)]
  have he : Real.log Q*(Real.log a/Real.log Q)=Real.log a := by
    field_simp [(Real.log_pos hQ).ne']
  rw [he,Real.exp_log ha]

theorem logWeight10_balance (Q : ℝ) (hQ : 1 < Q) (a b2 b3 : Fin 10 → ℝ)
    (ha : ∀ i,0<a i) (hp : (∏ i,a i*Q^(b2 i)*Q^(b3 i))=1) :
    (∑ i,logWeight10 Q (a i))+(∑ i,b2 i)+(∑ i,b3 i)=0 := by
  have hq := lt_trans zero_lt_one hQ
  have hpow : Q^(∑ i : Fin 10,(logWeight10 Q (a i)+b2 i+b3 i))=1 := by
    rw [Real.rpow_sum_of_pos hq]
    calc
      _ = ∏ i : Fin 10,a i*Q^(b2 i)*Q^(b3 i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Real.rpow_add hq,Real.rpow_add hq,logWeight10_power Q (a i) hQ (ha i)]
      _ = 1 := hp
  have hs := (Real.rpow_right_inj hq (ne_of_gt hQ)).mp (hpow.trans (Real.rpow_zero Q).symm)
  simpa only [Finset.sum_add_distrib] using hs


end CompoundFeasibility.SourceSampling10
