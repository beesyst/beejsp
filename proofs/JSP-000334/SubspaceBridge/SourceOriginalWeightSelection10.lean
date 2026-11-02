import SubspaceBridge.SourceOriginalFrame10
import SubspaceBridge.SourceTailSampling10
import Mathlib.Topology.MetricSpace.Pseudo.Pi
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalVariable10

theorem select_unbounded_original_weights10 (U : Set ℝ) (hU : ¬ BddAbove U)
    (alpha : ℝ → (Fin 3 × Fin 10) → ℝ) (hb : ∀ q ∈ U, ∀ i, |alpha q i| ≤ 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ V : Set ℝ, V ⊆ U ∧ ¬ BddAbove V ∧ ∃ q0 ∈ V,
      ∀ q ∈ V, ∀ i, |alpha q i-alpha q0 i| < epsilon := by
  let B : Set ((Fin 3 × Fin 10) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨S,hSB,hS,hcover⟩ := hB.finite_cover_balls (show 0 < epsilon/2 by positivity)
  let F : ((Fin 3 × Fin 10) → ℝ) → Set ℝ := fun x => {q | q ∈ U ∧ alpha q ∈ Metric.ball x (epsilon/2)}
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

end CompoundFeasibility.SourceOriginalVariable10
