import SubspaceBridge.SourceExterior52Lattice238
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior52_238
open Exterior52_237

def normalizedWeights238 (c : Fin 5 → ℝ) : Fin 10 → ℝ := fun s => pairWeights238 c s/2

theorem pairWeights_sum238 (c : Fin 5 → ℝ) :
    (∑ s, pairWeights238 c s) = 4*∑ i, c i := by
  simp [pairWeights238,lo237,hi237,Fin.sum_univ_succ]
  ring

theorem powered_gt_one238 (Q : ℝ) (hQ : 1 < Q) : 1 < Q^2 :=
  one_lt_pow₀ hQ (by decide)

theorem normalized_real_bound238 (c : Fin 5 → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    ∀ s, |normalizedWeights238 c s| ≤ 1 := by
  intro s
  change |(c (lo237 s)+c (hi237 s))/2| ≤ 1
  rw [abs_div,abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  apply (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
  have h := abs_add (c (lo237 s)) (c (hi237 s))
  linarith [hc (lo237 s),hc (hi237 s)]

theorem normalized_finite_bounds238 (c : Fin 5 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    ∀ s, -1 ≤ normalizedWeights238 c s ∧ normalizedWeights238 c s ≤ 0 := by
  intro s
  change -1 ≤ (c (lo237 s)+c (hi237 s))/2 ∧ (c (lo237 s)+c (hi237 s))/2 ≤ 0
  constructor <;> linarith [(hc (lo237 s)).1,(hc (lo237 s)).2,(hc (hi237 s)).1,(hc (hi237 s)).2]

theorem normalized_balance238 (c0 c2 c3 : Fin 5 → ℝ)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∑ s, (normalizedWeights238 c0 s+normalizedWeights238 c2 s+normalizedWeights238 c3 s)) = 0 := by
  calc
    _ = (∑ s, pairWeights238 (fun i => c0 i+c2 i+c3 i) s)/2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      dsimp [normalizedWeights238,pairWeights238]
      ring
    _ = 0 := by rw [pairWeights_sum238,hb]; norm_num

theorem powered_rpow238 (Q a b : ℝ) (hQ : 1 < Q) :
    (Q^2)^((a+b)/2) = Q^(a+b) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans hQ).le]
  congr 1
  ring

theorem powered_threshold238 (p : ℕ) (Q a b : ℝ) :
    JSP000334.qThreshold p (Q^2) ((a+b)/2) = JSP000334.qThreshold p Q (a+b) := by
  unfold JSP000334.qThreshold
  rw [Real.log_pow]
  ring

theorem powered_group238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ) :
    originalSourceGroup10 (compound237 A2) (compound237 A3) (Q^2)
      (normalizedWeights238 c2) (normalizedWeights238 c3) = directGroup238 A2 A3 Q c2 c3 := by
  unfold originalSourceGroup10 directGroup238 normalizedWeights238 pairWeights238
  simp_rw [powered_threshold238]

theorem powered_body238 (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 5 → ℝ) (x : Fin 10 → ℝ) (r : ℝ) :
    coordinateGauge10 (originalCoordinates10 (compound237 L) (compound_unit238 L hL)
      (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0)) x ≤ r ↔
      ∀ s, |(compound237 L *ᵥ x) s| ≤ r*Q^(pairWeights238 c0 s) := by
  change ‖originalCoordinates10 (compound237 L) (compound_unit238 L hL)
    (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0) x‖ ≤ r ↔ _
  rw [originalCoordinates10_bounds]
  simp only [normalizedWeights238,pairWeights238,powered_rpow238 Q _ _ hQ]

end CompoundFeasibility.Exterior52_238
