import SubspaceBridge.SourceSatz51Minima218
import SubspaceBridge.SourceSatz51Selection218
import SubspaceBridge.SourceOriginalData10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSatz51Entry218
open SourceOriginalVariable10

structure SourceData218 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (q : ℝ) (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ) (delta : ℝ) where
  positive : ∀ i, 0 < A i
  sizes : ∀ i, A i < q ∧ (A i)⁻¹ < q
  balance : (∏ i, A i*q^(c2 i)*q^(c3 i)) = 1
  u : Fin 10 → Fin 10 → ℤ
  member : ∀ j, u j ∈ originalSourceGroup10 A2 A3 q c2 c3
  independent : LinearIndependent ℝ (fun j => integerReal (u j))
  attaining : ∀ j, coordinateGauge10 (originalCoordinates10 L hL q hq
      (fun i => normalizedWidth10 q (A i))) (integerReal (u j)) =
    sourceMinima10 A2 A3 L hL q hq (fun i => normalizedWidth10 q (A i)) c2 c3 j
  small : sourceMinima10 A2 A3 L hL q hq (fun i => normalizedWidth10 q (A i)) c2 c3 8 < q^(-delta)

theorem squared_parameter218 (q : ℝ) (hq : 1 < q) : 1 < q^2 := by
  nlinarith [sq_nonneg (q-1)]

theorem corrected_minima218
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ} {hL : IsUnit L}
    {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}
    (h2 : ∀ i, c2 i ≤ 0) (h3 : ∀ i, c3 i ≤ 0)
    (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) (j : Fin 10) :
    sourceMinima10 A2 A3 L hL (q^2) (squared_parameter218 q hq)
      (fun i => normalizedWidth10 (q^2) (widthScale218 q c2 c3*A i))
      (fun i => normalizedFinite10 2 (q^2) (roundedExponent218 2 q (c2 i)))
      (fun i => normalizedFinite10 3 (q^2) (roundedExponent218 3 q (c3 i))) j =
    sourceMinima10 A2 A3 L hL q hq (fun i => normalizedWidth10 q (A i)) c2 c3 j /
      widthScale218 q c2 c3 := by
  have ht := width_scale_bounds218 q hq c2 c3 h2 h3
  exact source_minima_scale218 A2 A3 L hL q (q^2) hq (squared_parameter218 q hq)
    _ c2 c3 _ _ _ _ ht.2.2.1 (rounding_lattice218 A2 A3 q hq c2 c3).2
    (source_gauge_width_scale218 L hL q (q^2) hq (squared_parameter218 q hq) A D.positive _ ht.2.2.1) j

def toOriginalData218
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ} {hL : IsUnit L}
    {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) (hq6 : 6 < q)
    (hslack : 6 ≤ q^(delta/4)) (S0 : Finset (Fin 3 → Fin 10))
    (hS : sourceSet218 q delta A c2 c3 = S0) :
    OriginalData10 A2 A3 L hL (q^2) (squared_parameter218 q hq) (delta/2) S0 where
  A := fun i => widthScale218 q c2 c3*A i
  positive := fun i => mul_pos (width_scale_bounds218 q hq c2 c3 (fun i => (h2 i).2) (fun i => (h3 i).2)).2.2.1 (D.positive i)
  f2 := fun i => roundedExponent218 2 q (c2 i)
  f3 := fun i => roundedExponent218 3 q (c3 i)
  nonpos2 := fun i => (rounded_local218 2 (by decide) q (c2 i) hq (h2 i).2).1
  nonpos3 := fun i => (rounded_local218 3 (by decide) q (c3 i) hq (h3 i).2).1
  sizes := corrected_sizes218 q hq6 c2 c3 A h2 h3 D.positive D.sizes
  balance := corrected_width_balance218 q hq c2 c3 A (fun i => (h2 i).2) (fun i => (h3 i).2) D.balance
  selected := by
    intro s hs
    exact source_set_selected218 q delta hq c2 c3 A (fun i => (h2 i).2) (fun i => (h3 i).2)
      D.positive hslack s (hS.symm ▸ hs)
  u := D.u
  member2 := by
    intro j
    have hm : D.u j ∈ originalSourceGroup10 A2 A3 (q^2)
        (fun i => normalizedFinite10 2 (q^2) (roundedExponent218 2 q (c2 i)))
        (fun i => normalizedFinite10 3 (q^2) (roundedExponent218 3 q (c3 i))) := by
      rw [(rounding_lattice218 A2 A3 q hq c2 c3).2]
      exact D.member j
    exact ((normalized_source_group_exact10 A2 A3 (q^2) (squared_parameter218 q hq) _ _
      (fun i => (rounded_local218 2 (by decide) q (c2 i) hq (h2 i).2).1)
      (fun i => (rounded_local218 3 (by decide) q (c3 i) hq (h3 i).2).1) (D.u j)).mp hm).1
  member3 := by
    intro j
    have hm : D.u j ∈ originalSourceGroup10 A2 A3 (q^2)
        (fun i => normalizedFinite10 2 (q^2) (roundedExponent218 2 q (c2 i)))
        (fun i => normalizedFinite10 3 (q^2) (roundedExponent218 3 q (c3 i))) := by
      rw [(rounding_lattice218 A2 A3 q hq c2 c3).2]
      exact D.member j
    exact ((normalized_source_group_exact10 A2 A3 (q^2) (squared_parameter218 q hq) _ _
      (fun i => (rounded_local218 2 (by decide) q (c2 i) hq (h2 i).2).1)
      (fun i => (rounded_local218 3 (by decide) q (c3 i) hq (h3 i).2).1) (D.u j)).mp hm).2
  independent := D.independent
  attaining := by
    intro j
    rw [source_gauge_width_scale218 L hL q (q^2) hq (squared_parameter218 q hq) A D.positive _
      (width_scale_bounds218 q hq c2 c3 (fun i => (h2 i).2) (fun i => (h3 i).2)).2.2.1,
      D.attaining j,corrected_minima218 (fun i => (h2 i).2) (fun i => (h3 i).2) D j]
  small := by
    rw [corrected_minima218 (fun i => (h2 i).2) (fun i => (h3 i).2) D 8]
    have ht := width_scale_bounds218 q hq c2 c3 (fun i => (h2 i).2) (fun i => (h3 i).2)
    have hp := (sourceMinima10_pos_mono A2 A3 L hL q hq (fun i => normalizedWidth10 q (A i)) c2 c3).1 8
    have hle : sourceMinima10 A2 A3 L hL q hq (fun i => normalizedWidth10 q (A i)) c2 c3 8 /
        widthScale218 q c2 c3 ≤ sourceMinima10 A2 A3 L hL q hq (fun i => normalizedWidth10 q (A i)) c2 c3 8 := by
      apply (div_le_iff₀ ht.2.2.1).mpr
      nlinarith [ht.1]
    apply (hle.trans_lt D.small).trans_eq
    rw [← Real.rpow_natCast_mul (zero_lt_one.trans hq).le]
    congr 1
    ring

end CompoundFeasibility.SourceSatz51Entry218
