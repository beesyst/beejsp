import SubspaceBridge.BinaryZeroForms2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_integer_height_ball_finite (T : Set (Fin 2 → ℤ)) (M : ℝ)
    (hM : ∀ z ∈ T,(archPairHeight z : ℝ)≤M) : T.Finite := by
  have hbox : {z : Fin 2 → ℤ | ∀ i,-⌈M⌉≤z i ∧ z i≤⌈M⌉}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  apply hbox.subset
  intro z hz i
  have hc : |(z i : ℝ)|≤(archPairHeight z : ℝ) := by
    have hq : |(z i : ℚ)|≤archPairHeight z := by
      have hi : i=0 ∨ i=1 := by omega
      rcases hi with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact_mod_cast hq
  have hh := abs_le.mp (hc.trans (hM z hz))
  have hm := Int.le_ceil M
  constructor
  · exact_mod_cast (show -((⌈M⌉ : ℤ) : ℝ)≤(z i : ℝ) by linarith)
  · exact_mod_cast (show (z i : ℝ)≤((⌈M⌉ : ℤ) : ℝ) by linarith)

noncomputable def binaryRationalSpan (z : Fin 2 → ℤ) : Submodule ℚ (Fin 2 → ℚ) :=
  Submodule.span ℚ {(fun i => (z i : ℚ))}

theorem binary_rational_span_mem (z : Fin 2 → ℤ) : (fun i => (z i : ℚ)) ∈ binaryRationalSpan z :=
  Submodule.subset_span (Set.mem_singleton _)

theorem binary_rational_span_proper (z : Fin 2 → ℤ) (h1 : z 1 ≠ 0) : binaryRationalSpan z ≠ ⊤ := by
  have hline : binaryWeightedLine (-(z 1 : ℚ)) (z 0 : ℚ) ≠ ⊤ :=
    binary_weighted_line_proper _ _ (neg_ne_zero.mpr (by exact_mod_cast h1))
  have hle : binaryRationalSpan z≤binaryWeightedLine (-(z 1 : ℚ)) (z 0 : ℚ) := by
    apply Submodule.span_le.mpr
    intro x hx
    have he : x=(fun i => (z i : ℚ)) := Set.mem_singleton_iff.mp hx
    subst x
    change -(z 1 : ℚ)*(z 0 : ℚ)+(z 0 : ℚ)*(z 1 : ℚ)=0
    ring
  intro he
  rw [he] at hle
  exact hline (top_le_iff.mp hle)

end JSP000334
