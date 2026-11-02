import SubspaceBridge.SourceOriginalVariable10
open scoped BigOperators Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSampling10 OriginalDual10
noncomputable section

theorem original_source_group_envelope10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c2 c3 d2 d3 : Fin 10 → ℝ) (h2 : ∀ i, c2 i ≤ d2 i) (h3 : ∀ i, c3 i ≤ d3 i)
    (hd2 : ∀ i, d2 i ≤ 0) (hd3 : ∀ i, d3 i ≤ 0) :
    originalSourceGroup10 A2 A3 Q c2 c3 ≤ originalSourceGroup10 A2 A3 Q d2 d3 := by
  intro x hx
  constructor
  · apply (lattice10_spec 2 A2 _ x).mpr
    intro i
    have hn := source_finite_short_bound10 2 A2 Q hQ c2 (fun i => (h2 i).trans (hd2 i)) x hx.1 i
    rw [SourceForms10.finiteMatrix10,finite_form_norm10] at hn
    have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le hQ.le (h2 i))
    simpa only [zpow_neg,zpow_natCast] using (padic_rpow_ceil42 2 Q (d2 i) hQ (hd2 i) _).mp hh
  · apply (lattice10_spec 3 A3 _ x).mpr
    intro i
    have hn := source_finite_short_bound10 3 A3 Q hQ c3 (fun i => (h3 i).trans (hd3 i)) x hx.2 i
    rw [SourceForms10.finiteMatrix10,finite_form_norm10] at hn
    have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le hQ.le (h3 i))
    simpa only [zpow_neg,zpow_natCast] using (padic_rpow_ceil42 3 Q (d3 i) hQ (hd3 i) _).mp hh

end
end CompoundFeasibility.SourceOriginalVariable10
