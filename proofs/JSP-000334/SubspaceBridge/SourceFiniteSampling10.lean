import SubspaceBridge.SourceFrameSampling10
import SubspaceBridge.SourceForms10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10

theorem source_finite_short_bound10 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 10 → ℝ) (hc : ∀ i, c i ≤ 0) (z : Fin 10 → ℤ)
    (hz : z ∈ lattice10 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i)))) :
    ∀ i, ‖(SourceForms10.finiteMatrix10 p A *ᵥ (fun k => (z k : ℚ_[p]))) i‖ ≤ Q^(c i) := by
  intro i
  rw [SourceForms10.finiteMatrix10,OriginalDual10.finite_form_norm10]
  apply (padic_rpow_ceil42 p Q (c i) hQ (hc i) _).mpr
  have hi := (lattice10_spec p A _ z).mp hz i
  simpa only [zpow_neg,zpow_natCast] using hi

end CompoundFeasibility.SourceSampling10
