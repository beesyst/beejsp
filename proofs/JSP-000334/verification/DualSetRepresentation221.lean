import SubspaceBridge.SourceDualLattice219
open scoped BigOperators Matrix
namespace M221SetRepresentation
open CompoundFeasibility.SourceDualGeometry219

theorem raw_integral221 (G : AddSubgroup (Fin 10 → ℤ)) :
    {v : Fin 10 → ℚ | ∀ x : G, ∃ a : ℤ,
      (∑ i, ((x : Fin 10 → ℤ) i : ℚ)*v i) = (a : ℚ)} = integralDual219 G := by
  rfl

theorem raw_scaled221 (G : AddSubgroup (Fin 10 → ℤ)) :
    (fun v : Fin 10 → ℚ => (G.index : ℚ) • v) ''
      {v | ∀ x : G, ∃ a : ℤ, (∑ i, ((x : Fin 10 → ℤ) i : ℚ)*v i) = (a : ℚ)} =
        scaledDual219 G := by
  exact congrArg (fun S : Set (Fin 10 → ℚ) =>
    (fun v : Fin 10 → ℚ => (G.index : ℚ) • v) '' S) (raw_integral221 G)

end M221SetRepresentation
