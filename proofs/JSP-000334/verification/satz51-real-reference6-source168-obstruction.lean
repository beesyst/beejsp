import SubspaceBridge.OriginalShortPlane42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Inequality168Audit

theorem scalar_obstruction :
    (0 : ℚ) < 1/16 ∧ (1/16 : ℚ) ≤ 1/4 ∧ (1/4 : ℚ) ≤ 1024 ∧
    (1/16 : ℚ) < (1/4)*(1/2) ∧ (1/4 : ℚ) ≤ 1/2 ∧
    ¬ ((1/2 : ℚ) < 1/4) ∧ ¬ ((1/4 : ℚ) < 1/4) ∧
    (1/16 : ℚ)*(1/16)*(1/4)*1024 = 1 ∧
    (-1 : ℚ)+1/5+2/5+2/5 = 0 := by
  norm_num

theorem third_basis_vector_outside_first_two :
    ((Pi.single (1 : Fin 4) (1 : ℚ) : Fin 4 → ℚ)) ∉ Submodule.span ℚ
      {(Pi.single (2 : Fin 4) (1 : ℚ) : Fin 4 → ℚ),(Pi.single (3 : Fin 4) (1 : ℚ) : Fin 4 → ℚ)} := by
  intro hx
  have hker : Submodule.span ℚ
      {(Pi.single (2 : Fin 4) (1 : ℚ) : Fin 4 → ℚ),(Pi.single (3 : Fin 4) (1 : ℚ) : Fin 4 → ℚ)} ≤
        LinearMap.ker (LinearMap.proj (1 : Fin 4) : (Fin 4 → ℚ) →ₗ[ℚ] ℚ) := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [LinearMap.mem_ker,Pi.single_apply]
  have he := hker hx
  norm_num [LinearMap.mem_ker,Pi.single_apply] at he

end CompoundFeasibility.Inequality168Audit
#check CompoundFeasibility.originalCoordinates4_bounds
#print CompoundFeasibility.originalCoordinates4_bounds
#print axioms CompoundFeasibility.originalCoordinates4_bounds
#check CompoundFeasibility.lattice4_spec
#print CompoundFeasibility.lattice4_spec
#print axioms CompoundFeasibility.lattice4_spec
#check CompoundFeasibility.padic_rpow_ceil42
#print CompoundFeasibility.padic_rpow_ceil42
#print axioms CompoundFeasibility.padic_rpow_ceil42
#check CompoundFeasibility.sourceMinima4_eq_radius
#print CompoundFeasibility.sourceMinima4_eq_radius
#print axioms CompoundFeasibility.sourceMinima4_eq_radius
#check CompoundFeasibility.sourceMinima4_pos_mono
#print CompoundFeasibility.sourceMinima4_pos_mono
#print axioms CompoundFeasibility.sourceMinima4_pos_mono
#check CompoundFeasibility.OriginalShortPlane42.sourceMinima4_strict_third42
#print CompoundFeasibility.OriginalShortPlane42.sourceMinima4_strict_third42
#print axioms CompoundFeasibility.OriginalShortPlane42.sourceMinima4_strict_third42
#check CompoundFeasibility.OriginalShortPlane42.source_original_short_in_fixed_plane42
#print CompoundFeasibility.OriginalShortPlane42.source_original_short_in_fixed_plane42
#print axioms CompoundFeasibility.OriginalShortPlane42.source_original_short_in_fixed_plane42
#check CompoundFeasibility.source_original_uniform_minima_upper4
#print CompoundFeasibility.source_original_uniform_minima_upper4
#print axioms CompoundFeasibility.source_original_uniform_minima_upper4
#check CompoundFeasibility.Inequality168Audit.scalar_obstruction
#print CompoundFeasibility.Inequality168Audit.scalar_obstruction
#print axioms CompoundFeasibility.Inequality168Audit.scalar_obstruction
#check CompoundFeasibility.Inequality168Audit.third_basis_vector_outside_first_two
#print CompoundFeasibility.Inequality168Audit.third_basis_vector_outside_first_two
#print axioms CompoundFeasibility.Inequality168Audit.third_basis_vector_outside_first_two
