import SubspaceBridge.RestrictedCoordinates4
import SubspaceBridge.RestrictedVolume4
import SubspaceBridge.RestrictedMinkowski4
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry4

theorem source_restricted_minkowski_upper4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
      (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
        ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
          (4 : ℝ)^(Module.finrank ℚ P) := by
  obtain ⟨c,hshort⟩ := exists_restricted_short_coordinates4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  obtain ⟨_,_,_,hpos,hmono,_,_⟩ := exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let dim : Fin 4 := ⟨Module.finrank ℚ P,by omega⟩
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  let e := b.equivFun.symm
  let f : (Fin dim.val → ℝ) → ℝ := fun x => restrictedGauge4 P L hL Q hQ c₀ (e x)
  have hf : ∀ (r : ℝ) (x : Fin dim.val → ℝ), f (r • x) = |r| * f x := by
    intro r x
    simp [f,restrictedGauge4,coordinateGauge4,map_smul,norm_smul,Real.norm_eq_abs]
  have hp (z : Fin dim.val → ℤ) :
      e (fun i => (z i : ℝ)) = restrictedIntegerPoint4 c z := by
    apply b.equivFun.injective
    ext i
    change (b.equivFun (b.equivFun.symm (fun i => (z i : ℝ)))) i = _
    rw [LinearEquiv.apply_symm_apply]
    exact (restrictedIntegerPoint4_coord c z i).symm
  have hbody : {x | f x ≤ 1} = b.equivFun '' restrictedBody4 P L Q c₀ := by
    rw [LinearEquiv.image_eq_preimage]
    ext x
    change restrictedGauge4 P L hL Q hQ c₀ (e x) ≤ 1 ↔ e x ∈ restrictedBody4 P L Q c₀
    rw [restrictedBody4_gauge P L hL Q hQ c₀]
    rfl
  have hconv : Convex ℝ {x | f x ≤ 1} := by
    rw [hbody]
    exact (restrictedBody4_compact_convex P L hL Q hQ c₀).2.linear_image b.equivFun.toLinearMap
  have hsymm : ∀ x, f (-x) = f x := by
    intro x
    simp [f,restrictedGauge4,coordinateGauge4,map_neg]
  have hu := RestrictedMinkowski4.adapted_product_volume_upper dim f hf
    (restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃) hpos hmono
    (fun z k hk _ => by
      change _ ≤ restrictedGauge4 P L hL Q hQ c₀ (e (fun i => (z i : ℝ)))
      rw [hp]
      exact hshort z k hk) hsymm hconv
  have hvol := restrictedBasis4_volume_ratio c (restrictedBody4 P L Q c₀)
    (restrictedBody4_compact_convex P L hL Q hQ c₀).1
  rw [hbody,hvol] at hu
  simpa only [div_eq_mul_inv,mul_assoc] using hu

end CompoundFeasibility.RestrictedGeometry4
