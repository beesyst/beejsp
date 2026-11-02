import SubspaceBridge.MinimaBasis10
import SubspaceBridge.Minkowski10
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section

def integerPoint10 {b : Basis (Fin 10) ℝ (Fin 10 → ℝ)}
    (c : Basis (Fin 10) ℤ (lattice10Span b)) (z : Fin 10 → ℤ) : Fin 10 → ℝ :=
  (c.equivFun.symm z : lattice10Span b)

theorem integerPoint10_coord {b : Basis (Fin 10) ℝ (Fin 10 → ℝ)}
    (c : Basis (Fin 10) ℤ (lattice10Span b)) (z : Fin 10 → ℤ) (i : Fin 10) :
    (c.ofZLatticeBasis ℝ _).repr (integerPoint10 c z) i = (z i : ℝ) := by
  rw [integerPoint10,Basis.ofZLatticeBasis_repr_apply]
  change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = (z i : ℝ)
  rw [LinearEquiv.apply_symm_apply]

theorem integerPoint10_outside {b : Basis (Fin 10) ℝ (Fin 10 → ℝ)}
    (c : Basis (Fin 10) ℤ (lattice10Span b)) (v : Fin 10 → Fin 10 → ℝ)
    (hadapt : ∀ k : Fin 10, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice10Span b) : Fin 10 → ℝ))) = minimaFlag10 v k)
    (z : Fin 10 → ℤ) (k : Fin 10) (hk : z k ≠ 0) : integerPoint10 c z ∉ minimaFlag10 v k := by
  let a := c.ofZLatticeBasis ℝ (lattice10Span b)
  have hle : minimaFlag10 v k ≤ LinearMap.ker (a.coord k) := by
    rw [← hadapt k]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change a.repr ((c (Fin.castLE (by omega) j) : lattice10Span b) : Fin 10 → ℝ) k = 0
    have hne : (Fin.castLE (by omega) j : Fin 10) ≠ k := by
      intro h
      have heq := congrArg Fin.val h
      change j.val = k.val at heq
      omega
    simp [a,Basis.ofZLatticeBasis_repr_apply,hne]
  intro h
  have hzero := hle h
  change a.repr (integerPoint10 c z) k = 0 at hzero
  rw [integerPoint10_coord] at hzero
  exact hk (by exact_mod_cast hzero)

theorem successive_minima10_product_volume_upper
    (b : Basis (Fin 10) ℝ (Fin 10 → ℝ)) (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) :
    (∏ i, successiveRadius10 b e i) * volume.real {x | coordinateGauge10 e x ≤ 1} /
      ZLattice.covolume (lattice10Span b) ≤ (4 : ℝ)^10 := by
  obtain ⟨v,hv,hvL,hpos,hmono,hatt,hshort⟩ := exists_successive_minima10 b e
  obtain ⟨c,hc⟩ := exists_adapted_integer_basis10 b v hv hvL
  let a := c.ofZLatticeBasis ℝ (lattice10Span b)
  let F := a.equivFun.symm
  let f : (Fin 10 → ℝ) → ℝ := fun x => coordinateGauge10 e (F x)
  have hf : ∀ (r : ℝ) (x : Fin 10 → ℝ), f (r • x) = |r| * f x := by
    intro r x
    simp [f,coordinateGauge10,map_smul,norm_smul,Real.norm_eq_abs]
  have hp (z : Fin 10 → ℤ) : F (fun i => (z i : ℝ)) = integerPoint10 c z := by
    apply a.equivFun.injective
    ext i
    change (a.equivFun (a.equivFun.symm (fun i => (z i : ℝ)))) i = _
    rw [LinearEquiv.apply_symm_apply]
    exact (integerPoint10_coord c z i).symm
  have hbody : {x | f x ≤ 1} = a.equivFun '' {x | coordinateGauge10 e x ≤ 1} := by
    rw [LinearEquiv.image_eq_preimage]
    rfl
  have hconv : Convex ℝ {x | f x ≤ 1} := by
    simpa only [Metric.closedBall,dist_zero_right] using
      (convex_closedBall (0 : Fin 10 → ℝ) 1).linear_preimage (e.toLinearMap.comp F.toLinearMap)
  have hsymm : ∀ x, f (-x) = f x := by intro x; simp [f,coordinateGauge10,map_neg]
  have hu := Minkowski10.adapted_product_volume_upper f hf (successiveRadius10 b e) hpos hmono
    (fun z k hk _ => by
      change _ ≤ coordinateGauge10 e (F (fun i => (z i : ℝ)))
      rw [hp,← hatt k]
      exact hshort k _ (c.equivFun.symm z).property (integerPoint10_outside c v hc z k hk)) hsymm hconv
  have hvol : volume.real (a.equivFun '' {x | coordinateGauge10 e x ≤ 1}) =
      volume.real {x | coordinateGauge10 e x ≤ 1} / ZLattice.covolume (lattice10Span b) := by
    rw [measureReal_def,ZLattice.volume_image_eq_volume_div_covolume (lattice10Span b) c,
      ENNReal.toReal_div,ENNReal.toReal_ofReal (ZLattice.covolume_pos (lattice10Span b) volume).le]
    rfl
  rw [hbody,hvol] at hu
  simpa only [div_eq_mul_inv,mul_assoc] using hu

end
end CompoundFeasibility
