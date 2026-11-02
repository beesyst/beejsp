import SubspaceBridge.MinimaBasis5
import SubspaceBridge.Minkowski5
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section

def integerPoint5 {b : Basis (Fin 5) ℝ (Fin 5 → ℝ)}
    (c : Basis (Fin 5) ℤ (lattice5Span b)) (z : Fin 5 → ℤ) : Fin 5 → ℝ :=
  (c.equivFun.symm z : lattice5Span b)

theorem integerPoint5_coord {b : Basis (Fin 5) ℝ (Fin 5 → ℝ)}
    (c : Basis (Fin 5) ℤ (lattice5Span b)) (z : Fin 5 → ℤ) (i : Fin 5) :
    (c.ofZLatticeBasis ℝ _).repr (integerPoint5 c z) i = (z i : ℝ) := by
  rw [integerPoint5,Basis.ofZLatticeBasis_repr_apply]
  change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = (z i : ℝ)
  rw [LinearEquiv.apply_symm_apply]

theorem integerPoint5_outside {b : Basis (Fin 5) ℝ (Fin 5 → ℝ)}
    (c : Basis (Fin 5) ℤ (lattice5Span b)) (v : Fin 5 → Fin 5 → ℝ)
    (hadapt : ∀ k : Fin 5, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice5Span b) : Fin 5 → ℝ))) = minimaFlag5 v k)
    (z : Fin 5 → ℤ) (k : Fin 5) (hk : z k ≠ 0) : integerPoint5 c z ∉ minimaFlag5 v k := by
  let a := c.ofZLatticeBasis ℝ (lattice5Span b)
  have hle : minimaFlag5 v k ≤ LinearMap.ker (a.coord k) := by
    rw [← hadapt k]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change a.repr ((c (Fin.castLE (by omega) j) : lattice5Span b) : Fin 5 → ℝ) k = 0
    have hne : (Fin.castLE (by omega) j : Fin 5) ≠ k := by
      intro h
      have heq := congrArg Fin.val h
      change j.val = k.val at heq
      omega
    simp [a,Basis.ofZLatticeBasis_repr_apply,hne]
  intro h
  have hzero := hle h
  change a.repr (integerPoint5 c z) k = 0 at hzero
  rw [integerPoint5_coord] at hzero
  exact hk (by exact_mod_cast hzero)

theorem successive_minima5_product_volume_upper
    (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) :
    (∏ i, successiveRadius5 b e i) * volume.real {x | coordinateGauge5 e x ≤ 1} /
      ZLattice.covolume (lattice5Span b) ≤ (4 : ℝ)^5 := by
  obtain ⟨v,hv,hvL,hpos,hmono,hatt,hshort⟩ := exists_successive_minima5 b e
  obtain ⟨c,hc⟩ := exists_adapted_integer_basis5 b v hv hvL
  let a := c.ofZLatticeBasis ℝ (lattice5Span b)
  let F := a.equivFun.symm
  let f : (Fin 5 → ℝ) → ℝ := fun x => coordinateGauge5 e (F x)
  have hf : ∀ (r : ℝ) (x : Fin 5 → ℝ), f (r • x) = |r| * f x := by
    intro r x
    simp [f,coordinateGauge5,map_smul,norm_smul,Real.norm_eq_abs]
  have hp (z : Fin 5 → ℤ) : F (fun i => (z i : ℝ)) = integerPoint5 c z := by
    apply a.equivFun.injective
    ext i
    change (a.equivFun (a.equivFun.symm (fun i => (z i : ℝ)))) i = _
    rw [LinearEquiv.apply_symm_apply]
    exact (integerPoint5_coord c z i).symm
  have hbody : {x | f x ≤ 1} = a.equivFun '' {x | coordinateGauge5 e x ≤ 1} := by
    rw [LinearEquiv.image_eq_preimage]
    rfl
  have hconv : Convex ℝ {x | f x ≤ 1} := by
    simpa only [Metric.closedBall,dist_zero_right] using
      (convex_closedBall (0 : Fin 5 → ℝ) 1).linear_preimage (e.toLinearMap.comp F.toLinearMap)
  have hsymm : ∀ x, f (-x) = f x := by intro x; simp [f,coordinateGauge5,map_neg]
  have hu := Minkowski5.adapted_product_volume_upper f hf (successiveRadius5 b e) hpos hmono
    (fun z k hk _ => by
      change _ ≤ coordinateGauge5 e (F (fun i => (z i : ℝ)))
      rw [hp,← hatt k]
      exact hshort k _ (c.equivFun.symm z).property (integerPoint5_outside c v hc z k hk)) hsymm hconv
  have hvol : volume.real (a.equivFun '' {x | coordinateGauge5 e x ≤ 1}) =
      volume.real {x | coordinateGauge5 e x ≤ 1} / ZLattice.covolume (lattice5Span b) := by
    rw [measureReal_def,ZLattice.volume_image_eq_volume_div_covolume (lattice5Span b) c,
      ENNReal.toReal_div,ENNReal.toReal_ofReal (ZLattice.covolume_pos (lattice5Span b) volume).le]
    rfl
  rw [hbody,hvol] at hu
  simpa only [div_eq_mul_inv,mul_assoc] using hu

end
end CompoundFeasibility
