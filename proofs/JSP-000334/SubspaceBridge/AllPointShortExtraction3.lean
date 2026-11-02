import SubspaceBridge.AllPointRankThreshold3
import SubspaceBridge.AllPointRationalSpan3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_line_proper3 (b : IntegerTriple) (hb : b ≠ 0) :
    Submodule.span ℚ {fun i => (b i : ℚ)} ≠ ⊤ := by
  have hn : (fun i => (b i : ℚ)) ≠ 0 := by
    intro h
    apply hb
    funext i
    have hi := congrFun h i
    change (b i : ℚ) = 0 at hi
    change b i = 0
    exact_mod_cast hi
  have hf := finrank_span_singleton (K := ℚ) hn
  intro htop
  rw [htop] at hf
  norm_num at hf

theorem allpoint_kernel_proper3 (b : IntegerTriple) (hb : b ≠ 0) :
    LinearMap.ker (originalPlanePairing3 (fun i => (b i : ℚ))) ≠ ⊤ := by
  intro h
  have hf := LinearMap.ker_eq_top.mp h
  have hn : (fun i => (b i : ℚ)) ≠ 0 := by
    intro he
    apply hb
    funext i
    have hi := congrFun he i
    change (b i : ℚ) = 0 at hi
    change b i = 0
    exact_mod_cast hi
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hn
  have hh := congrArg (fun f : (Fin 3 → ℚ) →ₗ[ℚ] ℚ => f (Pi.single i 1)) hf
  apply hi
  simpa [originalPlanePairing3,Pi.single_apply] using hh

theorem allpoint_source_short_rational3 (k0 k2 k3 : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 3 → ℝ) (B : Basis (Fin 3) ℝ RealTriple)
    (u : Fin 3 → qSourceLattice3 k2 k3 Q c2 c3)
    (hB : lattice3 B = (qSourceLattice3 k2 k3 Q c2 c3).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (ha : ∀ j, coordinateGauge3 (qSourceCoordinates3 k0 Q c0 hQ) (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) j)
    (k : Fin 3)
    (hgap : ∀ i : Fin 3, i < k → successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) i <
      successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) k)
    (z : IntegerTriple) (hz : z ∈ qSourceLattice3 k2 k3 Q c2 c3)
    (hshort : coordinateGauge3 (qSourceCoordinates3 k0 Q c0 hQ) (integerTripleReal3 z) <
      successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) k) :
    (fun i => (z i : ℚ)) ∈ Submodule.span ℚ (Set.range
      (fun j : Fin k.val => fun i => ((u (Fin.castLE (by omega) j) : IntegerTriple) i : ℚ))) := by
  apply allpoint_rational_flag3 (fun j => (u j : IntegerTriple)) hu k z
  apply lattice3_short_mem_minimaFlag B (qSourceCoordinates3 k0 Q c0 hQ) _ hu _ ha k hgap _ _ hshort
  · intro i
    rw [hB]
    exact Submodule.mem_map.mpr ⟨(u i : IntegerTriple),(u i).property,rfl⟩
  · rw [hB]
    exact Submodule.mem_map.mpr ⟨z,hz,rfl⟩

theorem allpoint_first_rational_span3 (w : Fin 3 → IntegerTriple) :
    Submodule.span ℚ (Set.range (fun j : Fin (1 : Fin 3).val => fun i => (w (Fin.castLE (by omega) j) i : ℚ))) =
      Submodule.span ℚ {fun i => (w 0 i : ℚ)} := by
  congr 1
  ext x
  simp [Set.range_unique]

theorem allpoint_plane_annihilation3 (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℝ (fun j => integerTripleReal3 (w j)))
    (z : Fin 3 → ℚ) (hz : z ∈ Submodule.span ℚ (Set.range
      (fun j : Fin (2 : Fin 3).val => fun i => (w (Fin.castLE (by omega) j) i : ℚ)))) :
    originalPlanePairing3 (dualFrameVector3 w 2) z = 0 := by
  have hle : Submodule.span ℚ (Set.range
      (fun j : Fin (2 : Fin 3).val => fun i => (w (Fin.castLE (by omega) j) i : ℚ))) ≤
      LinearMap.ker (originalPlanePairing3 (dualFrameVector3 w 2)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change (∑ i, (w (Fin.castLE (by omega) j) i : ℚ)*dualFrameVector3 w 2 i) = 0
    rw [dualFrameVector3_pairing w (dualFrameMatrix3_rational_independent w hw),if_neg]
    intro he
    have hh := congrArg Fin.val he
    change j.val = 2 at hh
    omega
  exact hle hz

end JSP000334
