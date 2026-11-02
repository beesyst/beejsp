import SubspaceBridge.SelectedBoxVolume4
import SubspaceBridge.RestrictedSelectedBasis4
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility.RestrictedRealBody4
open RestrictedGeometry4 RestrictedRelaxed4 RestrictedIntegerCoordinates4 RestrictedRows4
open RestrictedWeightOrder4 SelectedRestriction4 RestrictedSelectedBasis4 SelectedBoxVolume4
noncomputable section

def baseRealBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan4 P) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  exact (baseIntegerBasis4 P hP).ofZLatticeBasis ℝ (baseLattice4 P)

def realSelection4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) : Fin (Module.finrank ℚ P) → Fin 4 :=
  fun k => weightOrder4 c (selectedIndex4 (realRestrictionCoordinates4 P hP L) c
    (realRestrictionCoordinates4_span P hP L hL) k)

def realSelectedMatrix4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℝ :=
  fun k => rowCoordinates4 (rationalRealSpan4 P) (baseRealBasis4 P hP) L (realSelection4 P hP L hL c k)

theorem realSelectedMatrix4_det_ne_zero (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    (realSelectedMatrix4 P hP L hL c).det ≠ 0 :=
  selected_basis_matrix_det4 (rationalRealSpan4 P) (realRestrictionBasis4 P hP) (baseRealBasis4 P hP)
    L c (realRestrictionCoordinates4_span P hP L hL)

def selectedRealEquiv4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    (Fin (Module.finrank ℚ P) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℚ P) → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (realSelectedMatrix4 P hP L hL c)) (by
    have hu : IsUnit (realSelectedMatrix4 P hP L hL c) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realSelectedMatrix4_det_ne_zero P hP L hL c))
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem rowCoordinates4_mulVec_basis {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (x : P) :
    rowCoordinates4 P b A *ᵥ b.equivFun x = A *ᵥ (x : Fin 4 → K) := by
  ext i
  let f : P →ₗ[K] K := (LinearMap.proj i).comp ((Matrix.toLin' A).comp P.subtype)
  have h := congrArg f (b.sum_repr x)
  change ∑ k, f (b k) * b.repr x k = f x
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using h

theorem relaxedBody4_coordinates (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (Q : ℝ) (c : Fin 4 → ℝ) :
    relaxedBody4 P L Q c (realSelection4 P hP L hL c) =
      (baseRealBasis4 P hP).equivFun ⁻¹' ((selectedRealEquiv4 P hP L hL c) ⁻¹'
        weightedBox4 (fun k => Q^(c (realSelection4 P hP L hL c k)))) := by
  have heval (x : rationalRealSpan4 P) (k : Fin (Module.finrank ℚ P)) :
      selectedRealEquiv4 P hP L hL c ((baseRealBasis4 P hP).equivFun x) k =
        (L *ᵥ (x : Fin 4 → ℝ)) (realSelection4 P hP L hL c k) :=
    congrFun (rowCoordinates4_mulVec_basis (rationalRealSpan4 P) (baseRealBasis4 P hP) L x)
      (realSelection4 P hP L hL c k)
  ext x
  simp only [relaxedBody4,Set.mem_setOf_eq,Set.mem_preimage,weightedBox4,Set.mem_pi,
    Set.mem_univ,forall_const,Set.mem_Icc,heval,abs_le]

theorem source_relaxed_body_geometry4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ) :
    IsCompact (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    Convex ℝ (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    (0 : rationalRealSpan4 P) ∈ interior (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    0 < (restrictedMeasure4 P).real (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    (restrictedMeasure4 P) (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) < ⊤ := by
  let r := fun k => Q^(c (realSelection4 P hP L hL c k))
  let e := selectedRealEquiv4 P hP L hL c
  let b := baseRealBasis4 P hP
  obtain ⟨hbox,hconvex⟩ := weightedBox4_compact_convex r e
  have hcompact : IsCompact (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) := by
    rw [relaxedBody4_coordinates]
    have hh : IsCompact (b.equivFun.symm '' (e ⁻¹' weightedBox4 r)) :=
      hbox.image b.equivFunL.symm.continuous
    simpa only [LinearEquiv.image_eq_preimage,LinearEquiv.symm_symm] using hh
  have hconv : Convex ℝ (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) := by
    rw [relaxedBody4_coordinates]
    exact hconvex.linear_preimage b.equivFun.toLinearMap
  have hi : (0 : rationalRealSpan4 P) ∈ interior (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) :=
    interior_mono (restrictedBody4_subset_relaxed P L Q c _) (restrictedBody4_zero_interior P L (sourceUnit42 L hL) Q hQ c)
  have hfinite := hcompact.measure_lt_top (μ := restrictedMeasure4 P)
  have hpos := Measure.measure_pos_of_nonempty_interior (restrictedMeasure4 P) ⟨0,hi⟩
  exact ⟨hcompact,hconv,hi,ENNReal.toReal_pos hpos.ne' hfinite.ne,hfinite⟩

theorem source_uniform_real_volume4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q →
      (restrictedMeasure4 P).real (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) =
      K * Q^(∑ k, c (realSelection4 P hP L hL c k)) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let b₀ := baseIntegerBasis4 P hP
  let b := baseRealBasis4 P hP
  let M := realSelectedMatrix4 P hP L hL c
  let e := selectedRealEquiv4 P hP L hL c
  let s := realSelection4 P hP L hL c
  let C₀ := ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P)
  let K := C₀ * (2 : ℝ)^(Module.finrank ℚ P) / |M.det|
  have hC₀ : 0 < C₀ := ZLattice.covolume_pos _ _
  have hM : 0 < |M.det| := abs_pos.mpr (realSelectedMatrix4_det_ne_zero P hP L hL c)
  have hK : 0 < K := div_pos (mul_pos hC₀ (by positivity)) hM
  refine ⟨K,hK,?_⟩
  intro Q hQ
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  let r := fun k => Q^(c (s k))
  have hc := (source_relaxed_body_geometry4 P hP L hL Q hQ c).1
  have himage : b.equivFun '' relaxedBody4 P L Q c s = e ⁻¹' weightedBox4 r := by
    rw [relaxedBody4_coordinates,Set.image_preimage_eq _ b.equivFun.surjective]
  have hratio := restrictedBasis4_volume_ratio (P := P) (A₂ := 0) (A₃ := 0) (Q := 2)
    (c₂ := fun _ => 0) (c₃ := fun _ => 0) b₀ (relaxedBody4 P L Q c s) hc
  change volume.real (b.equivFun '' relaxedBody4 P L Q c s) =
    (restrictedMeasure4 P).real (relaxedBody4 P L Q c s) / C₀ at hratio
  have hdet : LinearMap.det e.toLinearMap = M.det := LinearMap.det_toLin' M
  rw [himage,weightedBox4_volume r (fun k => Real.rpow_pos_of_pos hQpos _) e,hdet] at hratio
  have hprod : (∏ k, r k) = Q^(∑ k, c (s k)) := by
    dsimp [r]
    rw [← Real.rpow_sum_of_pos hQpos _ Finset.univ]
  rw [hprod] at hratio
  calc
    _ = ((2 : ℝ)^(Module.finrank ℚ P) * Q^(∑ k, c (s k)) / |M.det|) * C₀ :=
      ((eq_div_iff hC₀.ne').mp hratio).symm
    _ = _ := by dsimp [K];ring

end
end CompoundFeasibility.RestrictedRealBody4
