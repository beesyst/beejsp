import SubspaceBridge.SelectedBoxVolume5
import SubspaceBridge.RestrictedSelectedBasis5
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility.RestrictedRealBody5
open RestrictedGeometry5 RestrictedRelaxed5 RestrictedIntegerCoordinates5 RestrictedRows5
open RestrictedWeightOrder5 SelectedRestriction5 RestrictedSelectedBasis5 SelectedBoxVolume5
noncomputable section

def baseRealBasis5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan5 P) := by
  letI : DiscreteTopology (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  letI : IsZLattice ℝ (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  exact (baseIntegerBasis5 P hP).ofZLatticeBasis ℝ (baseLattice5 P)

def realSelection5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (c : Fin 5 → ℝ) : Fin (Module.finrank ℚ P) → Fin 5 :=
  fun k => weightOrder5 c (selectedIndex5 (realRestrictionCoordinates5 P hP L) c
    (realRestrictionCoordinates5_span P hP L hL) k)

def realSelectedMatrix5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (c : Fin 5 → ℝ) :
    Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℝ :=
  fun k => rowCoordinates5 (rationalRealSpan5 P) (baseRealBasis5 P hP) L (realSelection5 P hP L hL c k)

theorem realSelectedMatrix5_det_ne_zero (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (c : Fin 5 → ℝ) :
    (realSelectedMatrix5 P hP L hL c).det ≠ 0 :=
  selected_basis_matrix_det5 (rationalRealSpan5 P) (realRestrictionBasis5 P hP) (baseRealBasis5 P hP)
    L c (realRestrictionCoordinates5_span P hP L hL)

def selectedRealEquiv5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (c : Fin 5 → ℝ) :
    (Fin (Module.finrank ℚ P) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℚ P) → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (realSelectedMatrix5 P hP L hL c)) (by
    have hu : IsUnit (realSelectedMatrix5 P hP L hL c) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realSelectedMatrix5_det_ne_zero P hP L hL c))
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem rowCoordinates5_mulVec_basis {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 5 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 5) (Fin 5) K) (x : P) :
    rowCoordinates5 P b A *ᵥ b.equivFun x = A *ᵥ (x : Fin 5 → K) := by
  ext i
  let f : P →ₗ[K] K := (LinearMap.proj i).comp ((Matrix.toLin' A).comp P.subtype)
  have h := congrArg f (b.sum_repr x)
  change ∑ k, f (b k) * b.repr x k = f x
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using h

theorem relaxedBody5_coordinates (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (Q : ℝ) (c : Fin 5 → ℝ) :
    relaxedBody5 P L Q c (realSelection5 P hP L hL c) =
      (baseRealBasis5 P hP).equivFun ⁻¹' ((selectedRealEquiv5 P hP L hL c) ⁻¹'
        weightedBox5 (fun k => Q^(c (realSelection5 P hP L hL c k)))) := by
  have heval (x : rationalRealSpan5 P) (k : Fin (Module.finrank ℚ P)) :
      selectedRealEquiv5 P hP L hL c ((baseRealBasis5 P hP).equivFun x) k =
        (L *ᵥ (x : Fin 5 → ℝ)) (realSelection5 P hP L hL c k) :=
    congrFun (rowCoordinates5_mulVec_basis (rationalRealSpan5 P) (baseRealBasis5 P hP) L x)
      (realSelection5 P hP L hL c k)
  ext x
  simp only [relaxedBody5,Set.mem_setOf_eq,Set.mem_preimage,weightedBox5,Set.mem_pi,
    Set.mem_univ,forall_const,Set.mem_Icc,heval,abs_le]

theorem source_relaxed_body_geometry5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) :
    IsCompact (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) ∧
    Convex ℝ (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) ∧
    (0 : rationalRealSpan5 P) ∈ interior (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) ∧
    0 < (restrictedMeasure5 P).real (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) ∧
    (restrictedMeasure5 P) (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) < ⊤ := by
  let r := fun k => Q^(c (realSelection5 P hP L hL c k))
  let e := selectedRealEquiv5 P hP L hL c
  let b := baseRealBasis5 P hP
  obtain ⟨hbox,hconvex⟩ := weightedBox5_compact_convex r e
  have hcompact : IsCompact (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) := by
    rw [relaxedBody5_coordinates]
    have hh : IsCompact (b.equivFun.symm '' (e ⁻¹' weightedBox5 r)) :=
      hbox.image b.equivFunL.symm.continuous
    simpa only [LinearEquiv.image_eq_preimage,LinearEquiv.symm_symm] using hh
  have hconv : Convex ℝ (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) := by
    rw [relaxedBody5_coordinates]
    exact hconvex.linear_preimage b.equivFun.toLinearMap
  have hi : (0 : rationalRealSpan5 P) ∈ interior (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) :=
    interior_mono (restrictedBody5_subset_relaxed P L Q c _) (restrictedBody5_zero_interior P L ((Matrix.isUnit_iff_isUnit_det L).mpr (hL ▸ isUnit_one)) Q hQ c)
  have hfinite := hcompact.measure_lt_top (μ := restrictedMeasure5 P)
  have hpos := Measure.measure_pos_of_nonempty_interior (restrictedMeasure5 P) ⟨0,hi⟩
  exact ⟨hcompact,hconv,hi,ENNReal.toReal_pos hpos.ne' hfinite.ne,hfinite⟩

theorem source_uniform_real_volume5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (c : Fin 5 → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q →
      (restrictedMeasure5 P).real (relaxedBody5 P L Q c (realSelection5 P hP L hL c)) =
      K * Q^(∑ k, c (realSelection5 P hP L hL c k)) := by
  letI : DiscreteTopology (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  letI : IsZLattice ℝ (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  let b₀ := baseIntegerBasis5 P hP
  let b := baseRealBasis5 P hP
  let M := realSelectedMatrix5 P hP L hL c
  let e := selectedRealEquiv5 P hP L hL c
  let s := realSelection5 P hP L hL c
  let C₀ := ZLattice.covolume (baseLattice5 P) (restrictedMeasure5 P)
  let K := C₀ * (2 : ℝ)^(Module.finrank ℚ P) / |M.det|
  have hC₀ : 0 < C₀ := ZLattice.covolume_pos _ _
  have hM : 0 < |M.det| := abs_pos.mpr (realSelectedMatrix5_det_ne_zero P hP L hL c)
  have hK : 0 < K := div_pos (mul_pos hC₀ (by positivity)) hM
  refine ⟨K,hK,?_⟩
  intro Q hQ
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  let r := fun k => Q^(c (s k))
  have hc := (source_relaxed_body_geometry5 P hP L hL Q hQ c).1
  have himage : b.equivFun '' relaxedBody5 P L Q c s = e ⁻¹' weightedBox5 r := by
    rw [relaxedBody5_coordinates,Set.image_preimage_eq _ b.equivFun.surjective]
  have hratio := restrictedBasis5_volume_ratio (P := P) (A₂ := 0) (A₃ := 0) (Q := 2)
    (c₂ := fun _ => 0) (c₃ := fun _ => 0) b₀ (relaxedBody5 P L Q c s) hc
  change volume.real (b.equivFun '' relaxedBody5 P L Q c s) =
    (restrictedMeasure5 P).real (relaxedBody5 P L Q c s) / C₀ at hratio
  have hdet : LinearMap.det e.toLinearMap = M.det := LinearMap.det_toLin' M
  rw [himage,weightedBox5_volume r (fun k => Real.rpow_pos_of_pos hQpos _) e,hdet] at hratio
  have hprod : (∏ k, r k) = Q^(∑ k, c (s k)) := by
    dsimp [r]
    rw [← Real.rpow_sum_of_pos hQpos _ Finset.univ]
  rw [hprod] at hratio
  calc
    _ = ((2 : ℝ)^(Module.finrank ℚ P) * Q^(∑ k, c (s k)) / |M.det|) * C₀ :=
      ((eq_div_iff hC₀.ne').mp hratio).symm
    _ = _ := by dsimp [K];ring

end
end CompoundFeasibility.RestrictedRealBody5
