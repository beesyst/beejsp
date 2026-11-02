import SubspaceBridge.RestrictedVolume5
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry5

theorem crosspolytope_coordinate_volume5 (d : Fin 5) (hd : 0 < d.val) :
    volume {x : Fin d.val → ℝ | ∑ i, |x i| ≤ 1} =
      ENNReal.ofReal ((2 : ℝ)^d.val / (Nat.factorial d.val : ℝ)) := by
  letI : Nonempty (Fin d.val) := ⟨⟨0,hd⟩⟩
  have h := MeasureTheory.volume_sum_rpow_le (Fin d.val) (p := (1 : ℝ)) (by norm_num) 1
  simpa [Real.rpow_one,Real.Gamma_nat_eq_factorial,Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0),Real.Gamma_one] using h

theorem restrictedFrame5_det_lower {P : Submodule ℚ (Fin 5 → ℚ)}
    {A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ} {Q : ℝ} {c₂ c₃ : Fin 5 → ℝ} {d : ℕ}
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan5 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃) :
    1 ≤ |(Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det| := by
  classical
  let b := c.ofZLatticeBasis ℝ (restrictedLattice5 P A₂ A₃ Q c₂ c₃)
  let z : Matrix (Fin d) (Fin d) ℤ := fun i j => c.repr ⟨v i,hvL i⟩ j
  have hz : Matrix.of (fun i => b.equivFun (v i)) = z.map (Int.castRingHom ℝ) := by
    ext i j
    exact Basis.ofZLatticeBasis_repr_apply ℝ _ c ⟨v i,hvL i⟩ j
  have hind : LinearIndependent ℝ (fun i => b.equivFun (v i)) :=
    hv.map' b.equivFun.toLinearMap b.equivFun.ker
  let a := basisOfPiSpaceOfLinearIndependent hind
  have hne : (Matrix.of (fun i => b.equivFun (v i))).det ≠ 0 := by
    rw [← Pi.basisFun_det_apply]
    have ha : (fun i => b.equivFun (v i)) = (a : Fin d → Fin d → ℝ) :=
      (coe_basisOfPiSpaceOfLinearIndependent hind).symm
    rw [ha]
    exact isUnit_iff_ne_zero.mp ((Pi.basisFun ℝ (Fin d)).isUnit_det a)
  have hcast : (Matrix.of (fun i => b.equivFun (v i))).det = (z.det : ℝ) := by
    rw [hz]
    exact ((Int.castRingHom ℝ).map_det z).symm
  have hzne : z.det ≠ 0 := by
    intro h
    apply hne
    rw [hcast,h,Int.cast_zero]
  have hz1 : (1 : ℤ) ≤ |z.det| := by
    have hp : (0 : ℤ) < |z.det| := abs_pos.mpr hzne
    omega
  change 1 ≤ |(Matrix.of (fun i => b.equivFun (v i))).det|
  rw [hcast]
  exact_mod_cast hz1


variable {P : Submodule ℚ (Fin 5 → ℚ)}
variable {A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ} {Q : ℝ} {c₂ c₃ : Fin 5 → ℝ} {d : ℕ}

def restrictedCrosspolytopeMap5
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan5 P) (mu : Fin d → ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  (Pi.basisFun ℝ (Fin d)).constr ℕ
    (fun i => (mu i)⁻¹ • (c.ofZLatticeBasis ℝ _).equivFun (v i))

theorem restrictedCrosspolytopeMap5_det
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan5 P) (mu : Fin d → ℝ) :
    LinearMap.det (restrictedCrosspolytopeMap5 c v mu) =
      (∏ i, (mu i)⁻¹) * (Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det := by
  rw [restrictedCrosspolytopeMap5,← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin d)),
    ← Basis.toMatrix_eq_toMatrix_constr,← Basis.det_apply,Pi.basisFun_det_apply]
  exact Matrix.det_mul_column (fun i => (mu i)⁻¹) _

theorem restrictedCrosspolytopeMap5_pullback
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan5 P) (mu : Fin d → ℝ) (x : Fin d → ℝ) :
    (c.ofZLatticeBasis ℝ _).equivFun.symm (restrictedCrosspolytopeMap5 c v mu x) =
      ∑ i, (x i / mu i) • v i := by
  simp only [restrictedCrosspolytopeMap5,Basis.constr_apply_fintype,
    map_sum,map_smul,LinearEquiv.symm_apply_apply,smul_smul]
  rfl


theorem restrictedCrosspolytope5_subset
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ)
    (c : Basis (Fin d) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan5 P) (mu : Fin d → ℝ) (hpos : ∀ i, 0 < mu i)
    (hatt : ∀ i, restrictedGauge5 P L hL Q hQ c₀ (v i) = mu i) :
    restrictedCrosspolytopeMap5 c v mu '' {x | ∑ i, |x i| ≤ 1} ⊆
      (c.ofZLatticeBasis ℝ _).equivFun '' restrictedBody5 P L Q c₀ := by
  rintro _ ⟨x,hx,rfl⟩
  rw [LinearEquiv.image_eq_preimage]
  change (c.ofZLatticeBasis ℝ _).equivFun.symm (restrictedCrosspolytopeMap5 c v mu x) ∈
    restrictedBody5 P L Q c₀
  rw [restrictedCrosspolytopeMap5_pullback,restrictedBody5_gauge P L hL Q hQ c₀]
  change ‖originalCoordinates5 L hL Q hQ c₀
    ((∑ i, (x i / mu i) • v i : rationalRealSpan5 P) : Fin 5 → ℝ)‖ ≤ 1
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  calc
    _ ≤ ∑ i, ‖(x i / mu i) • originalCoordinates5 L hL Q hQ c₀ (v i : Fin 5 → ℝ)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      change |x i / mu i| * restrictedGauge5 P L hL Q hQ c₀ (v i) = |x i|
      rw [hatt,abs_div,abs_of_pos (hpos i),div_mul_cancel₀ _ (hpos i).ne']
    _ ≤ 1 := hx


theorem restrictedCrosspolytope5_volume (dim : Fin 5) (hdim : 0 < dim.val)
    (c : Basis (Fin dim.val) ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃))
    (v : Fin dim.val → rationalRealSpan5 P) (mu : Fin dim.val → ℝ) (hpos : ∀ i, 0 < mu i) :
    volume.real (restrictedCrosspolytopeMap5 c v mu '' {x | ∑ i, |x i| ≤ 1}) =
      ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det| / (∏ i, mu i) := by
  rw [measureReal_def,Measure.addHaar_image_linearMap,
    crosspolytope_coordinate_volume5 dim hdim,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _),ENNReal.toReal_ofReal (by positivity),
    restrictedCrosspolytopeMap5_det,abs_mul,Finset.prod_inv_distrib,
    abs_of_pos (inv_pos.mpr (Finset.prod_pos (fun i _ => hpos i)))]
  ring


theorem source_restricted_minkowski_lower5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hPlo : 1 ≤ Module.finrank ℚ P) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) :
    (2 : ℝ)^(Module.finrank ℚ P) / (Nat.factorial (Module.finrank ℚ P) : ℝ) ≤
      (∏ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
          ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) := by
  obtain ⟨v,hv,hvL,hpos,_,hatt,_⟩ := exists_restrictedMinima5_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let dim : Fin 5 := ⟨Module.finrank ℚ P,by omega⟩
  let G := restrictedLattice5 P A₂ A₃ Q c₂ c₃
  let c : Basis (Fin dim.val) ℤ G :=
    Module.finBasisOfFinrankEq ℤ G (restrictedLattice5_rank P hP A₂ A₃ Q c₂ c₃)
  let mu := restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let b := c.ofZLatticeBasis ℝ G
  let T := restrictedCrosspolytopeMap5 c v mu
  have hinc := restrictedCrosspolytope5_subset L hL hQ c₀ c v mu hpos hatt
  have hcpt : IsCompact (b.equivFun '' restrictedBody5 P L Q c₀) :=
    (restrictedBody5_compact_convex P L hL Q hQ c₀).1.image b.equivFunL.continuous
  have hm : volume.real (T '' {x | ∑ i, |x i| ≤ 1}) ≤
      volume.real (b.equivFun '' restrictedBody5 P L Q c₀) :=
    ENNReal.toReal_mono hcpt.measure_lt_top.ne (measure_mono hinc)
  have hvol := restrictedCrosspolytope5_volume dim (by change 0 < Module.finrank ℚ P; omega)
    c v mu hpos
  have hbody := restrictedBasis5_volume_ratio c (restrictedBody5 P L Q c₀)
    (restrictedBody5_compact_convex P L hL Q hQ c₀).1
  change volume.real (restrictedCrosspolytopeMap5 c v mu '' {x | ∑ i, |x i| ≤ 1}) ≤ _ at hm
  rw [hvol,hbody] at hm
  have hprod : 0 < ∏ i, mu i := Finset.prod_pos (fun i _ => hpos i)
  have hdet := restrictedFrame5_det_lower c v hv hvL
  have hconst : 0 ≤ (2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ) := by positivity
  have hlow : (2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ) ≤
      ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => b.equivFun (v i))).det| := by
    exact le_mul_of_one_le_right hconst hdet
  have hcancel := (div_le_iff₀ hprod).mp hm
  calc
    _ ≤ ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => b.equivFun (v i))).det| := hlow
    _ ≤ ((restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
        ZLattice.covolume G (restrictedMeasure5 P)) * (∏ i, mu i) := hcancel
    _ = _ := by ring


end CompoundFeasibility.RestrictedGeometry5
