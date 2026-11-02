import SubspaceBridge.RestrictedCoordinates4
import SubspaceBridge.RestrictedVolume4
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry4

theorem crosspolytope_coordinate_volume4 (d : Fin 4) (hd : 0 < d.val) :
    volume {x : Fin d.val → ℝ | ∑ i, |x i| ≤ 1} =
      ENNReal.ofReal ((2 : ℝ)^d.val / (Nat.factorial d.val : ℝ)) := by
  letI : Nonempty (Fin d.val) := ⟨⟨0,hd⟩⟩
  have h := MeasureTheory.volume_sum_rpow_le (Fin d.val) (p := (1 : ℝ)) (by norm_num) 1
  simpa [Real.rpow_one,Real.Gamma_nat_eq_factorial,Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0),Real.Gamma_one] using h

theorem restrictedFrame4_det_lower {P : Submodule ℚ (Fin 4 → ℚ)}
    {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {Q : ℝ} {c₂ c₃ : Fin 4 → ℝ} {d : ℕ}
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
    1 ≤ |(Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det| := by
  classical
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
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


variable {P : Submodule ℚ (Fin 4 → ℚ)}
variable {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {Q : ℝ} {c₂ c₃ : Fin 4 → ℝ} {d : ℕ}

def restrictedCrosspolytopeMap4
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  (Pi.basisFun ℝ (Fin d)).constr ℕ
    (fun i => (mu i)⁻¹ • (c.ofZLatticeBasis ℝ _).equivFun (v i))

theorem restrictedCrosspolytopeMap4_det
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) :
    LinearMap.det (restrictedCrosspolytopeMap4 c v mu) =
      (∏ i, (mu i)⁻¹) * (Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det := by
  rw [restrictedCrosspolytopeMap4,← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin d)),
    ← Basis.toMatrix_eq_toMatrix_constr,← Basis.det_apply,Pi.basisFun_det_apply]
  exact Matrix.det_mul_column (fun i => (mu i)⁻¹) _

theorem restrictedCrosspolytopeMap4_pullback
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) (x : Fin d → ℝ) :
    (c.ofZLatticeBasis ℝ _).equivFun.symm (restrictedCrosspolytopeMap4 c v mu x) =
      ∑ i, (x i / mu i) • v i := by
  simp only [restrictedCrosspolytopeMap4,Basis.constr_apply_fintype,
    map_sum,map_smul,LinearEquiv.symm_apply_apply,smul_smul]
  rfl


theorem restrictedCrosspolytope4_subset
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ)
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) (hpos : ∀ i, 0 < mu i)
    (hatt : ∀ i, restrictedGauge4 P L hL Q hQ c₀ (v i) = mu i) :
    restrictedCrosspolytopeMap4 c v mu '' {x | ∑ i, |x i| ≤ 1} ⊆
      (c.ofZLatticeBasis ℝ _).equivFun '' restrictedBody4 P L Q c₀ := by
  rintro _ ⟨x,hx,rfl⟩
  rw [LinearEquiv.image_eq_preimage]
  change (c.ofZLatticeBasis ℝ _).equivFun.symm (restrictedCrosspolytopeMap4 c v mu x) ∈
    restrictedBody4 P L Q c₀
  rw [restrictedCrosspolytopeMap4_pullback,restrictedBody4_gauge P L hL Q hQ c₀]
  change ‖originalCoordinates4 L hL Q hQ c₀
    ((∑ i, (x i / mu i) • v i : rationalRealSpan4 P) : Fin 4 → ℝ)‖ ≤ 1
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  calc
    _ ≤ ∑ i, ‖(x i / mu i) • originalCoordinates4 L hL Q hQ c₀ (v i : Fin 4 → ℝ)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      change |x i / mu i| * restrictedGauge4 P L hL Q hQ c₀ (v i) = |x i|
      rw [hatt,abs_div,abs_of_pos (hpos i),div_mul_cancel₀ _ (hpos i).ne']
    _ ≤ 1 := hx


theorem restrictedCrosspolytope4_volume (dim : Fin 4) (hdim : 0 < dim.val)
    (c : Basis (Fin dim.val) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin dim.val → rationalRealSpan4 P) (mu : Fin dim.val → ℝ) (hpos : ∀ i, 0 < mu i) :
    volume.real (restrictedCrosspolytopeMap4 c v mu '' {x | ∑ i, |x i| ≤ 1}) =
      ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det| / (∏ i, mu i) := by
  rw [measureReal_def,Measure.addHaar_image_linearMap,
    crosspolytope_coordinate_volume4 dim hdim,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _),ENNReal.toReal_ofReal (by positivity),
    restrictedCrosspolytopeMap4_det,abs_mul,Finset.prod_inv_distrib,
    abs_of_pos (inv_pos.mpr (Finset.prod_pos (fun i _ => hpos i)))]
  ring


theorem source_restricted_minkowski_lower4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hPlo : 1 ≤ Module.finrank ℚ P) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (2 : ℝ)^(Module.finrank ℚ P) / (Nat.factorial (Module.finrank ℚ P) : ℝ) ≤
      (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) := by
  obtain ⟨v,hv,hvL,hpos,_,hatt,_⟩ := exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let dim : Fin 4 := ⟨Module.finrank ℚ P,by omega⟩
  let G := restrictedLattice4 P A₂ A₃ Q c₂ c₃
  let c : Basis (Fin dim.val) ℤ G :=
    Module.finBasisOfFinrankEq ℤ G (restrictedLattice4_rank P hP A₂ A₃ Q c₂ c₃)
  let mu := restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let b := c.ofZLatticeBasis ℝ G
  let T := restrictedCrosspolytopeMap4 c v mu
  have hinc := restrictedCrosspolytope4_subset L hL hQ c₀ c v mu hpos hatt
  have hcpt : IsCompact (b.equivFun '' restrictedBody4 P L Q c₀) :=
    (restrictedBody4_compact_convex P L hL Q hQ c₀).1.image b.equivFunL.continuous
  have hm : volume.real (T '' {x | ∑ i, |x i| ≤ 1}) ≤
      volume.real (b.equivFun '' restrictedBody4 P L Q c₀) :=
    ENNReal.toReal_mono hcpt.measure_lt_top.ne (measure_mono hinc)
  have hvol := restrictedCrosspolytope4_volume dim (by change 0 < Module.finrank ℚ P; omega)
    c v mu hpos
  have hbody := restrictedBasis4_volume_ratio c (restrictedBody4 P L Q c₀)
    (restrictedBody4_compact_convex P L hL Q hQ c₀).1
  change volume.real (restrictedCrosspolytopeMap4 c v mu '' {x | ∑ i, |x i| ≤ 1}) ≤ _ at hm
  rw [hvol,hbody] at hm
  have hprod : 0 < ∏ i, mu i := Finset.prod_pos (fun i _ => hpos i)
  have hdet := restrictedFrame4_det_lower c v hv hvL
  have hconst : 0 ≤ (2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ) := by positivity
  have hlow : (2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ) ≤
      ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => b.equivFun (v i))).det| := by
    exact le_mul_of_one_le_right hconst hdet
  have hcancel := (div_le_iff₀ hprod).mp hm
  calc
    _ ≤ ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => b.equivFun (v i))).det| := hlow
    _ ≤ ((restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
        ZLattice.covolume G (restrictedMeasure4 P)) * (∏ i, mu i) := hcancel
    _ = _ := by ring


end CompoundFeasibility.RestrictedGeometry4
