import SubspaceBridge.DualFrame3

open scoped BigOperators
open MeasureTheory
namespace JSP000334

noncomputable def sourceDualRealCoordinates3 (k : Fin 3) : RealTriple ≃ₗ[ℝ] RealTriple :=
  LinearEquiv.ofBijective (Matrix.toLin' (retainedRealMatrix3 k)⁻¹.transpose) (by
    have h : IsUnit (retainedRealMatrix3 k) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [retainedRealMatrix3_det]
      split <;> norm_num
    have ht : IsUnit (retainedRealMatrix3 k)⁻¹.transpose := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact IsUnit.inv ((Matrix.isUnit_iff_isUnit_det _).mp h)
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr ht,
      Matrix.mulVec_surjective_iff_isUnit.mpr ht⟩)

noncomputable def sourceDualBody3 (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ) : Set RealTriple :=
  {x | ∀ i, |∑ j : Fin 3, (retainedRealMatrix3 k)⁻¹ j i * x j| ≤ D / a i}

noncomputable def sourceDualCoordinates3 (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ)
    (hD : 0 < D) (ha : ∀ i, 0 < a i) : RealTriple ≃ₗ[ℝ] RealTriple :=
  archCoordinates3 (sourceDualRealCoordinates3 k) (fun i => D / a i)
    (fun i => div_pos hD (ha i))

theorem sourceDualRealCoordinates3_apply (k : Fin 3) (x : RealTriple) (i : Fin 3) :
    sourceDualRealCoordinates3 k x i =
      ∑ j : Fin 3, (retainedRealMatrix3 k)⁻¹ j i * x j := rfl

theorem sourceDualRealCoordinates3_abs_det (k : Fin 3) :
    |LinearMap.det (sourceDualRealCoordinates3 k).toLinearMap| = 1 := by
  change |LinearMap.det (Matrix.toLin' (retainedRealMatrix3 k)⁻¹.transpose)| = 1
  rw [LinearMap.det_toLin', Matrix.det_transpose, Matrix.det_nonsing_inv,
    retainedRealMatrix3_det]
  split <;> norm_num

theorem sourceDualBody3_eq_parallelepiped (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ)
    (hD : 0 < D) (ha : ∀ i, 0 < a i) :
    sourceDualBody3 k D a = parallelepipedBody3 (sourceDualCoordinates3 k D a hD ha) := by
  exact archBody3_eq_parallelepiped (sourceDualRealCoordinates3 k)
    (fun i => D / a i) (fun i => div_pos hD (ha i))

theorem sourceDualBody3_volume (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ)
    (hD : 0 < D) (ha : ∀ i, 0 < a i) :
    volume.real (sourceDualBody3 k D a) = 8 * D ^ 3 / ∏ i, a i := by
  change volume.real (archBody3 (sourceDualRealCoordinates3 k) (fun i => D / a i)) = _
  rw [archBody3_volume _ _ (fun i => div_pos hD (ha i)),
    sourceDualRealCoordinates3_abs_det, div_one, Finset.prod_div_distrib]
  simp [Fin.prod_univ_succ, div_eq_mul_inv, pow_succ, mul_assoc]

def rationalTripleReal3 : (Fin 3 → ℚ) →ₗ[ℤ] RealTriple where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp [Int.cast_mul]

theorem dualFrameVector3_real_independent (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℝ (fun j => integerTripleReal3 (w j))) :
    LinearIndependent ℝ (fun j => rationalTripleReal3 (dualFrameVector3 w j)) := by
  have h : IsUnit (dualFrameRealMatrix3 w) := Matrix.linearIndependent_rows_iff_isUnit.mp hw
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_nonsing_inv_iff.mpr h)
  have he : (fun j => rationalTripleReal3 (dualFrameVector3 w j)) =
      (fun j i => (dualFrameRealMatrix3 w)⁻¹ i j) := by
    ext j i
    exact (dualFrameVector3_real_inverse w hw i j).symm
  rw [he]
  exact Matrix.linearIndependent_cols_of_det_ne_zero (isUnit_iff_ne_zero.mp hd)

theorem sourceDualBasis3_independent (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) :
    LinearIndependent ℝ (fun j => rationalTripleReal3
      (fun i => (G.index : ℚ) * dualFrameVector3 (fun k => (c k : IntegerTriple)) j i)) := by
  have h := (dualFrameVector3_real_independent _ hc).units_smul
    (fun _ => Units.mk0 (G.index : ℝ) (by exact_mod_cast hD))
  change LinearIndependent ℝ (fun j => (G.index : ℝ) •
    rationalTripleReal3 (dualFrameVector3 (fun k => (c k : IntegerTriple)) j)) at h
  simpa only [rationalTripleReal3, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_natCast] using h

noncomputable def sourceDualBasis3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) : Basis (Fin 3) ℝ RealTriple := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (sourceDualBasis3_independent G c hc hD)

theorem sourceDualBasis3_apply (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (j : Fin 3) :
    sourceDualBasis3 G c hc hD j = rationalTripleReal3
      (fun i => (G.index : ℚ) * dualFrameVector3 (fun k => (c k : IntegerTriple)) j i) :=
  congrFun (coe_basisOfPiSpaceOfLinearIndependent (sourceDualBasis3_independent G c hc hD)) j

theorem sourceDualBasis3_lattice (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) :
    lattice3 (sourceDualBasis3 G c hc hD) =
      (dualFrameSourceBasisLattice3 G c).map rationalTripleReal3 := by
  simp only [dualFrameSourceBasisLattice3, Submodule.map_span, lattice3,
    ← Set.range_comp', ← sourceDualBasis3_apply G c hc hD]

theorem successiveRadius3_monotone (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) : Monotone (successiveRadius3 b e) := by
  obtain ⟨_, _, _, _, h, _⟩ := exists_successive_minima3 b e
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  fin_cases i
  · exact h.1
  · exact h.2

theorem successiveRadius3_reverse_family (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (s : Fin 3 → ℝ)
    (hs : ∀ j, 0 < s j) (hm : Monotone s) (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (hL : ∀ j, v j ∈ lattice3 b)
    (hr : ∀ j, coordinateGauge3 e (v j) ≤ 6 / s j) (k : Fin 3) :
    successiveRadius3 b e k ≤ 6 / s k.rev := by
  let f : Fin (k.val + 1) → Fin 3 := fun i => (Fin.castLE (by omega) i).rev
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 3 - (i.val + 1) = 3 - (j.val + 1) at hv
    omega
  apply successiveRadius3_le_family b e k (v ∘ f) (hv.comp f hf)
    (fun i => hL (f i))
  intro i
  apply (hr (f i)).trans
  have hi : k.rev ≤ f i := by
    change 3 - (k.val + 1) ≤ 3 - (i.val + 1)
    omega
  exact div_le_div_of_nonneg_left (by norm_num) (hs _) (hm hi)

theorem sourceDual_frame_gauge_bound3 (k : Fin 3) (D t s : ℝ)
    (a : Fin 3 → ℝ) (hD : 0 < D) (ha : ∀ i, 0 < a i)
    (w : Fin 3 → IntegerTriple) (j : Fin 3)
    (h : ∀ i, |t * dualFrameRealLocalValue3 (retainedRealMatrix3 k) w j i| ≤
      6 * D * (a i)⁻¹ * s⁻¹) :
    coordinateGauge3 (sourceDualCoordinates3 k D a hD ha)
      (fun i => t * (dualFrameVector3 w j i : ℝ)) ≤ 6 * s⁻¹ := by
  change ‖sourceDualCoordinates3 k D a hD ha _‖ ≤ _
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  change |(∑ l : Fin 3, (retainedRealMatrix3 k)⁻¹ l i *
    (t * (dualFrameVector3 w j l : ℝ))) / (D / a i)| ≤ _
  have he : (∑ l : Fin 3, (retainedRealMatrix3 k)⁻¹ l i *
      (t * (dualFrameVector3 w j l : ℝ))) =
      t * dualFrameRealLocalValue3 (retainedRealMatrix3 k) w j i := by
    simp only [zero_add, dualFrameRealLocalValue3, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, abs_div, abs_of_pos (div_pos hD (ha i)), div_le_iff₀ (div_pos hD (ha i))]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h i

theorem dualFrameRelativeIndex3_pos (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple))) :
    0 < dualFrameRelativeIndex3 G u := by
  have hW : (dualFrameRealMatrix3 (fun j => (u j : IntegerTriple))).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hu))
  have hZ : (dualFrameIntegerMatrix3 (fun j => (u j : IntegerTriple))).det ≠ 0 := by
    intro hz
    apply hW
    rw [show (dualFrameRealMatrix3 (fun j => (u j : IntegerTriple))).det =
      ((dualFrameIntegerMatrix3 (fun j => (u j : IntegerTriple))).det : ℝ) from
      ((Int.castRingHom ℝ).map_det _).symm, hz, Int.cast_zero]
  have hJD : dualFrameRelativeIndex3 G u * G.index ≠ 0 := by
    rw [dualFrameRelativeIndex3_mul_index G c u hu]
    exact Int.natAbs_ne_zero.mpr hZ
  exact Nat.pos_of_ne_zero (left_ne_zero_of_mul hJD)

theorem sourceDual_minima_upper3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (B : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hpoint : ∀ j i, |∑ l : Fin 3, retainedRealMatrix3 k i l *
      ((u j : IntegerTriple) l : ℝ)| ≤ successiveRadius3 B e j * a i)
    (hprod : (∏ j, successiveRadius3 B e j) * (∏ i, a i) ≤ (G.index : ℝ))
    (i : Fin 3) :
    successiveRadius3 (sourceDualBasis3 G c hc hD)
      (sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) i ≤
      6 / successiveRadius3 B e i.rev := by
  let w := fun j => (u j : IntegerTriple)
  let t : ℝ := ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℝ)
  let v : Fin 3 → RealTriple := fun j l => t * (dualFrameVector3 w j l : ℝ)
  have ht : t ≠ 0 := by
    dsimp [t]
    exact_mod_cast mul_ne_zero (Nat.ne_of_gt (dualFrameRelativeIndex3_pos G c u hu)) hD
  have hv := (dualFrameVector3_real_independent w hu).units_smul (fun _ => Units.mk0 t ht)
  change LinearIndependent ℝ (fun j => t • rationalTripleReal3 (dualFrameVector3 w j)) at hv
  have hv' : LinearIndependent ℝ v := hv
  have hL : ∀ j, v j ∈ lattice3 (sourceDualBasis3 G c hc hD) := by
    intro j
    rw [sourceDualBasis3_lattice]
    refine ⟨_, dualFrameVector3_source_basis_mem G c
      (dualFrameMatrix3_rational_independent _ hc) u
      (dualFrameMatrix3_rational_independent _ hu) j, ?_⟩
    ext l
    simp [v, t, w, rationalTripleReal3]
  obtain ⟨_, _, _, hs, _, _⟩ := exists_successive_minima3 B e
  apply successiveRadius3_reverse_family _ _ _ hs (successiveRadius3_monotone B e) v hv' hL
  intro j
  rw [div_eq_mul_inv]
  apply sourceDual_frame_gauge_bound3 k G.index t (successiveRadius3 B e j) a _ ha w j
  intro l
  exact dualFrame3_source_real_bound G c u hu (retainedRealMatrix3 k)
    (by rw [retainedRealMatrix3_det]; split_ifs <;> norm_num)
    _ a hs ha hpoint hprod l j

theorem sourceBasis3_abs_det (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G) :
    |(dualFrameRealMatrix3 (fun j => (c j : IntegerTriple))).det| = (G.index : ℝ) := by
  have hi := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 3)) G c
  have hm : (Pi.basisFun ℤ (Fin 3)).toMatrix (fun j => (c j : IntegerTriple)) =
      (dualFrameIntegerMatrix3 (fun j => (c j : IntegerTriple))).transpose := by
    ext i j
    rfl
  rw [Basis.det_apply, hm, Matrix.det_transpose] at hi
  rw [show (dualFrameRealMatrix3 (fun j => (c j : IntegerTriple))).det =
    ((dualFrameIntegerMatrix3 (fun j => (c j : IntegerTriple))).det : ℝ) from
    ((Int.castRingHom ℝ).map_det _).symm]
  have hh := congrArg (fun n : ℕ => (n : ℝ)) hi
  simpa only [Int.cast_natAbs, Int.cast_abs] using hh.symm

theorem sourceDualBasis3_covolume (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) :
    ZLattice.covolume (lattice3 (sourceDualBasis3 G c hc hD)) = (G.index : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hm : columnMatrix3 (sourceDualBasis3 G c hc hD) =
      (G.index : ℝ) • (dualFrameRealMatrix3 (fun j => (c j : IntegerTriple)))⁻¹ := by
    ext i j
    simp only [columnMatrix3, sourceDualBasis3_apply, rationalTripleReal3,
      LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_mul, Rat.cast_natCast,
      Matrix.smul_apply, smul_eq_mul, dualFrameVector3_real_inverse _ hc]
  rw [lattice3_covolume, hm, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_mul, abs_pow,
    abs_of_pos hp, abs_inv, sourceBasis3_abs_det]
  field_simp
  ring

theorem sourceDual_minima_product_lower3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ i, a i) / (6 * (G.index : ℝ)) ≤
      ∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
        (sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) j := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hP : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have h := successive_minima3_parallelepiped_volume_lower (sourceDualBasis3 G c hc hD)
    (sourceDualCoordinates3 k G.index a hp ha)
  rw [sourceDualBasis3_covolume,
    ← sourceDualBody3_eq_parallelepiped k G.index a hp ha,
    sourceDualBody3_volume k G.index a hp ha] at h
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  have hh := (le_div_iff₀ hP).mp (show (8 / 6 : ℝ) * (G.index : ℝ) ^ 2 ≤
    (∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (sourceDualCoordinates3 k G.index a hp ha) j) * (8 * (G.index : ℝ) ^ 3) / (∏ i, a i) by
        simpa [mul_div_assoc] using h)
  nlinarith [sq_pos_of_pos hp]

theorem source_minima_product_lower3 (B : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (D P : ℝ) (hP : 0 < P)
    (hvol : volume.real (parallelepipedBody3 e) = 8 * P)
    (hcov : ZLattice.covolume (lattice3 B) = D) :
    D / (6 * P) ≤ ∏ j, successiveRadius3 B e j := by
  have h := successive_minima3_parallelepiped_volume_lower B e
  rw [hvol, hcov] at h
  apply (div_le_iff₀ (mul_pos (by norm_num) hP)).mpr
  linarith

theorem ternary_transference_product_lower3 (s t : Fin 3 → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hu : ∀ i, t i * s i.rev ≤ 6)
    (hp : (1 : ℝ) / 36 ≤ (∏ i, s i) * (∏ i, t i)) (k : Fin 3) :
    (1 : ℝ) / 1296 ≤ t k * s k.rev := by
  classical
  let a : Fin 3 → ℝ := fun i => t i * s i.rev
  have ha : ∀ i, 0 < a i := fun i => mul_pos (ht i) (hs _)
  have hprod : (∏ i, a i) = (∏ i, s i) * (∏ i, t i) := by
    simp [a, Fin.prod_univ_succ, Fin.rev]
    ring
  have hc : (Finset.univ.erase k : Finset (Fin 3)).card = 2 := by simp
  have hother : (∏ i ∈ Finset.univ.erase k, a i) ≤ 36 := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.erase k, (6 : ℝ) :=
        Finset.prod_le_prod (fun i _ => (ha i).le) (fun i _ => hu i)
      _ = 36 := by norm_num [Finset.prod_const, hc]
  have hmul := mul_le_mul_of_nonneg_left hother (ha k).le
  have he := Finset.mul_prod_erase Finset.univ a (Finset.mem_univ k)
  rw [he, hprod] at hmul
  change (1 : ℝ) / 1296 ≤ a k
  linarith

theorem sourceDual_minima_product_upper3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) j) ≤
        (∏ i, a i) / (G.index : ℝ) := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hP : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have h := successive_minima3_parallelepiped_volume_upper (sourceDualBasis3 G c hc hD)
    (sourceDualCoordinates3 k G.index a hp ha)
  rw [sourceDualBasis3_covolume,
    ← sourceDualBody3_eq_parallelepiped k G.index a hp ha,
    sourceDualBody3_volume k G.index a hp ha] at h
  apply (le_div_iff₀ hp).mpr
  have hh := (div_le_iff₀ hP).mp (show
    ((∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (sourceDualCoordinates3 k G.index a hp ha) j) * (8 * (G.index : ℝ) ^ 3)) /
      (∏ i, a i) ≤ 8 * (G.index : ℝ) ^ 2 by simpa [mul_div_assoc] using h)
  nlinarith [sq_pos_of_pos hp]

theorem sourceDual_minima_transference3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (B : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hcov : ZLattice.covolume (lattice3 B) = (G.index : ℝ))
    (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hvol : volume.real (parallelepipedBody3 e) = 8 * ∏ i, a i)
    (hpoint : ∀ j i, |∑ l : Fin 3, retainedRealMatrix3 k i l *
      ((u j : IntegerTriple) l : ℝ)| ≤ successiveRadius3 B e j * a i)
    (hprod : (∏ j, successiveRadius3 B e j) * (∏ i, a i) ≤ (G.index : ℝ)) (i : Fin 3) :
    1 / (1296 * successiveRadius3 B e i.rev) ≤
      successiveRadius3 (sourceDualBasis3 G c hc hD)
        (sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) i ∧
    successiveRadius3 (sourceDualBasis3 G c hc hD)
      (sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) i ≤
        6 / successiveRadius3 B e i.rev := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  let s := successiveRadius3 B e
  let t := successiveRadius3 (sourceDualBasis3 G c hc hD)
    (sourceDualCoordinates3 k G.index a hp ha)
  obtain ⟨_, _, _, hs, _, _⟩ := exists_successive_minima3 B e
  obtain ⟨_, _, _, ht, _, _⟩ := exists_successive_minima3 (sourceDualBasis3 G c hc hD)
    (sourceDualCoordinates3 k G.index a hp ha)
  have hP : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have hupper : ∀ j, t j ≤ 6 / s j.rev :=
    sourceDual_minima_upper3 G c hc hD u hu B e k a ha hpoint hprod
  refine ⟨?_, hupper i⟩
  have hl := source_minima_product_lower3 B e G.index (∏ i, a i) hP hvol hcov
  have hlstar := sourceDual_minima_product_lower3 G c hc hD k a ha
  have hpair := mul_le_mul hl hlstar (le_of_lt (div_pos hP (mul_pos (by norm_num) hp)))
    (Finset.prod_nonneg (fun j _ => (hs j).le))
  have hcancel : (G.index : ℝ) / (6 * ∏ i, a i) * ((∏ i, a i) / (6 * G.index)) = 1 / 36 := by
    field_simp
    ring
  rw [hcancel] at hpair
  have hbound := ternary_transference_product_lower3 s t hs ht
    (fun j => (le_div_iff₀ (hs _)).mp (hupper j)) hpair i
  apply (div_le_iff₀ (mul_pos (by norm_num) (hs i.rev))).mpr
  nlinarith

theorem exists_qSource_dual_minima3
    (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∃ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
      (c : Basis (Fin 3) ℤ (qSourceLattice3 k₂ k₃ Q c₂ c₃))
      (Bstar : Basis (Fin 3) ℝ RealTriple)
      (hD : (0 : ℝ) < (qSourceLattice3 k₂ k₃ Q c₂ c₃).index),
      lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 ∧
      LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
      (∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
        (integerTripleReal3 (u j : IntegerTriple)) =
          successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) ∧
      dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u ≤ 6 ∧
      (qSourceLattice3 k₂ k₃ Q c₂ c₃).index = qCongruenceIndex3 Q c₂ c₃ ∧
      (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) ≤
        qRoundingFactor3 Q c₂ c₃ ∧
      1 ≤ qRoundingFactor3 Q c₂ c₃ ∧ qRoundingFactor3 Q c₂ c₃ < 216 ∧
      lattice3 Bstar = (dualFrameSourceBasisLattice3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) c).map
        rationalTripleReal3 ∧
      ZLattice.covolume (lattice3 Bstar) = ((qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) ^ 2 ∧
      (∀ i, 1 / (1296 * successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) i.rev) ≤
        successiveRadius3 Bstar
          (sourceDualCoordinates3 k₀ (qSourceLattice3 k₂ k₃ Q c₂ c₃).index
            (fun l => Q ^ c₀ l) hD
            (fun l => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (c₀ l))) i ∧
        successiveRadius3 Bstar
          (sourceDualCoordinates3 k₀ (qSourceLattice3 k₂ k₃ Q c₂ c₃).index
            (fun l => Q ^ c₀ l) hD
            (fun l => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (c₀ l))) i ≤
          6 / successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) i.rev) := by
  obtain ⟨B, u, c, hB, hu, hatt, hJ, hindex, hprod, hR₁, hR₂, _⟩ :=
    exists_qSource_complete_dual_frame3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb
  let G := qSourceLattice3 k₂ k₃ Q c₂ c₃
  have hc := mixedCongruence3_basis_real_independent _ _ (retainedIntegerMatrix3_isUnit k₂)
    (retainedIntegerMatrix3_isUnit k₃) _ _ c
  have hD : G.index ≠ 0 := by
    rw [hindex]
    unfold qCongruenceIndex3
    positivity
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  have ha (l : Fin 3) : 0 < Q ^ c₀ l := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  let a := fun l => Q ^ c₀ l
  have hcov : ZLattice.covolume (lattice3 B) = (G.index : ℝ) := by
    rw [hB, hindex]
    exact (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  have hvol : volume.real (parallelepipedBody3 (qSourceCoordinates3 k₀ Q c₀ hQ)) =
      8 * ∏ l, a l := by
    rw [← qSourceBody3_eq_parallelepiped k₀ Q c₀ hQ]
    exact qSourceBody3_volume k₀ Q c₀ hQ
  have hpoint : ∀ j i, |∑ l : Fin 3, retainedRealMatrix3 k₀ i l *
      ((u j : IntegerTriple) l : ℝ)| ≤
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j * a i := by
    intro j i
    have h := qSource_arch_bound k₀ Q c₀ hQ (integerTripleReal3 (u j : IntegerTriple)) i
    rw [hatt] at h
    exact h
  have hprod' : (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) *
      (∏ l, a l) ≤ (G.index : ℝ) := by
    calc
      _ ≤ qRoundingFactor3 Q c₂ c₃ * (∏ l, a l) :=
        mul_le_mul_of_nonneg_right hprod (Finset.prod_nonneg (fun l _ => (ha l).le))
      _ = _ := by
        rw [hindex, qCongruenceIndex3_balanced Q c₀ c₂ c₃ hQ hb]
        ring
  refine ⟨B, u, c, sourceDualBasis3 G c hc hD, hp, hB, hu, hatt, hJ, hindex,
    hprod, hR₁, hR₂, sourceDualBasis3_lattice G c hc hD,
    sourceDualBasis3_covolume G c hc hD, ?_⟩
  exact sourceDual_minima_transference3 G c hc hD u hu B _ hcov k₀ a ha hvol hpoint hprod'

theorem sourceDual_minima_normalization3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (R : ℝ) (hR : 0 < R) (hbalance : (G.index : ℝ) = (∏ i, a i) * R) :
    volume.real (sourceDualBody3 k G.index a) /
      (8 * ZLattice.covolume (lattice3 (sourceDualBasis3 G c hc hD))) = R ∧
    1 / (6 * R) ≤ ∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) j ∧
    (∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) j) ≤ 1 / R := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hP : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have he₁ : (∏ i, a i) / (6 * (G.index : ℝ)) = 1 / (6 * R) := by
    rw [hbalance]
    field_simp
    ring
  have he₂ : (∏ i, a i) / (G.index : ℝ) = 1 / R := by
    rw [hbalance]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceDualBody3_volume k G.index a hp ha, sourceDualBasis3_covolume, hbalance]
    field_simp
    ring
  · rw [← he₁]
    exact sourceDual_minima_product_lower3 G c hc hD k a ha
  · rw [← he₂]
    exact sourceDual_minima_product_upper3 G c hc hD k a ha

end JSP000334
