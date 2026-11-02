import SubspaceBridge.CofactorSourceVanishing3
import SubspaceBridge.FixedDualDirection3
open scoped BigOperators Matrix
open MeasureTheory
namespace JSP000334
noncomputable section

noncomputable def cofactor_sourceDualBody3 (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ) : Set RealTriple :=
  {x | ∀ i, |∑ j : Fin 3, (cofactorRealMatrix3 k)⁻¹ j i * x j| ≤ D / a i}

noncomputable def cofactor_sourceDualCoordinates3 (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ)
    (hD : 0 < D) (ha : ∀ i, 0 < a i) : RealTriple ≃ₗ[ℝ] RealTriple :=
  archCoordinates3 (cofactorDualRealCoordinates3 k) (fun i => D / a i)
    (fun i => div_pos hD (ha i))

theorem cofactor_sourceDualRealCoordinates3_abs_det (k : Fin 3) :
    |LinearMap.det (cofactorDualRealCoordinates3 k).toLinearMap| = 1 := by
  change |LinearMap.det (Matrix.toLin' (cofactorRealMatrix3 k)⁻¹.transpose)| = 1
  rw [LinearMap.det_toLin', Matrix.det_transpose, Matrix.det_nonsing_inv,
    cofactorRealMatrix3_det]
  norm_num

theorem cofactor_sourceDualBody3_eq_parallelepiped (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ)
    (hD : 0 < D) (ha : ∀ i, 0 < a i) :
    cofactor_sourceDualBody3 k D a = parallelepipedBody3 (cofactor_sourceDualCoordinates3 k D a hD ha) := by
  exact archBody3_eq_parallelepiped (cofactorDualRealCoordinates3 k)
    (fun i => D / a i) (fun i => div_pos hD (ha i))

theorem cofactor_sourceDualBody3_volume (k : Fin 3) (D : ℝ) (a : Fin 3 → ℝ)
    (hD : 0 < D) (ha : ∀ i, 0 < a i) :
    volume.real (cofactor_sourceDualBody3 k D a) = 8 * D ^ 3 / ∏ i, a i := by
  change volume.real (archBody3 (cofactorDualRealCoordinates3 k) (fun i => D / a i)) = _
  rw [archBody3_volume _ _ (fun i => div_pos hD (ha i)),
    cofactor_sourceDualRealCoordinates3_abs_det, div_one, Finset.prod_div_distrib]
  simp [Fin.prod_univ_succ, div_eq_mul_inv, pow_succ, mul_assoc]

theorem cofactor_sourceDual_frame_gauge_bound3 (k : Fin 3) (D t s : ℝ)
    (a : Fin 3 → ℝ) (hD : 0 < D) (ha : ∀ i, 0 < a i)
    (w : Fin 3 → IntegerTriple) (j : Fin 3)
    (h : ∀ i, |t * dualFrameRealLocalValue3 (cofactorRealMatrix3 k) w j i| ≤
      6 * D * (a i)⁻¹ * s⁻¹) :
    coordinateGauge3 (cofactor_sourceDualCoordinates3 k D a hD ha)
      (fun i => t * (dualFrameVector3 w j i : ℝ)) ≤ 6 * s⁻¹ := by
  change ‖cofactor_sourceDualCoordinates3 k D a hD ha _‖ ≤ _
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  change |(∑ l : Fin 3, (cofactorRealMatrix3 k)⁻¹ l i *
    (t * (dualFrameVector3 w j l : ℝ))) / (D / a i)| ≤ _
  have he : (∑ l : Fin 3, (cofactorRealMatrix3 k)⁻¹ l i *
      (t * (dualFrameVector3 w j l : ℝ))) =
      t * dualFrameRealLocalValue3 (cofactorRealMatrix3 k) w j i := by
    simp only [zero_add, dualFrameRealLocalValue3, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, abs_div, abs_of_pos (div_pos hD (ha i)), div_le_iff₀ (div_pos hD (ha i))]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h i

theorem cofactor_sourceDual_minima_upper3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (B : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hpoint : ∀ j i, |∑ l : Fin 3, cofactorRealMatrix3 k i l *
      ((u j : IntegerTriple) l : ℝ)| ≤ successiveRadius3 B e j * a i)
    (hprod : (∏ j, successiveRadius3 B e j) * (∏ i, a i) ≤ (G.index : ℝ))
    (i : Fin 3) :
    successiveRadius3 (sourceDualBasis3 G c hc hD)
      (cofactor_sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) i ≤
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
  apply cofactor_sourceDual_frame_gauge_bound3 k G.index t (successiveRadius3 B e j) a _ ha w j
  intro l
  exact dualFrame3_source_real_bound G c u hu (cofactorRealMatrix3 k)
    (by rw [cofactorRealMatrix3_det]; norm_num)
    _ a hs ha hpoint hprod l j

theorem cofactor_sourceDual_minima_product_lower3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ i, a i) / (6 * (G.index : ℝ)) ≤
      ∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
        (cofactor_sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) j := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hP : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have h := successive_minima3_parallelepiped_volume_lower (sourceDualBasis3 G c hc hD)
    (cofactor_sourceDualCoordinates3 k G.index a hp ha)
  rw [sourceDualBasis3_covolume,
    ← cofactor_sourceDualBody3_eq_parallelepiped k G.index a hp ha,
    cofactor_sourceDualBody3_volume k G.index a hp ha] at h
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  have hh := (le_div_iff₀ hP).mp (show (8 / 6 : ℝ) * (G.index : ℝ) ^ 2 ≤
    (∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (cofactor_sourceDualCoordinates3 k G.index a hp ha) j) * (8 * (G.index : ℝ) ^ 3) / (∏ i, a i) by
        simpa [mul_div_assoc] using h)
  nlinarith [sq_pos_of_pos hp]

theorem cofactor_sourceDual_minima_product_upper3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (cofactor_sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) j) ≤
        (∏ i, a i) / (G.index : ℝ) := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hP : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have h := successive_minima3_parallelepiped_volume_upper (sourceDualBasis3 G c hc hD)
    (cofactor_sourceDualCoordinates3 k G.index a hp ha)
  rw [sourceDualBasis3_covolume,
    ← cofactor_sourceDualBody3_eq_parallelepiped k G.index a hp ha,
    cofactor_sourceDualBody3_volume k G.index a hp ha] at h
  apply (le_div_iff₀ hp).mpr
  have hh := (div_le_iff₀ hP).mp (show
    ((∏ j, successiveRadius3 (sourceDualBasis3 G c hc hD)
      (cofactor_sourceDualCoordinates3 k G.index a hp ha) j) * (8 * (G.index : ℝ) ^ 3)) /
      (∏ i, a i) ≤ 8 * (G.index : ℝ) ^ 2 by simpa [mul_div_assoc] using h)
  nlinarith [sq_pos_of_pos hp]

theorem cofactor_sourceDual_minima_transference3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : G.index ≠ 0) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (B : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hcov : ZLattice.covolume (lattice3 B) = (G.index : ℝ))
    (k : Fin 3) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hvol : volume.real (parallelepipedBody3 e) = 8 * ∏ i, a i)
    (hpoint : ∀ j i, |∑ l : Fin 3, cofactorRealMatrix3 k i l *
      ((u j : IntegerTriple) l : ℝ)| ≤ successiveRadius3 B e j * a i)
    (hprod : (∏ j, successiveRadius3 B e j) * (∏ i, a i) ≤ (G.index : ℝ)) (i : Fin 3) :
    1 / (1296 * successiveRadius3 B e i.rev) ≤
      successiveRadius3 (sourceDualBasis3 G c hc hD)
        (cofactor_sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) i ∧
    successiveRadius3 (sourceDualBasis3 G c hc hD)
      (cofactor_sourceDualCoordinates3 k G.index a (by exact_mod_cast Nat.pos_of_ne_zero hD) ha) i ≤
        6 / successiveRadius3 B e i.rev := by
  have hp : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  let s := successiveRadius3 B e
  let t := successiveRadius3 (sourceDualBasis3 G c hc hD)
    (cofactor_sourceDualCoordinates3 k G.index a hp ha)
  obtain ⟨_, _, _, hs, _, _⟩ := exists_successive_minima3 B e
  obtain ⟨_, _, _, ht, _, _⟩ := exists_successive_minima3 (sourceDualBasis3 G c hc hD)
    (cofactor_sourceDualCoordinates3 k G.index a hp ha)
  have hP : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have hupper : ∀ j, t j ≤ 6 / s j.rev :=
    cofactor_sourceDual_minima_upper3 G c hc hD u hu B e k a ha hpoint hprod
  refine ⟨?_, hupper i⟩
  have hl := source_minima_product_lower3 B e G.index (∏ i, a i) hP hvol hcov
  have hlstar := cofactor_sourceDual_minima_product_lower3 G c hc hD k a ha
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

end
end JSP000334
