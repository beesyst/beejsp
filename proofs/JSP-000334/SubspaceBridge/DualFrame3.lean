import SubspaceBridge

open scoped BigOperators
namespace JSP000334

def dualFrameIntegerMatrix3 (w : Fin 3 → IntegerTriple) : Matrix (Fin 3) (Fin 3) ℤ := w

def dualFrameRationalMatrix3 (w : Fin 3 → IntegerTriple) : Matrix (Fin 3) (Fin 3) ℚ :=
  (dualFrameIntegerMatrix3 w).map (Int.castRingHom ℚ)

noncomputable def dualFrameVector3 (w : Fin 3 → IntegerTriple) (j i : Fin 3) : ℚ :=
  (dualFrameRationalMatrix3 w)⁻¹ i j

theorem dualFrameMatrix3_det_ne_zero (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => (w j i : ℚ))) :
    (dualFrameRationalMatrix3 w).det ≠ 0 := by
  have hu : IsUnit (dualFrameRationalMatrix3 w) := Matrix.linearIndependent_rows_iff_isUnit.mp hw
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

theorem dualFrameVector3_pairing (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => (w j i : ℚ)))
    (i j : Fin 3) :
    (∑ k : Fin 3, (w i k : ℚ) * dualFrameVector3 w j k) = if i = j then 1 else 0 := by
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℚ => A i j)
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (dualFrameMatrix3_det_ne_zero w hw)))
  simpa [Matrix.mul_apply, Matrix.one_apply, dualFrameVector3, dualFrameRationalMatrix3,
    dualFrameIntegerMatrix3] using he

theorem dualFrameVector3_det_scaled (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => (w j i : ℚ)))
    (j i : Fin 3) :
    ((dualFrameIntegerMatrix3 w).det : ℚ) * dualFrameVector3 w j i =
      ((dualFrameIntegerMatrix3 w).adjugate i j : ℚ) := by
  have hd := dualFrameMatrix3_det_ne_zero w hw
  have hm := (Int.castRingHom ℚ).map_adjugate (dualFrameIntegerMatrix3 w)
  have hdet : ((dualFrameIntegerMatrix3 w).det : ℚ) = (dualFrameRationalMatrix3 w).det :=
    (Int.castRingHom ℚ).map_det _
  rw [hdet]
  unfold dualFrameVector3
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  change _ * (_⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  exact (congrArg (fun A : Matrix (Fin 3) (Fin 3) ℚ => A i j) hm).symm

theorem dualFrameVector3_det_integral (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => (w j i : ℚ)))
    (j : Fin 3) :
    ∃ z : IntegerTriple, ∀ i, ((dualFrameIntegerMatrix3 w).det : ℚ) *
      dualFrameVector3 w j i = (z i : ℚ) :=
  ⟨fun i => (dualFrameIntegerMatrix3 w).adjugate i j, dualFrameVector3_det_scaled w hw j⟩


def dualFrameRationalLattice3 (G : AddSubgroup IntegerTriple) : Set (Fin 3 → ℚ) :=
  {v | ∀ x : G, ∃ z : ℤ, (∑ i : Fin 3, ((x : IntegerTriple) i : ℚ) * v i) = (z : ℚ)}

def dualFrameSourceLattice3 (G : AddSubgroup IntegerTriple) : Set (Fin 3 → ℚ) :=
  (fun v : Fin 3 → ℚ => fun i => (G.index : ℚ) * v i) '' dualFrameRationalLattice3 G

noncomputable def dualFrameRelativeIndex3 (G : AddSubgroup IntegerTriple) (u : Fin 3 → G) : ℕ :=
  (Submodule.span ℤ (Set.range u)).toAddSubgroup.index

theorem dualFrameVector3_index_mem (G : AddSubgroup IntegerTriple) (u : Fin 3 → G)
    (hu : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((u j : IntegerTriple) i : ℚ)))
    (j : Fin 3) :
    (fun i => (dualFrameRelativeIndex3 G u : ℚ) *
      dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) ∈ dualFrameRationalLattice3 G := by
  intro x
  let N := Submodule.span ℤ (Set.range u)
  have hx : (dualFrameRelativeIndex3 G u) • x ∈ N :=
    N.toAddSubgroup.nsmul_index_mem x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  have he (i : Fin 3) : (∑ k : Fin 3, (c k : ℚ) * ((u k : IntegerTriple) i : ℚ)) =
      (dualFrameRelativeIndex3 G u : ℚ) * ((x : IntegerTriple) i : ℚ) := by
    have h := congrArg (fun y : G => ((y : IntegerTriple) i : ℚ)) hc
    simpa [Finset.sum_apply, Submodule.coe_sum, smul_eq_mul] using h
  refine ⟨c j, ?_⟩
  calc
    _ = ∑ i : Fin 3, (∑ k : Fin 3, (c k : ℚ) * ((u k : IntegerTriple) i : ℚ)) *
        dualFrameVector3 (fun k => (u k : IntegerTriple)) j i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [he]
      ring
    _ = ∑ k : Fin 3, (c k : ℚ) *
        (∑ i : Fin 3, ((u k : IntegerTriple) i : ℚ) *
          dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = (c j : ℚ) := by simp [dualFrameVector3_pairing _ hu]

theorem dualFrameSourceLattice3_integral (G : AddSubgroup IntegerTriple)
    (v : Fin 3 → ℚ) (hv : v ∈ dualFrameSourceLattice3 G) :
    ∃ z : IntegerTriple, ∀ i, v i = (z i : ℚ) := by
  obtain ⟨q, hq, rfl⟩ := hv
  have hcoord (i : Fin 3) : ∃ z : ℤ, (G.index : ℚ) * q i = (z : ℚ) := by
    let x : G := ⟨G.index • Pi.single i 1, G.nsmul_index_mem _⟩
    obtain ⟨z, hz⟩ := hq x
    refine ⟨z, ?_⟩
    simpa [x, Pi.single_apply, Finset.sum_ite_eq', mul_ite, nsmul_eq_mul] using hz
  choose z hz using hcoord
  exact ⟨z, hz⟩

theorem dualFrameVector3_source_mem (G : AddSubgroup IntegerTriple) (u : Fin 3 → G)
    (hu : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((u j : IntegerTriple) i : ℚ)))
    (j : Fin 3) :
    (fun i => ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) *
      dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) ∈ dualFrameSourceLattice3 G := by
  refine ⟨_, dualFrameVector3_index_mem G u hu j, ?_⟩
  funext i
  simp only [Nat.cast_mul]
  ring


theorem dualFrameMatrix3_rational_independent (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℝ (fun j => integerTripleReal3 (w j))) :
    LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => (w j i : ℚ)) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := (dualFrameIntegerMatrix3 w).map (Int.castRingHom ℝ)
  have hM : M.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hw))
  have hdZ : (dualFrameIntegerMatrix3 w).det ≠ 0 := by
    intro he
    apply hM
    rw [show M.det = ((dualFrameIntegerMatrix3 w).det : ℝ) from
      ((Int.castRingHom ℝ).map_det _).symm, he, Int.cast_zero]
  have hdQ : (dualFrameRationalMatrix3 w).det ≠ 0 := by
    rw [show (dualFrameRationalMatrix3 w).det = ((dualFrameIntegerMatrix3 w).det : ℚ) from
      ((Int.castRingHom ℚ).map_det _).symm]
    exact_mod_cast hdZ
  exact Matrix.linearIndependent_rows_of_det_ne_zero hdQ

theorem dualFrameRelativeIndex3_mul_index
    (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple))) :
    dualFrameRelativeIndex3 G u * G.index =
      (dualFrameIntegerMatrix3 (fun j => (u j : IntegerTriple))).det.natAbs := by
  have huZ : LinearIndependent ℤ u :=
    LinearIndependent.of_comp (integerTripleReal3.comp G.subtype.toIntLinearMap)
      (hu.restrict_scalars' ℤ)
  obtain ⟨_, hJ, _⟩ := integer_span3_index_det c u huZ
  have hD := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 3)) G c
  let B : Matrix (Fin 3) (Fin 3) ℤ := fun i j => (c j : IntegerTriple) i
  have hmul : B * c.toMatrix u = (dualFrameIntegerMatrix3 (fun j => (u j : IntegerTriple))).transpose := by
    ext i j
    have he := congrArg (fun x : G => (x : IntegerTriple) i) (c.sum_repr (u j))
    simpa [B, Matrix.mul_apply, Basis.toMatrix_apply, Finset.sum_apply,
      dualFrameIntegerMatrix3, mul_comm] using he
  have hB : B.det.natAbs = G.index := by
    rw [hD]
    congr 1
  unfold dualFrameRelativeIndex3
  rw [hJ, ← hB, ← Int.natAbs_mul, mul_comm (c.toMatrix u).det, ← Matrix.det_mul, hmul,
    Matrix.det_transpose]


theorem dualFrame3_abs_det_row_column_bounds (A : Matrix (Fin 3) (Fin 3) ℝ)
    (s t : Fin 3 → ℝ) (hA : ∀ i j, |A i j| ≤ s i * t j) :
    |A.det| ≤ 6 * (∏ i, s i) * (∏ i, t i) := by
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  change abv A.det ≤ _
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin 3), abv (Equiv.Perm.sign σ • ∏ j, A (σ j) j) := by
      rw [Matrix.det_apply]
      exact abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin 3), ∏ j, |A (σ j) j| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ σ : Equiv.Perm (Fin 3), ∏ j, s (σ j) * t j := by
      exact Finset.sum_le_sum fun σ _ => Finset.prod_le_prod
        (fun j _ => abs_nonneg _) (fun j _ => hA (σ j) j)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Equiv.prod_comp]
      simp [Fintype.card_perm, Nat.factorial, mul_assoc]

theorem dualFrame3_cofactor_bound (A : Matrix (Fin 3) (Fin 3) ℝ)
    (s t : Fin 3 → ℝ) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i)
    (hA : ∀ i j, |A i j| ≤ s i * t j) (i j : Fin 3) :
    |A.adjugate i j| * s j * t i ≤ 6 * (∏ k, s k) * (∏ k, t k) := by
  classical
  let N := A.updateRow j ((s j * t i) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ))
  have hN : ∀ a b, |N a b| ≤ s a * t b := by
    intro a b
    by_cases ha : a = j
    · subst a
      by_cases hb : b = i
      · subst b
        simp [N, Matrix.updateRow_self, abs_of_nonneg (mul_nonneg (hs j) (ht i))]
      · simp [N, Matrix.updateRow_self, Pi.single_apply, hb, Ne.symm hb,
          mul_nonneg (hs j) (ht b)]
    · simpa [N, Matrix.updateRow_ne ha] using hA a b
  have h := dualFrame3_abs_det_row_column_bounds N s t hN
  have he : |N.det| = |A.adjugate i j| * s j * t i := by
    dsimp [N]
    rw [Matrix.det_updateRow_smul, ← Matrix.adjugate_apply, abs_mul,
      abs_of_nonneg (mul_nonneg (hs j) (ht i))]
    ring
  rwa [he] at h


noncomputable def dualFrameRealMatrix3 (w : Fin 3 → IntegerTriple) : Matrix (Fin 3) (Fin 3) ℝ :=
  (dualFrameIntegerMatrix3 w).map (Int.castRingHom ℝ)

noncomputable def dualFrameRealLocalValue3 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (w : Fin 3 → IntegerTriple) (j i : Fin 3) : ℝ :=
  ∑ k : Fin 3, A⁻¹ k i * (dualFrameVector3 w j k : ℝ)

theorem dualFrameVector3_real_inverse (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℝ (fun j => integerTripleReal3 (w j))) (i j : Fin 3) :
    (dualFrameRealMatrix3 w)⁻¹ i j = (dualFrameVector3 w j i : ℝ) := by
  let C : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (dualFrameVector3 w j i : ℝ)
  have he : dualFrameRealMatrix3 w * C = 1 := by
    ext i j
    have h := dualFrameVector3_pairing w (dualFrameMatrix3_rational_independent w hw) i j
    have hh := congrArg (fun q : ℚ => (q : ℝ)) h
    by_cases hij : i = j <;>
      simpa [dualFrameRealMatrix3, dualFrameIntegerMatrix3, C, Matrix.mul_apply,
        Rat.cast_sum, Rat.cast_mul, Matrix.one_apply, hij] using hh
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) (Matrix.inv_eq_right_inv he)

theorem dualFrameRealLocalValue3_inverse (A : Matrix (Fin 3) (Fin 3) ℝ)
    (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℝ (fun j => integerTripleReal3 (w j))) (i j : Fin 3) :
    dualFrameRealLocalValue3 A w j i = (dualFrameRealMatrix3 w * A.transpose)⁻¹ i j := by
  rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dualFrameVector3_real_inverse w hw]
  rfl

theorem dualFrame3_source_real_bound
    (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : |A.det| = 1)
    (s t : Fin 3 → ℝ) (hs : ∀ j, 0 < s j) (ht : ∀ i, 0 < t i)
    (hpoint : ∀ j i, |∑ k : Fin 3, A i k * ((u j : IntegerTriple) k : ℝ)| ≤ s j * t i)
    (hprod : (∏ j, s j) * (∏ i, t i) ≤ (G.index : ℝ)) (i j : Fin 3) :
    |((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℝ) *
      dualFrameRealLocalValue3 A (fun k => (u k : IntegerTriple)) j i| ≤
      6 * (G.index : ℝ) * (t i)⁻¹ * (s j)⁻¹ := by
  let w := fun k => (u k : IntegerTriple)
  let U := dualFrameRealMatrix3 w * A.transpose
  have hd : |U.det| = ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℝ) := by
    rw [Matrix.det_mul, abs_mul, Matrix.det_transpose, hA, mul_one]
    have hcast : (dualFrameRealMatrix3 w).det = ((dualFrameIntegerMatrix3 w).det : ℝ) :=
      ((Int.castRingHom ℝ).map_det _).symm
    rw [hcast, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast,
      ← dualFrameRelativeIndex3_mul_index G c u hu]
  have hU : ∀ a b, |U a b| ≤ s a * t b := by
    intro a b
    simpa [U, dualFrameRealMatrix3, dualFrameIntegerMatrix3, w, Matrix.mul_apply,
      Matrix.transpose_apply, mul_comm] using hpoint a b
  have hb := dualFrame3_cofactor_bound U s t (fun k => (hs k).le) (fun k => (ht k).le) hU i j
  have hupper : |U.adjugate i j| * s j * t i ≤ 6 * (G.index : ℝ) :=
    hb.trans (by nlinarith [hprod])
  have hUnz : U.det ≠ 0 := by
    have hW : (dualFrameRealMatrix3 w).det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
        (Matrix.linearIndependent_rows_iff_isUnit.mp hu))
    have hAnz : A.det ≠ 0 := by intro h; rw [h, abs_zero] at hA; norm_num at hA
    dsimp [U]
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hW hAnz
  have he : U.det * U⁻¹ i j = U.adjugate i j := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    change _ * (_⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ hUnz, one_mul]
  have hab : |((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℝ) *
      dualFrameRealLocalValue3 A w j i| = |U.adjugate i j| := by
    rw [dualFrameRealLocalValue3_inverse A w hu, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg _), ← hd, ← abs_mul, he]
  rw [hab]
  have hf : |U.adjugate i j| ≤ 6 * (G.index : ℝ) / (t i * s j) :=
    (le_div_iff₀ (mul_pos (ht i) (hs j))).mpr (by nlinarith [hupper])
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hf


theorem exists_qSource_dual_frame3
    (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∃ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃),
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
      (∀ i j, (∑ l : Fin 3, ((u i : IntegerTriple) l : ℚ) *
        dualFrameVector3 (fun k => (u k : IntegerTriple)) j l) = if i = j then 1 else 0) ∧
      (∀ j, (fun i => ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
          dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) ∈
            dualFrameSourceLattice3 (qSourceLattice3 k₂ k₃ Q c₂ c₃)) ∧
      (∀ j, ∃ z : IntegerTriple, ∀ i,
        ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
          (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
            dualFrameVector3 (fun k => (u k : IntegerTriple)) j i = (z i : ℚ)) ∧
      (∀ i j, |((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℝ) *
          dualFrameRealLocalValue3 (retainedRealMatrix3 k₀) (fun k => (u k : IntegerTriple)) j i| ≤
        6 * ((qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) * (Q ^ c₀ i)⁻¹ *
          (successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j)⁻¹) := by
  obtain ⟨B,u,hB,hu,hatt,_hfinite,hJ,ha,_h2,_h3,hprod,hR,_⟩ :=
    exists_qSource_integer_attaining_frame k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb
  let G := qSourceLattice3 k₂ k₃ Q c₂ c₃
  have hindex : G.index = qCongruenceIndex3 Q c₂ c₃ :=
    (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1
  have hRQ := qRoundingFactor3_bounds Q c₂ c₃ hQ hc₂ hc₃
  have huQ := dualFrameMatrix3_rational_independent (fun k => (u k : IntegerTriple)) hu
  have hmem := dualFrameVector3_source_mem G u huQ
  refine ⟨B,u,hB,hu,hatt,hJ,hindex,hprod,hRQ.1,hR,
    dualFrameVector3_pairing _ huQ,hmem,?_,?_⟩
  · intro j
    exact dualFrameSourceLattice3_integral G _ (hmem j)
  · intro i j
    obtain ⟨c⟩ : Nonempty (Basis (Fin 3) ℤ G) := mixedCongruence3_has_basis _ _ _ _
    obtain ⟨_,_,_,hpos,_,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
    apply dualFrame3_source_real_bound G c u hu (retainedRealMatrix3 k₀) ?_
      (fun k => successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) k)
      (fun k => Q ^ c₀ k) hpos (fun k => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) ?_ ?_ i j
    · rw [retainedRealMatrix3_det]
      split_ifs <;> norm_num
    · intro a b
      exact ha b a
    · calc
        _ ≤ qRoundingFactor3 Q c₂ c₃ * (∏ k : Fin 3, Q ^ c₀ k) :=
          mul_le_mul_of_nonneg_right hprod (Finset.prod_nonneg (fun k _ =>
            (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (c₀ k)).le))
        _ = (G.index : ℝ) := by
          rw [hindex, qCongruenceIndex3_balanced Q c₀ c₂ c₃ hQ hb]
          ring

noncomputable def dualFrameSourceBasisLattice3 (G : AddSubgroup IntegerTriple)
    (c : Basis (Fin 3) ℤ G) : Submodule ℤ (Fin 3 → ℚ) :=
  Submodule.span ℤ (Set.range (fun j : Fin 3 => fun i : Fin 3 =>
    (G.index : ℚ) * dualFrameVector3 (fun k => (c k : IntegerTriple)) j i))

theorem dualFrameSourceLattice3_subset_basis
    (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((c j : IntegerTriple) i : ℚ)))
    (v : Fin 3 → ℚ) (hv : v ∈ dualFrameSourceLattice3 G) :
    v ∈ dualFrameSourceBasisLattice3 G c := by
  classical
  obtain ⟨q, hq, rfl⟩ := hv
  have hcoeff (j : Fin 3) : ∃ a : ℤ, (∑ i : Fin 3, ((c j : IntegerTriple) i : ℚ) * q i) = (a : ℚ) := hq (c j)
  choose a ha using hcoeff
  have hrepr : q = ∑ j : Fin 3, (a j : ℚ) • dualFrameVector3 (fun k => (c k : IntegerTriple)) j := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.linearIndependent_rows_iff_isUnit.mp hc)
    ext i
    change (∑ k : Fin 3, ((c i : IntegerTriple) k : ℚ) * q k) = _
    rw [ha i]
    change (a i : ℚ) = ∑ k : Fin 3, ((c i : IntegerTriple) k : ℚ) *
      ((∑ j : Fin 3, (a j : ℚ) • dualFrameVector3 (fun k => (c k : IntegerTriple)) j) k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm ((c i : IntegerTriple) _ : ℚ), ← Finset.mul_sum]
    simp [dualFrameVector3_pairing _ hc]
  have he : (fun i => (G.index : ℚ) * q i) =
      ∑ j : Fin 3, a j • (fun i => (G.index : ℚ) * dualFrameVector3 (fun k => (c k : IntegerTriple)) j i) := by
    ext i
    have hh := congrFun hrepr i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    rw [hh, Finset.mul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [zsmul_eq_mul]
    ring
  change (fun i => (G.index : ℚ) * q i) ∈ dualFrameSourceBasisLattice3 G c
  rw [he]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

theorem dualFrameVector3_source_basis_mem
    (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G)
    (hc : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((c j : IntegerTriple) i : ℚ)))
    (u : Fin 3 → G)
    (hu : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((u j : IntegerTriple) i : ℚ)))
    (j : Fin 3) :
    (fun i => ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) *
      dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) ∈ dualFrameSourceBasisLattice3 G c :=
  dualFrameSourceLattice3_subset_basis G c hc _ (dualFrameVector3_source_mem G u hu j)

theorem qSource_dual_frame3_basis
    (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple))) :
    ∃ c : Basis (Fin 3) ℤ (qSourceLattice3 k₂ k₃ Q c₂ c₃),
      ∀ j, (fun i => ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
          dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) ∈
            dualFrameSourceBasisLattice3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) c := by
  obtain ⟨c⟩ : Nonempty (Basis (Fin 3) ℤ (qSourceLattice3 k₂ k₃ Q c₂ c₃)) :=
    mixedCongruence3_has_basis _ _ _ _
  have hc := mixedCongruence3_basis_real_independent _ _ (retainedIntegerMatrix3_isUnit k₂)
    (retainedIntegerMatrix3_isUnit k₃) _ _ c
  have hcQ := dualFrameMatrix3_rational_independent (fun j => (c j : IntegerTriple)) hc
  have huQ := dualFrameMatrix3_rational_independent (fun j => (u j : IntegerTriple)) hu
  exact ⟨c, dualFrameVector3_source_basis_mem _ c hcQ u huQ⟩


theorem exists_qSource_complete_dual_frame3
    (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∃ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
      (c : Basis (Fin 3) ℤ (qSourceLattice3 k₂ k₃ Q c₂ c₃)),
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
      (∀ i j, (∑ l : Fin 3, ((u i : IntegerTriple) l : ℚ) *
        dualFrameVector3 (fun k => (u k : IntegerTriple)) j l) = if i = j then 1 else 0) ∧
      (∀ j, (fun i => ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
          dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) ∈
            dualFrameSourceLattice3 (qSourceLattice3 k₂ k₃ Q c₂ c₃)) ∧
      (∀ j, ∃ z : IntegerTriple, ∀ i,
        ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
          (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
            dualFrameVector3 (fun k => (u k : IntegerTriple)) j i = (z i : ℚ)) ∧
      (∀ i j, |((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℝ) *
          dualFrameRealLocalValue3 (retainedRealMatrix3 k₀) (fun k => (u k : IntegerTriple)) j i| ≤
        6 * ((qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) * (Q ^ c₀ i)⁻¹ *
          (successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j)⁻¹) ∧
      LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((u j : IntegerTriple) i : ℚ)) ∧
      (∀ j, (fun i => ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
          dualFrameVector3 (fun k => (u k : IntegerTriple)) j i) ∈
            dualFrameSourceBasisLattice3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) c) ∧
      (∀ i j, (∑ l : Fin 3, ((u i : IntegerTriple) l : ℚ) *
        (((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
          (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
            dualFrameVector3 (fun k => (u k : IntegerTriple)) j l)) =
        if i = j then ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
          (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) else 0) := by
  obtain ⟨B, u, hB, hu, hatt, hJ, hD, hprod, hR₁, hR₂, hpair, hmem, hint, hreal⟩ :=
    exists_qSource_dual_frame3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb
  obtain ⟨c, hc⟩ := qSource_dual_frame3_basis k₂ k₃ Q c₂ c₃ u hu
  have huQ := dualFrameMatrix3_rational_independent (fun j => (u j : IntegerTriple)) hu
  refine ⟨B, u, c, hB, hu, hatt, hJ, hD, hprod, hR₁, hR₂, hpair, hmem, hint, hreal, huQ, hc, ?_⟩
  intro i j
  calc
    _ = ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
        (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
        ∑ l : Fin 3, ((u i : IntegerTriple) l : ℚ) *
          dualFrameVector3 (fun k => (u k : IntegerTriple)) j l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [hpair i j]
      split_ifs <;> simp

end JSP000334
