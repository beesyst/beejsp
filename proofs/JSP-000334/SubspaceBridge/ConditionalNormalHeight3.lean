import SubspaceBridge.DualMinima3
import SubspaceBridge.AuxiliaryProductFormula

open scoped BigOperators Matrix
namespace JSP000334

noncomputable def conditionalRationalMatrix3 (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℚ :=
  (retainedIntegerMatrix3 k).map (Int.castRingHom ℚ)

noncomputable def conditionalDualValue3 (k : Fin 3) (x : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  ∑ l : Fin 3, (conditionalRationalMatrix3 k)⁻¹ l i * x l

theorem conditionalRationalMatrix3_det (k : Fin 3) :
    (conditionalRationalMatrix3 k).det = if k = 1 then -1 else 1 := by
  have hd : (conditionalRationalMatrix3 k).det = ((retainedIntegerMatrix3 k).det : ℚ) :=
    ((Int.castRingHom ℚ).map_det _).symm
  rw [hd, retainedIntegerMatrix3_det]
  split_ifs <;> norm_num

theorem conditionalDualValue3_inverse (k : Fin 3) (w : Fin 3 → IntegerTriple) (i j : Fin 3) :
    conditionalDualValue3 k (dualFrameVector3 w j) i =
      (dualFrameRationalMatrix3 w * (conditionalRationalMatrix3 k).transpose)⁻¹ i j := by
  rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  rfl

theorem conditional_padic_minor_bound3 (p : ℕ) [Fact p.Prime]
    (x y z w : ℚ) (s t : ℝ) (hs : 0 ≤ s)
    (hx : (padicNorm p x : ℝ) ≤ s) (hy : (padicNorm p y : ℝ) ≤ t)
    (hz : (padicNorm p z : ℝ) ≤ s) (hw : (padicNorm p w : ℝ) ≤ t) :
    (padicNorm p (x*y-z*w) : ℝ) ≤ s*t := by
  have h : (padicNorm p (x*y-z*w) : ℝ) ≤
      max ((padicNorm p x : ℝ)*(padicNorm p y : ℝ))
        ((padicNorm p z : ℝ)*(padicNorm p w : ℝ)) := by
    exact_mod_cast (show padicNorm p (x*y-z*w) ≤
      max (padicNorm p x * padicNorm p y) (padicNorm p z * padicNorm p w) by
        simpa only [padicNorm.mul] using (padicNorm.sub (p := p) (q := x*y) (r := z*w)))
  exact h.trans (max_le (mul_le_mul hx hy (by exact_mod_cast padicNorm.nonneg y) hs)
    (mul_le_mul hz hw (by exact_mod_cast padicNorm.nonneg w) hs))

theorem conditional_last_cofactor_bound3 (p : ℕ) [Fact p.Prime]
    (U : Matrix (Fin 3) (Fin 3) ℚ) (s : Fin 3 → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hU : ∀ j i, (padicNorm p (U j i) : ℝ) ≤ s i) (i : Fin 3) :
    (padicNorm p (U.adjugate i 2) : ℝ) ≤ s (i.succAbove 0) * s (i.succAbove 1) := by
  fin_cases i
  · simpa [Matrix.adjugate_fin_three, mul_comm] using
      conditional_padic_minor_bound3 p (U 0 1) (U 1 2) (U 1 1) (U 0 2)
        (s 1) (s 2) (hs 1) (hU 0 1) (hU 1 2) (hU 1 1) (hU 0 2)
  · simpa [Matrix.adjugate_fin_three, sub_eq_add_neg, mul_comm, add_comm] using
      conditional_padic_minor_bound3 p (U 1 0) (U 0 2) (U 0 0) (U 1 2)
        (s 0) (s 2) (hs 0) (hU 1 0) (hU 0 2) (hU 0 0) (hU 1 2)
  · simpa [Matrix.adjugate_fin_three, mul_comm] using
      conditional_padic_minor_bound3 p (U 0 0) (U 1 1) (U 1 0) (U 0 1)
        (s 0) (s 1) (hs 0) (hU 0 0) (hU 1 1) (hU 1 0) (hU 0 1)

theorem conditional_scaled_dual_padic_bound3 (p : ℕ) [Fact p.Prime]
    (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (k : Fin 3) (s : Fin 3 → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpoint : ∀ j i, (padicNorm p (∑ l : Fin 3,
      (conditionalRationalMatrix3 k) i l * ((u j : IntegerTriple) l : ℚ)) : ℝ) ≤ s i)
    (i : Fin 3) :
    (padicNorm p (conditionalDualValue3 k (fun l =>
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l) i) : ℝ) ≤
      s (i.succAbove 0) * s (i.succAbove 1) := by
  let w := fun j => (u j : IntegerTriple)
  let U := dualFrameRationalMatrix3 w * (conditionalRationalMatrix3 k).transpose
  have huQ := dualFrameMatrix3_rational_independent w hu
  have hUnz : U.det ≠ 0 := by
    dsimp [U]
    rw [Matrix.det_mul, Matrix.det_transpose]
    apply mul_ne_zero (dualFrameMatrix3_det_ne_zero w huQ)
    rw [conditionalRationalMatrix3_det]
    split_ifs <;> norm_num
  have hcof : U.det * U⁻¹ i 2 = U.adjugate i 2 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    change _ * (_⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ hUnz, one_mul]
  have hJD : padicNorm p U.det =
      padicNorm p (((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ)) := by
    dsimp [U]
    rw [Matrix.det_mul, Matrix.det_transpose, padicNorm.mul, conditionalRationalMatrix3_det]
    split_ifs <;> simp only [padicNorm.one, padicNorm.neg, mul_one]
    all_goals
      rw [dualFrameRelativeIndex3_mul_index G c u hu]
      have hd : (dualFrameRationalMatrix3 w).det = ((dualFrameIntegerMatrix3 w).det : ℚ) :=
        ((Int.castRingHom ℚ).map_det _).symm
      rw [hd, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      by_cases h : (0 : ℚ) ≤ ((dualFrameIntegerMatrix3 w).det : ℚ)
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h), padicNorm.neg]
  have he : conditionalDualValue3 k (fun l =>
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) * dualFrameVector3 w 2 l) i =
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) * U⁻¹ i 2 := by
    rw [← conditionalDualValue3_inverse k w i 2]
    simp only [conditionalDualValue3, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hnorm : padicNorm p (conditionalDualValue3 k (fun l =>
      ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) * dualFrameVector3 w 2 l) i) =
      padicNorm p (U.adjugate i 2) := by
    rw [he, ← hcof, padicNorm.mul, padicNorm.mul, hJD]
  rw [hnorm]
  apply conditional_last_cofactor_bound3 p U s hs
  intro j l
  have h := hpoint j l
  simpa [U, dualFrameRationalMatrix3, dualFrameIntegerMatrix3,
    Matrix.mul_apply, Matrix.transpose_apply, w, mul_comm] using h

theorem conditional_source_value3 (k i : Fin 3) (x : IntegerTriple) :
    (∑ l : Fin 3, conditionalRationalMatrix3 k i l * (x l : ℚ)) =
      threeCoordinateSumForms k i (fun l => (x l : ℚ)) := by
  rw [← retainedIntegerMatrix3_apply k i x]
  simp [conditionalRationalMatrix3, Matrix.mulVec, dotProduct]

theorem conditional_actual_finite_bounds3
    (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (c : Basis (Fin 3) ℤ (qSourceLattice3 k₂ k₃ Q c₂ c₃))
    (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple))) :
    let z := fun l => ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
      (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l
    (∀ i, (padicNorm 2 (conditionalDualValue3 k₂ z i) : ℝ) ≤
      Q ^ (c₂ (i.succAbove 0) + c₂ (i.succAbove 1))) ∧
    (∀ i, (padicNorm 3 (conditionalDualValue3 k₃ z i) : ℝ) ≤
      Q ^ (c₃ (i.succAbove 0) + c₃ (i.succAbove 1))) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hb j := (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).1 (u j)
  have hp := lt_trans zero_lt_one hQ
  constructor
  · intro i
    rw [Real.rpow_add hp]
    apply conditional_scaled_dual_padic_bound3 2 _ c u hu k₂ (fun i => Q ^ c₂ i)
      (fun i => (Real.rpow_pos_of_pos hp _).le)
    intro j l
    rw [conditional_source_value3]
    exact ((hb j).mp (u j).property).1 l
  · intro i
    rw [Real.rpow_add hp]
    apply conditional_scaled_dual_padic_bound3 3 _ c u hu k₃ (fun i => Q ^ c₃ i)
      (fun i => (Real.rpow_pos_of_pos hp _).le)
    intro j l
    rw [conditional_source_value3]
    exact ((hb j).mp (u j).property).2 l

theorem conditional_primitive_integer3 (z : IntegerTriple) (hz : z ≠ 0) :
    ∃ (g : ℤ) (m : IntegerTriple), g ≠ 0 ∧ m ≠ 0 ∧
      (∀ i, z i = g * m i) ∧ Ideal.span (Set.range m) = ⊤ ∧
      Finset.univ.gcd (fun i => (m i).natAbs) = 1 := by
  classical
  let I : Ideal ℤ := Ideal.span (Set.range z)
  let g := Submodule.IsPrincipal.generator I
  have hdiv (i : Fin 3) : g ∣ z i := by
    apply (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
    exact Ideal.subset_span (Set.mem_range_self i)
  choose m hm using hdiv
  have hg : g ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hm i, he, zero_mul]
    rfl
  have hgm : g ∈ Submodule.span ℤ (Set.range z) := by
    rw [Ideal.submodule_span_eq]
    exact Submodule.IsPrincipal.generator_mem I
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hgm
  simp only [smul_eq_mul] at ha
  have hsum : ∑ i : Fin 3, a i * m i = 1 := by
    apply mul_left_cancel₀ hg
    calc
      g * (∑ i : Fin 3, a i * m i) = ∑ i : Fin 3, a i * z i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hm i]
        ring
      _ = g * 1 := by simpa using ha
  have hspan : Ideal.span (Set.range m) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hsum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  have hm0 : m ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hm i, he]
    simp
  refine ⟨g, m, hg, hm0, hm, hspan, ?_⟩
  apply rothPrimitiveTriple_common_divisor m hspan
  intro i
  exact Finset.gcd_dvd (Finset.mem_univ i)

theorem conditional_actual_primitive_normal3
    (G : AddSubgroup IntegerTriple) (c : Basis (Fin 3) ℤ G) (u : Fin 3 → G)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple))) :
    ∃ (z m : IntegerTriple) (g : ℤ),
      (∀ i, ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i = (z i : ℚ)) ∧
      g ≠ 0 ∧ m ≠ 0 ∧ (∀ i, z i = g * m i) ∧
      Ideal.span (Set.range m) = ⊤ ∧ Finset.univ.gcd (fun i => (m i).natAbs) = 1 ∧
      (∀ i, (m i : ℚ) =
        (((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) / g) *
          dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i) ∧
      (∀ j : Fin 2, (∑ i : Fin 3, m i * ((u j.castSucc : G) : IntegerTriple) i) = 0) := by
  have huQ := dualFrameMatrix3_rational_independent _ hu
  obtain ⟨z, hz⟩ := dualFrameSourceLattice3_integral G _ (dualFrameVector3_source_mem G u huQ 2)
  have hJD : dualFrameRelativeIndex3 G u * G.index ≠ 0 := by
    rw [dualFrameRelativeIndex3_mul_index G c u hu]
    have hd := dualFrameMatrix3_det_ne_zero _ huQ
    have hZ : (dualFrameIntegerMatrix3 (fun j => (u j : IntegerTriple))).det ≠ 0 := by
      intro he
      apply hd
      rw [show (dualFrameRationalMatrix3 (fun j => (u j : IntegerTriple))).det =
        ((dualFrameIntegerMatrix3 (fun j => (u j : IntegerTriple))).det : ℚ) from
        ((Int.castRingHom ℚ).map_det _).symm, he, Int.cast_zero]
    exact Int.natAbs_ne_zero.mpr hZ
  have hz0 : z ≠ 0 := by
    intro he
    have hpair := dualFrameVector3_pairing _ huQ 2 2
    have hzero (i : Fin 3) : dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i = 0 := by
      have hi := hz i
      rw [he] at hi
      simp only [Pi.zero_apply, Int.cast_zero, mul_eq_zero] at hi
      exact hi.resolve_left (by exact_mod_cast hJD)
    simp [hzero] at hpair
  obtain ⟨g, m, hg, hm0, hgm, hprim, hgcd⟩ := conditional_primitive_integer3 z hz0
  have hmq (i : Fin 3) : (m i : ℚ) =
      (((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) / g) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i := by
    have he := hz i
    rw [hgm i, Int.cast_mul] at he
    have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
    apply (mul_left_cancel₀ hgQ)
    calc
      (g : ℚ) * (m i : ℚ) = _ := he.symm
      _ = _ := by field_simp
  refine ⟨z, m, g, hz, hg, hm0, hgm, hprim, hgcd, hmq, ?_⟩
  intro j
  have hp := dualFrameVector3_pairing _ huQ j.castSucc 2
  have hj : j.castSucc ≠ (2 : Fin 3) := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  rw [if_neg hj] at hp
  have he : (∑ i : Fin 3, (m i : ℚ) * (((u j.castSucc : G) : IntegerTriple) i : ℚ)) = 0 := by
    simp_rw [hmq]
    calc
      _ = (((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) / g) *
          (∑ i : Fin 3, (((u j.castSucc : G) : IntegerTriple) i : ℚ) *
            dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hp, mul_zero]
  exact_mod_cast he


def conditionalDualInt3 (k : Fin 3) (m : IntegerTriple) : IntegerTriple :=
  ![m (k.succAbove 0) - m k, m (k.succAbove 1) - m k, m k]

theorem conditionalDualInt3_value (k : Fin 3) (m : IntegerTriple) (i : Fin 3) :
    conditionalDualValue3 k (fun l => (m l : ℚ)) i = (conditionalDualInt3 k m i : ℚ) := by
  let A := conditionalRationalMatrix3 k
  let v : Fin 3 → ℚ := fun l => (conditionalDualInt3 k m l : ℚ)
  have hAv : A.transpose *ᵥ v = fun l => (m l : ℚ) := by
    ext l
    fin_cases k <;> fin_cases l <;>
      simp [A, v, conditionalRationalMatrix3, conditionalDualInt3, retainedIntegerMatrix3,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_succ,
        Pi.single_apply, Fin.succAbove]
  have hunit : IsUnit A.det := by
    dsimp [A]
    rw [conditionalRationalMatrix3_det]
    split_ifs <;> norm_num
  change (A⁻¹.transpose *ᵥ (fun l => (m l : ℚ))) i = v i
  rw [← hAv, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv A hunit, Matrix.transpose_one, Matrix.one_mulVec]

theorem conditional_height_coord3 (m : IntegerTriple) (i : Fin 3) :
    |(m i : ℝ)| ≤ (rothKernelRowHeight m : ℝ) := by
  have h := Finset.le_sup (f := fun i => (m i).natAbs) (Finset.mem_univ i)
  have hab : ((m i).natAbs : ℝ) = |(m i : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [← hab]
  exact_mod_cast h

theorem conditional_height_pos3 (m : IntegerTriple) (hm : m ≠ 0) :
    0 < (rothKernelRowHeight m : ℝ) := by
  have hH : 0 < rothKernelRowHeight m := by
    by_contra h
    have he : rothKernelRowHeight m = 0 := by omega
    apply hm
    ext i
    have hi := Finset.le_sup (f := fun i => (m i).natAbs) (Finset.mem_univ i)
    change (m i).natAbs ≤ rothKernelRowHeight m at hi
    rw [he] at hi
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)
  exact_mod_cast hH

theorem conditionalDualInt3_height_bound (k : Fin 3) (m : IntegerTriple) (i : Fin 3) :
    |(conditionalDualInt3 k m i : ℝ)| ≤ 3 * (rothKernelRowHeight m : ℝ) := by
  have hi := conditional_height_coord3 m
  have hn : (0 : ℝ) ≤ rothKernelRowHeight m := Nat.cast_nonneg _
  fin_cases i
  · change |((m (k.succAbove 0) - m k : ℤ) : ℝ)| ≤ _
    rw [Int.cast_sub]
    exact (abs_sub _ _).trans (by linarith [hi (k.succAbove 0), hi k])
  · change |((m (k.succAbove 1) - m k : ℤ) : ℝ)| ≤ _
    rw [Int.cast_sub]
    exact (abs_sub _ _).trans (by linarith [hi (k.succAbove 1), hi k])
  · exact (hi k).trans (by linarith)

theorem conditional_integer_local_lower3 (z : ℤ) (hz : z ≠ 0) :
    1 ≤ |(z : ℝ)| * (padicNorm 2 (z : ℚ) : ℝ) ∧
    1 ≤ |(z : ℝ)| * (padicNorm 3 (z : ℚ) : ℝ) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := rothInteger_three_place_lower z hz
  change 1 ≤ |(z : ℝ)| * (padicNorm 2 (z : ℚ) : ℝ) * (padicNorm 3 (z : ℚ) : ℝ) at h
  have h2 : (padicNorm 2 (z : ℚ) : ℝ) ≤ 1 := by exact_mod_cast padicNorm.of_int (p := 2) z
  have h3 : (padicNorm 3 (z : ℚ) : ℝ) ≤ 1 := by exact_mod_cast padicNorm.of_int (p := 3) z
  have h2n : (0 : ℝ) ≤ padicNorm 2 (z : ℚ) := by exact_mod_cast padicNorm.nonneg _
  have h3n : (0 : ℝ) ≤ padicNorm 3 (z : ℚ) := by exact_mod_cast padicNorm.nonneg _
  constructor
  · exact h.trans (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) h2n) h3)
  · have hh := mul_le_of_le_one_right (mul_nonneg (abs_nonneg (z : ℝ)) h3n) h2
    nlinarith

noncomputable def conditionalSelectedProduct3 (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (x : Fin 3 → ℚ) : ℝ :=
  |(conditionalDualValue3 k₀ x (s 0) : ℝ)| *
    (padicNorm 2 (conditionalDualValue3 k₂ x (s 1)) : ℝ) *
    (padicNorm 3 (conditionalDualValue3 k₃ x (s 2)) : ℝ)

theorem conditional_selected_product_lower3 (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (m : IntegerTriple) (hm : m ≠ 0)
    (hn : conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) ≠ 0) :
    1 / (9 * (rothKernelRowHeight m : ℝ) ^ 2) ≤
      conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) := by
  let z₀ := conditionalDualInt3 k₀ m (s 0)
  let z₂ := conditionalDualInt3 k₂ m (s 1)
  let z₃ := conditionalDualInt3 k₃ m (s 2)
  have hp : conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) =
      |(z₀ : ℝ)| * (padicNorm 2 (z₂ : ℚ) : ℝ) * (padicNorm 3 (z₃ : ℚ) : ℝ) := by
    simp only [conditionalSelectedProduct3, conditionalDualInt3_value, Rat.cast_intCast]
    rfl
  rw [hp] at hn ⊢
  have hz₀ : z₀ ≠ 0 := by intro h; simp [h] at hn
  have hz₂ : z₂ ≠ 0 := by intro h; simp [h] at hn
  have hz₃ : z₃ ≠ 0 := by intro h; simp [h] at hn
  have hH := conditional_height_pos3 m hm
  have h0 : 1 ≤ |(z₀ : ℝ)| := by
    have hh : 1 ≤ z₀.natAbs := Int.natAbs_pos.mpr hz₀
    have hab : (z₀.natAbs : ℝ) = |(z₀ : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [← hab]
    exact_mod_cast hh
  have h2 := (conditional_integer_local_lower3 z₂ hz₂).1
  have h3 := (conditional_integer_local_lower3 z₃ hz₃).2
  have h2n : (0 : ℝ) ≤ padicNorm 2 (z₂ : ℚ) := by exact_mod_cast padicNorm.nonneg _
  have h3n : (0 : ℝ) ≤ padicNorm 3 (z₃ : ℚ) := by exact_mod_cast padicNorm.nonneg _
  have hu2 := conditionalDualInt3_height_bound k₂ m (s 1)
  have hu3 := conditionalDualInt3_height_bound k₃ m (s 2)
  have hl2 : 1 / (3 * (rothKernelRowHeight m : ℝ)) ≤ (padicNorm 2 (z₂ : ℚ) : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hu2 h2n]
  have hl3 : 1 / (3 * (rothKernelRowHeight m : ℝ)) ≤ (padicNorm 3 (z₃ : ℚ) : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hu3 h3n]
  have hmul := mul_le_mul hl2 hl3 (by positivity) h2n
  have hfull := mul_le_mul h0 hmul (by positivity) (abs_nonneg (z₀ : ℝ))
  calc
    _ = (1 : ℝ) * (1 / (3 * (rothKernelRowHeight m : ℝ)) *
        (1 / (3 * (rothKernelRowHeight m : ℝ)))) := by ring
    _ ≤ _ := by simpa [mul_assoc] using hfull


theorem conditional_reciprocal_last3 (s : Fin 3 → ℝ) (hs : ∀ i, 0 < s i)
    (horder : s 0 ≤ s 1) (D P x : ℝ) (hD : 0 < D) (hP : 0 < P) (hx : 0 < x)
    (hl : D / (6 * P) ≤ ∏ i, s i) (hsmall : s 1 ≤ x) :
    (s 2)⁻¹ ≤ 6 * P * x ^ 2 / D := by
  have hpair : s 0 * s 1 ≤ x ^ 2 := by
    nlinarith [mul_le_mul (horder.trans hsmall) hsmall (hs 1).le hx.le]
  have hl' : D ≤ (s 0 * s 1 * s 2) * (6 * P) := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      (div_le_iff₀ (by positivity : 0 < 6 * P)).mp hl
  have hm := mul_le_mul_of_nonneg_right hpair (mul_pos (by positivity : 0 < 6 * P) (hs 2)).le
  apply (le_div_iff₀ hD).mpr
  have hh : D / s 2 ≤ 6 * P * x ^ 2 :=
    (div_le_iff₀ (hs 2)).mpr (by nlinarith)
  have hh' := (div_le_iff₀ (hs 2)).mp hh
  have hd' : D ≤ (6 * P * x ^ 2) * s 2 := hh'
  have hsne := (hs 2).ne'
  apply (mul_le_mul_right (hs 2)).mp
  field_simp
  nlinarith

theorem conditional_actual_real_bound3
    (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (B : Basis (Fin 3) ℝ RealTriple)
    (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hreal : ∀ i, |((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
      (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℝ) *
        dualFrameRealLocalValue3 (retainedRealMatrix3 k₀)
          (fun j => (u j : IntegerTriple)) 2 i| ≤
      6 * ((qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) * (Q ^ c₀ i)⁻¹ *
        (successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 2)⁻¹)
    (hsmall : successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 1 < Q ^ (-delta))
    (i : Fin 3) :
    |((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
      (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℝ) *
        dualFrameRealLocalValue3 (retainedRealMatrix3 k₀)
          (fun j => (u j : IntegerTriple)) 2 i| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta) := by
  let G := qSourceLattice3 k₂ k₃ Q c₂ c₃
  let P := ∏ l : Fin 3, Q ^ c₀ l
  have ha (i : Fin 3) : 0 < Q ^ c₀ i := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  have hP : 0 < P := Finset.prod_pos (fun l _ => ha l)
  have hD : (0 : ℝ) < G.index := by
    rw [(qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    unfold qCongruenceIndex3
    positivity
  have hcov : ZLattice.covolume (lattice3 B) = (G.index : ℝ) := by
    rw [hB, (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    exact (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  have hvol : MeasureTheory.volume.real (parallelepipedBody3 (qSourceCoordinates3 k₀ Q c₀ hQ)) =
      8 * P := by
    rw [← qSourceBody3_eq_parallelepiped k₀ Q c₀ hQ]
    exact qSourceBody3_volume k₀ Q c₀ hQ
  have hl := source_minima_product_lower3 B (qSourceCoordinates3 k₀ Q c₀ hQ) G.index P hP hvol hcov
  obtain ⟨_, _, _, hs, horder, _⟩ := exists_successive_minima3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
  have hrec := conditional_reciprocal_last3 _ hs horder.1 G.index P (Q ^ (-delta)) hD hP
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) hl hsmall.le
  have he : (Q ^ (-delta)) ^ 2 = Q ^ (-2 * delta) := by
    rw [pow_two, ← Real.rpow_add (lt_trans zero_lt_one hQ)]
    congr 1
    ring
  rw [he] at hrec
  have hh := mul_le_mul_of_nonneg_left hrec
    (by positivity : 0 ≤ 6 * (G.index : ℝ) * (Q ^ c₀ i)⁻¹)
  apply (hreal i).trans
  calc
    _ ≤ _ := hh
    _ = _ := by field_simp; ring


theorem conditionalDualInt3_real_value (k : Fin 3) (z : IntegerTriple) (i : Fin 3) :
    sourceDualRealCoordinates3 k (integerTripleReal3 z) i = (conditionalDualInt3 k z i : ℝ) := by
  let A := retainedRealMatrix3 k
  let v : RealTriple := fun l => (conditionalDualInt3 k z l : ℝ)
  have hAv : A.transpose *ᵥ v = integerTripleReal3 z := by
    ext l
    fin_cases k <;> fin_cases l <;>
      simp [A, v, retainedRealMatrix3, conditionalDualInt3, retainedIntegerMatrix3,
        integerTripleReal3, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove]
  have hunit : IsUnit A.det := by
    dsimp [A]
    rw [retainedRealMatrix3_det]
    split_ifs <;> norm_num
  change (A⁻¹.transpose *ᵥ integerTripleReal3 z) i = v i
  rw [← hAv, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv A hunit, Matrix.transpose_one, Matrix.one_mulVec]

theorem conditional_scaled_real_value3 (k : Fin 3) (w : Fin 3 → IntegerTriple)
    (t : ℕ) (z : IntegerTriple)
    (hz : ∀ i, (t : ℚ) * dualFrameVector3 w 2 i = (z i : ℚ)) (i : Fin 3) :
    |(conditionalDualValue3 k (fun l => (z l : ℚ)) i : ℝ)| =
      |(t : ℝ) * dualFrameRealLocalValue3 (retainedRealMatrix3 k) w 2 i| := by
  rw [conditionalDualInt3_value, Rat.cast_intCast, ← conditionalDualInt3_real_value,
    sourceDualRealCoordinates3_apply]
  congr 1
  have hr (l : Fin 3) : (z l : ℝ) = (t : ℝ) * (dualFrameVector3 w 2 l : ℝ) := by
    exact_mod_cast (hz l).symm
  simp only [integerTripleReal3, LinearMap.coe_mk, AddHom.coe_mk, hr,
    dualFrameRealLocalValue3, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem conditionalDualValue3_scale (k : Fin 3) (q : ℚ) (x : Fin 3 → ℚ) (i : Fin 3) :
    conditionalDualValue3 k (fun l => q * x l) i = q * conditionalDualValue3 k x i := by
  simp only [conditionalDualValue3, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem conditionalSelectedProduct3_nonneg (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (x : Fin 3 → ℚ) : 0 ≤ conditionalSelectedProduct3 k₀ k₂ k₃ s x := by
  unfold conditionalSelectedProduct3
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (by exact_mod_cast padicNorm.nonneg _))
    (by exact_mod_cast padicNorm.nonneg _)

theorem conditionalSelectedProduct3_scale (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (q : ℚ) (x : Fin 3 → ℚ) :
    conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => q * x l) =
      (|((q : ℚ) : ℝ)| * (padicNorm 2 q : ℝ) * (padicNorm 3 q : ℝ)) *
        conditionalSelectedProduct3 k₀ k₂ k₃ s x := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  simp only [conditionalSelectedProduct3, conditionalDualValue3_scale, Rat.cast_mul,
    abs_mul, padicNorm.mul]
  ring

theorem conditional_primitive_product_le3 (k₀ k₂ k₃ : Fin 3)
    (s : Fin 3 → Fin 3) (g : ℤ) (hg : g ≠ 0) (z m : IntegerTriple)
    (hz : ∀ i, z i = g * m i) :
    conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) ≤
      conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => (z l : ℚ)) := by
  have he : (fun l => (z l : ℚ)) = fun l => (g : ℚ) * (m l : ℚ) := by
    ext l
    rw [hz l, Int.cast_mul]
  rw [he, conditionalSelectedProduct3_scale]
  have hl := rothInteger_three_place_lower g hg
  change (1 : ℝ) ≤ |(g : ℝ)| * (padicNorm 2 (g : ℚ) : ℝ) * (padicNorm 3 (g : ℚ) : ℝ) at hl
  have hh := mul_le_mul_of_nonneg_right hl
    (conditionalSelectedProduct3_nonneg k₀ k₂ k₃ s (fun l => (m l : ℚ)))
  simpa using hh

theorem conditional_primitive_padic_bound3 (p : ℕ) [Fact p.Prime]
    (k : Fin 3) (g : ℤ) (hg : g ≠ 0) (z m : IntegerTriple)
    (hz : ∀ i, z i = g * m i) (i : Fin 3) (b : ℝ)
    (hb : (padicNorm p (conditionalDualValue3 k (fun l => (z l : ℚ)) i) : ℝ) ≤ b) :
    (padicNorm p (conditionalDualValue3 k (fun l => (m l : ℚ)) i) : ℝ) ≤
      b / (padicNorm p (g : ℚ) : ℝ) := by
  have he : (fun l => (z l : ℚ)) = fun l => (g : ℚ) * (m l : ℚ) := by
    ext l
    rw [hz l, Int.cast_mul]
  have hgp : (0 : ℝ) < padicNorm p (g : ℚ) := by
    have hgpQ : 0 < padicNorm p (g : ℚ) := lt_of_le_of_ne (padicNorm.nonneg _)
      (Ne.symm (padicNorm.nonzero (by exact_mod_cast hg : (g : ℚ) ≠ 0)))
    exact_mod_cast hgpQ
  rw [he, conditionalDualValue3_scale, padicNorm.mul, Rat.cast_mul] at hb
  apply (le_div_iff₀ hgp).mpr
  nlinarith


theorem conditional_sum_others3 (c : Fin 3 → ℝ) (i : Fin 3) :
    c (i.succAbove 0) + c (i.succAbove 1) = (∑ j, c j) - c i := by
  fin_cases i <;> simp [Fin.sum_univ_succ, Fin.succAbove] <;> ring

theorem conditional_selected_product_upper3
    (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hd : 0 < delta)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (s : Fin 3 → Fin 3) (hweight : -(3 * delta) / 4 ≤ c₀ (s 0) + c₂ (s 1) + c₃ (s 2))
    (z : IntegerTriple)
    (hreal : ∀ i, |(conditionalDualValue3 k₀ (fun l => (z l : ℚ)) i : ℝ)| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta))
    (h2 : ∀ i, (padicNorm 2 (conditionalDualValue3 k₂ (fun l => (z l : ℚ)) i) : ℝ) ≤
      Q ^ (c₂ (i.succAbove 0) + c₂ (i.succAbove 1)))
    (h3 : ∀ i, (padicNorm 3 (conditionalDualValue3 k₃ (fun l => (z l : ℚ)) i) : ℝ) ≤
      Q ^ (c₃ (i.succAbove 0) + c₃ (i.succAbove 1))) :
    conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => (z l : ℚ)) ≤ 36 * Q ^ (-delta / 4) := by
  have hp := lt_trans zero_lt_one hQ
  have he : (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ (s 0))⁻¹ * Q ^ (-2 * delta) *
      Q ^ (c₂ ((s 1).succAbove 0) + c₂ ((s 1).succAbove 1)) *
      Q ^ (c₃ ((s 2).succAbove 0) + c₃ ((s 2).succAbove 1)) =
        Q ^ (-2 * delta - (c₀ (s 0) + c₂ (s 1) + c₃ (s 2))) := by
    rw [← Real.rpow_sum_of_pos hp, ← Real.rpow_neg hp.le,
      conditional_sum_others3, conditional_sum_others3]
    rw [← Real.rpow_add hp, ← Real.rpow_add hp, ← Real.rpow_add hp, ← Real.rpow_add hp]
    congr 1
    simp only [Finset.sum_add_distrib] at hb
    linarith
  have hn2 : (0 : ℝ) ≤ padicNorm 2 (conditionalDualValue3 k₂ (fun l => (z l : ℚ)) (s 1)) := by
    exact_mod_cast padicNorm.nonneg _
  have hn3 : (0 : ℝ) ≤ padicNorm 3 (conditionalDualValue3 k₃ (fun l => (z l : ℚ)) (s 2)) := by
    exact_mod_cast padicNorm.nonneg _
  have hr0 : 0 ≤ 36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ (s 0))⁻¹ * Q ^ (-2 * delta) := by
    positivity
  have hr2 : 0 ≤ Q ^ (c₂ ((s 1).succAbove 0) + c₂ ((s 1).succAbove 1)) :=
    (Real.rpow_pos_of_pos hp _).le
  have hmul := mul_le_mul (mul_le_mul (hreal (s 0)) (h2 (s 1)) hn2 hr0)
    (h3 (s 2)) hn3 (mul_nonneg hr0 hr2)
  have hbound := Real.rpow_le_rpow_of_exponent_le hQ.le
    (show -2 * delta - (c₀ (s 0) + c₂ (s 1) + c₃ (s 2)) ≤ -delta / 4 by linarith)
  calc
    _ ≤ _ := hmul
    _ = 36 * Q ^ (-2 * delta - (c₀ (s 0) + c₂ (s 1) + c₃ (s 2))) := by
      rw [← he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

theorem conditional_height_lower_power3 (Q delta H : ℝ) (hQ : 1 < Q)
    (hH : 0 < H)
    (hbound : 1 / (9 * H ^ 2) ≤ 36 * Q ^ (-delta / 4)) :
    Q ^ (delta / 8) ≤ 18 * H := by
  have hp := lt_trans zero_lt_one hQ
  have hpow : 0 < Q ^ (delta / 4) := Real.rpow_pos_of_pos hp _
  have hneg : Q ^ (-delta / 4) = (Q ^ (delta / 4))⁻¹ := by
    rw [show -delta / 4 = -(delta / 4) by ring, Real.rpow_neg hp.le]
  rw [hneg] at hbound
  have hh := (div_le_iff₀ (by positivity : 0 < 9 * H ^ 2)).mp hbound
  have hh' := mul_le_mul_of_nonneg_right hh hpow.le
  have hcancel : (36 * (Q ^ (delta / 4))⁻¹ * (9 * H ^ 2)) * Q ^ (delta / 4) =
      324 * H ^ 2 := by field_simp; ring
  rw [hcancel] at hh'
  have hsquare : (Q ^ (delta / 8)) ^ 2 = Q ^ (delta / 4) := by
    rw [pow_two, ← Real.rpow_add hp]
    congr 1
    ring
  have hpos : 0 < Q ^ (delta / 8) := Real.rpow_pos_of_pos hp _
  nlinarith

theorem conditional_height_lower_absorb3 (Q delta H : ℝ) (hQ : 1 < Q)
    (hd : 0 < delta) (hcut : (18 : ℝ) ^ (16 / delta) ≤ Q)
    (hl : Q ^ (delta / 8) ≤ 18 * H) :
    Q ^ (delta / 16) ≤ H := by
  have hp := lt_trans zero_lt_one hQ
  have hc : 18 ≤ Q ^ (delta / 16) := by
    calc
      (18 : ℝ) = ((18 : ℝ) ^ (16 / delta)) ^ (delta / 16) := by
        rw [← Real.rpow_mul (by norm_num)]
        have he : (16 / delta) * (delta / 16) = 1 := by field_simp
        rw [he, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hcut (by positivity)
  have he : Q ^ (delta / 8) = (Q ^ (delta / 16)) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hp]
    congr 1
    ring
  rw [he] at hl
  nlinarith


theorem conditionalDualInt3_reconstruct (k : Fin 3) (z : IntegerTriple) (l : Fin 3) :
    (z l : ℝ) = ∑ i : Fin 3, retainedRealMatrix3 k i l * (conditionalDualInt3 k z i : ℝ) := by
  fin_cases k <;> fin_cases l <;>
    simp [retainedRealMatrix3, conditionalDualInt3, retainedIntegerMatrix3,
      Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove]

theorem conditional_primitive_height_bound3 (k : Fin 3) (g : ℤ) (hg : g ≠ 0)
    (z m : IntegerTriple) (hz : ∀ i, z i = g * m i) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i, |(conditionalDualValue3 k (fun l => (z l : ℚ)) i : ℝ)| ≤ M) :
    (rothKernelRowHeight m : ℝ) ≤ 3 * M := by
  have hgabs : (1 : ℝ) ≤ |(g : ℝ)| := by
    have h : 1 ≤ g.natAbs := Int.natAbs_pos.mpr hg
    have he : (g.natAbs : ℝ) = |(g : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [← he]
    exact_mod_cast h
  have hcoeff (i l : Fin 3) : |retainedRealMatrix3 k i l| ≤ 1 := by
    fin_cases k <;> fin_cases i <;> fin_cases l <;>
      simp [retainedRealMatrix3, retainedIntegerMatrix3, Pi.single_apply, Fin.succAbove] <;>
      split_ifs <;> norm_num
  have hm (l : Fin 3) : |(m l : ℝ)| ≤ 3 * M := by
    have hzbound : |(z l : ℝ)| ≤ 3 * M := by
      rw [conditionalDualInt3_reconstruct k z l]
      calc
        _ ≤ ∑ i : Fin 3, |retainedRealMatrix3 k i l * (conditionalDualInt3 k z i : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 3, M := by
          apply Finset.sum_le_sum
          intro i _
          have hb' := hb i
          rw [conditionalDualInt3_value, Rat.cast_intCast] at hb'
          rw [abs_mul]
          exact (mul_le_mul (hcoeff i l) hb' (abs_nonneg _) (by norm_num)).trans_eq (one_mul M)
        _ = 3 * M := by simp
    rw [hz l, Int.cast_mul, abs_mul] at hzbound
    nlinarith [abs_nonneg (m l : ℝ)]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => (m i).natAbs)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
  have he : rothKernelRowHeight m = (m i).natAbs := by
    apply le_antisymm
    · exact Finset.sup_le (fun j hj => hmax j hj)
    · exact Finset.le_sup (f := fun j : Fin 3 => (m j).natAbs) hi
  rw [he]
  have hab : ((m i).natAbs : ℝ) = |(m i : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hab]
  exact hm i

theorem conditional_upper_height_power3 (k : Fin 3) (Q delta : ℝ) (c₀ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hd : 0 < delta) (hc₀ : ∀ i, |c₀ i| ≤ 1) (hcut : 108 ≤ Q)
    (g : ℤ) (hg : g ≠ 0) (z m : IntegerTriple) (hz : ∀ i, z i = g * m i)
    (hb : ∀ i, |(conditionalDualValue3 k (fun l => (z l : ℚ)) i : ℝ)| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta)) :
    (rothKernelRowHeight m : ℝ) ≤ Q ^ (9 : ℝ) := by
  have hp := lt_trans zero_lt_one hQ
  have hP : (∏ i : Fin 3, Q ^ c₀ i) ≤ Q ^ (3 : ℕ) := by
    calc
      _ ≤ ∏ _i : Fin 3, Q := Finset.prod_le_prod
        (fun i _ => (Real.rpow_pos_of_pos hp _).le)
        (fun i _ => (Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc₀ i)).2).trans_eq
          (Real.rpow_one Q))
      _ = _ := by simp
  have hi (i : Fin 3) : (Q ^ c₀ i)⁻¹ ≤ Q := by
    rw [← Real.rpow_neg hp.le]
    exact (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith [(abs_le.mp (hc₀ i)).1])).trans_eq
      (Real.rpow_one Q)
  have hdQ : Q ^ (-2 * delta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ.le (by linarith)
  have hheight : (rothKernelRowHeight m : ℝ) ≤ 3 * (36 * Q ^ (4 : ℕ)) := by
    apply conditional_primitive_height_bound3 k g hg z m hz (36 * Q ^ (4 : ℕ)) (by positivity)
    intro i
    apply (hb i).trans
    have hbase := mul_le_mul (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 36))
      (hi i) (inv_nonneg.mpr (Real.rpow_pos_of_pos hp _).le) (by positivity : 0 ≤ 36 * Q ^ (3 : ℕ))
    have hfull := mul_le_mul hbase hdQ (Real.rpow_pos_of_pos hp _).le
      (by positivity : 0 ≤ 36 * Q ^ (3 : ℕ) * Q)
    nlinarith
  change (rothKernelRowHeight m : ℝ) ≤ Q ^ ((9 : ℕ) : ℝ)
  rw [Real.rpow_natCast]
  calc
    _ ≤ 108 * Q ^ (4 : ℕ) := by nlinarith
    _ ≤ Q * Q ^ (4 : ℕ) := mul_le_mul_of_nonneg_right hcut (pow_nonneg hp.le _)
    _ = Q ^ (5 : ℕ) := by ring
    _ ≤ Q ^ (9 : ℕ) := pow_le_pow_right₀ hQ.le (by decide)


theorem conditional_normal_height3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (S : Set (Fin 3 → Fin 3)) (_hS : S.Nonempty) :
    ∃ C1 C2 C3 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q), C3 < Q →
      ∀ c₀ c₂ c₃ : Fin 3 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s ∈ S, -(3 * delta) / 4 ≤ c₀ (s 0) + c₂ (s 1) + c₃ (s 2)) →
        ∀ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃),
          lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 →
          LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) →
          (∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
            (integerTripleReal3 (u j : IntegerTriple)) =
              successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) →
          dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u ≤ 6 →
          successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 1 < Q ^ (-delta) →
          (∃ s ∈ S, conditionalSelectedProduct3 k₀ k₂ k₃ s
            (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ≠ 0) →
          ∃ (z m : IntegerTriple) (g : ℤ),
            g ≠ 0 ∧ m ≠ 0 ∧
            (∀ i, ((dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u *
              (qSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
                dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i = (z i : ℚ)) ∧
            (∀ i, z i = g * m i) ∧ Ideal.span (Set.range m) = ⊤ ∧
            Finset.univ.gcd (fun i => (m i).natAbs) = 1 ∧
            (∃ r : ℚ, r ≠ 0 ∧ (fun i => (m i : ℚ)) =
              r • dualFrameVector3 (fun j => (u j : IntegerTriple)) 2) ∧
            Submodule.span ℚ ({fun i => (m i : ℚ)} : Set (Fin 3 → ℚ)) =
              Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} ∧
            (∀ j : Fin 2, (∑ i : Fin 3, m i * ((u j.castSucc : IntegerTriple) i)) = 0) ∧
            dualFrameRelativeIndex3 (qSourceLattice3 k₂ k₃ Q c₂ c₃) u ≤ 6 ∧
            Q ^ C1 ≤ (rothKernelRowHeight m : ℝ) ∧ (rothKernelRowHeight m : ℝ) ≤ Q ^ C2 := by
  refine ⟨delta / 16, 9, max 108 ((18 : ℝ) ^ (16 / delta)), by positivity,
    by norm_num, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_max_left _ _), ?_⟩
  intro Q hQ hcut c₀ c₂ c₃ hc₀ hc₂' hc₃' hbalance hweights B u hB hu hatt hJ hsmall hnonzero
  have hc₂ := fun i => (hc₂' i).2
  have hc₃ := fun i => (hc₃' i).2
  have hp := lt_trans zero_lt_one hQ
  let G := qSourceLattice3 k₂ k₃ Q c₂ c₃
  obtain ⟨c⟩ : Nonempty (Basis (Fin 3) ℤ G) := mixedCongruence3_has_basis _ _ _ _
  have hD : (0 : ℝ) < G.index := by
    rw [(qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    unfold qCongruenceIndex3
    positivity
  have hDnat : G.index ≠ 0 := by exact_mod_cast hD.ne'
  have ha (i : Fin 3) : 0 < Q ^ c₀ i := Real.rpow_pos_of_pos hp _
  have hP : 0 < ∏ i : Fin 3, Q ^ c₀ i := Finset.prod_pos (fun i _ => ha i)
  have hcov : ZLattice.covolume (lattice3 B) = (G.index : ℝ) := by
    rw [hB, (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    exact (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  have hvol : MeasureTheory.volume.real (parallelepipedBody3 (qSourceCoordinates3 k₀ Q c₀ hQ)) =
      8 * ∏ i : Fin 3, Q ^ c₀ i := by
    rw [← qSourceBody3_eq_parallelepiped k₀ Q c₀ hQ]
    exact qSourceBody3_volume k₀ Q c₀ hQ
  have hprod : (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) *
      (∏ i : Fin 3, Q ^ c₀ i) ≤ (G.index : ℝ) := by
    have h := successive_minima3_parallelepiped_volume_upper B (qSourceCoordinates3 k₀ Q c₀ hQ)
    rw [hvol, hcov] at h
    nlinarith
  obtain ⟨_, _, _, hs, _, _⟩ := exists_successive_minima3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
  have hpoint : ∀ j i, |∑ l : Fin 3, retainedRealMatrix3 k₀ i l *
      ((u j : IntegerTriple) l : ℝ)| ≤
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j * Q ^ c₀ i := by
    intro j i
    have h := qSource_arch_bound k₀ Q c₀ hQ (integerTripleReal3 (u j : IntegerTriple)) i
    rw [hatt] at h
    exact h
  have hreal (i : Fin 3) := dualFrame3_source_real_bound G c u hu (retainedRealMatrix3 k₀)
    (by rw [retainedRealMatrix3_det]; split_ifs <;> norm_num) _ _ hs ha hpoint hprod i 2
  obtain ⟨z, m, g, hz, hg, hm, hgm, hprim, hgcd, hmq, horth⟩ :=
    conditional_actual_primitive_normal3 G c u hu
  have hrealz (i : Fin 3) : |(conditionalDualValue3 k₀ (fun l => (z l : ℚ)) i : ℝ)| ≤
      36 * (∏ l : Fin 3, Q ^ c₀ l) * (Q ^ c₀ i)⁻¹ * Q ^ (-2 * delta) := by
    rw [conditional_scaled_real_value3 k₀ (fun j => (u j : IntegerTriple)) _ z hz]
    exact conditional_actual_real_bound3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ hc₂ hc₃ B u hB hreal hsmall i
  have hfinite := conditional_actual_finite_bounds3 k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃ c u hu
  dsimp only at hfinite
  have hez : (fun l => ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) *
      dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l) = fun l => (z l : ℚ) := funext hz
  rw [hez] at hfinite
  obtain ⟨s, hsS, hsnonzero⟩ := hnonzero
  have hzproduct := conditional_selected_product_upper3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ hd
    hbalance s (hweights s hsS) z hrealz hfinite.1 hfinite.2
  let q : ℚ := ((dualFrameRelativeIndex3 G u * G.index : ℕ) : ℚ) / g
  have hq : q ≠ 0 := div_ne_zero
    (by exact_mod_cast mul_ne_zero (Nat.ne_of_gt (dualFrameRelativeIndex3_pos G c u hu)) hDnat)
    (by exact_mod_cast hg)
  have hmcast : (fun i => (m i : ℚ)) = q • dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 :=
    funext hmq
  have hline : Submodule.span ℚ ({fun i => (m i : ℚ)} : Set (Fin 3 → ℚ)) =
      Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} := by
    rw [hmcast]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hq) _
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hq2 : (padicNorm 2 q : ℝ) ≠ 0 := by exact_mod_cast padicNorm.nonzero hq
  have hq3 : (padicNorm 3 q : ℝ) ≠ 0 := by exact_mod_cast padicNorm.nonzero hq
  have hmproduct : conditionalSelectedProduct3 k₀ k₂ k₃ s (fun l => (m l : ℚ)) ≠ 0 := by
    rw [hmcast]
    change conditionalSelectedProduct3 k₀ k₂ k₃ s
      (fun l => q * dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 l) ≠ 0
    rw [conditionalSelectedProduct3_scale]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (abs_ne_zero.mpr hqreal) hq2) hq3) hsnonzero
  have hlower := conditional_selected_product_lower3 k₀ k₂ k₃ s m hm hmproduct
  have hupper := conditional_primitive_product_le3 k₀ k₂ k₃ s g hg z m hgm
  have hl := conditional_height_lower_power3 Q delta (rothKernelRowHeight m) hQ
    (conditional_height_pos3 m hm) (hlower.trans (hupper.trans hzproduct))
  have hfinalLower := conditional_height_lower_absorb3 Q delta (rothKernelRowHeight m) hQ hd
    ((le_max_right _ _).trans hcut.le) hl
  have hfinalUpper := conditional_upper_height_power3 k₀ Q delta c₀ hQ hd hc₀
    ((le_max_left _ _).trans hcut.le) g hg z m hgm hrealz
  exact ⟨z, m, g, hg, hm, hz, hgm, hprim, hgcd, ⟨q, hq, hmcast⟩, hline, horth, hJ,
    hfinalLower, hfinalUpper⟩


theorem conditionalDualValue3_real_cast (k : Fin 3) (x : Fin 3 → ℚ) (i : Fin 3) :
    (conditionalDualValue3 k x i : ℝ) =
      ∑ l : Fin 3, (retainedRealMatrix3 k)⁻¹ l i * (x l : ℝ) := by
  have hmap : (conditionalRationalMatrix3 k).map (Rat.castHom ℝ) = retainedRealMatrix3 k := by
    ext l j
    simp [conditionalRationalMatrix3, retainedRealMatrix3]
  have hdet : ((conditionalRationalMatrix3 k).det : ℝ) = (retainedRealMatrix3 k).det := by
    rw [← hmap]
    exact (Rat.castHom ℝ).map_det _
  have hentry (l j : Fin 3) : (((conditionalRationalMatrix3 k)⁻¹ l j : ℚ) : ℝ) =
      (retainedRealMatrix3 k)⁻¹ l j := by
    rw [Matrix.inv_def, Matrix.inv_def]
    change ((Ring.inverse (conditionalRationalMatrix3 k).det *
      (conditionalRationalMatrix3 k).adjugate l j : ℚ) : ℝ) =
        Ring.inverse (retainedRealMatrix3 k).det * (retainedRealMatrix3 k).adjugate l j
    rw [Ring.inverse_eq_inv, Ring.inverse_eq_inv, Rat.cast_mul, Rat.cast_inv, hdet]
    congr 1
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M l j)
      ((Rat.castHom ℝ).map_adjugate (conditionalRationalMatrix3 k))
    simpa only [hmap, Matrix.map_apply] using h
  simp only [conditionalDualValue3, Rat.cast_sum, Rat.cast_mul, hentry]

end JSP000334
