import SubspaceBridge.SchlickeweiAuxiliaryLine6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiReference6
open SourceReadiness6 SourceHeightBounds6 SourceRelativeIndex6 SchlickeweiDualVanishing6
open SchlickeweiEquation4106 SchlickeweiEquation4116 SchlickeweiEquation4126
open SchlickeweiSatz51Selected6 SchlickeweiIntegerPairing6 SchlickeweiAuxiliaryLine6
open SourceMixed6 Auxiliary6.SourceExpansion

theorem signed_cofactor_norm6 {K : Type*} [NormedField K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (N : ℕ) (hN : N = v.det.natAbs) (i : Fin 6) :
    ‖dualFormValue6 B (fun k => (rawNormal6 v k : ℚ)) i‖ =
      ‖∑ k, ((N : K) * algebraMap ℚ K (dualVector6 v hv k)) * B⁻¹.transpose i k‖ := by
  have hc (k : Fin 6) : algebraMap ℚ K (rawNormal6 v k : ℚ) =
      (v.det : K) * algebraMap ℚ K (dualVector6 v hv k) := by
    simpa only [map_mul, map_intCast] using
      congrArg (algebraMap ℚ K) (last_dual_adjugate6 v hv k)
  have hleft : dualFormValue6 B (fun k => (rawNormal6 v k : ℚ)) i =
      (v.det : K) * dualFormValue6 B (dualVector6 v hv) i := by
    simp only [dualFormValue6, hc, Finset.mul_sum, mul_assoc]
  have hright : (∑ k, ((N : K) * algebraMap ℚ K (dualVector6 v hv k)) * B⁻¹.transpose i k) =
      (N : K) * dualFormValue6 B (dualVector6 v hv) i := by
    simp only [dualFormValue6, Finset.mul_sum, mul_assoc]
  rw [hleft, hright, norm_mul, norm_mul, hN, norm_natAbs_cast6]

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

def sourceReference6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) : Fin 6 → ℤ :=
  rawNormal6 (Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ)))

theorem source_reference_nonzero6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) :
    sourceReference6 R q1 ≠ 0 :=
  rawNormal6_nonzero _ (sourceFrameIndependent6 R q1)

theorem source_reference_line6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) :
    Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} =
      Submodule.span ℚ {fun i => (R.M q1 i : ℚ)} := by
  obtain ⟨hg, hscale, _⟩ := source_signed_minors6 R q1
  let g : ℤ := ∑ k, R.a q1 k * sourceReference6 R q1 k
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have he : (fun i => (sourceReference6 R q1 i : ℚ)) =
      (g : ℚ) • (fun i => (R.M q1 i : ℚ)) := by
    funext i
    change (sourceReference6 R q1 i : ℚ) = (g : ℚ) * (R.M q1 i : ℚ)
    have hi : sourceReference6 R q1 i = g * R.M q1 i := hscale i
    exact_mod_cast hi
  rw [he]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hgQ) _


theorem source_reference_signed_dual6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V) (i : Fin 6) :
    (sourceReference6 R q1 i : ℚ) =
      ((Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ))).det : ℚ) *
        dualVector6 (fun j => (R.w q1 j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q1) i := by
  let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ))
  have hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)) := sourceFrameIndependent6 R q1
  have hraw := last_dual_adjugate6 v hv i
  have he := source_last_dual_eq6 R q1 hv
  rw [he] at hraw
  simpa only [sourceReference6, v] using hraw

theorem source_reference_norm6 {K : Type*} [NormedField K] [Algebra ℚ K]
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V)
    (B : Matrix (Fin 6) (Fin 6) K) (i : Fin 6) :
    let G := directCompoundGroup42 A2 A3 q1.val c2 c3
    let N := frameRelativeIndex G (R.w q1) * G.index
    ‖dualFormValue6 B (fun k => (sourceReference6 R q1 k : ℚ)) i‖ =
      ‖∑ k, ((N : K) * algebraMap ℚ K
        (dualVector6 (fun j => (R.w q1 j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q1) k)) *
          B⁻¹.transpose i k‖ := by
  dsimp only
  let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ))
  have hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)) := sourceFrameIndependent6 R q1
  have hN := (source_integer_scale6 R q1).2.1
  let G := directCompoundGroup42 A2 A3 q1.val c2 c3
  let N : ℕ := frameRelativeIndex G (R.w q1) * G.index
  have hn : N = v.det.natAbs := by
    with_reducible exact hN
  have h := signed_cofactor_norm6 B v hv N hn i
  have he := source_last_dual_eq6 R q1 hv
  rw [he] at h
  simpa only [sourceReference6, v, N, G] using h


theorem source_reference_real_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (q1 : V) (i : Fin 6) :
    ‖dualFormValue6 (compound L) (fun k => (sourceReference6 R q1 k : ℚ)) i‖ ≤
      120 * ((q1.val ^ (11 : ℕ)) ^ (R.c 0 i))⁻¹ *
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q1.val c2 c3)) *
          (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta) := by
  have hn := source_reference_norm6 R q1 (compound L) i
  have hs := (source_integer_scale6 R q1).2.2
  have hb := source_equation4106 R h2 h3 hLdet q1 i
  apply hn.trans_le
  rw [hs]
  with_reducible exact hb


theorem source_reference_p2_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 : V) (i : Fin 6) :
    ‖dualFormValue6 (finiteMatrix 2 A2) (fun k => (sourceReference6 R q1 k : ℚ)) i‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 2 q1.val c2 (i.succAbove k)) := by
  have hn := source_reference_norm6 R q1 (finiteMatrix 2 A2) i
  have hb := (source_equation4116 R h2 h3 q1 i).2.2.2.2.1
  apply hn.trans_le
  with_reducible exact hb


theorem source_reference_p3_bound6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 : V) (i : Fin 6) :
    ‖dualFormValue6 (finiteMatrix 3 A3) (fun k => (sourceReference6 R q1 k : ℚ)) i‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 3 q1.val c3 (i.succAbove k)) := by
  have hn := source_reference_norm6 R q1 (finiteMatrix 3 A3) i
  have hb := (source_equation4116 R h2 h3 q1 i).2.2.2.2.2
  apply hn.trans_le
  with_reducible exact hb

theorem source_reference_auxiliary6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (q1 : V)
    (hsmall : 120 * (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta) ≤ 1) :
    sourceAuxiliaryInteger6 R q1 (sourceReference6 R q1) := by
  refine ⟨?_, source_reference_p2_bound6 R h2 h3 q1, source_reference_p3_bound6 R h2 h3 q1⟩
  intro i
  have hQ : 0 < q1.val ^ (11 : ℕ) := lt_trans zero_lt_one (source_parameter_gt_one6 R q1)
  have hd : 0 < ZLattice.covolume (integerRealImage
      (directCompoundGroup42 A2 A3 q1.val c2 c3)) := (source_frame_normalization6 R q1).2.2.2.2.2
  have hA : 0 < (q1.val ^ (11 : ℕ)) ^ (R.c 0 i) := Real.rpow_pos_of_pos hQ _
  calc
    _ ≤ 120 * ((q1.val ^ (11 : ℕ)) ^ (R.c 0 i))⁻¹ *
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q1.val c2 c3)) *
          (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta) := source_reference_real_bound6 R h2 h3 hLdet q1 i
    _ = (((q1.val ^ (11 : ℕ)) ^ (R.c 0 i))⁻¹ *
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q1.val c2 c3))) *
          (120 * (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta)) := by ring
    _ ≤ (((q1.val ^ (11 : ℕ)) ^ (R.c 0 i))⁻¹ *
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q1.val c2 c3))) * 1 :=
      mul_le_mul_of_nonneg_left hsmall (mul_nonneg (inv_nonneg.mpr hA.le) hd.le)
    _ = _ := by rw [mul_one, div_eq_mul_inv]; ring


theorem reference_smallness_cutoff6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    ∃ T : ℝ, 1 < T ∧ ∀ q1 : V, T < q1.val →
      120 * (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta) ≤ 1 := by
  obtain ⟨T, hT, hcut⟩ := pairing_power_cutoff6 20 (5 * R.delta) (by norm_num)
    (mul_pos (by norm_num) R.delta_pos)
  refine ⟨T, hT, ?_⟩
  intro q1 hq1
  have hle : q1.val ≤ q1.val ^ (11 : ℕ) :=
    le_self_pow₀ (hQV q1.val q1.property).le (by decide)
  have h := (hcut _ (lt_of_lt_of_le hq1 hle) (source_parameter_gt_one6 R q1)).le
  simpa only [show (6 : ℝ) * 20 = 120 by norm_num,
    show -(5 * R.delta) = -5 * R.delta by ring] using h

theorem source_fixed_reference6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) :
    ∃ (Bzero Bpoint T : ℝ) (q1 : V),
      max Bzero (max Bpoint T) < q1.val ∧
      (120 * (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta) ≤ 1) ∧
      sourceReference6 R q1 ≠ 0 ∧
      sourceAuxiliaryInteger6 R q1 (sourceReference6 R q1) ∧
      (Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} =
        Submodule.span ℚ {fun i => (R.M q1 i : ℚ)}) ∧
      (∀ q : V, Bpoint < q.val → ∀ y : Fin 6 → ℤ, sourceAuxiliaryInteger6 R q y →
        (fun i => (y i : ℚ)) ∈ Submodule.span ℚ {fun i => (R.M q i : ℚ)}) ∧
      ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
        publishedDualProduct6 A2 A3 L
          (dualVector6 (fun j => (R.w q1 j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q1)) s = 0 := by
  obtain ⟨Bzero, _, hdual⟩ := source_equation4126 R h2 h3
  obtain ⟨Bpoint, _, _, hpoint⟩ := source_auxiliary_line6 R h2 h3
  obtain ⟨T, _, hsmall⟩ := reference_smallness_cutoff6 R
  obtain ⟨q1, hq1⟩ := SourceHeightUpper6.unbounded_original_q_cutoff6 V R.unbounded
    Bzero (max Bpoint T)
  have hz : Bzero < q1.val := lt_of_le_of_lt (le_max_left _ _) hq1
  have ht : T < q1.val := lt_of_le_of_lt
    ((le_max_right Bpoint T).trans (le_max_right Bzero (max Bpoint T))) hq1
  obtain ⟨a, ha, hf, hs, hi, hprod⟩ := hdual q1 hz
  refine ⟨Bzero, Bpoint, T, q1, hq1, hsmall q1 ht,
    source_reference_nonzero6 R q1,
    source_reference_auxiliary6 R h2 h3 hLdet q1 (hsmall q1 ht),
    source_reference_line6 R q1, hpoint, ?_⟩
  intro s hs
  exact (hprod s hs).2


def finiteSupport6 (p : ℕ) [Fact p.Prime] (B : Matrix (Fin 6) (Fin 6) ℚ_[p])
    (b : Fin 6 → ℤ) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => dualFormValue6 B (fun k => (b k : ℚ)) i ≠ 0)

theorem finiteSupport_nonempty6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (hB : IsUnit B) (b : Fin 6 → ℤ) (hb : b ≠ 0) :
    (finiteSupport6 p B b).Nonempty := by
  by_contra h
  have hz : ∀ i, dualFormValue6 B (fun k => (b k : ℚ)) i = 0 := by
    intro i
    by_contra hi
    exact h ⟨i, by simp only [finiteSupport6, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
  have hvec : B⁻¹.transpose *ᵥ (fun k => (b k : ℚ_[p])) = 0 := by
    funext i
    exact (native_dual_coordinates6 p B b i).symm.trans (hz i)
  have hinv : IsUnit B⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hB
  have ht : IsUnit B⁻¹.transpose := (Matrix.isUnit_transpose B⁻¹).mpr hinv
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr ht
  have hb0 : (fun k => (b k : ℚ_[p])) = 0 := hi (hvec.trans (Matrix.mulVec_zero _).symm)
  apply hb
  funext i
  have he : (b i : ℚ_[p]) = 0 := congrFun hb0 i
  change b i = 0
  exact_mod_cast he

theorem source_reference_supports6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q1 : V) :
    (finiteSupport6 2 (finiteMatrix 2 A2) (sourceReference6 R q1)).Nonempty ∧
      (finiteSupport6 3 (finiteMatrix 3 A3) (sourceReference6 R q1)).Nonempty := by
  constructor
  · apply finiteSupport_nonempty6 2 _ _ _ (source_reference_nonzero6 R q1)
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [finite_matrix_det_one6 2 A2 h2]
    exact isUnit_one
  · apply finiteSupport_nonempty6 3 _ _ _ (source_reference_nonzero6 R q1)
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [finite_matrix_det_one6 3 A3 h3]
    exact isUnit_one


theorem dual_scalar_value6 {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (a : ℚ) (D : Fin 6 → ℚ) (i : Fin 6) :
    dualFormValue6 B (a • D) i = algebraMap ℚ K a * dualFormValue6 B D i := by
  simp only [dualFormValue6, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem published_product_scalar_zero6
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (a : ℚ) (D : Fin 6 → ℚ) (s : MixedIndex6)
    (hz : publishedDualProduct6 A2 A3 L D s = 0) :
    publishedDualProduct6 A2 A3 L (a • D) s = 0 := by
  simp only [publishedDualProduct6, dual_scalar_value6, norm_mul]
  calc
    _ = (‖algebraMap ℚ ℝ a‖ * ‖algebraMap ℚ ℚ_[2] a‖ * ‖algebraMap ℚ ℚ_[3] a‖) *
        publishedDualProduct6 A2 A3 L D s := by unfold publishedDualProduct6; ring
    _ = 0 := by rw [hz, mul_zero]

theorem source_reference_product_zero6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q1 : V)
    (s : MixedIndex6)
    (hz : publishedDualProduct6 A2 A3 L
      (dualVector6 (fun j => (R.w q1 j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q1)) s = 0) :
    publishedDualProduct6 A2 A3 L (fun k => (sourceReference6 R q1 k : ℚ)) s = 0 := by
  have he : (fun k => (sourceReference6 R q1 k : ℚ)) =
      ((Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ))).det : ℚ) •
        dualVector6 (fun j => (R.w q1 j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q1) := by
    funext k
    exact source_reference_signed_dual6 R q1 k
  rw [he]
  exact published_product_scalar_zero6 A2 A3 L _ _ s hz


theorem source_reference_selected6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) :
    ∃ (Bzero Bpoint T : ℝ) (q1 : V),
      max Bzero (max Bpoint T) < q1.val ∧
      sourceReference6 R q1 ≠ 0 ∧
      sourceAuxiliaryInteger6 R q1 (sourceReference6 R q1) ∧
      (Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} =
        Submodule.span ℚ {fun i => (R.M q1 i : ℚ)}) ∧
      (finiteSupport6 2 (finiteMatrix 2 A2) (sourceReference6 R q1)).Nonempty ∧
      (finiteSupport6 3 (finiteMatrix 3 A3) (sourceReference6 R q1)).Nonempty ∧
      ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
        publishedDualProduct6 A2 A3 L (fun k => (sourceReference6 R q1 k : ℚ)) s = 0 := by
  obtain ⟨Bzero, Bpoint, T, q1, hq1, _, hb, haux, hline, _, hzero⟩ :=
    source_fixed_reference6 R h2 h3 hLdet
  have hs := source_reference_supports6 R h2 h3 q1
  exact ⟨Bzero, Bpoint, T, q1, hq1, hb, haux, hline, hs.1, hs.2,
    fun s h => source_reference_product_zero6 R q1 s (hzero s h)⟩

end CompoundFeasibility.SchlickeweiReference6
