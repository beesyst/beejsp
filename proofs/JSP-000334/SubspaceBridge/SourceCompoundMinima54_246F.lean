import SubspaceBridge.SourceExterior54Powered246F
import SubspaceBridge.SourceExterior54Frame246F
import SubspaceBridge.SourceFourProducts246F
import SubspaceBridge.MinimaProduct5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

def compoundMinima4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ) : Fin 5 → ℝ :=
  sourceMinima5 (compound4246 A2) (compound4246 A3) (compound4246 L)
    (compound_unit4246 L hL) (Q^4) (powered_gt_one4246 Q hQ)
    (normalizedWeights4246 c0) (normalizedWeights4246 c2) (normalizedWeights4246 c3)

theorem compoundMinima_pos_mono4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ) :
    (∀ j, 0 < compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
    Monotone (compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3) :=
  sourceMinima5_pos_mono _ _ _ _ _ _ _ _ _

theorem signedQuad_real_bound246 (L : Matrix (Fin 5) (Fin 5) ℝ)
    (u : Fin 5 → Fin 5 → ℤ) (a : Fin 5 → ℝ) (Q : ℝ) (hQ : 1 < Q)
    (c0 : Fin 5 → ℝ)
    (hu : ∀ j k, |(L *ᵥ integerReal (u j)) k| ≤ a j * Q^(c0 k)) (j i : Fin 5) :
    |(compound4246 L *ᵥ integerReal (signedQuad246 u j.rev)) i| ≤
      24 * fourProducts246 a j * Q^(fourWeights246 c0 i) := by
  rw [signedQuad_cast246]
  change |(compound4246 L *ᵥ ((-1 : ℝ)^j.rev.val •
    wedge4246 (fun k : Fin 4 => integerReal (u (j.rev.succAbove k))))) i| ≤ _
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul]
  have h := real_source_wedge4246 L (fun k => u (j.rev.succAbove k))
    (fun k => a (j.rev.succAbove k)) Q hQ c0 (fun k => hu _) i
  have he : integerReal (wedge4246 (fun k : Fin 4 => u (j.rev.succAbove k))) =
      wedge4246 (fun k : Fin 4 => integerReal (u (j.rev.succAbove k))) :=
    wedge_map4246 (Int.castRingHom ℝ) _
  rw [he] at h
  exact h

theorem actual_wedge_frame4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ) :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 5 → ℤ)) ∧
      (∀ j, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u j : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
      let w : Fin 5 → Fin 5 → ℤ := fun j => signedQuad246 (fun k => (u k : Fin 5 → ℤ)) j.rev
      (∀ j, w j ∈ originalSourceGroup5 (compound4246 A2) (compound4246 A3) (Q^4)
        (normalizedWeights4246 c2) (normalizedWeights4246 c3)) ∧
      LinearIndependent ℝ (fun j => integerReal (w j)) ∧
      ∀ j, coordinateGauge5 (originalCoordinates5 (compound4246 L) (compound_unit4246 L hL)
        (Q^4) (powered_gt_one4246 Q hQ) (normalizedWeights4246 c0)) (integerReal (w j)) ≤
          24 * fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  obtain ⟨u,hu,_,_,hatt,hpoint⟩ := exists_sourceMinima5_attaining A2 A3 L hL Q hQ c0 c2 c3
  refine ⟨u,hu,hatt,?_,?_,?_⟩
  · intro j
    exact signedQuad_source_group246 A2 A3 Q c2 c3 u j.rev
  · exact (integer_signedQuad_independent246 _ hu).comp Fin.rev (by
      intro i j h
      exact Fin.rev_injective h)
  · intro j
    apply (powered_body4246 L hL Q hQ c0 _ _).mpr
    exact signedQuad_real_bound246 L _ _ Q hQ c0 hpoint j

theorem compoundMinima_upper4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ) :
    ∀ j, compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j ≤
      24 * fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  intro j
  obtain ⟨u,_,_,hm,hi,hg⟩ := actual_wedge_frame4246 A2 A3 L hL Q hQ c0 c2 c3
  let w : Fin 5 → Fin 5 → ℤ := fun j => signedQuad246 (fun k => (u k : Fin 5 → ℤ)) j.rev
  let f : Fin (j.val+1) → Fin 5 := Fin.castLE (by omega)
  apply (sourceMinima5_radius_set_properties (compound4246 A2) (compound4246 A3) (compound4246 L)
    (compound_unit4246 L hL) (Q^4) (powered_gt_one4246 Q hQ)
    (normalizedWeights4246 c0) (normalizedWeights4246 c2) (normalizedWeights4246 c3) j).2.2.2
  refine ⟨fun i => integerReal (w (f i)),hi.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    exact ⟨w (f i),hm (f i),rfl⟩
  · intro i
    have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
    exact (hg (f i)).trans (mul_le_mul_of_nonneg_left
      (fourProducts_mono246 _ hp.1 hp.2 (show f i ≤ j by change i.val ≤ j.val; omega)) (by norm_num))

end CompoundFeasibility.Exterior54_246
