import SubspaceBridge.OriginalDeformation4
import SubspaceBridge.OriginalAuxiliaryDual4
import SubspaceBridge.SourceRelativeIndex6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalDeformedFrame4
open OriginalDeformation4 OriginalLastDual4 OriginalAuxiliaryDual4

theorem exists_deformed_attaining4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) :
    ∃ w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ)) ∧
      ∃ hw : LinearIndependent ℚ (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)),
      (∀ j, 0 < originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) ∧
      Monotone (originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd) ∧
      (∀ j, coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
        (integerReal (w j : Fin 4 → ℤ)) =
        originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) ∧
      lastDual4 (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)) hw ≠ 0 := by
  let b := sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd
  obtain ⟨v,hv,hmem,hpos,hmono,hatt⟩ := exists_successive_minima4 b e
  have hlift (j : Fin 4) : ∃ z : originalSourceGroup4 A2 A3 Q c2 c3,
      integerReal (z : Fin 4 → ℤ) = v j := by
    have hj := hmem j
    rw [sourceRealBasis4_span] at hj
    obtain ⟨z,hz,he⟩ := hj
    exact ⟨⟨z,hz⟩,he⟩
  choose w hw using hlift
  have hreal : LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ)) := by
    simpa only [hw] using hv
  have hrat := integral_frame_rational_independent (fun j => (w j : Fin 4 → ℤ)) hreal
  refine ⟨w,hreal,hrat,hpos,hmono,?_,lastDual4_nonzero _ hrat⟩
  intro j
  change coordinateGauge4 e (integerReal (w j : Fin 4 → ℤ)) = successiveRadius4 b e j
  rw [hw j]
  exact hatt j

theorem deformed_gauge_bounds4
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i)
    (x : Fin 4 → ℝ) (r : ℝ) :
    coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) x ≤ r ↔
      ∀ i, |(L *ᵥ x) i| ≤ r*deformedWidths4 Q c0 d sigma i := by
  rw [coordinateGauge4,pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro i
  rw [originalDeformedCoordinates4_apply,Real.norm_eq_abs,abs_div,abs_mul,
    abs_of_pos (hd _),abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _),
    div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)]
  dsimp [deformedWidths4]
  rw [← mul_div_assoc,le_div_iff₀ (hd _)]
  constructor <;> intro h <;> nlinarith

theorem frame_normalization4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c2 c3 : Fin 4 → ℝ)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ))) :
    let G := originalSourceGroup4 A2 A3 Q c2 c3
    let J := SourceRelativeIndex6.frameRelativeIndex G w
    let v : Matrix (Fin 4) (Fin 4) ℤ := fun j => (w j : Fin 4 → ℤ)
    Finite (G ⧸ Submodule.span ℤ (Set.range w)) ∧ 0 < J ∧
      J*G.index = v.det.natAbs ∧
      |(v.det : ℝ)| = (J : ℝ)*ZLattice.covolume (integerRealImage G) ∧
      v.det ≠ 0 ∧ 0 < ZLattice.covolume (integerRealImage G) := by
  obtain ⟨b⟩ := sourceLattice4_has_basis A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  have hwZ : LinearIndependent ℤ w := LinearIndependent.of_comp
    (integerReal.comp (originalSourceGroup4 A2 A3 Q c2 c3).subtype.toIntLinearMap)
    (hw.restrict_scalars' ℤ)
  letI : IsZLattice ℝ (integerRealImage (originalSourceGroup4 A2 A3 Q c2 c3)) := by
    dsimp [originalSourceGroup4]
    infer_instance
  exact ⟨(SourceRelativeIndex6.integer_span_index_det b w hwZ).1,
    SourceRelativeIndex6.frameRelativeIndex_pos _ b w hwZ,
    SourceRelativeIndex6.frameRelativeIndex_mul_index _ b w hwZ,
    SourceRelativeIndex6.frame_abs_det_covolume _ b w hwZ,
    integerFrame4_det_ne_zero _ (integral_frame_rational_independent _ hw),
    ZLattice.covolume_pos _ MeasureTheory.volume⟩


theorem deformed_frame_real_cofactor4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
      (integerReal (w j : Fin 4 → ℤ)) =
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℝ))) i‖ ≤
      6 * (∏ j : Fin 3, originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j.castSucc) *
        (∏ k : Fin 3, deformedWidths4 Q c0 d sigma (i.succAbove k)) := by
  apply real_cofactor_bound4 L hLdet _ _ _ _ i
  intro j k
  exact (deformed_gauge_bounds4 L hL Q hQ c0 d sigma hd _ _).mp (hatt j.castSucc).le k

theorem first_three_deformed_product4
    (mu : Fin 4 → ℝ) (hp : ∀ i, 0 < mu i) (hm : Monotone mu)
    (Q delta : ℝ) (hQ : 0 < Q) (hsmall : mu 2 < Q^(-delta)) :
    (∏ j : Fin 3, mu j.castSucc) < Q^(-3*delta) := by
  have hle : (∏ j : Fin 3, mu j.castSucc) ≤ (mu 2)^3 := by
    calc
      _ ≤ ∏ _j : Fin 3, mu 2 := Finset.prod_le_prod
        (fun j _ => (hp _).le) (fun j _ => hm (by change j.val ≤ 2; omega))
      _ = _ := by simp
  apply hle.trans_lt
  calc
    (mu 2)^3 < (Q^(-delta))^3 := pow_lt_pow_left₀ hsmall (hp 2).le (by decide)
    _ = Q^(-3*delta) := by rw [← Real.rpow_mul_natCast hQ.le]; congr 1; ring

theorem omitted_positive_widths4 (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i) (i : Fin 4) :
    (∏ k : Fin 3, A (i.succAbove k)) = (∏ k : Fin 4, A k)/A i := by
  rw [Fin.prod_univ_succAbove (fun k => A k) i]
  apply (eq_div_iff (hA i).ne').mpr
  ring

theorem deformed_cofactor_decay4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
      (integerReal (w j : Fin 4 → ℤ)) =
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j)
    (delta : ℝ)
    (hsmall : originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 <
      (Q^(5 : ℕ))^(-delta)) (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℝ))) i‖ <
      6 * ((∏ k : Fin 4, deformedWidths4 Q c0 d sigma k)/deformedWidths4 Q c0 d sigma i) *
        (Q^(5 : ℕ))^(-3*delta) := by
  obtain ⟨_,_,_,hp,hm,_⟩ := exists_successive_minima4
    (sourceRealBasis4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))))
    (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
  have hprod := first_three_deformed_product4 _ hp hm _ delta (by positivity) hsmall
  change (∏ j : Fin 3, originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j.castSucc) <
    (Q^(5 : ℕ))^(-3*delta) at hprod
  have hbound := deformed_frame_real_cofactor4 A2 A3 L hL hLdet Q hQ c0 c2 c3 d sigma hd w hatt i
  rw [omitted_positive_widths4 _ (deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 d hd sigma) i] at hbound
  apply hbound.trans_lt
  have hW : 0 < (∏ k : Fin 4, deformedWidths4 Q c0 d sigma k)/deformedWidths4 Q c0 d sigma i :=
    div_pos (Finset.prod_pos (fun k _ => deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 d hd sigma k))
      (deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 d hd sigma i)
  nlinarith

theorem deformed_frame_finite_cofactor4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (Q : ℝ) (c2 c3 : Fin 4 → ℝ)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3) (i : Fin 4) :
    (‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℚ_[2]))) i‖ ≤
      (2 : ℝ)^(∑ k : Fin 3, -(Nat.ceil (JSP000334.qThreshold 2 Q (c2 (i.succAbove k))) : ℤ))) ∧
    (‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℚ_[3]))) i‖ ≤
      (3 : ℝ)^(∑ k : Fin 3, -(Nat.ceil (JSP000334.qThreshold 3 Q (c3 (i.succAbove k))) : ℤ))) := by
  exact ⟨finite_cofactor_bound4 2 A2 h2 _ _ (fun j => (w j).property.1) i,
    finite_cofactor_bound4 3 A3 h3 _ _ (fun j => (w j).property.2) i⟩

end CompoundFeasibility.OriginalDeformedFrame4
