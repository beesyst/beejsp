import SubspaceBridge.AllPointActualValues3
import SubspaceBridge.AllPointPrimitive3
import SubspaceBridge.AllPointFixedWeights3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

def allpoint_norms3 (choice : Fin 3 → Fin 3) (z : IntegerTriple) (tau i : Fin 3) : ℝ :=
  rationalPlaceNorm tau (threeCoordinateSumForms (choice tau) i (fun j => (z j : ℚ)))

theorem allpoint_source_weights3 {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3)
    (z : IntegerTriple) (s : fixedSUnitGroup) (hz : PrimitiveTriple z)
    (hscale : ∀ i : Fin 3, (z i : ℚ) = ((s : ℚˣ) : ℚ)*x i.castSucc)
    (hH : 3 ≤ (archTripleHeight z : ℝ)) :
    let Q := (archTripleHeight z : ℝ)^4
    ∃ choice : Fin 3 → Fin 3, ∃ c : Fin 3 → Fin 3 → ℝ,
      ∃ hQ : 1 < Q, sourceWeightConditions3 c ∧
      c = sourceLogWeights3 Q (allpoint_balanced_values3 Q (allpoint_norms3 choice z)) ∧
      z ∈ qSourceLattice3 (choice 1) (choice 2) Q (c 1) (c 2) ∧
      coordinateGauge3 (qSourceCoordinates3 (choice 0) Q (c 0) hQ) (integerTripleReal3 z) ≤ Q^(-(1 : ℝ)/12) := by
  intro Q
  obtain ⟨choice,hret⟩ := allpoint_primitive_product3 hx z s hz hscale
  let a := allpoint_norms3 choice z
  have hlocal (tau i : Fin 3) :
      0 < a tau i ∧ (a tau i)⁻¹ ≤ 3*(archTripleHeight z : ℝ) ∧
      (tau ≠ 0 → a tau i ≤ 1) := by
    let m := (retainedIntegerMatrix3 (choice tau) *ᵥ z) i
    have hp : threePlaceProduct (m : ℚ) = 1 := by
      rw [retainedIntegerMatrix3_apply]
      exact allpoint_form_product3 hx z s hscale _ _
    have hl := allpoint_local_inverse3 m hp tau
    have ha := allpoint_form_arch_bound3 z (choice tau) i
    have hm : (m : ℚ) = threeCoordinateSumForms (choice tau) i (fun j => (z j : ℚ)) :=
      retainedIntegerMatrix3_apply _ _ _
    rw [hm] at hl
    dsimp only [a,allpoint_norms3]
    refine ⟨by exact_mod_cast hl.1,?_,?_⟩
    · have hb := hl.2.1.trans ha
      exact_mod_cast hb
    · intro ht
      exact_mod_cast hl.2.2 ht
  have hprod : (∏ tau, ∏ i, a tau i)*(archTripleHeight z : ℝ) = 1 := by
    unfold tripleChoiceFormsProduct at hret
    dsimp only [a,allpoint_norms3]
    exact_mod_cast hret
  obtain ⟨hQ,hc,heq,hreal,hfinite⟩ := allpoint_balanced_weights3 (archTripleHeight z : ℝ) hH a
    (fun tau i => (hlocal tau i).1)
    (fun i => by
      change ((|threeCoordinateSumForms (choice 0) i (fun j => (z j : ℚ))| : ℚ) : ℝ) ≤ 3*(archTripleHeight z : ℝ)
      exact_mod_cast allpoint_form_arch_bound3 z (choice 0) i)
    (fun tau ht i => (hlocal tau i).2.2 ht)
    (fun tau i => (hlocal tau i).2.1) hprod
  let c := sourceLogWeights3 Q (allpoint_balanced_values3 Q a)
  refine ⟨choice,c,hQ,hc,rfl,?_,?_⟩
  · apply ((qSourceLattice3_spec (choice 1) (choice 2) Q (c 1) (c 2) hQ
      (fun i => (hc.2.1 1 (by decide) i).2) (fun i => (hc.2.1 2 (by decide) i).2)).1 z).mpr
    constructor
    · intro i
      change a 1 i ≤ Q^(c 1 i)
      exact (hfinite 1 (by decide) i).le
    · intro i
      change a 2 i ≤ Q^(c 2 i)
      exact (hfinite 2 (by decide) i).le
  · apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    have hQ0 := lt_trans zero_lt_one hQ
    change |retainedRealCoordinates3 (choice 0) (integerTripleReal3 z) i / Q^(c 0 i)| ≤ _
    rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos hQ0 _),← finiteWeight_real_local_value3,
      finiteWeight_rational_local_value3]
    have hnorm : rothLocalAbs 0 (threeCoordinateSumForms (choice 0) i (fun j => (z j : ℚ))) = a 0 i := by
      simp [a,allpoint_norms3,rothLocalAbs,rationalPlaceNorm]
    rw [hnorm,hreal]
    have hp : Q^(c 0 i-(1 : ℝ)/12) = Q^(-(1 : ℝ)/12)*Q^(c 0 i) := by
      rw [← Real.rpow_add hQ0]; congr 1; ring
    rw [hp,mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hQ0 _).ne']

theorem allpoint_fixed_source_point3 {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3)
    (z : IntegerTriple) (s : fixedSUnitGroup) (hz : PrimitiveTriple z)
    (hscale : ∀ i : Fin 3, (z i : ℚ) = ((s : ℚˣ) : ℚ)*x i.castSucc)
    (hH : 3 ≤ (archTripleHeight z : ℝ)) :
    let Q := (archTripleHeight z : ℝ)^4
    ∃ choice : Fin 3 → Fin 3, ∃ d ∈ finiteWeightCandidates3 168,
      ∃ hQ : 1 < Q, sourceWeightConditions3 d ∧
      z ∈ qSourceLattice3 (choice 1) (choice 2) Q (d 1) (d 2) ∧
      coordinateGauge3 (qSourceCoordinates3 (choice 0) Q (d 0) hQ) (integerTripleReal3 z) ≤ Q^(-(1 : ℝ)/24) := by
  intro Q
  obtain ⟨choice,c,hQ,hc,_,hzL,hg⟩ := allpoint_source_weights3 hx z s hz hscale hH
  obtain ⟨hd,hcond,hmem,hgauge⟩ := allpoint_round_point3 Q hQ (choice 0) (choice 1) (choice 2) c hc z hzL hg
  exact ⟨choice,finiteWeightApprox3 168 c,hd,hQ,hcond,hmem,hgauge⟩

end
end JSP000334
