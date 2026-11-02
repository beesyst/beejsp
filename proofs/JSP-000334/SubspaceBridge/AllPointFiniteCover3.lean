import SubspaceBridge.AllPointGeneralPosition3
open scoped BigOperators Matrix
namespace JSP000334

def allpointEligible3 (z : IntegerTriple) : Prop :=
  PrimitiveTriple z ∧ ∃ x : Fin 4 → ℚ, x ∈ normalizedRelations fixedSUnitGroup 3 ∧
    ∃ s : fixedSUnitGroup, ∀ i : Fin 3, (z i : ℚ) = ((s : ℚˣ) : ℚ)*x i.castSucc

theorem source_primitive_four_term_finite_cover3 :
    ∃ F : Set (Submodule ℚ (Fin 3 → ℚ)), F.Finite ∧ (∀ P ∈ F, P ≠ ⊤) ∧
      ∀ z : IntegerTriple, allpointEligible3 z → ∃ P ∈ F, (fun i => (z i : ℚ)) ∈ P := by
  classical
  by_contra hno
  change allpoint_no_finite_cover3 allpointEligible3 at hno
  obtain ⟨z,hE,hheight,hmono,havoid⟩ := allpoint_general_position_sequence3 allpointEligible3 hno
  choose x hx s hscale using (fun n => (hE n).2)
  let q (n : ℕ) : ℝ := (archTripleHeight (z n) : ℝ)^4
  let Omega : Set ℝ := Set.range q
  have hOmega : ¬ BddAbove Omega := by
    rintro ⟨M,hM⟩
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hb := hM (show q n ∈ Omega from Set.mem_range_self n)
    have hH := (hheight n).1
    have hHn := (hheight n).2
    have hsq : (archTripleHeight (z n) : ℝ) ≤ (archTripleHeight (z n) : ℝ)^2 := by nlinarith
    have hfour : (archTripleHeight (z n) : ℝ)^2 ≤ (archTripleHeight (z n) : ℝ)^4 := by
      nlinarith [sq_nonneg ((archTripleHeight (z n) : ℝ)^2-1)]
    change (archTripleHeight (z n) : ℝ)^4 ≤ M at hb
    linarith
  have hex (t : Omega) : ∃ n : ℕ, q n = t.val := t.property
  choose original hparam using hex
  obtain ⟨P,hP,W,hWO,hW,hm⟩ := allpoint_source_family3 Omega hOmega
    (fun t => x (original t)) (fun t => hx (original t)) (fun t => z (original t))
    (fun t => s (original t)) (fun t => (hE (original t)).1) (fun t => hscale (original t))
    (fun t => (hheight (original t)).1.le) (fun t => (hparam t).symm)
  have hS := (allpoint_general_position_intersection3 z (fun n => (hheight n).1) havoid P hP).1
  have hsub : W ⊆ q '' {n | (fun i => (z n i : ℚ)) ∈ P} := by
    intro Q hQW
    let t : Omega := ⟨Q,hWO hQW⟩
    exact ⟨original t,hm t hQW,hparam t⟩
  exact hW ((hS.image q).bddAbove.mono hsub)

theorem allpoint_four_term_recovery3 {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) (w : Fin 4 → ℤ) (s : fixedSUnitGroup)
    (hscale : ∀ i, (w i : ℚ) = ((s : ℚˣ) : ℚ)*x i) :
    ∀ i, x i = (w i : ℚ)/(w 0 : ℚ) := by
  have h0 : (w 0 : ℚ) = ((s : ℚˣ) : ℚ) := by simpa only [hx.1,mul_one] using hscale 0
  intro i
  rw [hscale,h0]
  exact (mul_div_cancel_left₀ (x i) (Units.ne_zero (s : ℚˣ))).symm

theorem source_four_term_finite_cover3 :
    ∃ F : Set (Submodule ℚ (Fin 3 → ℚ)), F.Finite ∧ (∀ P ∈ F, P ≠ ⊤) ∧
      ∀ x ∈ normalizedRelations fixedSUnitGroup 3,
        ∃ w : Fin 4 → ℤ, ∃ s : fixedSUnitGroup,
          PrimitiveTriple (fun i => w i.castSucc) ∧ (∀ i, w i ≠ 0) ∧
          (∑ i, w i = 0) ∧ Nondegenerate (fun i => (w i : ℚ)) ∧
          (∀ i, (w i : ℚ) = ((s : ℚˣ) : ℚ)*x i) ∧
          (∀ i, x i = (w i : ℚ)/(w 0 : ℚ)) ∧ ∃ P ∈ F, (fun i : Fin 3 => (w i.castSucc : ℚ)) ∈ P := by
  obtain ⟨F,hF,hproper,hcover⟩ := source_primitive_four_term_finite_cover3
  refine ⟨F,hF,hproper,?_⟩
  intro x hx
  obtain ⟨w,s,hprim,hn,hs,hd,hscale⟩ := exists_primitive_four_term_relation hx
  refine ⟨w,s,hprim,hn,hs,hd,hscale,allpoint_four_term_recovery3 hx w s hscale,?_⟩
  exact hcover _ ⟨hprim,x,hx,s,fun i => hscale i.castSucc⟩

end JSP000334
