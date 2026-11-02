import SubspaceBridge.AllPointSourceFamily4
import SubspaceBridge.AllPointGeneralPosition4
namespace JSP000334
open scoped BigOperators Matrix

theorem source_primitive_five_term_finite_cover4 :
    ∃ F : Set (Submodule ℚ (Fin 4 → ℚ)),F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ z : Fin 4 → ℤ,allpointEligible4 z → ∃ P∈F,(fun i => (z i : ℚ))∈P := by
  classical
  by_contra hno
  change allpoint_no_finite_cover4 allpointEligible4 at hno
  obtain ⟨z,hE,hheight,hmono,havoid⟩ := allpoint_general_position_sequence4 allpointEligible4 hno
  choose x hx s hscale using fun n => (hE n).2
  let q (n : ℕ) : ℝ := (archFourHeight (z n) : ℝ)^8
  let Omega : Set ℝ := Set.range q
  have hOmega : ¬BddAbove Omega := by
    rintro ⟨M,hM⟩
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hb := hM (show q n∈Omega from Set.mem_range_self n)
    have hH := (hheight n).1
    have hHn := (hheight n).2
    have hsq : (archFourHeight (z n) : ℝ)≤(archFourHeight (z n) : ℝ)^2 := by nlinarith
    have hfour : (archFourHeight (z n) : ℝ)^2≤(archFourHeight (z n) : ℝ)^4 := by
      nlinarith [sq_nonneg ((archFourHeight (z n) : ℝ)^2-1)]
    have height : (archFourHeight (z n) : ℝ)^4≤(archFourHeight (z n) : ℝ)^8 := by
      nlinarith [sq_nonneg ((archFourHeight (z n) : ℝ)^4-1)]
    change (archFourHeight (z n) : ℝ)^8≤M at hb
    linarith
  have hex (t : Omega) : ∃ n : ℕ,q n=t.val := t.property
  choose original hparam using hex
  obtain ⟨P,hP,W,hWO,hW,hm⟩ := allpoint_source_family4 Omega hOmega
    (fun t => x (original t)) (fun t => hx (original t)) (fun t => z (original t))
    (fun t => s (original t)) (fun t => (hE (original t)).1) (fun t => hscale (original t))
    (fun t => (hheight (original t)).1.le) (fun t => (hparam t).symm)
  have hS := allpoint_general_position_intersection4 z (fun n => (hheight n).1) havoid P hP
  have hsub : W⊆q '' {n | (fun i => (z n i : ℚ))∈P} := by
    intro Q hQW
    let t : Omega := ⟨Q,hWO hQW⟩
    exact ⟨original t,hm t hQW,hparam t⟩
  exact hW ((hS.image q).bddAbove.mono hsub)

theorem allpoint_five_term_original_mem4 {x : Fin 5 → ℚ}
    (P : Submodule ℚ (Fin 4 → ℚ)) (w : Fin 5 → ℤ) (s : fixedSUnitGroup)
    (hscale : ∀ i,(w i : ℚ)=((s : ℚˣ) : ℚ)*x i)
    (hw : (fun i : Fin 4 => (w i.castSucc : ℚ))∈P) :
    (fun i : Fin 4 => x i.castSucc)∈P := by
  have hs : ((s : ℚˣ) : ℚ)≠0 := Units.ne_zero _
  have hm := P.smul_mem (((s : ℚˣ) : ℚ)⁻¹) hw
  have he : (((s : ℚˣ) : ℚ)⁻¹) • (fun i : Fin 4 => (w i.castSucc : ℚ))=
      (fun i : Fin 4 => x i.castSucc) := by
    ext i
    change ((s : ℚˣ) : ℚ)⁻¹*(w i.castSucc : ℚ)=x i.castSucc
    rw [hscale,inv_mul_cancel_left₀ hs]
  rw [he] at hm
  exact hm

theorem source_five_term_finite_cover4 :
    ∃ F : Set (Submodule ℚ (Fin 4 → ℚ)),
      F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ x∈normalizedRelations fixedSUnitGroup 4,
        ∃ P∈F,(fun i : Fin 4 => x i.castSucc)∈P := by
  obtain ⟨F,hF,hproper,hcover⟩ := source_primitive_five_term_finite_cover4
  refine ⟨F,hF,hproper,?_⟩
  intro x hx
  obtain ⟨w,s,hprim,_,_,_,hscale,_⟩ := exists_primitive_five_term_relation hx
  obtain ⟨P,hPF,hwP⟩ := hcover (fun i => w i.castSucc) ⟨hprim,x,hx,s,fun i => hscale i.castSucc⟩
  exact ⟨P,hPF,allpoint_five_term_original_mem4 P w s hscale hwP⟩

end JSP000334
