import SubspaceBridge.SchlickeweiReferenceRescaling4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiFixedLine4
open SchlickeweiReference4 SchlickeweiReferenceRescaling4 SourceSelectedDual4
open OriginalSelectedSystem4 OriginalDeformedSource4 OriginalDeformation4
open OriginalAuxiliaryGeometry4 OriginalAuxiliaryDual4 OriginalLastDual4

theorem cofactor_finite_unit4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (e : Fin 4 → ℕ)
    (v : Fin 4 → Fin 4 → ℤ) (hv : ∀ j, v j ∈ lattice4 p A e) (i : Fin 4) :
    ‖dualValue4 (A.map (algebraMap ℚ ℚ_[p])) (integerLastDual4 v) i‖ ≤ 1 := by
  have hbound := finite_cofactor_bound4 p A hA e v hv i
  have he : (∑ k : Fin 3, -(e (i.succAbove k) : ℤ)) ≤ 0 :=
    Finset.sum_nonpos (fun k _ => by omega)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact hbound.trans (by simpa only [zpow_zero] using zpow_le_zpow_right₀ hp he)

theorem nonzero_mem_line_span4 (x y : Fin 4 → ℚ) (hx : x ≠ 0)
    (hxy : x ∈ Submodule.span ℚ {y}) : Submodule.span ℚ {x} = Submodule.span ℚ {y} := by
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hxy
  have hne : a ≠ 0 := by intro hz; rw [hz,zero_smul] at ha; exact hx ha.symm
  rw [← ha]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hne) y

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

theorem same_deformed_auxiliary_line4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (hd : 0 < delta)
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q)) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : U, T < q.val → ∀ y : Fin 4 → ℤ,
      auxiliaryInteger4 A2 A3 L
        (fun i => Nat.ceil (JSP000334.qThreshold 2 q.val (c2 i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 q.val (c3 i)))
        (SourceWeights4.frameWidths F q) y →
      (∀ j : Fin 3, integerPairing4 ((F q).w j.castSucc : Fin 4 → ℤ) y = 0) ∧
      (fun i => (y i : ℚ)) ∈ Submodule.span ℚ
        {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} := by
  have hLd : L.det ≠ 0 := by rw [hLdet]; exact one_ne_zero
  obtain ⟨T,hT,hpoint⟩ := source_auxiliary_line4 A2 A3 L h2 h3 hLd (delta/24) (by positivity)
  refine ⟨T,hT,?_⟩
  intro q hq y hy
  exact hpoint q.val hq (hQU q.val q.property) c2 c3 (SourceWeights4.frameWidths F q)
    (F q).widths_pos (F q).w (F q).rational_independent (attaining_first_three4 (F q)) y hy

theorem same_frame_fixed_last_dual4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) (hd : 0 < delta)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (S : Finset MixedIndex4)
    (hselected : ∀ q : U, publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
      (SourceWeights4.frameWidths F q) (fun i => c2 i/5) (fun i => c3 i/5) = S)
    (Tzero : ℝ) (hzero : ∀ q : U, Tzero < q.val → ∀ s ∈ S,
      lastDualProduct4 A2 A3 L (fun j => ((F q).w j : Fin 4 → ℤ)) (F q).rational_independent s = 0) :
    ∃ (q1 : U) (b : Fin 4 → ℤ) (B : ℝ), Tzero < q1.val ∧
      b = integerLastDual4 (fun j => ((F q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
      Submodule.span ℚ {fun i => (b i : ℚ)} =
        Submodule.span ℚ {lastDual4 (fun j i => (((F q1).w j : Fin 4 → ℤ) i : ℚ)) (F q1).rational_independent} ∧
      (∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0) ∧
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ U ∧ B < q} ∧
      ∀ q : U, B < q.val →
        Submodule.span ℚ {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} =
          Submodule.span ℚ {fun i => (b i : ℚ)} := by
  obtain ⟨Tpoint,hTp,hpoint⟩ := same_deformed_auxiliary_line4 (A2 := A2) (A3 := A3) (L := L) (hL := hL) (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := U) (hQU := hQU) (u := u) h2 h3 hLdet hd F
  obtain ⟨q1,hq1,hfar⟩ := not_bddAbove_iff.mp hU (max Tzero Tpoint)
  let r1 : U := ⟨q1,hq1⟩
  let b := integerLastDual4 (fun j => ((F r1).w j : Fin 4 → ℤ))
  have hb : b ≠ 0 := integerLastDual4_nonzero _ (F r1).rational_independent
  have hunit (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
      IsUnit (A.map (algebraMap ℚ ℚ_[p])) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [mapped_det_one4 A hA]
    exact isUnit_one
  have hT2 := finiteSupport_nonempty4 2 _ (hunit 2 A2 h2) b hb
  have hT3 := finiteSupport_nonempty4 3 _ (hunit 3 A3 h3) b hb
  have hb2 (i : Fin 4) : ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) b i‖ ≤ 1 :=
    cofactor_finite_unit4 2 A2 h2 _ _ (fun j => ((F r1).w j).property.1) i
  have hb3 (i : Fin 4) : ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) b i‖ ≤ 1 :=
    cofactor_finite_unit4 3 A3 h3 _ _ (fun j => ((F r1).w j).property.2) i
  have hzero1 := hzero r1 ((le_max_left _ _).trans_lt hfar)
  have hz : ∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0 := by
    intro s hs
    exact (primitive_lastDualProduct4_zero A2 A3 L _ (F r1).rational_independent b 1
      one_ne_zero (fun i => by simp [b]) s).mpr (hzero1 s hs)
  obtain ⟨Treal,hTr,haux⟩ := rescaled_reference_auxiliary4 (A2 := A2) (A3 := A3) (L := L) (hL := hL) (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := U) (hQU := hQU) (u := u) h2 h3 hd hc2 hc3 F S hselected b hT2 hT3 hb2 hb3 hz
  let B := max Tzero (max Tpoint Treal)
  have hpt : Tpoint ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hrt : Treal ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨r1,b,B,(le_max_left _ _).trans_lt hfar,rfl,hb,
    integerLastDual4_line _ (F r1).rational_independent,hz,hTr.trans_le hrt,
    JSP000334.sourceDual_unbounded_tail3 U hU B,?_⟩
  intro q hq
  let y := rescaledReference4 q.val c2 c3 _ _ hT2 hT3 b
  have hy := haux q (hrt.trans_lt hq)
  have hmem := (hpoint q (hpt.trans_lt hq) y hy).2
  have hyn : y ≠ 0 := integer_rescale_nonzero4 _ _ b hb
  have hyQ : (fun i => (y i : ℚ)) ≠ 0 := by
    intro he
    apply hyn
    funext i
    have hi : (y i : ℚ) = 0 := congrFun he i
    exact_mod_cast hi
  have heq := (nonzero_mem_line_span4 _ _ hyQ hmem).symm
  exact heq.trans (integer_rescale_line4 _ _ b)

theorem source_deformed_fixed_last_dual4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ U : Set ℝ, ∃ hUV : U ⊆ V, ¬ BddAbove U ∧
      ∃ u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ∃ F : (q : U) → DeformedAttaining4 A2 A3 L (sourceUnit42 L hLdet) q.val
        (hQV q.val (hUV q.property)) c0 c2 c3 delta (u q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ W : Set ℝ, ∃ hWU : W ⊆ U, ¬ BddAbove W ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
        (∀ q : U, q.val ∈ W →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
            (OriginalDeformation4.deformedWidths4 q.val c0
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q.val
                  (hQV q.val (hUV q.property)) c0 c2 c3)) (F q).sigma) (fun i => c2 i/5) (fun i => c3 i/5) = S) ∧
        ∃ (q1 : U) (b : Fin 4 → ℤ) (B : ℝ), q1.val ∈ W ∧
          b = integerLastDual4 (fun j => ((F q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
          Submodule.span ℚ {fun i => (b i : ℚ)} =
            Submodule.span ℚ {lastDual4 (fun j i => (((F q1).w j : Fin 4 → ℤ) i : ℚ)) (F q1).rational_independent} ∧
          (∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0) ∧
          1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ W ∧ B < q} ∧
          ∀ q : U, q.val ∈ W → B < q.val →
            Submodule.span ℚ {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} =
              Submodule.span ℚ {fun i => (b i : ℚ)} := by
  obtain ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,Tzero,hzero⟩ :=
    SourceSelectedVanishing4.source_selected_vanishing4 A2 A3 L h2 h3 hLdet hAlg delta hd
      c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap
  let lift : W → U := fun q => ⟨q.val,hWU q.property⟩
  obtain ⟨q1,b,B,hq1,hb,hbn,hline,hbz,hB,htail,hfixed⟩ := same_frame_fixed_last_dual4
    (A2 := A2) (A3 := A3) (L := L) (hL := sourceUnit42 L hLdet)
    (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := W)
    (hQU := fun q hq => hQV q (hUV (hWU hq))) (u := fun q : W => u (lift q))
    h2 h3 hLdet hd (fun i => (hc2 i).2) (fun i => (hc3 i).2)
    (fun q : W => F (lift q)) hW S
    (fun q => hselected (lift q) q.property) Tzero
    (fun q hq s hs => hzero (lift q) q.property hq s hs)
  refine ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,lift q1,b,B,q1.property,
    hb,hbn,hline,hbz,hB,htail,?_⟩
  intro q hq hBq
  exact hfixed ⟨q.val,hq⟩ hBq

end CompoundFeasibility.SchlickeweiFixedLine4
