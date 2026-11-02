import SubspaceBridge.RestrictedSource4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalAttainmentFlag4
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4

def ambientFrame4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃) : Prop :=
  LinearIndependent ℝ (fun i => integerReal (u i : Fin 4 → ℤ)) ∧
    ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal (u i : Fin 4 → ℤ)) =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i

def attainingFlagFamily4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (d : Fin 4) (V : Set ℝ) (hQV : ∀ Q ∈ V, 1 < Q) : Prop :=
  ∃ (W : Set ℝ) (hWV : W ⊆ V), ¬ BddAbove W ∧
    ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = d.val ∧
      ∃ u : (q : W) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
        ∀ q : W, P = originalFirstFlag4 d (fun j => (u q j : Fin 4 → ℤ)) ∧
          ambientFrame4 A₂ A₃ L hL q.val (hQV q.val (hWV q.property)) c₀ c₂ c₃ (u q)

theorem source_rank1_attaining_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 0 <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 1*Q^(-delta)) :
    attainingFlagFamily4 A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ 1 V hQV := by
  classical
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,htails⟩ :=
    source_original_fixed_rank1_4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  obtain ⟨_,_,_,_,hfamilies⟩ := htails c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨V₀,hV₀V,_,_,u,hframes,Vprime,hVpV₀,_,_,Wnorm,hWR,_,_,_,_,hsource⟩ := hfamilies V hV hQV hgap
  obtain ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,b,B,hq1,hbint,hbn,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,Pc,hTspan,hF_eq,hF,hPc,hPcdim,hflags,C₄,kappa,hC₄,hk,hkeq,
    Qfixed,hQfV,hQfeq,hQf,hQcube,hret,R₀,hR₀,hcut,Qfinal,hQfinal,hQfinaleq,hQfinalU,hfinal,hlineFamily⟩ := hsource
  obtain ⟨a,_,ha,P1,hP1,hP1dim,_,hcontrol⟩ := hlineFamily
  have hWV : Qfinal ⊆ V := fun _ h => hV₀V (hVpV₀ (hQfV (hQfinal h)))
  let uFinal : (q : Qfinal) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃ :=
    fun q => u ⟨q.val,hVpV₀ (hQfV (hQfinal q.property))⟩
  refine ⟨Qfinal,hWV,hQfinalU,P1,hP1dim,uFinal,?_⟩
  intro q
  constructor
  · rw [originalFirstFlag4_one]
    exact (hcontrol q).2.2.2.2.2.symm
  · have hf := (hframes ⟨q.val,hVpV₀ (hQfV (hQfinal q.property))⟩).1
    exact ⟨hf.1,hf.2.1⟩

theorem source_rank2_attaining_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 1 <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 2*Q^(-delta)) :
    attainingFlagFamily4 A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ 2 V hQV := by
  classical
  obtain ⟨V₀,hV₀V,R,u,v,sigma,w,kappa,B,q1,b,P,hprops,hbref,hbn,hfn,hP,hPdim,hB,hTail,hpoints⟩ :=
    OriginalPlaneRecovery42.source_original_fixed_plane42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
      c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap
  let W : Set ℝ := {Q | Q ∈ V₀ ∧ B < Q}
  have hWV : W ⊆ V := fun _ h => hV₀V h.1
  let uFinal : (q : W) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃ :=
    fun q => u ⟨q.val,q.property.1⟩
  refine ⟨W,hWV,hTail,P,hPdim,uFinal,?_⟩
  intro q
  obtain ⟨_,hu,_,_,a,ha,hrel,hspan⟩ := hpoints ⟨q.val,q.property.1⟩ q.property.2
  constructor
  · rw [originalFirstFlag4_two]
    exact hspan
  · have hs := (hprops.2.2.2.2.2 ⟨q.val,q.property.1⟩).1
    exact ⟨hs.1,hs.2.1⟩


theorem source_rank3_attaining_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 2 <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 3*Q^(-delta)) :
    attainingFlagFamily4 A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ 3 V hQV := by
  obtain ⟨T,hT,u0,_,hU,_,hframes,hready⟩ :=
    OriginalDeformation4.source_normalized_unbounded_deformation4 A₂ A₃ L h₂ h₃ hL hAlg
      delta hd c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap
  let U : Set ℝ := {Q | Q ∈ V ∧ T < Q}
  let hUV : U ⊆ V := fun _ h => h.1
  let hQU : ∀ Q ∈ U, 1 < Q := fun Q h => hQV Q h.1
  let u : (q : U) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃ :=
    fun q => u0 ⟨q.val,q.property.1⟩
  have hr (q : U) : OriginalDeformation4.deformationReady4 A₂ A₃ L (sourceUnit42 L hL)
      q.val (hQU q.val q.property) c₀ c₂ c₃ delta (u q) :=
    (hready ⟨q.val,q.property.1⟩ q.property.2).2.2
  obtain ⟨F,S,hS,W,hWU,hW,hWp,hselected⟩ := OriginalSelectedSystem4.deformed_fixed_selected_system4
    A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ delta hd U hU hQU u hr
  let lift : W → U := fun q => ⟨q.val,hWU q.property⟩
  obtain ⟨Tzero,hzero⟩ := SourceSelectedVanishing4.same_frame_selected_vanishing4
    (A2 := A₂) (A3 := A₃) (L := L) (hL := sourceUnit42 L hL)
    (c0 := c₀) (c2 := c₂) (c3 := c₃) (delta := delta) (U := W)
    (hQU := fun Q h => hQU Q (hWU h)) (u := fun q : W => u (lift q))
    h₂ h₃ hL hAlg (fun q : W => F (lift q)) hW hd hc₂ hc₃ S
    (fun q s hs => by
      have heq := hselected (lift q) q.property
      exact Eq.mpr (congrArg (fun K : Finset OriginalSelectedSystem4.MixedIndex4 => s ∈ K) heq) hs)
  obtain ⟨q1,b,B,hq1,hbint,hbn,hline,hbz,hB,htail,hfixed⟩ :=
    SchlickeweiFixedLine4.same_frame_fixed_last_dual4
      (A2 := A₂) (A3 := A₃) (L := L) (hL := sourceUnit42 L hL)
      (c0 := c₀) (c2 := c₂) (c3 := c₃) (delta := delta) (U := W)
      (hQU := fun Q h => hQU Q (hWU h)) (u := fun q : W => u (lift q))
      h₂ h₃ hL hd (fun i => (hc₂ i).2) (fun i => (hc₃ i).2)
      (fun q : W => F (lift q)) hW S (fun q => hselected (lift q) q.property) Tzero hzero
  obtain ⟨Tspan,hTspan,hcut⟩ := OriginalSpanTransport4.span_cutoff4 delta hd
  let Wfinal : Set ℝ := {Q | Q ∈ W ∧ max B Tspan < Q}
  have hFinalV : Wfinal ⊆ V := fun _ h => hUV (hWU h.1)
  have hFinal : ¬ BddAbove Wfinal := JSP000334.sourceDual_unbounded_tail3 W hW (max B Tspan)
  let P := LinearMap.ker (normalForm4 b)
  have hPdim : Module.finrank ℚ P = 3 :=
    (fixed_line_kernel4 _ (F (lift q1)).rational_independent b hbn hline.symm).2.2
  let uFinal : (q : Wfinal) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃ :=
    fun q => u0 ⟨q.val,hFinalV q.property⟩
  refine ⟨Wfinal,hFinalV,hFinal,P,hPdim,uFinal,?_⟩
  intro q
  let qw : W := ⟨q.val,q.property.1⟩
  have hBq : B < q.val := (le_max_left _ _).trans_lt q.property.2
  have hTq : Tspan < q.val := (le_max_right _ _).trans_lt q.property.2
  have hg := hgap q.val (hFinalV q.property)
  have ho := (OriginalSpanTransport4.rational_kernel_transport4 (F (lift qw))
    (hcut q.val hTq) hg b hbn (hfixed qw hBq)).1
  constructor
  · rw [originalFirstFlag4_three]
    exact ho
  · exact hframes ⟨q.val,hFinalV q.property⟩


theorem source_selected_gap_attaining_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    attainingFlagFamily4 A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ j.succ V hQV := by
  fin_cases j
  · exact source_rank1_attaining_flag4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
      c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap
  · exact source_rank2_attaining_flag4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
      c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap
  · exact source_rank3_attaining_flag4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
      c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap

theorem attainingFlagFamily4_forget (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (d : Fin 4) (V : Set ℝ) (hQV : ∀ Q ∈ V, 1 < Q)
    (h : attainingFlagFamily4 A₂ A₃ L hL c₀ c₂ c₃ d V hQV) :
    selectedFlagFamily4 A₂ A₃ c₂ c₃ d V := by
  obtain ⟨W,hWV,hW,P,hP,u,hu⟩ := h
  exact ⟨W,hWV,hW,P,hP,u,fun q => (hu q).1⟩

end CompoundFeasibility.OriginalAttainmentFlag4
