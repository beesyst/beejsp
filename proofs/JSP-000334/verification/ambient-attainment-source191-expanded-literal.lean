import SubspaceBridge.RestrictedSource4
open scoped BigOperators Classical Matrix

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.M191LiteralOriginalAttainmentFlag4
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

end CompoundFeasibility.M191LiteralOriginalAttainmentFlag4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.M191LiteralOriginalAttainmentTransport4
open M191LiteralOriginalAttainmentFlag4 BoundedWeights4 OriginalFlagAssembly4 Exterior3 OriginalLastDual4

theorem source_scaled_selected_attaining_flag4 (N : ℕ) (hN : 1 ≤ N)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc : ∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧
      (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (delta : ℝ) (hd : 0 < delta) (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q)
    (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    attainingFlagFamily4 A₂ A₃ L (sourceUnit42 L hL)
      (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃)
      j.succ (powerImage4 N U) (powerImage4_gt_one N hN U hQU) := by
  obtain ⟨ha₀,ha₂,ha₃,hab⟩ := scaledWeights4_conditions N hN c₀ c₂ c₃ hc hb
  obtain ⟨hdn,hgapn⟩ := selected_gap_powerImage4 N hN A₂ A₃ L (sourceUnit42 L hL)
    c₀ c₂ c₃ delta hd U hQU j hgap
  exact source_selected_gap_attaining_flag4 A₂ A₃ L h₂ h₃ hL hAlg (delta/(N : ℝ)) hdn
    (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) ha₀ ha₂ ha₃ hab
    (powerImage4 N U) (powerImage4_unbounded N hN U hU) (powerImage4_gt_one N hN U hQU) j hgapn

theorem transportedFrame4_attaining (N : ℕ) (hN : 1 ≤ N)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (U Wfixed : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q)
    (hWR : ∀ R ∈ Wfixed, 1 < R)
    (v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃))
    (hv : ∀ r : Wfixed, ambientFrame4 A₂ A₃ L hL r.val (hWR r.val r.property)
      (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) :
    ∀ q : originalPreimage4 N U Wfixed, ambientFrame4 A₂ A₃ L hL q.val (hQU q.val q.property.1)
      c₀ c₂ c₃ (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q) := by
  intro q
  let r : Wfixed := ⟨q.val^N,q.property.2⟩
  have hvalues : (fun i => integerReal
      (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q i : Fin 4 → ℤ)) =
      (fun i => integerReal (v r i : Fin 4 → ℤ)) := by
    funext i
    exact congrArg integerReal (transportedFrame4_values N hN A₂ A₃ c₂ c₃ U Wfixed v q i)
  have hnorm := exactNormalization4_proved N hN A₂ A₃ L hL c₀ c₂ c₃ q.val (hQU q.val q.property.1)
  constructor
  · rw [hvalues]
    exact (hv r).1
  · intro i
    change coordinateGauge4 (originalCoordinates4 L hL q.val (hQU q.val q.property.1) c₀)
      ((fun j => integerReal (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q j : Fin 4 → ℤ)) i) = _
    rw [hvalues]
    have hatt := (hv r).2 i
    change coordinateGauge4 (originalCoordinates4 L hL (q.val^N)
      (power_gt_one4 N hN q.val (hQU q.val q.property.1)) (scaledWeights4 N c₀))
      (integerReal (v r i : Fin 4 → ℤ)) =
      sourceMinima4 A₂ A₃ L hL (q.val^N) (power_gt_one4 N hN q.val (hQU q.val q.property.1))
        (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) i at hatt
    rw [hnorm.2.1,hnorm.2.2.2.2.2 i] at hatt
    exact hatt


theorem source_bounded_weights_attaining_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (delta : ℝ) (hd : 0 < delta) (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q)
    (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    ∃ (N : ℕ) (hN : 1 ≤ N),
      (∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧ (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) ∧
      (∀ i, |scaledWeights4 N c₀ i| ≤ 1) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₂ i ∧ scaledWeights4 N c₂ i ≤ 0) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₃ i ∧ scaledWeights4 N c₃ i ≤ 0) ∧
      (∑ i, (scaledWeights4 N c₀ i+scaledWeights4 N c₂ i+scaledWeights4 N c₃ i) = 0) ∧
      exactNormalization4 N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ ∧
      0 < delta/(N : ℝ) ∧
      (∀ Q ∈ U, Q^(-delta) = (Q^N)^(-(delta/(N : ℝ)))) ∧
      ¬ BddAbove (powerImage4 N U) ∧
      ∃ hWR : ∀ R ∈ powerImage4 N U, 1 < R,
        (∀ (R : ℝ) (hR : R ∈ powerImage4 N U),
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ*R^(-(delta/(N : ℝ)))) ∧
        ∃ (Wfixed : Set ℝ) (hWsub : Wfixed ⊆ powerImage4 N U), ¬ BddAbove Wfixed ∧
          ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = j.val+1 ∧
            (1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3) ∧ P ≠ ⊤ ∧
            ∃ v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃),
              (∀ r : Wfixed, P = originalFirstFlag4 j.succ (fun i => (v r i : Fin 4 → ℤ))) ∧
              (∀ r : Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) r.val
                (hWR r.val (hWsub r.property)) (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) ∧
              originalPreimage4 N U Wfixed ⊆ U ∧ ¬ BddAbove (originalPreimage4 N U Wfixed) ∧
              ∃ u : (q : originalPreimage4 N U Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                (∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ))) ∧
                ∀ q : originalPreimage4 N U Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val q.property.1)
                  c₀ c₂ c₃ (u q) := by
  obtain ⟨N,hN,hc⟩ := exists_weight_bound4 c₀ c₂ c₃ hc₂ hc₃
  obtain ⟨ha₀,ha₂,ha₃,hab⟩ := scaledWeights4_conditions N hN c₀ c₂ c₃ hc hb
  obtain ⟨hdn,hgapn⟩ := selected_gap_powerImage4 N hN A₂ A₃ L (sourceUnit42 L hL)
    c₀ c₂ c₃ delta hd U hQU j hgap
  obtain ⟨Wfixed,hWsub,hW,P,hPdim,v,hv⟩ := source_scaled_selected_attaining_flag4 N hN A₂ A₃ L
    h₂ h₃ hL hAlg c₀ c₂ c₃ hc hb delta hd U hU hQU j hgap
  have hproper : P ≠ ⊤ := by
    intro htop
    have hfour : Module.finrank ℚ P = 4 := by
      rw [htop,finrank_top]
      simp
    change Module.finrank ℚ P = j.val+1 at hPdim
    omega
  have hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3 := by
    change Module.finrank ℚ P = j.val+1 at hPdim
    constructor <;> omega
  have hvFlag := fun r => (hv r).1
  have hvAtt := fun r => (hv r).2
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,exactNormalization4_proved N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃,
    hdn,(fun Q hQ => scaled_gap_power4 N hN Q (hQU Q hQ) delta),powerImage4_unbounded N hN U hU,
    powerImage4_gt_one N hN U hQU,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hvFlag,hvAtt,
    (fun _ h => h.1),originalPreimage4_unbounded N U Wfixed hQU hW hWsub,?_⟩
  refine ⟨transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v,
    transportedFrame4_values N hN A₂ A₃ c₂ c₃ U Wfixed v,
    transportedFrame4_flag N hN A₂ A₃ c₂ c₃ U Wfixed j.succ P v hvFlag,?_⟩
  exact transportedFrame4_attaining N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ U Wfixed hQU
      (fun R hR => powerImage4_gt_one N hN U hQU R (hWsub hR)) v hvAtt


end CompoundFeasibility.M191LiteralOriginalAttainmentTransport4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.M191LiteralOriginalAttainmentFlag4

theorem source_same_frame_restricted_prefix4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (d : Fin 4) (hPdim : Module.finrank ℚ P = d.val)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : ambientFrame4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ u)
    (hflag : P = OriginalFlagAssembly4.originalFirstFlag4 d (fun i => (u i : Fin 4 → ℤ))) :
    ∀ k, RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (RestrictedGeometry4.ambientPrefixIndex4 P hP k) := by
  let emb := RestrictedGeometry4.ambientPrefixIndex4 P hP
  let v : Fin (Module.finrank ℚ P) → originalSourceGroup4 A₂ A₃ Q c₂ c₃ := fun i => u (emb i)
  have hv : LinearIndependent ℝ (fun i => integerReal (v i : Fin 4 → ℤ)) :=
    hu.1.comp emb (Fin.castLE_injective _)
  have hmem (i : Fin (Module.finrank ℚ P)) : integerReal (v i : Fin 4 → ℤ) ∈
      RestrictedGeometry4.rationalRealSpan4 P := by
    have hr : (fun j => ((u (emb i) : Fin 4 → ℤ) j : ℚ)) ∈ P := by
      rw [hflag]
      apply Submodule.subset_span
      refine ⟨⟨i.val,by omega⟩,?_⟩
      rfl
    apply Submodule.subset_span
    refine ⟨(fun j => ((u (emb i) : Fin 4 → ℤ) j : ℚ)),hr,?_⟩
    ext j
    simp [v,integerReal]
  exact RestrictedGeometry4.source_restricted_prefix_eq4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ v hv hmem
    (fun i => hu.2 (emb i))

end CompoundFeasibility.M191LiteralOriginalAttainmentFlag4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M191LiteralNonrothAttainmentFlag4
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4 BoundedWeights4 M191LiteralOriginalAttainmentFlag4 M191LiteralOriginalAttainmentTransport4
noncomputable section

def selectedAttainingExceptionalFlag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3) (hQV : ∀ Q ∈ V, 1 < Q) : Prop :=
    ∃ (N : ℕ) (hN : 1 ≤ N),
      (∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧ (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) ∧
      (∀ i, |scaledWeights4 N c₀ i| ≤ 1) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₂ i ∧ scaledWeights4 N c₂ i ≤ 0) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₃ i ∧ scaledWeights4 N c₃ i ≤ 0) ∧
      (∑ i, (scaledWeights4 N c₀ i+scaledWeights4 N c₂ i+scaledWeights4 N c₃ i) = 0) ∧
      exactNormalization4 N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ ∧
      0 < delta/(N : ℝ) ∧
      (∀ Q ∈ V, Q^(-delta) = (Q^N)^(-(delta/(N : ℝ)))) ∧
      ¬ BddAbove (powerImage4 N V) ∧
      ∃ hWR : ∀ R ∈ powerImage4 N V, 1 < R,
        (∀ (R : ℝ) (hR : R ∈ powerImage4 N V),
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ*R^(-(delta/(N : ℝ)))) ∧
        ∃ (Wfixed : Set ℝ) (hWsub : Wfixed ⊆ powerImage4 N V), ¬ BddAbove Wfixed ∧
          ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = j.val+1 ∧
            ∃ hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3, P ≠ ⊤ ∧
            ∃ v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃),
              (∀ r : Wfixed, P = originalFirstFlag4 j.succ (fun i => (v r i : Fin 4 → ℤ))) ∧
              (∀ r : Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) r.val (hWR r.val (hWsub r.property))
                (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) ∧
              originalPreimage4 N V Wfixed ⊆ V ∧ ¬ BddAbove (originalPreimage4 N V Wfixed) ∧
              ∃ u : (q : originalPreimage4 N V Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                (∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ))) ∧
                (∀ q : originalPreimage4 N V Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1)
                  c₀ c₂ c₃ (u q)) ∧
                (∀ (q : originalPreimage4 N V Wfixed) (k : Fin (Module.finrank ℚ P)),
                  RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L (sourceUnit42 L hL) q.val
                    (hQV q.val q.property.1) c₀ c₂ c₃ k =
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃
                    (RestrictedGeometry4.ambientPrefixIndex4 P hPbounds.2 k)) ∧
                originalPreimage4 N V Wfixed ⊆ U ∧
                (∀ q : originalPreimage4 N V Wfixed,
                  1 < q.val ∧ B < q.val ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.castSucc <
                    sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.succ*q.val^(-delta) ∧
                  c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ∧
                  (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ≤ C4) ∧
                (∀ Q ∈ originalPreimage4 N V Wfixed, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
                  OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
                  x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
                  coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2)))

theorem source_selected_attaining_exceptional_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (epsilon delta c4 C4 B : ℝ) (hd : 0 < delta) (U V : Set ℝ) (j : Fin 3) (hVU : V ⊆ U) (hV : ¬ BddAbove V)
    (hQV : ∀ Q ∈ V, 1 < Q)
    (hpoints : ∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-delta))
    (hsol : ∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
      OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
      x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
      coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2)))
    (hprod : ∀ (Q : ℝ) (hQ : 1 < Q),
      c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ∧
      (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ≤ C4)
    : selectedAttainingExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV := by
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,u,hvalues,hflag,hAtt⟩ :=
    source_bounded_weights_attaining_flag4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb
      delta hd V hV hQV j (fun Q hq => (hpoints Q hq).2)
  obtain ⟨_,hFinalU,hFinalpoints,hFinalsol⟩ := NonrothFixedFlag4.source_preimage_evidence4 A₂ A₃ L hL c₀ c₂ c₃
    epsilon delta c4 C4 B U V j hVU hQV hpoints hsol hprod N Wfixed
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,?_⟩
  refine ⟨u,hvalues,hflag,hAtt,?_,hFinalU,hFinalpoints,hFinalsol⟩
  intro q
  exact source_same_frame_restricted_prefix4 P hPbounds.2 j.succ hPdim A₂ A₃ L
    (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ (u q) (hAtt q) (hflag q)

theorem source_nonroth_attaining_fixed_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hn : ¬ OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃) :
    ∃ epsilon deltaGap c4 C4 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 3,
      0 < epsilon ∧ deltaGap = (epsilon/2)/4 ∧ 0 < deltaGap ∧
      0 < c4 ∧ 0 < C4 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
        x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ∧
        (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ≤ C4) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧
      ∃ hQV : ∀ Q ∈ V, 1 < Q,
        (∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-deltaGap)) ∧
        selectedAttainingExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon deltaGap c4 C4 B U V j hQV := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints⟩ :=
    OriginalFlagAssembly4.source_normalized_nonroth_gap4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ hc₂ hc₃ hb hn
  refine ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,?_⟩
  exact source_selected_attaining_exceptional_flag4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ hAlg hc₂ hc₃ hb
    epsilon deltaGap c4 C4 B hd U V j hVU hV hQV hpoints hsol hprod

theorem selectedAttainingExceptionalFlag4_forget
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3)
    (hQV : ∀ Q ∈ V, 1 < Q)
    (h : selectedAttainingExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV) :
    NonrothFixedFlag4.selectedExceptionalFlag4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV := by
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol⟩ := h
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hFinalV,hFinal,?_⟩
  exact ⟨u,hvalues,hflag,hFinalU,hFinalpoints,hFinalsol⟩

theorem source_original_restricted_prefix_eq4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hn : ¬ OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃) :
    ∃ (W : Set ℝ) (hQW : ∀ Q ∈ W, 1 < Q), ¬ BddAbove W ∧
      ∃ P : Submodule ℚ (Fin 4 → ℚ),
        ∃ hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3,
          P ≠ ⊤ ∧ ∃ d : Fin 4, Module.finrank ℚ P = d.val ∧
            ∃ u : (q : W) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              (∀ q : W, P = originalFirstFlag4 d (fun i => (u q i : Fin 4 → ℤ))) ∧
              (∀ q : W, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQW q.val q.property)
                c₀ c₂ c₃ (u q)) ∧
              ∀ (q : W) (k : Fin (Module.finrank ℚ P)),
                RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L (sourceUnit42 L hL) q.val
                  (hQW q.val q.property) c₀ c₂ c₃ k =
                sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQW q.val q.property) c₀ c₂ c₃
                  (RestrictedGeometry4.ambientPrefixIndex4 P hPbounds.2 k) := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,hselected⟩ :=
    source_nonroth_attaining_fixed_flag4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb hn
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol⟩ := hselected
  exact ⟨originalPreimage4 N V Wfixed,(fun Q hQ => hQV Q hQ.1),hFinal,
    P,hPbounds,hproper,j.succ,hPdim,u,hflag,hAtt,hEq⟩


end
end CompoundFeasibility.M191LiteralNonrothAttainmentFlag4

#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.ambientFrame4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.attainingFlagFamily4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.source_rank1_attaining_flag4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.source_rank2_attaining_flag4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.source_rank3_attaining_flag4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.source_selected_gap_attaining_flag4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.attainingFlagFamily4_forget


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentTransport4.source_scaled_selected_attaining_flag4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentTransport4.transportedFrame4_attaining


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentTransport4.source_bounded_weights_attaining_flag4


#print axioms CompoundFeasibility.M191LiteralOriginalAttainmentFlag4.source_same_frame_restricted_prefix4


#print axioms CompoundFeasibility.M191LiteralNonrothAttainmentFlag4.selectedAttainingExceptionalFlag4


#print axioms CompoundFeasibility.M191LiteralNonrothAttainmentFlag4.source_selected_attaining_exceptional_flag4


#print axioms CompoundFeasibility.M191LiteralNonrothAttainmentFlag4.source_nonroth_attaining_fixed_flag4


#print axioms CompoundFeasibility.M191LiteralNonrothAttainmentFlag4.selectedAttainingExceptionalFlag4_forget


#print axioms CompoundFeasibility.M191LiteralNonrothAttainmentFlag4.source_original_restricted_prefix_eq4
