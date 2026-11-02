import SubspaceBridge.Exterior3OriginalLine4
import SubspaceBridge.OriginalPlaneRecovery42
import SubspaceBridge.OriginalSpanTransport4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.OriginalFlagAssembly4
open Exterior3 OriginalLastDual4
noncomputable section

def originalFirstFlag4 (d : Fin 4) (u : Fin 4 → Fin 4 → ℤ) : Submodule ℚ (Fin 4 → ℚ) :=
  Submodule.span ℚ (Set.range (fun j : Fin d.val => fun i =>
    (u (Fin.castLE (Nat.le_of_lt d.isLt) j) i : ℚ)))

theorem originalFirstFlag4_one (u : Fin 4 → Fin 4 → ℤ) :
    originalFirstFlag4 1 u = Submodule.span ℚ {fun i => (u 0 i : ℚ)} := by
  unfold originalFirstFlag4
  change Submodule.span ℚ (Set.range (fun j : Fin 1 => fun i => (u (Fin.castLE (by decide : 1 ≤ 4) j) i : ℚ))) = _
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,rfl⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  · intro hx
    exact ⟨0,hx.symm⟩

theorem originalFirstFlag4_two (u : Fin 4 → Fin 4 → ℤ) :
    originalFirstFlag4 2 u = Submodule.span ℚ {fun i => (u 0 i : ℚ),fun i => (u 1 i : ℚ)} := by
  unfold originalFirstFlag4
  change Submodule.span ℚ (Set.range (fun j : Fin 2 => fun i => (u (Fin.castLE (by decide : 2 ≤ 4) j) i : ℚ))) = _
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,rfl⟩
    fin_cases j <;> simp
  · rintro (hx | hx)
    · exact ⟨0,hx.symm⟩
    · exact ⟨1,hx.symm⟩

theorem originalFirstFlag4_three (u : Fin 4 → Fin 4 → ℤ) :
    originalFirstFlag4 3 u = firstThreeSpan4 (fun j i => (u j i : ℚ)) := rfl

theorem originalFirstFlag4_three_eq (u : Fin 4 → Fin 4 → ℤ) :
    originalFirstFlag4 3 u = Submodule.span ℚ
      {fun i => (u 0 i : ℚ),fun i => (u 1 i : ℚ),fun i => (u 2 i : ℚ)} :=
  (originalFirstFlag4_three u).trans (firstThreeSpan4_eq _)

def selectedFlagFamily4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (c₂ c₃ : Fin 4 → ℝ)
    (d : Fin 4) (V : Set ℝ) : Prop :=
  ∃ (W : Set ℝ) (hWV : W ⊆ V), ¬ BddAbove W ∧
    ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = d.val ∧
      ∃ u : (q : W) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
        ∀ q : W, P = originalFirstFlag4 d (fun j => (u q j : Fin 4 → ℤ))

theorem source_rank1_flag_projection4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 0 <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 1*Q^(-delta)) :
    ∃ a : Fin 4 → ℤ, a ≠ 0 ∧
      ∃ (W : Set ℝ) (hWV : W ⊆ V), ¬ BddAbove W ∧
        ∃ P : Submodule ℚ (Fin 4 → ℚ), P = Submodule.span ℚ {fun i => (a i : ℚ)} ∧
          Module.finrank ℚ P = 1 ∧
          ∃ u : (q : W) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
            ∀ q : W, P = originalFirstFlag4 1 (fun j => (u q j : Fin 4 → ℤ)) := by
  classical
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,htails⟩ :=
    source_original_fixed_rank1_4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  obtain ⟨_,_,_,_,hfamilies⟩ := htails c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨V₀,hV₀V,_,_,u,_,Vprime,hVpV₀,_,_,Wnorm,hWR,_,_,_,_,hsource⟩ := hfamilies V hV hQV hgap
  obtain ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,b,B,hq1,hbint,hbn,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,Pc,hTspan,hF_eq,hF,hPc,hPcdim,hflags,C₄,kappa,hC₄,hk,hkeq,
    Qfixed,hQfV,hQfeq,hQf,hQcube,hret,R₀,hR₀,hcut,Qfinal,hQfinal,hQfinaleq,hQfinalU,hfinal,hlineFamily⟩ := hsource
  obtain ⟨a,_,ha,P1,hP1,hP1dim,_,hcontrol⟩ := hlineFamily
  have hWV : Qfinal ⊆ V := fun _ h => hV₀V (hVpV₀ (hQfV (hQfinal h)))
  let uFinal : (q : Qfinal) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃ :=
    fun q => u ⟨q.val,hVpV₀ (hQfV (hQfinal q.property))⟩
  refine ⟨a,ha,Qfinal,hWV,hQfinalU,P1,hP1,hP1dim,uFinal,?_⟩
  intro q
  rw [originalFirstFlag4_one]
  exact (hcontrol q).2.2.2.2.2.symm

theorem source_rank2_flag_projection4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 1 <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 2*Q^(-delta)) :
    selectedFlagFamily4 A₂ A₃ c₂ c₃ 2 V := by
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
  rw [originalFirstFlag4_two]
  exact hspan

theorem source_rank3_flag_projection4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 2 <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ 3*Q^(-delta)) :
    selectedFlagFamily4 A₂ A₃ c₂ c₃ 3 V := by
  classical
  obtain ⟨Uc,hUcV,hUc,u,F,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,b,B,hq1,hbint,hbn,hline,hbz,hB,htail,hfixed,
    Tspan,Wfinal,P,hTspan,hEq,hWfinal,hP,hPdim,hflags⟩ :=
    OriginalSpanTransport4.source_original_fixed_rank3_4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
      c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap
  have hFinalUc : Wfinal ⊆ Uc := by
    intro Q hQ
    rw [hEq] at hQ
    exact hWcU hQ.1
  have hWV : Wfinal ⊆ V := fun _ h => hUcV (hFinalUc h)
  let uFinal : (q : Wfinal) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃ :=
    fun q => u ⟨q.val,hFinalUc q.property⟩
  refine ⟨Wfinal,hWV,hWfinal,P,hPdim,uFinal,?_⟩
  intro q
  rw [originalFirstFlag4_three]
  exact (hflags ⟨q.val,hFinalUc q.property⟩ q.property).1


theorem source_normalized_nonroth_gap4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
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
        ∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-deltaGap) := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,_,_,hpoints⟩ :=
    OriginalVariableGap4.source_original_nonroth_gap4 A₂ A₃ L
      (sourceUnit42 A₂ h₂) (sourceUnit42 A₃ h₃) (sourceUnit42 L hL) c₀ c₂ c₃ hc₂ hc₃ hb hn
  have hQV : ∀ Q ∈ V, 1 < Q := fun Q hq => hB.trans (hpoints Q hq).1
  refine ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,?_⟩
  intro Q hq
  obtain ⟨hBQ,hQ,hgap⟩ := hpoints Q hq
  exact ⟨hBQ,hgap⟩

theorem source_selected_gap_fixed_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ V), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    selectedFlagFamily4 A₂ A₃ c₂ c₃ j.succ V := by
  fin_cases j
  · obtain ⟨a,ha,W,hWV,hW,P,hPa,hPdim,u,hu⟩ :=
      source_rank1_flag_projection4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
        c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap
    exact ⟨W,hWV,hW,P,hPdim,u,hu⟩
  · exact source_rank2_flag_projection4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
      c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap
  · exact source_rank3_flag_projection4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
      c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV hgap

theorem source_normalized_nonroth_fixed_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
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
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-deltaGap) ) ∧
        ∃ (W : Set ℝ) (hWV : W ⊆ V), ¬ BddAbove W ∧ (∀ Q ∈ W, 1 < Q) ∧
          ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = j.val+1 ∧
            1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3 ∧ P ≠ ⊤ ∧
            ∃ u : (q : W) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              ∀ q : W, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ)) := by
  classical
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints⟩ :=
    source_normalized_nonroth_gap4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃
      (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb hn
  obtain ⟨W,hWV,hW,P,hPdim,u,hu⟩ := source_selected_gap_fixed_flag4 A₂ A₃ L h₂ h₃ hL hAlg
    deltaGap hd c₀ c₂ c₃ hc₀ hc₂ hc₃ hb V hV hQV j (fun Q hq => (hpoints Q hq).2)
  have hdim : Module.finrank ℚ P = j.val+1 := hPdim
  have hlo : 1 ≤ Module.finrank ℚ P := by omega
  have hhi : Module.finrank ℚ P ≤ 3 := by have hj := j.isLt; omega
  have hproper : P ≠ ⊤ := by
    intro htop
    have hfour : Module.finrank ℚ P = 4 := by
      rw [htop,finrank_top]
      simp
    omega
  exact ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,
    W,hWV,hW,(fun Q hq => hQV Q (hWV hq)),P,hdim,hlo,hhi,hproper,u,hu⟩

end
end CompoundFeasibility.OriginalFlagAssembly4
