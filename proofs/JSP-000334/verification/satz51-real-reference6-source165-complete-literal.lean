import SubspaceBridge.OriginalPlaneCoupling42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Coupling165Literal
open SourceWeights SourceReadiness6 OriginalPlaneRecovery42
open SchlickeweiRealCompletion6 SchlickeweiReference6 SchlickeweiDualVanishing6
theorem complete_literal (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (delta4 : ℝ) (hd : 0 < delta4) (c0 c2 c3 : Fin 4 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hbalance : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ U),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 1 <
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 2 * q^(-delta4)) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U)
      (R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)))
      (u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3)
      (v : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (sigma : V → Equiv.Perm (Fin 6))
      (w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (kappa : ℝ),
      ¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)) ∧
      R.w = w ∧ R.sigma = sigma ∧
      (∃ q0 : V, R.c = fixedWeights
        (fun i => logWeight (q0.val^(11 : ℕ)) (actualWidths A2 A3 L (sourceUnit42 L hL)
          q0.val (hQU q0.val (hVU q0.property)) c0 c2 c3 (sigma q0) i))
        (finiteWeight c2) (finiteWeight c3)) ∧
      ∀ q : V,
        sourceHyperplane42 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property))
          c0 c2 c3 kappa (u q) (v q) ∧
        rationalDualLine42 (fun i => (u q i : Fin 4 → ℤ)) (fun j => (v q j : Fin 6 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) ∧
        (firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => (orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
            (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) j i : ℚ))) ∧
        (firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => ((v q j : Fin 6 → ℤ) i : ℚ))) ∧
        orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) 5 =
            wedge (u q 2 : Fin 4 → ℤ) (u q 3 : Fin 4 → ℤ) := by
  exact source_original_coupled_readiness42 A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap

theorem same_R_fixed_line_literal (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (delta4 : ℝ) (hd : 0 < delta4) (c0 c2 c3 : Fin 4 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hbalance : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ U),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 1 <
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 2 * q^(-delta4)) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U)
      (R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)))
      (u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3)
      (v : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (sigma : V → Equiv.Perm (Fin 6))
      (w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (kappa : ℝ),
      (¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)) ∧
      R.w = w ∧ R.sigma = sigma ∧
      (∃ q0 : V, R.c = fixedWeights
        (fun i => logWeight (q0.val^(11 : ℕ)) (actualWidths A2 A3 L (sourceUnit42 L hL)
          q0.val (hQU q0.val (hVU q0.property)) c0 c2 c3 (sigma q0) i))
        (finiteWeight c2) (finiteWeight c3)) ∧
      ∀ q : V,
        sourceHyperplane42 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property))
          c0 c2 c3 kappa (u q) (v q) ∧
        rationalDualLine42 (fun i => (u q i : Fin 4 → ℤ)) (fun j => (v q j : Fin 6 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) ∧
        (firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => (orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
            (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) j i : ℚ))) ∧
        (firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => ((v q j : Fin 6 → ℤ) i : ℚ))) ∧
        orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) 5 =
            wedge (u q 2 : Fin 4 → ℤ) (u q 3 : Fin 4 → ℤ)) ∧
      ∃ (B : ℝ) (q1 : V), 1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
        sourceReference6 R q1 ≠ 0 ∧ ∀ q : V, B < q.val →
          Submodule.span ℚ {dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
            (sourceFrameIndependent6 R q)} =
          Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} := by
  obtain ⟨V,hVU,R,u,v,sigma,w,kappa,hprops⟩ := source_original_coupled_readiness42 A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  obtain ⟨B,q1,hB,htail,hb,hline⟩ := source_satz51_selected6 R h2 h3 hL hc2 hc3
  exact ⟨V,hVU,R,u,v,sigma,w,kappa,hprops,B,q1,hB,htail,hb,fun q hq => (hline q hq).2.2.2.2⟩

#check complete_literal
#print complete_literal
#print axioms complete_literal
#check same_R_fixed_line_literal
#print same_R_fixed_line_literal
#print axioms same_R_fixed_line_literal
end CompoundFeasibility.Coupling165Literal
