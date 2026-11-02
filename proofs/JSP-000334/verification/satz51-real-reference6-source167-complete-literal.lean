import SubspaceBridge.OriginalShortPlane42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Short167Literal
open OriginalShortPlane42 OriginalPlaneRecovery42 SourceWeights SourceReadiness6 SourceNormalIndex SchlickeweiDualVanishing6
open SchlickeweiReference6 SchlickeweiRealCompletion6

theorem source_signature_literal (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
      (kappa B : ℝ) (q1 : V) (b : Fin 6 → ℤ) (P : Submodule ℚ (Fin 4 → ℚ)),
      ((¬ BddAbove V ∧
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
      b = sourceReference6 R q1 ∧ b ≠ 0 ∧ normalForm6 b ≠ 0 ∧
      P = radical42 (normalForm6 b) ∧ Module.finrank ℚ P = 2 ∧
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
      ∀ q : V, B < q.val →
        LinearMap.ker (normalForm6 b) = firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) ∧
        ∃ hu : LinearIndependent ℚ (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)),
          let g := wedgeDual42 (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 2)
            (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 3)
          g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker (normalForm6 b) ∧
          ∃ a : ℚ, a ≠ 0 ∧ normalForm6 b = a • g ∧
            P = Submodule.span ℚ {fun i => ((u q 0 : Fin 4 → ℤ) i : ℚ),
              fun i => ((u q 1 : Fin 4 → ℤ) i : ℚ)}) ∧
      ∀ q : V, B < q.val → ∀ x : originalSourceGroup4 A2 A3 q.val c2 c3,
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL)
          q.val (hQU q.val (hVU q.property)) c0) (integerReal (x : Fin 4 → ℤ)) <
          sourceMinima4 A2 A3 L (sourceUnit42 L hL)
            q.val (hQU q.val (hVU q.property)) c0 c2 c3 2 →
        (fun i => ((x : Fin 4 → ℤ) i : ℚ)) ∈ P := by
  exact source_original_short_in_fixed_plane42 A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap

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
      (kappa B : ℝ) (q1 : V) (b : Fin 6 → ℤ) (P : Submodule ℚ (Fin 4 → ℚ)),
      (      ((¬ BddAbove V ∧
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
      b = sourceReference6 R q1 ∧ b ≠ 0 ∧ normalForm6 b ≠ 0 ∧
      P = radical42 (normalForm6 b) ∧ Module.finrank ℚ P = 2 ∧
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
      ∀ q : V, B < q.val →
        LinearMap.ker (normalForm6 b) = firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) ∧
        ∃ hu : LinearIndependent ℚ (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)),
          let g := wedgeDual42 (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 2)
            (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 3)
          g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker (normalForm6 b) ∧
          ∃ a : ℚ, a ≠ 0 ∧ normalForm6 b = a • g ∧
            P = Submodule.span ℚ {fun i => ((u q 0 : Fin 4 → ℤ) i : ℚ),
              fun i => ((u q 1 : Fin 4 → ℤ) i : ℚ)}) ∧
      ∀ q : V, B < q.val → ∀ x : originalSourceGroup4 A2 A3 q.val c2 c3,
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL)
          q.val (hQU q.val (hVU q.property)) c0) (integerReal (x : Fin 4 → ℤ)) <
          sourceMinima4 A2 A3 L (sourceUnit42 L hL)
            q.val (hQU q.val (hVU q.property)) c0 c2 c3 2 →
        (fun i => ((x : Fin 4 → ℤ) i : ℚ)) ∈ P) ∧
      ∀ q : V, B < q.val → ∀ x : Fin 4 → ℤ,
        x ∈ sourceLattice4 A2 A3
          (fun i => Nat.ceil (JSP000334.qThreshold 2 q.val (c2 i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 q.val (c3 i))) →
        ‖originalCoordinates4 L (sourceUnit42 L hL)
          q.val (hQU q.val (hVU q.property)) c0 (integerReal x)‖ <
          sourceMinima4 A2 A3 L (sourceUnit42 L hL)
            q.val (hQU q.val (hVU q.property)) c0 c2 c3 2 →
        (fun i => (x i : ℚ)) ∈ P := by
  obtain ⟨V,hVU,R,u,v,sigma,w,kappa,B,q1,b,P,hrest⟩ := source_original_short_in_fixed_plane42
    A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  refine ⟨V,hVU,R,u,v,sigma,w,kappa,B,q1,b,P,hrest,?_⟩
  intro q hq x hx hnorm
  exact hrest.2 q hq ⟨x,hx⟩ hnorm

end CompoundFeasibility.Short167Literal
#check CompoundFeasibility.Short167Literal.source_signature_literal
#print CompoundFeasibility.Short167Literal.source_signature_literal
#print axioms CompoundFeasibility.Short167Literal.source_signature_literal
#check CompoundFeasibility.Short167Literal.complete_literal
#print CompoundFeasibility.Short167Literal.complete_literal
#print axioms CompoundFeasibility.Short167Literal.complete_literal
