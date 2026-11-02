import verification.SchlickeweiLiteralBridges163
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.Reference161Literal
open SourceReadiness6 SourceMixed6 SchlickeweiReference6 SchlickeweiDualVanishing6
open SchlickeweiIntegerPairing6 SchlickeweiEquation4116 Auxiliary6.SourceExpansion
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

open Reference163Bridges SchlickeweiRealCompletion6

theorem complete_literal
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ (B : ℝ) (q1 : V),
      let b : Fin 6 → ℤ := SourceHeightBounds6.rawNormal6 (Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ)))
      let T2 := Finset.univ.filter (fun i =>
        (∑ k, algebraMap ℚ ℚ_[2] (b k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)
      let T3 := Finset.univ.filter (fun i =>
        (∑ k, algebraMap ℚ ℚ_[3] (b k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧ b ≠ 0 ∧
      ∃ (hT2 : T2.Nonempty) (hT3 : T3.Nonempty), ∀ q : V, B < q.val →
        let Q := q.val ^ (11 : ℕ)
        let g2 : ℤ := T2.inf' hT2 (fun i => ⌊Real.log Q / Real.log (2 : ℝ) *
          (∑ k : Fin 5, R.c 1 (i.succAbove k))⌋)
        let g3 : ℤ := T3.inf' hT3 (fun i => ⌊Real.log Q / Real.log (3 : ℝ) *
          (∑ k : Fin 5, R.c 2 (i.succAbove k))⌋)
        let y : Fin 6 → ℤ := ((6 : ℤ) ^ (5 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat) • b
        y ≠ 0 ∧ sourceAuxiliaryInteger6 R q y ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℝ (y k : ℚ) * (compound L)⁻¹.transpose i k‖ ≤
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
          Q ^ (R.c 0 i)) ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℚ_[2] (y k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
        (2 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ))) ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℚ_[3] (y k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
        (3 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ))) ∧
      (Submodule.span ℚ {fun i => (y i : ℚ)} = Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
      (Submodule.span ℚ {fun i => (R.M q i : ℚ)} = Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
      (Submodule.span ℚ {fun i => rationalFrameDual42
        (fun j k => ((R.w q j : Fin 6 → ℤ) k : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single i 1)} =
          Submodule.span ℚ {fun i => (b i : ℚ)}) := by
  obtain ⟨B, q1, hB, htail, hb, hall⟩ := source_satz51_selected6 R h2 h3 hLdet hc2 hc3
  have hs := source_reference_supports6 R h2 h3 q1
  have hT2 := support_representation6 2 A2 (sourceReference6 R q1) hs.1
  have hT3 := support_representation6 3 A3 (sourceReference6 R q1) hs.2
  refine ⟨B, q1, ?_⟩
  refine And.intro hB ?_
  refine And.intro htail ?_
  refine And.intro hb ?_
  refine ⟨hT2, hT3, ?_⟩
  intro q hq
  let g2 : ℤ := (Finset.univ.filter (fun i =>
    (∑ k, algebraMap ℚ ℚ_[2] (sourceReference6 R q1 k : ℚ) *
      ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)).inf' hT2
      (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (2 : ℝ) *
        (∑ k : Fin 5, R.c 1 (i.succAbove k))⌋)
  let g3 : ℤ := (Finset.univ.filter (fun i =>
    (∑ k, algebraMap ℚ ℚ_[3] (sourceReference6 R q1 k : ℚ) *
      ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)).inf' hT3
      (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (3 : ℝ) *
        (∑ k : Fin 5, R.c 2 (i.succAbove k))⌋)
  let y : Fin 6 → ℤ := ((6 : ℤ) ^ (5 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat) • sourceReference6 R q1
  have he2 : sourceFloor2 R h2 h3 q1 q = g2 := source_floor2_representation6 R h2 h3 q1 q hT2
  have he3 : sourceFloor3 R h2 h3 q1 q = g3 := source_floor3_representation6 R h2 h3 q1 q hT3
  have hy : rescaledReference6 R h2 h3 q1 q = y := source_rescale_representation6 R h2 h3 q1 q hT2 hT3
  have hr := hall q hq
  have hny : y ≠ 0 := hy ▸ hr.1
  have hay : sourceAuxiliaryInteger6 R q y :=
    (congrArg (fun z : Fin 6 → ℤ => sourceAuxiliaryInteger6 R q z) hy).mp hr.2.1
  have hreal := real_bound_representation6 (compound L) y _ _ _ hay.1
  have hp2 := finite_bound_representation6 2 A2 y q.val c2 hay.2.1
  have hp3 := finite_bound_representation6 3 A3 y q.val c3 hay.2.2
  have hly : Submodule.span ℚ {fun i => (y i : ℚ)} =
      Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} :=
    (congrArg (fun z : Fin 6 → ℤ => Submodule.span ℚ {fun i => (z i : ℚ)}) hy).symm.trans hr.2.2.1
  have hM := hr.2.2.2.1
  have hD := hr.2.2.2.2
  refine And.intro hny ?_
  refine And.intro hay ?_
  refine And.intro hreal ?_
  refine And.intro hp2 ?_
  refine And.intro hp3 ?_
  refine And.intro hly ?_
  exact And.intro hM hD

theorem original_family_literal (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
        (fun q hq => hQU q (hVU hq))),
    ∃ (B : ℝ) (q1 : V),
      let b : Fin 6 → ℤ := SourceHeightBounds6.rawNormal6 (Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ)))
      let T2 := Finset.univ.filter (fun i =>
        (∑ k, algebraMap ℚ ℚ_[2] (b k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)
      let T3 := Finset.univ.filter (fun i =>
        (∑ k, algebraMap ℚ ℚ_[3] (b k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧ b ≠ 0 ∧
      ∃ (hT2 : T2.Nonempty) (hT3 : T3.Nonempty), ∀ q : V, B < q.val →
        let Q := q.val ^ (11 : ℕ)
        let g2 : ℤ := T2.inf' hT2 (fun i => ⌊Real.log Q / Real.log (2 : ℝ) *
          (∑ k : Fin 5, R.c 1 (i.succAbove k))⌋)
        let g3 : ℤ := T3.inf' hT3 (fun i => ⌊Real.log Q / Real.log (3 : ℝ) *
          (∑ k : Fin 5, R.c 2 (i.succAbove k))⌋)
        let y : Fin 6 → ℤ := ((6 : ℤ) ^ (5 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat) • b
        y ≠ 0 ∧ sourceAuxiliaryInteger6 R q y ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℝ (y k : ℚ) * (compound L)⁻¹.transpose i k‖ ≤
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3)) /
          Q ^ (R.c 0 i)) ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℚ_[2] (y k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
        (2 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ))) ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℚ_[3] (y k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
        (3 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ))) ∧
      (Submodule.span ℚ {fun i => (y i : ℚ)} = Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
      (Submodule.span ℚ {fun i => (R.M q i : ℚ)} = Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
      (Submodule.span ℚ {fun i => rationalFrameDual42
        (fun j k => ((R.w q j : Fin 6 → ℤ) k : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single i 1)} =
          Submodule.span ℚ {fun i => (b i : ℚ)}) := by
  obtain ⟨V, hVU, _, _, hR⟩ := source_compound_unbounded_readiness42 A2 A3 L h2 h3 hL hAlg
    delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  obtain ⟨R⟩ := hR
  exact ⟨V, hVU, R, complete_literal R h2 h3 hL hc2 hc3⟩

end CompoundFeasibility.Reference161Literal
#check CompoundFeasibility.Reference161Literal.complete_literal
#print CompoundFeasibility.Reference161Literal.complete_literal
#print axioms CompoundFeasibility.Reference161Literal.complete_literal
#check CompoundFeasibility.Reference161Literal.original_family_literal
#print CompoundFeasibility.Reference161Literal.original_family_literal
#print axioms CompoundFeasibility.Reference161Literal.original_family_literal
