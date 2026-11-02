import verification.SchlickeweiLiteralBridges163
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.Reference159Literal
open SourceReadiness6 SourceMixed6 SchlickeweiReference6 SchlickeweiDualVanishing6
open SchlickeweiIntegerPairing6 SchlickeweiEquation4116 Auxiliary6.SourceExpansion
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

open Reference163Bridges

theorem complete_literal
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ (Bzero Bpoint T : ℝ) (q1 : V),
      let b : Fin 6 → ℤ := SourceHeightBounds6.rawNormal6 (Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ)))
      let T2 := Finset.univ.filter (fun i =>
        (∑ k, algebraMap ℚ ℚ_[2] (b k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) ≠ 0)
      let T3 := Finset.univ.filter (fun i =>
        (∑ k, algebraMap ℚ ℚ_[3] (b k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) ≠ 0)
      max Bzero (max Bpoint T) < q1.val ∧
      120 * (q1.val ^ (11 : ℕ)) ^ (-5 * R.delta) ≤ 1 ∧ b ≠ 0 ∧
      (∀ i, (b i : ℚ) = ((Matrix.of (fun j => (R.w q1 j : Fin 6 → ℤ))).det : ℚ) *
        dualVector6 (fun j => (R.w q1 j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q1) i) ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℝ (b k : ℚ) * (compound L)⁻¹.transpose i k‖ ≤
        ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q1.val c2 c3)) /
          (q1.val ^ (11 : ℕ)) ^ (R.c 0 i)) ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℚ_[2] (b k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
        (2 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 2 q1.val
            (pairWeights42 c2 (i.succAbove k))) : ℤ))) ∧
      (∀ i, ‖∑ k, algebraMap ℚ ℚ_[3] (b k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
        (3 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 3 q1.val
            (pairWeights42 c3 (i.succAbove k))) : ℤ))) ∧
      (Submodule.span ℚ {fun i => (b i : ℚ)} = Submodule.span ℚ {fun i => (R.M q1 i : ℚ)}) ∧
      (∀ s ∈ admissibleMixed6 R.c (R.delta/2),
        ‖∑ k, algebraMap ℚ ℝ (b k : ℚ) * (compound L)⁻¹.transpose (s 0) k‖ *
        ‖∑ k, algebraMap ℚ ℚ_[2] (b k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose (s 1) k‖ *
        ‖∑ k, algebraMap ℚ ℚ_[3] (b k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose (s 2) k‖ = 0) ∧
      ∃ (hT2 : T2.Nonempty) (hT3 : T3.Nonempty), ∀ q : V,
        let g2 : ℤ := T2.inf' hT2 (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (2 : ℝ) *
          (∑ k : Fin 5, R.c 1 (i.succAbove k))⌋)
        let g3 : ℤ := T3.inf' hT3 (fun i => ⌊Real.log (q.val ^ (11 : ℕ)) / Real.log (3 : ℝ) *
          (∑ k : Fin 5, R.c 2 (i.succAbove k))⌋)
        let y : Fin 6 → ℤ := ((6 : ℤ) ^ (5 : ℕ) * 2 ^ (-g2).toNat * 3 ^ (-g3).toNat) • b
        g2 ≤ 0 ∧ g3 ≤ 0 ∧ y ≠ 0 ∧
        (Submodule.span ℚ {fun i => (y i : ℚ)} = Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
        ((fun i => (y i : ℚ)) = ((6 : ℚ) ^ (5 : ℕ) * 2 ^ (-g2) * 3 ^ (-g3)) •
          (fun i => (b i : ℚ))) ∧
        (∀ i, ‖∑ k, algebraMap ℚ ℚ_[2] (y k : ℚ) *
          ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
        (2 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 2 q.val
            (pairWeights42 c2 (i.succAbove k))) : ℤ))) ∧
        (∀ i, ‖∑ k, algebraMap ℚ ℚ_[3] (y k : ℚ) *
          ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
        (3 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 3 q.val
            (pairWeights42 c3 (i.succAbove k))) : ℤ))) := by
  obtain ⟨Bzero, Bpoint, T, q1, hq1, hsmall, hb, haux, hline, hs2, hs3, hzero, hres⟩ :=
    source_reference_rescaling6 R h2 h3 hLdet hc2 hc3
  have hreal := real_bound_representation6 (compound L) (sourceReference6 R q1) _ _ _ haux.1
  have hp2 := finite_bound_representation6 2 A2 (sourceReference6 R q1) q1.val c2 haux.2.1
  have hp3 := finite_bound_representation6 3 A3 (sourceReference6 R q1) q1.val c3 haux.2.2
  have hprod := product_zero_representation6 A2 A3 L (sourceReference6 R q1) _ hzero
  have hT2 := support_representation6 2 A2 (sourceReference6 R q1) hs2
  have hT3 := support_representation6 3 A3 (sourceReference6 R q1) hs3
  refine ⟨Bzero, Bpoint, T, q1, ?_⟩
  refine And.intro hq1 ?_
  refine And.intro hsmall ?_
  refine And.intro hb ?_
  refine And.intro (source_reference_signed_dual6 R q1) ?_
  refine And.intro hreal ?_
  refine And.intro hp2 ?_
  refine And.intro hp3 ?_
  refine And.intro hline ?_
  refine And.intro hprod ?_
  refine ⟨hT2, hT3, ?_⟩
  intro q
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
  have hn := source_floor_nonpos6 R h2 h3 hc2 hc3 q1 q
  have hr := hres q
  have hn2 : g2 ≤ 0 := he2 ▸ hn.1
  have hn3 : g3 ≤ 0 := he3 ▸ hn.2
  have hny : y ≠ 0 := hy ▸ hr.1
  have hly : Submodule.span ℚ {fun i => (y i : ℚ)} =
      Submodule.span ℚ {fun i => (sourceReference6 R q1 i : ℚ)} :=
    (congrArg (fun z : Fin 6 → ℤ => Submodule.span ℚ {fun i => (z i : ℚ)}) hy).symm.trans hr.2.1
  have hpub := rescaled_reference_published6 R h2 h3 hc2 hc3 q1 q
  have hcast := congrArg (fun z : Fin 6 → ℤ => fun i => (z i : ℚ)) hy
  have hscalar := congrArg₂ (fun u v : ℤ =>
    ((6 : ℚ) ^ (5 : ℕ) * 2 ^ (-u) * 3 ^ (-v)) • (fun i => (sourceReference6 R q1 i : ℚ))) he2 he3
  have hpy : (fun i => (y i : ℚ)) =
      ((6 : ℚ) ^ (5 : ℕ) * 2 ^ (-g2) * 3 ^ (-g3)) •
        (fun i => (sourceReference6 R q1 i : ℚ)) := hcast.symm.trans (hpub.trans hscalar)
  have hy2 := finite_bound_representation6 2 A2 (rescaledReference6 R h2 h3 q1 q) q.val c2 hr.2.2.1
  have hby2 : ∀ i, ‖∑ k, algebraMap ℚ ℚ_[2] (y k : ℚ) *
      ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5,
        -(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ)) :=
    (congrArg (fun z : Fin 6 → ℤ => ∀ i,
      ‖∑ k, algebraMap ℚ ℚ_[2] (z k : ℚ) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
        (2 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ))) hy).mp hy2
  have hy3 := finite_bound_representation6 3 A3 (rescaledReference6 R h2 h3 q1 q) q.val c3 hr.2.2.2
  have hby3 : ∀ i, ‖∑ k, algebraMap ℚ ℚ_[3] (y k : ℚ) *
      ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5,
        -(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ)) :=
    (congrArg (fun z : Fin 6 → ℤ => ∀ i,
      ‖∑ k, algebraMap ℚ ℚ_[3] (z k : ℚ) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
        (3 : ℝ) ^ (∑ k : Fin 5,
          -(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ))) hy).mp hy3
  refine And.intro hn2 ?_
  refine And.intro hn3 ?_
  refine And.intro hny ?_
  refine And.intro hly ?_
  refine And.intro hpy ?_
  exact And.intro hby2 hby3

end CompoundFeasibility.Reference159Literal
#check CompoundFeasibility.Reference159Literal.complete_literal
#print CompoundFeasibility.Reference159Literal.complete_literal
#print axioms CompoundFeasibility.Reference159Literal.complete_literal
