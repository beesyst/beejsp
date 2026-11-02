import SubspaceBridge.SourceRelativeIndex6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.RelativeIndex145Literal
open SourceRelativeIndex6 SourceNormalIndex SourceReadiness6 SourceHeightBounds6
  SourceNormalHeight SchlickeweiDualVanishing6
open Auxiliary6.SourceExpansion

theorem expand_signed_identity {F : Type*} [CommRing F]
    (B : Matrix (Fin 6) (Fin 6) F) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M : Fin 6 → ℤ) (g : ℤ) (i : Fin 6)
    (h : (-1 : F) ^ (5+i.val) *
      ((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det =
      (g : F) * CompoundFeasibility.SourceProper6.cofactorValue6 B M i) :
    (-1 : F) ^ (5+i.val) *
      (((v.map (Int.castRingHom F)) * B.transpose).submatrix
        Fin.castSucc i.succAbove).det =
      (g : F) * (∑ k, (M k : F) * B.adjugate.transpose i k) := by
  dsimp only [transformedFrame6, SourceProper6.cofactorValue6, SourceProper6.cofactor6] at h
  exact h


def literalMinors (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ) : Prop :=
  let g : ℤ := ∑ k, a k * v.adjugate k 5
  let d := Finset.univ.gcd (fun k => (v.adjugate k 5).natAbs)
  (fun k => v.adjugate k 5) ≠ 0 ∧ g ≠ 0 ∧
    (∀ k, v.adjugate k 5 = g * M k) ∧
    (∀ b : ℤ, (∀ k, b ∣ v.adjugate k 5) ↔ b ∣ g) ∧ d = g.natAbs ∧
    ((fun k => v.adjugate k 5 / (d : ℤ)) = M ∨
      (fun k => v.adjugate k 5 / (d : ℤ)) = -M)

def literalCofactors (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M a : Fin 6 → ℤ) : Prop :=
  let g : ℤ := ∑ k, a k * v.adjugate k 5
  ∀ i : Fin 6,
    (-1 : ℝ) ^ (5+i.val) *
      (((v.map (Int.castRingHom ℝ)) * (compound L).transpose).submatrix
        Fin.castSucc i.succAbove).det =
      (g : ℝ) * (∑ k, (M k : ℝ) * (compound L).adjugate.transpose i k) ∧
    (-1 : ℚ_[2]) ^ (5+i.val) *
      (((v.map (Int.castRingHom ℚ_[2])) * (finiteMatrix 2 A2).transpose).submatrix
        Fin.castSucc i.succAbove).det =
      (g : ℚ_[2]) * (∑ k, (M k : ℚ_[2]) * (finiteMatrix 2 A2).adjugate.transpose i k) ∧
    (-1 : ℚ_[3]) ^ (5+i.val) *
      (((v.map (Int.castRingHom ℚ_[3])) * (finiteMatrix 3 A3).transpose).submatrix
        Fin.castSucc i.succAbove).det =
      (g : ℚ_[3]) * (∑ k, (M k : ℚ_[3]) * (finiteMatrix 3 A3).adjugate.transpose i k)



theorem expanded_cofactors
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ)
    (hc : actualTransformedCofactors6 A2 A3 L v M a) :
    literalCofactors A2 A3 L v M a := by
  dsimp only [literalCofactors]
  dsimp only [actualTransformedCofactors6, rawNormal6] at hc
  generalize compound L = B0 at hc ⊢
  generalize finiteMatrix 2 A2 = B2 at hc ⊢
  generalize finiteMatrix 3 A3 = B3 at hc ⊢
  intro i
  constructor
  · apply expand_signed_identity
    exact (hc i).1
  · constructor
    · apply expand_signed_identity
      exact (hc i).2.1
    · apply expand_signed_identity
      exact (hc i).2.2

theorem signed_minor_normalization
    (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ)
    (hm : minorNormalization6 v M a) :
    let g : ℤ := ∑ k, a k * v.adjugate k 5
    g ≠ 0 ∧ (∀ k, v.adjugate k 5 = g * M k) ∧ literalMinors v M a := by
  exact ⟨hm.2.1, hm.2.2.1, hm⟩

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}


theorem original_normalization
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
    0 < (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index ∧
    (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index * G.index = v.det.natAbs ∧
    |(v.det : ℝ)| = ((Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index : ℝ) *
      ZLattice.covolume (integerRealImage G) ∧
    v.det ≠ 0 ∧ 0 < ZLattice.covolume (integerRealImage G) := by
  obtain ⟨c⟩ := directCompoundGroup42_has_basis A2 A3 q.val c2 c3
  exact frame_normalization6 _ c (R.w q) (R.frames q).1

theorem original_last_dual
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    ∃ b : ℚ, b ≠ 0 ∧
      normalForm6 (R.M q) = b • rationalFrameDual42
        (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
      (∀ k, (R.M q k : ℚ) = b * dualVector6
        (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k) ∧
      (∀ k, dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
        (sourceFrameIndependent6 R q) k = b⁻¹ * (R.M q k : ℚ)) := by
  exact source_normal_dual6 R q

theorem complete_literal
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let Q := q.val ^ (11 : ℕ)
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    let g : ℤ := ∑ k, R.a q k * v.adjugate k 5
    directCompoundGroup42 A2 A3 Q (fun i => c2 i / 11) (fun i => c3 i / 11) = G ∧
    sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV R.delta R.c R.sigma R.widths_pos R.w q ∧
    sourceNormals6 A2 A3 c2 c3 V R.w R.M R.a q ∧
    Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
    0 < (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index ∧
    (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index * G.index = v.det.natAbs ∧
    |(v.det : ℝ)| = ((Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index : ℝ) *
      ZLattice.covolume (integerRealImage G) ∧
    v.det ≠ 0 ∧ 0 < ZLattice.covolume (integerRealImage G) ∧
    g ≠ 0 ∧ (∀ k, v.adjugate k 5 = g * R.M q k) ∧
    literalMinors v (R.M q) (R.a q) ∧
    literalCofactors A2 A3 L v (R.M q) (R.a q) ∧
    ∃ b : ℚ, b ≠ 0 ∧
      normalForm6 (R.M q) = b • rationalFrameDual42
        (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
      (∀ k, (R.M q k : ℚ) = b * dualVector6
        (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k) ∧
      (∀ k, dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
        (sourceFrameIndependent6 R q) k = b⁻¹ * (R.M q k : ℚ)) := by
  have hn := original_normalization R q
  have hminor : minorNormalization6
      (Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))) (R.M q) (R.a q) := by
    rw [show Matrix.of (fun j => (R.w q j : Fin 6 → ℤ)) =
      (fun j => (R.w q j : Fin 6 → ℤ)) from rfl]
    exact (R.minors q).1
  have hcofactor : actualTransformedCofactors6 A2 A3 L
      (Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))) (R.M q) (R.a q) := by
    rw [show Matrix.of (fun j => (R.w q j : Fin 6 → ℤ)) =
      (fun j => (R.w q j : Fin 6 → ℤ)) from rfl]
    exact (R.minors q).2
  have hm := signed_minor_normalization
    (Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))) (R.M q) (R.a q) hminor
  have hc := expanded_cofactors A2 A3 L
    (Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))) (R.M q) (R.a q) hcofactor
  exact ⟨(R.frames q).2.2.1, R.frames q, R.normals q,
    hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2,
    hm.1, hm.2.1, hm.2.2, hc, original_last_dual R q⟩

end CompoundFeasibility.RelativeIndex145Literal
#print axioms CompoundFeasibility.RelativeIndex145Literal.expand_signed_identity
#print axioms CompoundFeasibility.RelativeIndex145Literal.expanded_cofactors
#print axioms CompoundFeasibility.RelativeIndex145Literal.signed_minor_normalization
#print axioms CompoundFeasibility.RelativeIndex145Literal.original_normalization
#print axioms CompoundFeasibility.RelativeIndex145Literal.original_last_dual
#print axioms CompoundFeasibility.RelativeIndex145Literal.complete_literal
