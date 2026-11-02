import SubspaceBridge.SchlickeweiEquation4116
import SubspaceBridge.SchlickeweiEquation4126
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiSatz41Selected6
open SourceMixed6 SourceReadiness6 SchlickeweiDualVanishing6

theorem balanced_mixed_nonnegative6 (c : Fin 3 → Fin 6 → ℝ)
    (hbal : (∑ tau, ∑ i, c tau i) = 0) :
    ∃ s : MixedIndex6, 0 ≤ ∑ tau, c tau (s tau) := by
  have hm (tau : Fin 3) : ∃ i : Fin 6, ∀ j : Fin 6, c tau j ≤ c tau i := by
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (c tau) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  choose s hs using hm
  refine ⟨s, ?_⟩
  have hb (tau : Fin 3) : (∑ i, c tau i) ≤ 6 * c tau (s tau) := by
    calc
      _ ≤ ∑ _i : Fin 6, c tau (s tau) := Finset.sum_le_sum (fun j _ => hs tau j)
      _ = _ := by simp
  have h := Finset.sum_le_sum (fun tau (_ : tau ∈ Finset.univ) => hb tau)
  rw [hbal, ← Finset.mul_sum] at h
  linarith

theorem source_admissible_nonempty6
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    (admissibleMixed6 R.c (R.delta/2)).Nonempty := by
  obtain ⟨s, hs⟩ := balanced_mixed_nonnegative6 R.c R.weights_balance
  refine ⟨s, (mem_admissibleMixed6 R.c (R.delta/2) s).mpr ?_⟩
  have hd := R.delta_pos
  linarith

open SourceNormalHeight SourceNormalIndex
open SchlickeweiEquation4116

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_satz41_selected6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) :
    ∃ B : ℝ, (admissibleMixed6 R.c (R.delta/2)).Nonempty ∧
      (∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
        actualNormProduct6 A2 A3 L (R.M q) s = 0) ∧
      ∀ q : V, B < q.val →
        let G := directCompoundGroup42 A2 A3 q.val c2 c3
        let Q := q.val ^ (11 : ℕ)
        let J := SourceRelativeIndex6.frameRelativeIndex G (R.w q)
        let d := ZLattice.covolume (integerRealImage G)
        let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
        let D := dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)
        sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV R.delta R.c R.sigma R.widths_pos R.w q ∧
        sourceNormals6 A2 A3 c2 c3 V R.w R.M R.a q ∧
        Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
        0 < J ∧ J * G.index = v.det.natAbs ∧
        |(v.det : ℝ)| = (J : ℝ) * d ∧ v.det ≠ 0 ∧ 0 < d ∧
        d = (G.index : ℝ) ∧ ((J * G.index : ℕ) : ℝ) = (J : ℝ) * d ∧
        (∀ i, sourceExponent6 2 q.val c2 i =
          -(Nat.ceil (JSP000334.qThreshold 2 Q (R.c 1 i)) : ℤ)) ∧
        (∀ i, sourceExponent6 3 q.val c3 i =
          -(Nat.ceil (JSP000334.qThreshold 3 Q (R.c 2 i)) : ℤ)) ∧
        (∀ i, ‖∑ k, ((J : ℝ) * d * algebraMap ℚ ℝ (D k)) *
            (compound L)⁻¹.transpose i k‖ ≤
          120 * (Q ^ (R.c 0 i))⁻¹ * d * Q ^ (-5 * R.delta)) ∧
        (∀ i, (‖∑ k, (((J * G.index : ℕ) : ℚ_[2]) * algebraMap ℚ ℚ_[2] (D k)) *
            (Auxiliary6.SourceExpansion.finiteMatrix 2 A2)⁻¹.transpose i k‖ ≤
          (2 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 2 q.val c2 (i.succAbove k))) ∧
          (‖∑ k, (((J * G.index : ℕ) : ℚ_[3]) * algebraMap ℚ ℚ_[3] (D k)) *
            (Auxiliary6.SourceExpansion.finiteMatrix 3 A3)⁻¹.transpose i k‖ ≤
          (3 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 3 q.val c3 (i.succAbove k)))) ∧
        ∃ a : ℚ, a ≠ 0 ∧
          normalForm6 (R.M q) = a • rationalFrameDual42
            (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
          (∀ k, (R.M q k : ℚ) = a * D k) ∧
          (∀ k, D k = a⁻¹ * (R.M q k : ℚ)) ∧
          ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
            dualNormProduct6 A2 A3 L D s = 0 ∧
            SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L D s = 0 := by
  obtain ⟨B, hzero, hdual⟩ := SchlickeweiEquation4126.source_equation4126 R h2 h3
  refine ⟨B, source_admissible_nonempty6 R, hzero, ?_⟩
  intro q hq
  dsimp only
  have hn := SourceRelativeIndex6.source_frame_normalization6 R q
  have hf (i : Fin 6) := source_equation4116 R h2 h3 q i
  refine ⟨R.frames q, R.normals q, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
    hn.2.2.2.2.1, hn.2.2.2.2.2, (hf 0).1, (hf 0).2.1,
    (hf 0).2.2.1, (hf 0).2.2.2.1, ?_, ?_, hdual q hq⟩
  · intro i
    exact SchlickeweiEquation4106.source_equation4106 R h2 h3 hLdet q i
  · intro i
    exact (hf i).2.2.2.2

end CompoundFeasibility.SchlickeweiSatz41Selected6
