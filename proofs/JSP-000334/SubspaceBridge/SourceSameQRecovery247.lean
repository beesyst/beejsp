import SubspaceBridge.SourceShortSpan247
import SubspaceBridge.SourceShortFour247
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag247
open Exterior54_246 SourceFlag241

theorem sameQ_rank1_recovery247
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (kappa delta : ℝ) (hk : 0 < kappa)
    (hcut : 24/kappa < Q^delta)
    (hsource : sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 1*Q^(-delta))
    (hcomp : kappa * fourProducts246 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) 4 ≤
      compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 4)
    (H : Submodule ℚ (Fin 5 → ℚ)) (hH : Module.finrank ℚ H = 4)
    (w : Fin 5 → originalSourceGroup5 (compound4246 A2) (compound4246 A3) (Q^4)
      (normalizedWeights4246 c2) (normalizedWeights4246 c3))
    (hw : LinearIndependent ℝ (fun j => integerReal (w j : Fin 5 → ℤ)))
    (ha : ∀ j, coordinateGauge5 (originalCoordinates5 (compound4246 L) (compound_unit4246 L hL)
      (Q^4) (powered_gt_one4246 Q hQ) (normalizedWeights4246 c0)) (integerReal (w j : Fin 5 → ℤ)) =
      compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 j)
    (hspan : H = Submodule.span ℚ (Set.range
      (fun j : Fin 4 => fun i => ((w j.castSucc : Fin 5 → ℤ) i : ℚ)))) :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 5 → ℤ)) ∧
      (∀ j, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u j : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
      annihilator247 H = Submodule.span ℚ {fun i => ((u 0 : Fin 5 → ℤ) i : ℚ)} := by
  have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hshort := short_four_bound247 _ hp.1 hp.2 _ kappa Q delta hk hQ hcomp hsource hcut
  have h34 : compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 3 <
      compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 4 :=
    (compoundMinima_upper4246 A2 A3 L hL Q hQ c0 c2 c3 3).trans_lt (hshort 3)
  obtain ⟨u,hu,huatt,hm,hi,hg⟩ := actual_wedge_frame4246 A2 A3 L hL Q hQ c0 c2 c3
  let uZ : Fin 5 → Fin 5 → ℤ := fun j => (u j : Fin 5 → ℤ)
  let uR : Fin 5 → Fin 5 → ℚ := fun j i => (uZ j i : ℚ)
  let v : Fin 4 → Fin 5 → ℚ := fun j i => ((signedQuad246 uZ j.castSucc.rev i : ℤ) : ℚ)
  have hmem (j : Fin 4) : v j ∈ H := by
    let z := signedQuad246 uZ j.castSucc.rev
    have hz : z ∈ originalSourceGroup5 (compound4246 A2) (compound4246 A3) (Q^4)
        (normalizedWeights4246 c2) (normalizedWeights4246 c3) := hm j.castSucc
    have hzg : coordinateGauge5 (originalCoordinates5 (compound4246 L) (compound_unit4246 L hL)
        (Q^4) (powered_gt_one4246 Q hQ) (normalizedWeights4246 c0)) (integerReal z) <
        compoundMinima4246 A2 A3 L hL Q hQ c0 c2 c3 4 :=
      (hg j.castSucc).trans_lt (hshort j)
    have hs := attaining_short_span247 (compound4246 A2) (compound4246 A3) (compound4246 L)
      (compound_unit4246 L hL) (Q^4) (powered_gt_one4246 Q hQ)
      (normalizedWeights4246 c0) (normalizedWeights4246 c2) (normalizedWeights4246 c3)
      w hw ha h34 z hz hzg
    rw [hspan]
    exact rational_span_of_real247 (fun k => (w k : Fin 5 → ℤ)) hw z hs
  have hcast : v = fun j : Fin 4 => signedQuad246 uR j.castSucc.rev := by
    funext j
    exact signedQuad_rat_cast247 uZ j.castSucc.rev
  have hur : LinearIndependent ℚ uR := original_rational_independent241 uZ hu
  have hvi : LinearIndependent ℚ v := by
    rw [hcast]
    exact (signedQuad_rat_independent247 uR hur).comp (fun j : Fin 4 => j.castSucc.rev)
      (Fin.rev_injective.comp (Fin.castSucc_injective 4))
  have hle : Submodule.span ℚ (Set.range v) ≤ H := Submodule.span_le.mpr (by
    rintro _ ⟨j,rfl⟩
    exact hmem j)
  have hd : Module.finrank ℚ (Submodule.span ℚ (Set.range v)) = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hvi
  have heq : H = Submodule.span ℚ (Set.range v) :=
    (Submodule.eq_of_le_of_finrank_eq hle (hd.trans hH.symm)).symm
  rw [hcast] at heq
  have hr := four_wedge_annihilator247 uR hur
  dsimp only at hr
  rw [← heq] at hr
  exact ⟨u,hu,huatt,hr.1⟩

end CompoundFeasibility.SourceFlag247
