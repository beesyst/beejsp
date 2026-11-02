import SubspaceBridge.SourcePairRadical241
import SubspaceBridge.SourceExceptionalPair241
import SubspaceBridge.SourceShortSpan241
import SubspaceBridge.SourcePairFlag241
import SubspaceBridge.SourceCompoundFixedLine240G
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open Exterior52_237 Exterior52_238 ExteriorGap52_239 SchmidtNormal10 OriginalDual10 SourceOriginalDual10

theorem sameQ_radical_recovery241
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (kappa delta : ℝ) (hk : 0 < kappa) (hd : 0 < delta)
    (hcut : 2/kappa < Q^(delta/2))
    (hcomp : kappa*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) 8 ≤
      compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 8)
    (hgap : compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 8 <
      compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 9*(Q^2)^(-delta/4))
    (hsource : sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 2 <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta))
    (b : Fin 10 → ℤ) (hb : b ≠ 0)
    (w : Fin 10 → originalSourceGroup10 (compound237 A2) (compound237 A3) (Q^2)
      (normalizedWeights238 c2) (normalizedWeights238 c3))
    (hw : LinearIndependent ℝ (fun i => integerReal (w i : Fin 10 → ℤ)))
    (hatt : ∀ i, coordinateGauge10 (originalCoordinates10 (compound237 L) (compound_unit238 L hL)
      (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0))
      (integerReal (w i : Fin 10 → ℤ)) = compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 i)
    (hline : Submodule.span ℚ {lastDual10 (fun j i => ((w j : Fin 10 → ℤ) i : ℚ))
      (integer_frame_rational_independent10 _ hw)} = Submodule.span ℚ {fun i => (b i : ℚ)}) :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
      (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
      radical241 b = Submodule.span ℚ (Set.range
        (fun j : Fin 3 => fun i => ((u (Fin.castLE (by decide) j) : Fin 5 → ℤ) i : ℚ))) ∧
      Module.finrank ℚ (radical241 b) = 3 := by
  have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hshort := short_pair_bound241 _ _ kappa Q delta hk hQ
    (pairProducts_pos239 _ hp.1 8) hcomp hgap hcut
  obtain ⟨u,hu,hua,hmem,hi,hg⟩ := actual_short_wedges241 A2 A3 L hL Q hQ c0 c2 c3 hshort
  let u0 : Fin 5 → Fin 5 → ℤ := fun i => (u i : Fin 5 → ℤ)
  let a := sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3
  let z := orderedWedge239 u0 a
  have hlast := pairOrder_last241 a hp.1 hp.2 Q delta hQ hd hsource
  have hstrict : compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 8 <
      compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 9 := hgap.trans_le (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (powered_gt_one238 Q hQ).le (by linarith : -delta/4 ≤ 0))
      ((compoundMinima_pos_mono239 A2 A3 L hL Q hQ c0 c2 c3).1 9).le)
  have hz (s : Fin 10) (hs : s ≠ 9) : normalForm10 b
      (fun i => (wedge237 (R := ℤ) (u0 (lo237 s)) (u0 (hi237 s)) i : ℚ)) = 0 := by
    obtain ⟨j,hj⟩ := (pairOrder_first_nine241 a hlast s).mpr hs
    have hm : z j.castSucc ∈ originalSourceGroup10 (compound237 A2) (compound237 A3)
        (Q^2) (normalizedWeights238 c2) (normalizedWeights238 c3) := by
      rw [powered_group238]
      exact hmem j.castSucc
    have hspan := attaining_short_span241 (compound237 A2) (compound237 A3) (compound237 L)
      (compound_unit238 L hL) (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0)
      (normalizedWeights238 c2) (normalizedWeights238 c3) w hw hatt hstrict (z j.castSucc) hm (hg j)
    have hn := rational_annihilation_from_real_span241 (fun i => (w i : Fin 10 → ℤ))
      (integer_frame_rational_independent10 _ hw) b hline (z j.castSucc) hspan
    have he : z j.castSucc = wedge237 (R := ℤ) (u0 (lo237 s)) (u0 (hi237 s)) := by
      dsimp only [z,orderedWedge239]
      rw [hj]
    simpa only [he] using hn
  have hn := exceptional_pair_nonzero241 u0 hu b hb hz
  have hrat := original_rational_independent241 u0 hu
  have hr := radical_rank3_241 b (fun j i => (u0 j i : ℚ)) hrat
    (fun s hs => by rw [pairForm_integer_cast241]; exact hz s hs)
    (by rw [pairForm_integer_cast241]; exact hn)
  exact ⟨u,hu,hua,hr.1,hr.2⟩

end CompoundFeasibility.SourceFlag241
