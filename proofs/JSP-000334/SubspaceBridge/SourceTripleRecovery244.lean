import SubspaceBridge.SourceTripleRadical244
import SubspaceBridge.SourceExceptionalTriple244
import SubspaceBridge.SourceShortSpan241
import SubspaceBridge.SourceTripleFlag244
import SubspaceBridge.SourceShortTriples244
import SubspaceBridge.SourceCompound3FixedLine243
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag244
open Exterior53_242 SourceFlag241 SchmidtNormal10 OriginalDual10 SourceOriginalDual10

theorem sameQ_radical_recovery244
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (kappa delta : ℝ) (hk : 0 < kappa) (hd : 0 < delta)
    (hcut : 6/kappa < Q^(delta/2))
    (hcomp : kappa*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) 8 ≤
      compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 8)
    (hgap : compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 8 <
      compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 9*(Q^3)^(-delta/6))
    (hsource : sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 1 <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 2*Q^(-delta))
    (b : Fin 10 → ℤ) (hb : b ≠ 0)
    (w : Fin 10 → originalSourceGroup10 (compound3242 A2) (compound3242 A3) (Q^3)
      (normalizedWeights3242 c2) (normalizedWeights3242 c3))
    (hw : LinearIndependent ℝ (fun i => integerReal (w i : Fin 10 → ℤ)))
    (hatt : ∀ i, coordinateGauge10 (originalCoordinates10 (compound3242 L) (compound_real_unit3242 L hL)
      (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0))
      (integerReal (w i : Fin 10 → ℤ)) = compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 i)
    (hline : Submodule.span ℚ {lastDual10 (fun j i => ((w j : Fin 10 → ℤ) i : ℚ))
      (integer_frame_rational_independent10 _ hw)} = Submodule.span ℚ {fun i => (b i : ℚ)}) :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
      (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
      radical244 b = Submodule.span ℚ (Set.range
        (fun j : Fin 2 => fun i => ((u (Fin.castLE (by decide) j) : Fin 5 → ℤ) i : ℚ))) ∧
      Module.finrank ℚ (radical244 b) = 2 := by
  have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hshort := short_triple_bound244 _ _ kappa Q delta hk hQ
    (tripleProducts_pos242 _ hp.1 8) hcomp hgap hcut
  obtain ⟨u,hu,hua,hmem,hi,hg⟩ := actual_short_triples244 A2 A3 L hL Q hQ c0 c2 c3 hshort
  let u0 : Fin 5 → Fin 5 → ℤ := fun i => (u i : Fin 5 → ℤ)
  let a := sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3
  let z := orderedWedge3242 u0 a
  have hlast := tripleOrder_last244 a hp.1 hp.2 Q delta hQ hd hsource
  have hstrict : compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 8 <
      compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 9 := hgap.trans_le (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (powered_gt_one3242 Q hQ).le (by linarith : -delta/6 ≤ 0))
      ((compoundMinima_pos_mono3242 A2 A3 L hL Q hQ c0 c2 c3).1 9).le)
  have hz (s : Fin 10) (hs : s ≠ 9) : normalForm10 b
      (fun i => (wedge3242 (R := ℤ) (u0 (lo242 s)) (u0 (mid242 s)) (u0 (hi242 s)) i : ℚ)) = 0 := by
    obtain ⟨j,hj⟩ := (tripleOrder_first_nine244 a hlast s).mpr hs
    have hm : z j.castSucc ∈ originalSourceGroup10 (compound3242 A2) (compound3242 A3)
        (Q^3) (normalizedWeights3242 c2) (normalizedWeights3242 c3) := by
      rw [powered_group3242]
      exact hmem j.castSucc
    have hspan := attaining_short_span241 (compound3242 A2) (compound3242 A3) (compound3242 L)
      (compound_real_unit3242 L hL) (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0)
      (normalizedWeights3242 c2) (normalizedWeights3242 c3) w hw hatt hstrict (z j.castSucc) hm (hg j)
    have hn := rational_annihilation_from_real_span241 (fun i => (w i : Fin 10 → ℤ))
      (integer_frame_rational_independent10 _ hw) b hline (z j.castSucc) hspan
    have he : z j.castSucc = wedge3242 (R := ℤ) (u0 (lo242 s)) (u0 (mid242 s)) (u0 (hi242 s)) := by
      dsimp only [z,orderedWedge3242]
      rw [hj]
    simpa only [he] using hn
  have hn := exceptional_triple_nonzero244 u0 hu b hb hz
  have hrat := original_rational_independent241 u0 hu
  have hr := radical_rank2_244 b (fun j i => (u0 j i : ℚ)) hrat
    (fun s hs => by rw [tripleForm_integer_cast244]; exact hz s hs)
    (by rw [tripleForm_integer_cast244]; exact hn)
  exact ⟨u,hu,hua,hr.1,hr.2⟩

end CompoundFeasibility.SourceFlag244
