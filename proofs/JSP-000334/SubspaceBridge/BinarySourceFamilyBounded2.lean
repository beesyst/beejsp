import SubspaceBridge.BinaryFixedSourceFamily2
import SubspaceBridge.BinaryParameterSelection2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_weighted_source_family_bounded (B C : ℚ) (hB : B ≠ 0) (hC : C ≠ 0)
    (d : ℕ) (hd : 0<d) (b c : ℤ) (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) :
    ∃ cut : ℝ,1≤cut ∧ ∀ U : Set ℝ,∀ z : U → Fin 2 → ℤ,
    (∀ q,PrimitivePair (z q)) →
    (∀ q,z q 0 ≠ 0 ∧ z q 1 ≠ 0 ∧ B*(z q 0 : ℚ)+C*(z q 1 : ℚ) ≠ 0) →
    (∀ q,cut<(archPairHeight (z q) : ℝ)) →
    (∀ q,(weightedNormalizedProduct2 B C (z q 0 : ℚ) (z q 1 : ℚ) : ℝ)<
      Real.rpow (archPairHeight (z q) : ℝ) (-(5 : ℝ)/2)) →
    (∀ q,q.val=(archPairHeight (z q) : ℝ)^4) → BddAbove U := by
  obtain ⟨cut,hcut,hfamily⟩ := binary_fixed_source_family B C d hd b c hb hc
  refine ⟨cut,hcut,?_⟩
  intro U z hz hn htail hproduct hparam
  by_contra hU
  obtain ⟨k,v,hv,W,hWU,hW,hlocal⟩ := hfamily U hU z hz hn htail hproduct hparam
  let L : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ := fun tau => binaryIntegerRetained2 d b c (k tau)
  have hL (tau) : (binaryLocalRationalMatrix (L tau)).det ≠ 0 :=
    binary_integer_retained_det B C hB hC d hd b c hb hc (k tau)
  obtain ⟨D,E,hD,hE,hcontr⟩ := binary_auxiliary_integer_analytic_contradiction L hL
  obtain ⟨eta,theta,m,hm,he,he1,ht,ht1,htb,hed,hcount,hselect⟩ :=
    binary_parameter_selection D E ((1 : ℝ)/384) hD hE (by norm_num) (by norm_num)
  obtain ⟨Q,r,hQ,hr,hsep,hlog,hthreshold,hbudgets⟩ := hselect W hW 1
  let qh : Fin m → U := fun h => ⟨Q h,hWU (hQ h).1⟩
  let Z : Fin m → Fin 2 → ℤ := fun h => z (qh h)
  let V : Fin m → Fin 2 → ℤ := fun h => binaryPairNormal (Z h)
  let H : Fin m → ℝ := fun h => (archPairHeight (Z h) : ℝ)
  have hHone (h) : 1<H h := lt_of_le_of_lt hcut (htail (qh h))
  have hHQ (h) : H h=(Q h)^((1 : ℝ)/4) := by
    have hh := hparam (qh h)
    change Q h=(H h)^4 at hh
    rw [hh,← Real.rpow_natCast,← Real.rpow_mul (show 0≤H h by linarith [hHone h])]
    norm_num
  obtain ⟨hgrowth,hden,hheight⟩ := hbudgets H hHQ
  have hVH (h) : (binaryNormalHeight (V h) : ℝ)=H h := binary_pair_normal_height (Z h)
  apply hcontr eta he he1 m hm hcount r hr theta 1 ht ht1 htb (by norm_num) (by norm_num) hsep
    ((1 : ℝ)/384) hed (by norm_num) v hv.2.1 hv.2.2 Q (fun h => (hQ h).2.2) hthreshold hlog V
  · intro h
    exact ⟨binary_pair_normal_nonzero (Z h) (hz (qh h)),binary_pair_normal_ideal (Z h) (hz (qh h))⟩
  · intro h _
    simpa only [hVH] using hgrowth h
  · intro h
    simpa only [hVH] using hden h
  · simpa only [hVH] using hheight
  · intro tau h i
    change rothLocalAbs tau (binaryLocalVectorValue (L tau) (binaryKernelVector (binaryPairNormal (Z h))) i)≤_
    rw [binary_pair_normal_vector]
    exact (hlocal (qh h) (hQ h).1).2 tau i

end JSP000334
