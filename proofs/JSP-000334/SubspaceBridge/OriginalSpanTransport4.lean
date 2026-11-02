import SubspaceBridge.SchlickeweiFixedLine4
import SubspaceBridge.OriginalShortPlane42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalSpanTransport4
open OriginalDeformation4 OriginalLastDual4 OriginalDeformedSource4 OriginalSelectedSystem4 SourceSelectedDual4

theorem span_gap_bound4 (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (Q delta : ℝ) (hQ : 1 < Q) (hcut : 256 < Q^delta)
    (hgap : lam 2 < lam 3 * Q^(-delta)) :
    16*gapRadius4 lam < gapDeformation4 lam 3*lam 3/16 := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have he : Q^(-delta)*Q^delta = 1 := by
    rw [← Real.rpow_add hq,neg_add_cancel,Real.rpow_zero]
  have hmul : lam 2 * Q^delta < lam 3 := by
    have hh := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos hq delta)
    simpa only [mul_assoc,he,mul_one] using hh
  have hratio : 256*lam 2 < lam 3 := by
    have hh := mul_lt_mul_of_pos_left hcut (hp 2)
    nlinarith
  rw [gapDeformation4_last]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  apply (lt_div_iff₀ (hp 2)).mpr
  have hr := gapRadius4_pos lam hp
  nlinarith [mul_lt_mul_of_pos_left hratio hr]

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}

theorem deformed_first_three_mem_original4
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (hcut : 256 < Q^delta)
    (hgap : sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 <
      sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta)) :
    ∀ j : Fin 3, integerReal (F.w j.castSucc : Fin 4 → ℤ) ∈
      minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) 3 := by
  have hp := (sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1
  have hstrict := span_gap_bound4 _ hp Q delta hQ hcut hgap
  intro j
  by_contra hout
  have hlo := F.separation 3 (F.w j.castSucc) hout
  have hhi := (F.minima_mono (show j.castSucc ≤ (2 : Fin 4) by change j.val ≤ 2; omega)).trans (F.comparison 2).2
  rw [gapDeformation4_first _ hp 2 le_rfl] at hhi
  rw [F.attaining] at hlo
  exact (not_lt_of_ge hlo) (hhi.trans_lt hstrict)

theorem real_first_three_span4
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (hcut : 256 < Q^delta)
    (hgap : sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 <
      sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta)) :
    minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) 3 =
      minimaFlag4 (fun i => integerReal (F.w i : Fin 4 → ℤ)) 3 ∧
    Module.finrank ℝ (minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) 3) = 3 ∧
    LinearIndependent ℝ (fun j : Fin 3 => integerReal (u j.castSucc : Fin 4 → ℤ)) := by
  have hinc : minimaFlag4 (fun i => integerReal (F.w i : Fin 4 → ℤ)) 3 ≤
      minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) 3 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact deformed_first_three_mem_original4 F hcut hgap j
  have hd := minimaFlag4_finrank _ F.real_independent 3
  have hle : Module.finrank ℝ (minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) 3) ≤ 3 := by
    exact finrank_range_le_card (fun j : Fin 3 => integerReal (u j.castSucc : Fin 4 → ℤ))
  have heq := Submodule.eq_of_le_of_finrank_le hinc (by simpa only [hd] using hle)
  have hrank : Module.finrank ℝ (minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) 3) = 3 := by
    rw [← heq,hd]
    rfl
  refine ⟨heq.symm,hrank,?_⟩
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  exact hrank.symm

theorem span_cutoff4 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → 256 < Q^delta := by
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 256 (2*delta) (by positivity)
  refine ⟨T,hT,?_⟩
  intro Q hQ
  simpa only [mul_div_cancel_left₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using hcut Q hQ

theorem integer_three_rational_independent4 (v : Fin 3 → Fin 4 → ℤ)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j))) :
    LinearIndependent ℚ (fun j i => (v j i : ℚ)) := by
  let castMap : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  apply LinearIndependent.of_comp castMap
  convert hv.restrict_scalars' ℚ using 1

theorem rational_kernel_transport4
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (hcut : 256 < Q^delta)
    (hgap : sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 <
      sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta))
    (b : Fin 4 → ℤ) (hb : b ≠ 0)
    (hline : Submodule.span ℚ
        {lastDual4 (fun j i => ((F.w j : Fin 4 → ℤ) i : ℚ)) F.rational_independent} =
      Submodule.span ℚ {fun i => (b i : ℚ)}) :
    LinearMap.ker (normalForm4 b) = firstThreeSpan4 (fun j i => ((u j : Fin 4 → ℤ) i : ℚ)) ∧
    LinearMap.ker (normalForm4 b) = firstThreeSpan4 (fun j i => ((F.w j : Fin 4 → ℤ) i : ℚ)) ∧
    Module.finrank ℚ (LinearMap.ker (normalForm4 b)) = 3 ∧
    LinearIndependent ℚ (fun j : Fin 3 => fun i => ((u j.castSucc : Fin 4 → ℤ) i : ℚ)) := by
  obtain ⟨hreal,hrank,hind⟩ := real_first_three_span4 F hcut hgap
  obtain ⟨hn,hker,hdim⟩ := fixed_line_kernel4 _ F.rational_independent b hb hline
  let f := normalForm4 b
  have hrealKer : minimaFlag4 (fun j => integerReal (F.w j : Fin 4 → ℤ)) 3 ≤
      LinearMap.ker (OriginalShortPlane42.rationalFunctionalReal42 f) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change OriginalShortPlane42.rationalFunctionalReal42 f (integerReal (F.w j.castSucc : Fin 4 → ℤ)) = 0
    rw [show integerReal (F.w j.castSucc : Fin 4 → ℤ) =
      (fun i => (((F.w j.castSucc : Fin 4 → ℤ) i : ℚ) : ℝ)) by ext i; simp [integerReal]]
    rw [OriginalShortPlane42.rationalFunctionalReal42_cast]
    have hz : f (fun i => ((F.w j.castSucc : Fin 4 → ℤ) i : ℚ)) = 0 := by
      apply (show firstThreeSpan4 (fun j i => ((F.w j : Fin 4 → ℤ) i : ℚ)) ≤ LinearMap.ker f from hker.ge)
      exact Submodule.subset_span ⟨j,rfl⟩
    rw [hz,Rat.cast_zero]
  have hinc : firstThreeSpan4 (fun j i => ((u j : Fin 4 → ℤ) i : ℚ)) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have hmem : integerReal (u j.castSucc : Fin 4 → ℤ) ∈
        minimaFlag4 (fun i => integerReal (F.w i : Fin 4 → ℤ)) 3 := by
      rw [← hreal]
      exact Submodule.subset_span ⟨j,rfl⟩
    have hz := hrealKer hmem
    change OriginalShortPlane42.rationalFunctionalReal42 f (integerReal (u j.castSucc : Fin 4 → ℤ)) = 0 at hz
    have hc := OriginalShortPlane42.rationalFunctionalReal42_cast f
      (fun i => ((u j.castSucc : Fin 4 → ℤ) i : ℚ))
    have he : (fun i => (((u j.castSucc : Fin 4 → ℤ) i : ℚ) : ℝ)) =
        integerReal (u j.castSucc : Fin 4 → ℤ) := by ext i; simp [integerReal]
    rw [he] at hc
    rw [hc] at hz
    change f _ = 0
    exact_mod_cast hz
  have hrat := integer_three_rational_independent4
    (fun j : Fin 3 => (u j.castSucc : Fin 4 → ℤ)) hind
  have hd : Module.finrank ℚ (firstThreeSpan4 (fun j i => ((u j : Fin 4 → ℤ) i : ℚ))) = 3 := by
    exact finrank_span_eq_card hrat
  exact ⟨(Submodule.eq_of_le_of_finrank_eq hinc (hd.trans hdim.symm)).symm,hker,hdim,hrat⟩

theorem source_original_fixed_rank3_4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ U : Set ℝ, ∃ hUV : U ⊆ V, ¬ BddAbove U ∧
      ∃ u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ∃ F : (q : U) → DeformedAttaining4 A2 A3 L (sourceUnit42 L hLdet) q.val
        (hQV q.val (hUV q.property)) c0 c2 c3 delta (u q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ W : Set ℝ, ∃ hWU : W ⊆ U, ¬ BddAbove W ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
        (∀ q : U, q.val ∈ W →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
            (OriginalDeformation4.deformedWidths4 q.val c0
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q.val
                  (hQV q.val (hUV q.property)) c0 c2 c3)) (F q).sigma) (fun i => c2 i/5) (fun i => c3 i/5) = S) ∧
        ∃ (q1 : U) (b : Fin 4 → ℤ) (B : ℝ), q1.val ∈ W ∧
          b = integerLastDual4 (fun j => ((F q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
          Submodule.span ℚ {fun i => (b i : ℚ)} =
            Submodule.span ℚ {lastDual4 (fun j i => (((F q1).w j : Fin 4 → ℤ) i : ℚ)) (F q1).rational_independent} ∧
          (∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0) ∧
          1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ W ∧ B < q} ∧
          (∀ q : U, q.val ∈ W → B < q.val →
            Submodule.span ℚ {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} =
              Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
          ∃ (Tspan : ℝ) (Vprime : Set ℝ) (P : Submodule ℚ (Fin 4 → ℚ)),
            1 < Tspan ∧ Vprime = {Q | Q ∈ W ∧ max B Tspan < Q} ∧
            ¬ BddAbove Vprime ∧ P = LinearMap.ker (normalForm4 b) ∧
            Module.finrank ℚ P = 3 ∧
            ∀ q : U, q.val ∈ Vprime →
              P = firstThreeSpan4 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) ∧
              P = firstThreeSpan4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) ∧
              minimaFlag4 (fun j => integerReal (u q j : Fin 4 → ℤ)) 3 =
                minimaFlag4 (fun j => integerReal ((F q).w j : Fin 4 → ℤ)) 3 ∧
              Module.finrank ℝ (minimaFlag4 (fun j => integerReal (u q j : Fin 4 → ℤ)) 3) = 3 ∧
              LinearIndependent ℚ (fun j : Fin 3 => fun i => ((u q j.castSucc : Fin 4 → ℤ) i : ℚ)) := by
  obtain ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,q1,b,B,hq1,hb,hbn,hline,hbz,hB,htail,hfixed⟩ :=
    SchlickeweiFixedLine4.source_deformed_fixed_last_dual4 A2 A3 L h2 h3 hLdet hAlg delta hd
      c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap
  obtain ⟨T,hT,hcut⟩ := span_cutoff4 delta hd
  refine ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,q1,b,B,hq1,hb,hbn,hline,hbz,hB,htail,hfixed,
    T,{Q | Q ∈ W ∧ max B T < Q},LinearMap.ker (normalForm4 b),hT,rfl,
    JSP000334.sourceDual_unbounded_tail3 W hW (max B T),rfl,?_,?_⟩
  · exact (fixed_line_kernel4 _ (F q1).rational_independent b hbn hline.symm).2.2
  · intro q hq
    have hBq : B < q.val := (le_max_left _ _).trans_lt hq.2
    have hTq : T < q.val := (le_max_right _ _).trans_lt hq.2
    have hg := hgap q.val (hUV q.property)
    obtain ⟨ho,hw,_,hi⟩ := rational_kernel_transport4 (F q) (hcut q.val hTq) hg b hbn (hfixed q hq.1 hBq)
    obtain ⟨he,hr,_⟩ := real_first_three_span4 (F q) (hcut q.val hTq) hg
    exact ⟨ho,hw,he,hr,hi⟩

end CompoundFeasibility.OriginalSpanTransport4
