import SubspaceBridge.SourceDeformedData236
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceRatioLine236
open OriginalDeformation10 SourceOriginalVariable10 SourceSatz51Entry218

theorem flag_cutoff236 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → (1024 : ℝ)^2 < Q^delta := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hd).eventually (Filter.eventually_gt_atTop ((1024 : ℝ)^2)))
  refine ⟨max B 2,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro Q hQ
  exact hB Q ((le_max_left B 2).trans hQ.le)

theorem flag_separation236 (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i)
    (Q delta : ℝ) (hQ : 1 < Q)
    (hgap : lam 8 < lam 9*Q^(-delta)) (hcut : (1024 : ℝ)^2 < Q^delta) :
    1024*gapRadius10 lam < gapRadius10 lam*lam 9/(1024*lam 8) := by
  have hQp : 0 < Q := zero_lt_one.trans hQ
  have hr := gapRadius10_pos lam hp
  have hmul : lam 8*Q^delta < lam 9 := by
    have hh := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos hQp delta)
    rw [mul_assoc,← Real.rpow_add hQp,neg_add_cancel,Real.rpow_zero,mul_one] at hh
    exact hh
  have hh : (1024 : ℝ)^2*lam 8 < lam 9 :=
    (mul_lt_mul_of_pos_right hcut (hp 8)).trans (by simpa only [mul_comm] using hmul)
  apply (lt_div_iff₀ (mul_pos (by norm_num) (hp 8))).mpr
  nlinarith [mul_lt_mul_of_pos_left hh hr]

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 10 → ℝ} {delta : ℝ}
  {u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3}

theorem deformed_first_nine236
    (F : DeformedAttaining236 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (hgap : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9*Q^(-delta))
    (hcut : (1024 : ℝ)^2 < Q^delta) (j : Fin 9) :
    integerReal (F.w j.castSucc : Fin 10 → ℤ) ∈
      minimaFlag10 (fun i => integerReal (u i : Fin 10 → ℤ)) 9 := by
  by_contra hout
  let lam := sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3
  have hp := (sourceMinima10_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1
  have hlo := F.separation 9 (F.w j.castSucc) hout
  rw [gapDeformation10_last lam] at hlo
  have hup := (F.minima_mono (show j.castSucc ≤ (8 : Fin 10) by
    change j.val ≤ 8
    omega)).trans F.radius_upper
  rw [← F.attaining j.castSucc] at hup
  have hs := flag_separation236 lam hp Q delta hQ hgap hcut
  have he : gapRadius10 lam*lam 9/lam 8/1024 =
      gapRadius10 lam*lam 9/(1024*lam 8) := by ring
  rw [he] at hlo
  exact (not_le_of_gt hs) (hlo.trans hup)

open OriginalDual10 SourceOriginalDual10 SourceSecondMinimum226

theorem cofactor_flag_zero236 (u : Fin 10 → Fin 10 → ℤ) (x : Fin 10 → ℝ)
    (hx : x ∈ minimaFlag10 (fun j => integerReal (u j)) 9) :
    ∑ i, x i*(integerLastDual10 u i : ℝ) = 0 := by
  let f : Module.Dual ℝ (Fin 10 → ℝ) := ∑ i, (integerLastDual10 u i : ℝ) • LinearMap.proj i
  have hf (y : Fin 10 → ℝ) : f y = ∑ i, y i*(integerLastDual10 u i : ℝ) := by
    simp [f,mul_comm]
  have hs : minimaFlag10 (fun j => integerReal (u j)) 9 ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change f (integerReal (u j.castSucc)) = 0
    rw [hf]
    have hp := integerLastDual10_pairing u j.castSucc
    have hne : j.castSucc ≠ Fin.last 9 := by
      intro he
      have := congrArg Fin.val he
      change j.val = 9 at this
      omega
    rw [if_neg hne] at hp
    change ∑ i, (u j.castSucc i : ℝ)*(integerLastDual10 u i : ℝ) = 0
    exact_mod_cast hp
  exact (hf x).symm.trans (hs hx)

theorem flag_pairing_zero236 (u w : Fin 10 → Fin 10 → ℤ)
    (hflag : ∀ j : Fin 9, integerReal (w j.castSucc) ∈
      minimaFlag10 (fun i => integerReal (u i)) 9) :
    ∀ j : Fin 9, ∑ i, (w j.castSucc i : ℚ)*(integerLastDual10 u i : ℚ) = 0 := by
  intro j
  have he := cofactor_flag_zero236 u (integerReal (w j.castSucc)) (hflag j)
  change ∑ i, (w j.castSucc i : ℝ)*(integerLastDual10 u i : ℝ) = 0 at he
  exact_mod_cast he

theorem rational_line_transfer236 (u w : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j)))
    (hw : LinearIndependent ℝ (fun j => integerReal (w j)))
    (hflag : ∀ j : Fin 9, integerReal (w j.castSucc) ∈
      minimaFlag10 (fun i => integerReal (u i)) 9) :
    Submodule.span ℚ {lastDual10 (fun j i => (u j i : ℚ))
      (integer_frame_rational_independent10 u hu)} =
    Submodule.span ℚ {lastDual10 (fun j i => (w j i : ℚ))
      (integer_frame_rational_independent10 w hw)} := by
  have huQ := integer_frame_rational_independent10 u hu
  have hwQ := integer_frame_rational_independent10 w hw
  have hn := integerLastDual10_nonzero u huQ
  have hrat : (fun i => (integerLastDual10 u i : ℚ)) ≠ 0 := by
    intro he
    apply hn
    funext i
    have hi := congrFun he i
    simp only [Pi.zero_apply] at hi
    change integerLastDual10 u i = 0
    exact_mod_cast hi
  have hm := rational_annihilator226 (fun j i => (w j i : ℚ)) hwQ
    (fun i => (integerLastDual10 u i : ℚ)) (flag_pairing_zero236 u w hflag)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  have ha0 : a ≠ 0 := by
    intro he
    apply hrat
    rw [← ha,he,zero_smul]
  rw [← integerLastDual10_line u huQ,← ha]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha0) _

theorem deformed_line_transfer236
    (F : DeformedAttaining236 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j : Fin 10 → ℤ)))
    (hgap : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9*Q^(-delta))
    (hcut : (1024 : ℝ)^2 < Q^delta) :
    Submodule.span ℚ {lastDual10 (fun j i => ((u j : Fin 10 → ℤ) i : ℚ))
      (integer_frame_rational_independent10 _ hu)} =
    Submodule.span ℚ {lastDual10 (fun j i => ((F.w j : Fin 10 → ℤ) i : ℚ))
      F.rational_independent} :=
  rational_line_transfer236 _ _ hu F.real_independent (deformed_first_nine236 F hgap hcut)

end CompoundFeasibility.SourceRatioLine236
