import SubspaceBridge.SourceHeightEnvelopes6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightUpper6
open SourceNormalHeight SourceHeightBounds6 SourceMixed6 SourceLocalUpper6 SourceHeightEnvelopes6 SourceProper6

theorem cofactor_identity6 (M : Fin 6 → ℤ) (i : Fin 6) :
    cofactorValue6 (1 : Matrix (Fin 6) (Fin 6) ℝ) M i = (M i : ℝ) := by
  simp [cofactorValue6,cofactor6,Matrix.one_apply,mul_ite]

theorem identity_frame_entry6 (v : Matrix (Fin 6) (Fin 6) ℤ) (j k : Fin 6) :
    transformedFrame6 (1 : Matrix (Fin 6) (Fin 6) ℝ) v j k = (v j k : ℝ) := by
  rw [transformedFrame6_apply,Matrix.one_mulVec]

theorem identity_signed_minor6 (v : Matrix (Fin 6) (Fin 6) ℤ) (M : Fin 6 → ℤ)
    (g : ℤ) (hscale : ∀ k, rawNormal6 v k = g*M k) (i : Fin 6) :
    (-1 : ℝ)^(5+i.val)*
      ((transformedFrame6 (1 : Matrix (Fin 6) (Fin 6) ℝ) v).submatrix
        Fin.castSucc i.succAbove).det = (g : ℝ)*(M i : ℝ) := by
  have h := transformed_minor_cofactor6 (1 : Matrix (Fin 6) (Fin 6) ℝ) v M g hscale i
  simpa only [cofactor_identity6] using h

theorem identity_real_minor_upper6 (v : Matrix (Fin 6) (Fin 6) ℤ) (A Q : ℝ)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hv : ∀ (j : Fin 5) i, |(v j.castSucc i : ℝ)| ≤ A*Q) (i : Fin 6) :
    ‖((transformedFrame6 (1 : Matrix (Fin 6) (Fin 6) ℝ) v).submatrix
      Fin.castSucc i.succAbove).det‖ ≤ 120*A^5*Q^5 := by
  have h := real_det5_le
    ((transformedFrame6 (1 : Matrix (Fin 6) (Fin 6) ℝ) v).submatrix
      Fin.castSucc i.succAbove) (fun _ => A*Q)
    (fun _ => mul_nonneg hA hQ) (fun j k => by
      change ‖transformedFrame6 (1 : Matrix (Fin 6) (Fin 6) ℝ) v j.castSucc (i.succAbove k)‖ ≤ _
      rw [identity_frame_entry6,Real.norm_eq_abs]
      exact hv j (i.succAbove k))
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow,mul_assoc] using h


theorem integer_abs_ge_one6 (g : ℤ) (hg : g ≠ 0) : 1 ≤ |(g : ℝ)| := by
  have hn : 1 ≤ g.natAbs := Int.natAbs_pos.mpr hg
  have he : (g.natAbs : ℝ) = |(g : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [← he]
  exact_mod_cast hn

theorem normalized_coordinate_upper6 (v : Matrix (Fin 6) (Fin 6) ℤ) (M : Fin 6 → ℤ)
    (g : ℤ) (hg : g ≠ 0) (hscale : ∀ k, rawNormal6 v k = g*M k)
    (A Q : ℝ) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hv : ∀ (j : Fin 5) i, |(v j.castSucc i : ℝ)| ≤ A*Q) (i : Fin 6) :
    |(M i : ℝ)| ≤ 120*A^5*Q^5 := by
  have hi := congrArg (fun x : ℝ => |x|) (identity_signed_minor6 v M g hscale i)
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] at hi
  have hb := identity_real_minor_upper6 v A Q hA hQ hv i
  rw [Real.norm_eq_abs] at hb
  calc
    |(M i : ℝ)| = 1*|(M i : ℝ)| := by ring
    _ ≤ |(g : ℝ)| *|(M i : ℝ)| :=
      mul_le_mul_of_nonneg_right (integer_abs_ge_one6 g hg) (abs_nonneg _)
    _ = _ := hi.symm
    _ ≤ _ := hb

theorem normalHeight6_real_le (M : Fin 6 → ℤ) (B : ℝ)
    (h : ∀ i, |(M i : ℝ)| ≤ B) : (normalHeight6 M : ℝ) ≤ B := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 6))
    Finset.univ_nonempty (fun i => (M i).natAbs)
  change ((Finset.univ.sup (fun i => (M i).natAbs) : ℕ) : ℝ) ≤ B
  rw [hi]
  have he : ((M i).natAbs : ℝ) = |(M i : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [he]
  exact h i

theorem factor_height_upper6 (v : Matrix (Fin 6) (Fin 6) ℤ) (M : Fin 6 → ℤ)
    (g : ℤ) (hg : g ≠ 0) (hscale : ∀ k, rawNormal6 v k = g*M k)
    (A Q : ℝ) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hv : ∀ (j : Fin 5) i, |(v j.castSucc i : ℝ)| ≤ A*Q) :
    (normalHeight6 M : ℝ) ≤ 120*A^5*Q^5 :=
  normalHeight6_real_le M _ (normalized_coordinate_upper6 v M g hg hscale A Q hA hQ hv)

theorem primitive_height_upper6 (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (hM : M ≠ 0) (ha : (∑ i, a i*M i)=1)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i)=0)
    (A Q : ℝ) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hcoord : ∀ (j : Fin 5) i, |(v j.castSucc i : ℝ)| ≤ A*Q) :
    (normalHeight6 M : ℝ) ≤ 120*A^5*Q^5 := by
  have hf := primitive_minor_factor6 v hv M a hM ha hann
  exact factor_height_upper6 v M _ hf.1 hf.2.1 A Q hA hQ hcoord

def upperConstant6 (L : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  120*(inverseConstant6 (compound L))^5

theorem upperConstant6_pos (L : Matrix (Fin 4) (Fin 4) ℝ) : 0 < upperConstant6 L :=
  mul_pos (by norm_num) (pow_pos (inverseConstant6_pos _) _)

theorem actual_height_upper6 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ)
    (hn : minorNormalization6 v M a) (Q delta : ℝ) (c : Fin 6 → ℝ)
    (hQ : 1 < Q) (hd : 0 < delta) (hc : ∀ i, |c i| ≤ 1)
    (hR : ∀ (j : Fin 5) i, ‖(compound L *ᵥ (fun k => (v j.castSucc k : ℝ))) i‖ ≤ Q^(c i-delta)) :
    (normalHeight6 M : ℝ) ≤ upperConstant6 L*Q^5 := by
  exact factor_height_upper6 v M _ hn.2.1 hn.2.2.1 _ Q (inverseConstant6_pos _).le
    (zero_lt_one.trans hQ).le (frame_coordinate6 L hL v Q delta c hQ hd hc hR)

theorem upper_absorption6 (B Q N : ℝ) (hQ : 1 < Q) (hBQ : B ≤ Q)
    (hN : N ≤ B*Q^5) : max 1 N ≤ Q^(6 : ℝ) := by
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  apply max_le
  · exact one_le_pow₀ hQ.le
  · calc
      N ≤ B*Q^5 := hN
      _ ≤ Q*Q^5 := mul_le_mul_of_nonneg_right hBQ (pow_nonneg (zero_lt_one.trans hQ).le _)
      _ = Q^6 := by ring


theorem actual_lower_power6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 6 → ℤ) (s : MixedIndex6)
    (K : IntermediateField ℚ ℝ) (C delta Q : ℝ) (hC : 0 < C) (hd : 0 < delta)
    (hQ : 1 < Q) (hT : lowerThreshold6 C delta ≤ Q)
    (hu : actualNormProduct6 A2 A3 L M s ≤ 120*Q^(-delta/8))
    (hl : C ≤ actualNormProduct6 A2 A3 L M s*
      (max 1 (normalHeight6 M : ℝ))^(Module.finrank ℚ K+1)) :
    Q^(heightAlpha6 delta (Module.finrank ℚ K)) ≤ max 1 (normalHeight6 M : ℝ) := by
  apply lower_absorption6 C delta Q _ _ hC hd hT (le_max_left _ _)
  exact combined_product6 C Q delta _ _ _ (zero_lt_one.trans hQ)
    (zero_le_one.trans (le_max_left _ _)) hl hu

def sourceHeightCutoff6 (L : Matrix (Fin 4) (Fin 4) ℝ) (C delta : ℝ) : ℝ :=
  max (lowerThreshold6 C delta) (upperConstant6 L)

theorem sourceHeightCutoff6_gt_one (L : Matrix (Fin 4) (Fin 4) ℝ) (C delta : ℝ) :
    1 < sourceHeightCutoff6 L C delta := by
  have h : 2 ≤ sourceHeightCutoff6 L C delta :=
    (le_max_left _ _).trans (le_max_left (lowerThreshold6 C delta) (upperConstant6 L))
  linarith

theorem original_q_cutoff6 (L : Matrix (Fin 4) (Fin 4) ℝ) (C delta q : ℝ)
    (hq : 1 < q) (hT : sourceHeightCutoff6 L C delta < q) :
    lowerThreshold6 C delta ≤ q^(11 : ℕ) ∧ upperConstant6 L ≤ q^(11 : ℕ) ∧
      1 < q^(11 : ℕ) := by
  have hqQ : q ≤ q^(11 : ℕ) := le_self_pow₀ hq.le (by decide)
  have hTQ : sourceHeightCutoff6 L C delta ≤ q^(11 : ℕ) := hT.le.trans hqQ
  exact ⟨(le_max_left _ _).trans hTQ,(le_max_right _ _).trans hTQ,
    one_lt_pow₀ hq (by decide)⟩

theorem same_normal_envelopes6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ)
    (hn : minorNormalization6 v M a) (s : MixedIndex6)
    (K : IntermediateField ℚ ℝ) (C delta q : ℝ) (c : Fin 6 → ℝ)
    (hC : 0 < C) (hd : 0 < delta) (hq : 1 < q) (hc : ∀ i, |c i| ≤ 1)
    (hR : ∀ (j : Fin 5) i, ‖(compound L *ᵥ (fun k => (v j.castSucc k : ℝ))) i‖ ≤
      (q^(11 : ℕ))^(c i-delta))
    (hu : actualNormProduct6 A2 A3 L M s ≤ 120*(q^(11 : ℕ))^(-delta/8))
    (hl : C ≤ actualNormProduct6 A2 A3 L M s*
      (max 1 (normalHeight6 M : ℝ))^(Module.finrank ℚ K+1))
    (hT : sourceHeightCutoff6 L C delta < q) :
    (q^(11 : ℕ))^(heightAlpha6 delta (Module.finrank ℚ K)) ≤ max 1 (normalHeight6 M : ℝ) ∧
      max 1 (normalHeight6 M : ℝ) ≤ (q^(11 : ℕ))^(6 : ℝ) := by
  obtain ⟨hlo,hup,hQ⟩ := original_q_cutoff6 L C delta q hq hT
  exact ⟨actual_lower_power6 A2 A3 L M s K C delta _ hC hd hQ hlo hu hl,
    upper_absorption6 (upperConstant6 L) _ _ hQ hup
      (actual_height_upper6 L hL v M a hn _ delta c hQ hd hc hR)⟩

theorem unbounded_original_q_cutoff6 (F : Set ℝ) (hF : ¬ BddAbove F) (T R : ℝ) :
    ∃ q : F, max T R < q.val := by
  obtain ⟨q,hq,hgt⟩ := not_bddAbove_iff.mp hF (max T R)
  exact ⟨⟨q,hq⟩,hgt⟩

end CompoundFeasibility.SourceHeightUpper6
