import SubspaceBridge.SourceFieldLowerIntegration6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelopes6
open SourceNormalHeight SourceHeightBounds6 SourceMixed6 SourceLocalUpper6

theorem combined_product6 (C Q delta H P : ℝ) (n : ℕ)
    (hQ : 0 < Q) (hH : 0 ≤ H)
    (hl : C ≤ P*H^n) (hu : P ≤ 120*Q^(-delta/8)) :
    (C/120)*Q^(delta/8) ≤ H^n := by
  have h := hl.trans (mul_le_mul_of_nonneg_right hu (pow_nonneg hH n))
  have hp : 0 < Q^(delta/8) := Real.rpow_pos_of_pos hQ _
  have he : Q^(-delta/8)*Q^(delta/8) = 1 := by
    rw [← Real.rpow_add hQ]
    convert Real.rpow_zero Q using 1 <;> ring
  have ht := mul_le_mul_of_nonneg_right h hp.le
  have hr : (120*Q^(-delta/8)*H^n)*Q^(delta/8) = 120*H^n := by
    calc
      _ = 120*H^n*(Q^(-delta/8)*Q^(delta/8)) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hr] at ht
  linarith

def lowerThreshold6 (C delta : ℝ) : ℝ := max 2 ((120/C)^((delta/16)⁻¹))

def heightAlpha6 (delta : ℝ) (d : ℕ) : ℝ := delta/(16*((d : ℝ)+1))

theorem heightAlpha6_pos (delta : ℝ) (hd : 0 < delta) (d : ℕ) :
    0 < heightAlpha6 delta d := by unfold heightAlpha6; positivity

theorem lower_absorption6 (C delta Q H : ℝ) (d : ℕ) (hC : 0 < C)
    (hd : 0 < delta) (hQ : lowerThreshold6 C delta ≤ Q) (hH : 1 ≤ H)
    (hl : (C/120)*Q^(delta/8) ≤ H^(d+1)) :
    Q^(heightAlpha6 delta d) ≤ H := by
  have hQ2 : 2 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := by linarith
  have he : 0 < delta/16 := by positivity
  have hc : 0 < 120/C := by positivity
  have ht : (120/C)^((delta/16)⁻¹) ≤ Q := (le_max_right _ _).trans hQ
  have hb := Real.rpow_le_rpow (Real.rpow_nonneg hc.le _) ht he.le
  rw [Real.rpow_inv_rpow hc.le he.ne'] at hb
  have hconst : 1 ≤ (C/120)*Q^(delta/16) := by
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ C/120 by positivity)
    have hh0 : (C/120)*(120/C) = 1 := by field_simp
    rwa [hh0] at hh
  have hn : 0 < ((d+1 : ℕ) : ℝ) := by positivity
  have hpow : (Q^(heightAlpha6 delta d))^(d+1) = Q^(delta/16) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ0.le]
    congr 1
    simp only [heightAlpha6,Nat.cast_add,Nat.cast_one]
    field_simp
    <;> ring
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hQ0.le _) (zero_le_one.trans hH) hn).mp
  simp only [Real.rpow_natCast]
  rw [hpow]
  calc
    Q^(delta/16) ≤ ((C/120)*Q^(delta/16))*Q^(delta/16) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hQ0.le _)
    _ = (C/120)*Q^(delta/8) := by
      rw [mul_assoc,← Real.rpow_add hQ0]
      congr 2
      ring
    _ ≤ _ := hl


def inverseConstant6 (B : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  1+∑ i, ∑ k, |B⁻¹ i k|

theorem inverseConstant6_pos (B : Matrix (Fin 6) (Fin 6) ℝ) : 0 < inverseConstant6 B := by
  have h : 0 ≤ ∑ i, ∑ k, |B⁻¹ i k| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
  unfold inverseConstant6
  linarith

theorem inverse_coordinate6 (B : Matrix (Fin 6) (Fin 6) ℝ) (hB : IsUnit B)
    (x : Fin 6 → ℝ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hx : ∀ k, ‖(B *ᵥ x) k‖ ≤ Q) (i : Fin 6) :
    |x i| ≤ inverseConstant6 B*Q := by
  have hid : B⁻¹ *ᵥ (B *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB),Matrix.one_mulVec]
  have hrow : (∑ k, |B⁻¹ i k|) ≤ inverseConstant6 B := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 6 => ∑ k, |B⁻¹ i k|)
      (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ i)
    unfold inverseConstant6
    linarith
  calc
    |x i| = ‖∑ k, B⁻¹ i k*(B *ᵥ x) k‖ := by
      change |x i| = ‖(B⁻¹ *ᵥ (B *ᵥ x)) i‖
      rw [hid,Real.norm_eq_abs]
    _ ≤ ∑ k, ‖B⁻¹ i k*(B *ᵥ x) k‖ := norm_sum_le _ _
    _ ≤ ∑ k, |B⁻¹ i k| *Q := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
    _ = (∑ k, |B⁻¹ i k|)*Q := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hQ

theorem transformed_le_Q6 (B : Matrix (Fin 6) (Fin 6) ℝ)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (Q delta : ℝ) (c : Fin 6 → ℝ)
    (hQ : 1 < Q) (hd : 0 < delta) (hc : ∀ i, |c i| ≤ 1)
    (hv : ∀ (j : Fin 5) i, ‖(B *ᵥ (fun k => (v j.castSucc k : ℝ))) i‖ ≤ Q^(c i-delta)) :
    ∀ (j : Fin 5) i, ‖(B *ᵥ (fun k => (v j.castSucc k : ℝ))) i‖ ≤ Q := by
  intro j i
  have he : c i-delta ≤ 1 := by have h := (abs_le.mp (hc i)).2; linarith
  exact (hv j i).trans ((Real.rpow_le_rpow_of_exponent_le hQ.le he).trans_eq (Real.rpow_one Q))

theorem frame_coordinate6 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (v : Matrix (Fin 6) (Fin 6) ℤ) (Q delta : ℝ) (c : Fin 6 → ℝ)
    (hQ : 1 < Q) (hd : 0 < delta) (hc : ∀ i, |c i| ≤ 1)
    (hv : ∀ (j : Fin 5) i, ‖(compound L *ᵥ (fun k => (v j.castSucc k : ℝ))) i‖ ≤ Q^(c i-delta)) :
    ∀ (j : Fin 5) i, |(v j.castSucc i : ℝ)| ≤ inverseConstant6 (compound L)*Q := by
  intro j i
  exact inverse_coordinate6 (compound L) (compound_unit L hL) _ Q
    (zero_lt_one.trans hQ).le (transformed_le_Q6 _ v Q delta c hQ hd hc hv j) i


end CompoundFeasibility.SourceHeightEnvelopes6
