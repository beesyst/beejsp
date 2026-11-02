import SubspaceBridge.SourceCubeDomain243
import SubspaceBridge.SourceFin5Dual245
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245P

def blockIndex245P : Fin 5 ⊕ Fin 5 ≃ Fin 10 := finSumFinEquiv

def block245P {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    Matrix (Fin 10) (Fin 10) R :=
  Matrix.reindex blockIndex245P blockIndex245P (Matrix.fromBlocks A 0 0 1)

def weight0245P (c : Fin 5 → ℝ) (i : Fin 10) : ℝ :=
  Sum.elim (fun j => (c j-2)/3) (fun _ => 2/3) (blockIndex245P.symm i)

def weightp245P (c : Fin 5 → ℝ) (i : Fin 10) : ℝ :=
  Sum.elim (fun j => c j/3) (fun _ => 0) (blockIndex245P.symm i)

theorem weight_bounds245P (c0 c2 c3 : Fin 5 → ℝ)
    (h0 : ∀ i, |c0 i| ≤ 1) (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    (∀ i, |weight0245P c0 i| ≤ 1) ∧
    (∀ i, -1 ≤ weightp245P c2 i ∧ weightp245P c2 i ≤ 0) ∧
    (∀ i, -1 ≤ weightp245P c3 i ∧ weightp245P c3 i ≤ 0) := by
  have hreal (i : Fin 10) : |weight0245P c0 i| ≤ 1 := by
    unfold weight0245P
    cases h : blockIndex245P.symm i with
    | inl j => simp only [Sum.elim_inl]; exact abs_le.mpr ⟨by linarith [(abs_le.mp (h0 j)).1],by linarith [(abs_le.mp (h0 j)).2]⟩
    | inr j => apply abs_le.mpr; constructor <;> norm_num
  have hfinite (c : Fin 5 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) (i : Fin 10) :
      -1 ≤ weightp245P c i ∧ weightp245P c i ≤ 0 := by
    unfold weightp245P
    cases h : blockIndex245P.symm i with
    | inl j => simp only [Sum.elim_inl]; constructor <;> linarith [(hc j).1,(hc j).2]
    | inr j => norm_num
  exact ⟨hreal,hfinite c2 h2,hfinite c3 h3⟩

theorem weight_balance245P (c0 c2 c3 : Fin 5 → ℝ)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∑ i, (weight0245P c0 i+weightp245P c2 i+weightp245P c3 i)) = 0 := by
  rw [← Equiv.sum_comp blockIndex245P]
  simp only [weight0245P,weightp245P,Equiv.symm_apply_apply,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_div,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin] at hb
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  linarith

end CompoundFeasibility.BlockReduction245P
