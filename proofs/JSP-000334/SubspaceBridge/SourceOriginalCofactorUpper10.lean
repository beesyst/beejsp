import SubspaceBridge.SourceOriginalVariable10
import SubspaceBridge.SourceOriginalBudget10
open scoped BigOperators Matrix
namespace CompoundFeasibility.SourceOriginalBudget10
open SourceSelectedUpper10 SourceSelectedSet10 OriginalDual10 SourceOriginalVariable10
noncomputable section

theorem finite_integer_cofactor10 (p : ℕ) [Fact p.Prime] (hp : 1 < p)
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1)
    (Q : ℝ) (hQ : 1 < Q) (f : Fin 10 → ℤ) (hf : ∀ i, f i ≤ 0)
    (u : Fin 10 → Fin 10 → ℤ)
    (hu : ∀ j i, padicNorm p ((A *ᵥ (fun k => (u j k : ℚ))) i) ≤ (p : ℚ)^(f i))
    (i : Fin 10) :
    ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual10 u k : ℚ_[p]))) i‖ ≤
        ∏ k : Fin 9, (p : ℝ)^(f (i.succAbove k)) := by
  have hm (j) := (normalized_lattice_exact10 p hp A Q hQ f hf (u j)).mpr (hu j)
  have h := finite_cofactor_rounded10 p A hA Q (fun i => normalizedFinite10 p Q (f i)) u hm i
  have he (k : Fin 10) : roundedRadius10 p Q (normalizedFinite10 p Q (f k)) = (p : ℝ)^(f k) := by
    unfold roundedRadius10
    rw [normalized_threshold_exact10 p hp Q hQ]
    rw [← zpow_natCast,Int.toNat_of_nonneg (neg_nonneg.mpr (hf k)),zpow_neg,inv_inv]
  simpa only [he] using h

theorem original_absolute_cofactor_upper10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (Q delta : ℝ) (hQ : 1 < Q) (A : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (f2 f3 : Fin 10 → ℤ) (hf2 : ∀ i, f2 i ≤ 0) (hf3 : ∀ i, f3 i ≤ 0)
    (hbal : (∏ i, A i*(2 : ℝ)^(f2 i)*(3 : ℝ)^(f3 i)) = 1)
    (lam : Fin 10 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hsmall : lam 8 < Q^(-delta)) (u : Fin 10 → Fin 10 → ℤ)
    (hreal : ∀ (j : Fin 9) i, |(L *ᵥ integerReal (u j.castSucc)) i| ≤ lam j.castSucc*A i)
    (hu2 : ∀ j i, padicNorm 2 ((A2 *ᵥ (fun k => (u j k : ℚ))) i) ≤ (2 : ℚ)^(f2 i))
    (hu3 : ∀ j i, padicNorm 3 ((A3 *ᵥ (fun k => (u j k : ℚ))) i) ≤ (3 : ℚ)^(f3 i))
    (s : MixedIndex10) (hsel : 1 ≤ A (s 0)*(2 : ℝ)^(f2 (s 1))*(3 : ℝ)^(f3 (s 2))*Q^(delta/2)) :
    mixedProduct10 A2 A3 L (integerLastDual10 u) s ≤ 362880*Q^(-17*delta/2) := by
  have h0 := real_cofactor_fin10 L hL u (fun j => lam j.castSucc) A hreal (s 0)
  rw [real_dual_cast_norm10] at h0
  have h2b := finite_integer_cofactor10 2 (by decide) A2 h2 Q hQ f2 hf2 u hu2 (s 1)
  have h3b := finite_integer_cofactor10 3 (by decide) A3 h3 Q hQ f3 hf3 u hu3 (s 2)
  have hn : (∏ j : Fin 9, lam j.castSucc) ≤ Q^(-9*delta) := by
    calc
      _ ≤ ∏ _j : Fin 9, Q^(-delta) := Finset.prod_le_prod
        (fun j _ => (hp _).le) (fun j _ => (hm (by change j.val ≤ 8; omega)).trans hsmall.le)
      _ = _ := by
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans hQ).le]
        congr 1
        ring
  have hb : (∏ i, A i)*(∏ i, (2 : ℝ)^(f2 i))*(∏ i, (3 : ℝ)^(f3 i)) = 1 := by
    simpa only [Finset.prod_mul_distrib] using hbal
  rw [finite_dual_norm_canonical10 2 A2 h2] at h2b
  rw [finite_dual_norm_canonical10 3 A3 h3] at h3b
  apply (mixedProduct10_le_canonical_bounds A2 A3 L h2 h3 (integerLastDual10 u) s
    _ _ _ h0 h2b h3b).trans
  exact absolute_selected_budget10 Q delta _ hQ hn A _ _ hA (fun _ => by positivity)
    (fun _ => by positivity) hb s hsel

end
end CompoundFeasibility.SourceOriginalBudget10
