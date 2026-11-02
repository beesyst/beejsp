import SubspaceBridge.SourceOriginalVariable10
open scoped BigOperators Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
noncomputable section

def finiteUpper10 (x e : ℝ) : ℝ := min 0 (x+e)

def balanceCorrection10 (x : Fin 3 → Fin 10 → ℝ) (e : ℝ) : ℝ :=
  ((∑ i, (finiteUpper10 (x 1 i) e-x 1 i))+(∑ i, (finiteUpper10 (x 2 i) e-x 2 i)))/10

def fixedOriginalWeights10 (x : Fin 3 → Fin 10 → ℝ) (e : ℝ) : Fin 3 → Fin 10 → ℝ :=
  ![fun i => x 0 i-balanceCorrection10 x e,
    fun i => finiteUpper10 (x 1 i) e,fun i => finiteUpper10 (x 2 i) e]

theorem finite_upper_bounds10 (x e : ℝ) (hx : x ≤ 0) (he : 0 ≤ e) :
    x ≤ finiteUpper10 x e ∧ finiteUpper10 x e ≤ 0 ∧ finiteUpper10 x e-x ≤ e := by
  unfold finiteUpper10
  exact ⟨le_min hx (by linarith),min_le_left _ _,by have := min_le_right 0 (x+e); linarith⟩

theorem fixed_original_weights10 (x : Fin 3 → Fin 10 → ℝ) (e : ℝ)
    (he : 0 < e) (he1 : e ≤ 1/40) (hx : ∀ tau i, |x tau i| ≤ 1/5)
    (hx1 : ∀ i, x 1 i ≤ 0) (hx2 : ∀ i, x 2 i ≤ 0)
    (hbal : (∑ tau, ∑ i, x tau i) = 0) :
    let c := fixedOriginalWeights10 x e
    (∀ tau i, |c tau i| ≤ 1) ∧ (∑ tau, ∑ i, c tau i) = 0 ∧
      (∀ i, c 1 i ≤ 0 ∧ c 2 i ≤ 0) ∧
      (∀ i, c 0 i+2*e ≥ x 0 i) ∧
      (∀ i, x 1 i ≤ c 1 i ∧ x 2 i ≤ c 2 i) := by
  have h1 (i) := finite_upper_bounds10 (x 1 i) e (hx1 i) he.le
  have h2 (i) := finite_upper_bounds10 (x 2 i) e (hx2 i) he.le
  have hc : 0 ≤ balanceCorrection10 x e ∧ balanceCorrection10 x e ≤ 2*e := by
    have hs (tau : Fin 3) (ht : ∀ i, x tau i ≤ 0) :
        0 ≤ (∑ i, (finiteUpper10 (x tau i) e-x tau i)) ∧
          (∑ i, (finiteUpper10 (x tau i) e-x tau i)) ≤ 10*e := by
      constructor
      · exact Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (finite_upper_bounds10 _ _ (ht i) he.le).1)
      · calc
          _ ≤ ∑ _i : Fin 10, e := Finset.sum_le_sum (fun i _ => (finite_upper_bounds10 _ _ (ht i) he.le).2.2)
          _ = _ := by simp
    unfold balanceCorrection10
    constructor <;> linarith [(hs 1 hx1).1,(hs 1 hx1).2,(hs 2 hx2).1,(hs 2 hx2).2]
  dsimp only [fixedOriginalWeights10]
  refine ⟨?_,?_,fun i => ⟨(h1 i).2.1,(h2 i).2.1⟩,fun i => ?_,fun i => ⟨(h1 i).1,(h2 i).1⟩⟩
  · intro tau i
    fin_cases tau
    · change |x 0 i-balanceCorrection10 x e| ≤ 1
      exact abs_le.mpr ⟨by linarith [(abs_le.mp (hx 0 i)).1],by linarith [(abs_le.mp (hx 0 i)).2]⟩
    · change |finiteUpper10 (x 1 i) e| ≤ 1
      exact abs_le.mpr ⟨by linarith [(abs_le.mp (hx 1 i)).1,(h1 i).1],by linarith [(h1 i).2.1]⟩
    · change |finiteUpper10 (x 2 i) e| ≤ 1
      exact abs_le.mpr ⟨by linarith [(abs_le.mp (hx 2 i)).1,(h2 i).1],by linarith [(h2 i).2.1]⟩
  · simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_ofNat,
      Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      balanceCorrection10]
    simp only [Fin.sum_univ_three] at hbal
    linarith
  · change x 0 i-balanceCorrection10 x e+2*e ≥ x 0 i
    linarith

end
end CompoundFeasibility.SourceOriginalVariable10
