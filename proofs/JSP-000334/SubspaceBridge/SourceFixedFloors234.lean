import SubspaceBridge.SourceLattice10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedArithmetic234
def dualSupport234 (A : Matrix (Fin 10) (Fin 10) ℚ) (v : Fin 10 → ℤ) : Finset (Fin 10) :=
  Finset.univ.filter (fun i => (A⁻¹.transpose *ᵥ (fun j => (v j : ℚ))) i ≠ 0)

theorem dualSupport_nonempty234 (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A)
    (v : Fin 10 → ℤ) (hv : v ≠ 0) : (dualSupport234 A v).Nonempty := by
  by_contra he
  have hz : A⁻¹.transpose *ᵥ (fun j => (v j : ℚ)) = 0 := by
    funext i
    by_contra hi
    change (A⁻¹.transpose *ᵥ (fun j => (v j : ℚ))) i ≠ 0 at hi
    exact he ⟨i,by simp [dualSupport234,hi]⟩
  have hr := congrArg (Matrix.mulVec A.transpose) hz
  rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA),
    Matrix.transpose_one,Matrix.one_mulVec,Matrix.mulVec_zero] at hr
  apply hv
  funext i
  have hi := congrFun hr i
  simp only [Pi.zero_apply] at hi
  change v i = 0
  exact_mod_cast hi

def complementaryFloor234 (p : ℕ) (q : ℝ) (c : Fin 10 → ℝ) (i : Fin 10) : ℤ :=
  Int.floor ((Real.log q/Real.log p)*(∑ j : Fin 9, c (i.succAbove j)))

def floorMin234 (p : ℕ) (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A)
    (q : ℝ) (c : Fin 10 → ℝ) (v : Fin 10 → ℤ) (hv : v ≠ 0) : ℤ :=
  ((dualSupport234 A v).image (complementaryFloor234 p q c)).min'
    ((dualSupport_nonempty234 A hA v hv).image _)

theorem floorMin_le234 (p : ℕ) (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A)
    (q : ℝ) (c : Fin 10 → ℝ) (v : Fin 10 → ℤ) (hv : v ≠ 0)
    (i : Fin 10) (hi : i ∈ dualSupport234 A v) :
    floorMin234 p A hA q c v hv ≤ complementaryFloor234 p q c i := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

theorem floorMin_nonpos234 (p : ℕ) (hp : 1 < p) (A : Matrix (Fin 10) (Fin 10) ℚ)
    (hA : IsUnit A) (q : ℝ) (hq : 1 < q) (c : Fin 10 → ℝ)
    (hc : ∀ i, c i ≤ 0) (v : Fin 10 → ℤ) (hv : v ≠ 0) :
    floorMin234 p A hA q c v hv ≤ 0 := by
  obtain ⟨i,hi⟩ := dualSupport_nonempty234 A hA v hv
  apply (floorMin_le234 p A hA q c v hv i hi).trans
  apply Int.floor_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (Real.log_pos hq).le (Real.log_pos (by exact_mod_cast hp)).le)
    (Finset.sum_nonpos (fun j _ => hc (i.succAbove j)))

theorem rounding_margin234 (x : Fin 9 → ℝ) (hx : ∀ j, 0 ≤ x j) :
    (∑ j, Nat.ceil (x j)) ≤ (9-Int.floor (-(∑ j, x j))).toNat := by
  have hg : Int.floor (-(∑ j, x j)) ≤ 0 :=
    Int.floor_nonpos (neg_nonpos.mpr (Finset.sum_nonneg (fun j _ => hx j)))
  have hn : 0 ≤ 9-Int.floor (-(∑ j, x j)) := by omega
  have he : (((9-Int.floor (-(∑ j, x j))).toNat : ℕ) : ℝ) =
      9-(Int.floor (-(∑ j, x j)) : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hn]
    push_cast
    rfl
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => (Nat.ceil_lt_add_one (hx j)).le)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hsum
  have hf := Int.floor_le (-(∑ j, x j))
  have hh : (∑ j : Fin 9, (Nat.ceil (x j) : ℝ)) ≤
      (((9-Int.floor (-(∑ j, x j))).toNat : ℕ) : ℝ) := by
    rw [he]
    norm_num at hsum
    linarith
  exact_mod_cast hh

theorem floor_bound234 (p : ℕ) (hp : 1 < p) (q : ℝ) (hq : 1 < q)
    (c : Fin 10 → ℝ) (hc : ∀ i, c i ≤ 0) (i : Fin 10) :
    (∑ j, Nat.ceil (JSP000334.qThreshold p q (c j))) -
      Nat.ceil (JSP000334.qThreshold p q (c i)) ≤
        (9-complementaryFloor234 p q c i).toNat := by
  have ht (j : Fin 10) : 0 ≤ JSP000334.qThreshold p q (c j) :=
    JSP000334.qThreshold_nonneg p hp q (c j) hq (hc j)
  have h := rounding_margin234 (fun j : Fin 9 => JSP000334.qThreshold p q (c (i.succAbove j)))
    (fun j => ht (i.succAbove j))
  have he : (Real.log q/Real.log p)*(∑ j : Fin 9, c (i.succAbove j)) =
      -(∑ j : Fin 9, JSP000334.qThreshold p q (c (i.succAbove j))) := by
    rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold JSP000334.qThreshold
    ring
  unfold complementaryFloor234
  rw [he]
  have hs := Fin.sum_univ_succAbove (fun j => Nat.ceil (JSP000334.qThreshold p q (c j))) i
  rw [hs,Nat.add_sub_cancel_left]
  exact h


end CompoundFeasibility.SourceFixedArithmetic234
