import SubspaceBridge.SourceDualBody222
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceDualAnnihilation222

theorem coordinate_pairing222 (a d s r x z : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hx : |x| ≤ s*a) (hz : |z| ≤ r*(d/a)) :
    |x*z| ≤ s*r*d := by
  rw [abs_mul]
  calc
    _ ≤ (s*a)*(r*(d/a)) := mul_le_mul hx hz (abs_nonneg _) (mul_nonneg hs ha.le)
    _ = s*r*d := by field_simp [ha.ne']; ring

theorem sum_pairing222 (x z A : Fin 10 → ℝ) (d s r : ℝ)
    (hA : ∀ i, 0 < A i) (hd : 0 < d) (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hx : ∀ i, |x i| ≤ s*A i) (hz : ∀ i, |z i| ≤ r*(d/A i)) :
    |∑ i, x i*z i| ≤ 10*r*d*s := by
  calc
    _ ≤ ∑ i, |x i*z i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 10, s*r*d := Finset.sum_le_sum (fun i _ =>
      coordinate_pairing222 (A i) d s r _ _ (hA i) hd hs hr (hx i) (hz i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end CompoundFeasibility.SourceDualAnnihilation222
