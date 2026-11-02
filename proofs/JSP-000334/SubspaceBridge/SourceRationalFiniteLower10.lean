import SubspaceBridge.SourceRealLiouville10
import SubspaceBridge.SourceFieldLower6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10
open SchmidtNormal10 OriginalDual10

def finiteValue10 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 10) (Fin 10) ℚ) (M : Fin 10 → ℤ) (i : Fin 10) : ℚ_[p] :=
  ∑ k, (B i k : ℚ_[p])*(M k : ℚ_[p])

theorem fixed_rational_denominator10 (B : Matrix (Fin 10) (Fin 10) ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ N : Matrix (Fin 10) (Fin 10) ℤ,
      ∀ i j, (N i j : ℚ) = (d : ℚ)*B i j := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun ij : Fin 10 × Fin 10 => B ij.1 ij.2)
  choose N hN using hd
  refine ⟨d.val,mem_nonZeroDivisors_iff_ne_zero.mp d.property,fun i j => N (i,j),?_⟩
  intro i j
  simpa only [Algebra.smul_def,eq_intCast] using hN (i,j)

theorem finite_denominator_identity10 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 10) (Fin 10) ℚ) (d : ℤ) (hd : d ≠ 0)
    (N : Matrix (Fin 10) (Fin 10) ℤ)
    (hN : ∀ i j, (N i j : ℚ) = (d : ℚ)*B i j)
    (M : Fin 10 → ℤ) (s : Fin 10) :
    finiteValue10 p B M s = ((∑ i, M i*N s i : ℤ) : ℚ_[p])/(d : ℚ_[p]) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hr : (∑ i, B s i*(M i : ℚ)) = ((∑ i, M i*N s i : ℤ) : ℚ)/(d : ℚ) := by
    apply (eq_div_iff hdQ).mpr
    simp only [Int.cast_sum,Int.cast_mul,Finset.sum_mul,hN]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = algebraMap ℚ ℚ_[p] (∑ i, B s i*(M i : ℚ)) := by
      simp [finiteValue10]
    _ = _ := by rw [hr,map_div₀,map_intCast,map_intCast]

theorem integer_numerator_height10 (N : Matrix (Fin 10) (Fin 10) ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 10 → ℤ) s,
      |((∑ i, M i*N s i : ℤ) : ℝ)| ≤ C*max 1 (normalHeight10 M : ℝ) := by
  let C : ℝ := 1+∑ s, ∑ i, |(N s i : ℝ)|
  have hsum : 0 ≤ ∑ s, ∑ i, |(N s i : ℝ)| :=
    Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro M s
  have hrow : (∑ i, |(N s i : ℝ)|) ≤ C := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun s : Fin 10 => ∑ i, |(N s i : ℝ)|)
      (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  calc
    _ = ‖∑ i, (M i : ℝ)*(N s i : ℝ)‖ := by simp only [Int.cast_sum,Int.cast_mul,Real.norm_eq_abs]
    _ ≤ ∑ i, |(M i : ℝ)| *|(N s i : ℝ)| := by
      simpa only [norm_mul,Real.norm_eq_abs] using
        norm_sum_le (s := Finset.univ) (f := fun i => (M i : ℝ)*(N s i : ℝ))
    _ ≤ ∑ i, max 1 (normalHeight10 M : ℝ)*|(N s i : ℝ)| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        ((normalHeight10_coord M i).trans (le_max_right _ _)) (abs_nonneg _)
    _ = (∑ i, |(N s i : ℝ)|)*max 1 (normalHeight10 M : ℝ) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow (zero_le_one.trans (le_max_left _ _))

theorem finite_form_lower10 (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (A : Matrix (Fin 10) (Fin 10) ℚ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : Fin 10 → ℤ) s,
      finiteValue10 p A M s ≠ 0 →
      c ≤ ‖finiteValue10 p A M s‖*max 1 (normalHeight10 M : ℝ) ∧
      c/max 1 (normalHeight10 M : ℝ) ≤ ‖finiteValue10 p A M s‖ := by
  obtain ⟨d,hd,N,hN⟩ := fixed_rational_denominator10 A
  obtain ⟨C,hC,hheight⟩ := integer_numerator_height10 N
  have hdp : (d : ℚ_[p]) ≠ 0 := by exact_mod_cast hd
  have hdn : 0 < ‖(d : ℚ_[p])‖ := norm_pos_iff.mpr hdp
  have hden : 0 < C*‖(d : ℚ_[p])‖ := mul_pos hC hdn
  refine ⟨1/(C*‖(d : ℚ_[p])‖),one_div_pos.mpr hden,?_⟩
  intro M s hne
  let z : ℤ := ∑ i, M i*N s i
  have hz : z ≠ 0 := by
    intro hz
    apply hne
    rw [finite_denominator_identity10 p A d hd N hN M s]
    change (z : ℚ_[p])/(d : ℚ_[p]) = 0
    rw [hz,Int.cast_zero,zero_div]
  have ha : 0 < |(z : ℝ)| := abs_pos.mpr (by exact_mod_cast hz)
  have hzlower : 1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := by
    rcases hp with rfl | rfl
    · exact (div_le_iff₀ ha).mp (SourceFieldLower6.integer_padic2_lower6 z hz) |>.trans_eq (mul_comm _ _)
    · exact (div_le_iff₀ ha).mp (SourceFieldLower6.integer_padic3_lower6 z hz) |>.trans_eq (mul_comm _ _)
  have hnorm : ‖(z : ℚ_[p])‖ = ‖finiteValue10 p A M s‖*‖(d : ℚ_[p])‖ := by
    rw [finite_denominator_identity10 p A d hd N hN M s,norm_div,div_mul_cancel₀ _ hdn.ne']
  have htotal : 1 ≤ (C*‖(d : ℚ_[p])‖)*
      (‖finiteValue10 p A M s‖*max 1 (normalHeight10 M : ℝ)) := by
    calc
      1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := hzlower
      _ ≤ (C*max 1 (normalHeight10 M : ℝ))*‖(z : ℚ_[p])‖ :=
        mul_le_mul_of_nonneg_right (hheight M s) (norm_nonneg _)
      _ = _ := by rw [hnorm]; ring
  have hl : 1/(C*‖(d : ℚ_[p])‖) ≤
      ‖finiteValue10 p A M s‖*max 1 (normalHeight10 M : ℝ) :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)
  exact ⟨hl,(div_le_iff₀ (zero_lt_one.trans_le (le_max_left _ _))).mpr hl⟩




end CompoundFeasibility.SourceHeightEnvelope10
