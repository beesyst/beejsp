import SubspaceBridge.SourceAbsoluteGap10
import SubspaceBridge.SourceSelectedCofactor10
open scoped BigOperators Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
noncomputable section

def normalizedWidth10 (Q A : ℝ) : ℝ := Real.log A/Real.log Q

def normalizedFinite10 (p : ℕ) (Q : ℝ) (f : ℤ) : ℝ :=
  (f : ℝ)*Real.log (p : ℝ)/Real.log Q

theorem normalized_width_exact10 (Q A : ℝ) (hQ : 1 < Q) (hA : 0 < A) :
    Q^(normalizedWidth10 Q A) = A := by
  rw [normalizedWidth10,Real.rpow_def_of_pos (zero_lt_one.trans hQ)]
  have he : Real.log Q*(Real.log A/Real.log Q) = Real.log A := by
    field_simp [(Real.log_pos hQ).ne']
  rw [he,Real.exp_log hA]

theorem normalized_finite_exact10 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q) (f : ℤ) :
    Q^(normalizedFinite10 p Q f) = (p : ℝ)^f := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  rw [normalizedFinite10,Real.rpow_def_of_pos (zero_lt_one.trans hQ),
    ← Real.rpow_intCast (p : ℝ) f,
    Real.rpow_def_of_pos (zero_lt_one.trans hpR)]
  congr 1
  field_simp [(Real.log_pos hQ).ne']
  ring

theorem normalized_threshold_exact10 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (f : ℤ) :
    Nat.ceil (JSP000334.qThreshold p Q (normalizedFinite10 p Q f)) = (-f).toNat := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have he : JSP000334.qThreshold p Q (normalizedFinite10 p Q f) = ((-f : ℤ) : ℝ) := by
    unfold JSP000334.qThreshold normalizedFinite10
    push_cast
    field_simp [(Real.log_pos hQ).ne',(Real.log_pos hpR).ne']
    ring
  rw [he,Nat.ceil_intCast]

theorem normalized_lattice_exact10 (p : ℕ) [Fact p.Prime] (hp : 1 < p)
    (A : Matrix (Fin 10) (Fin 10) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (f : Fin 10 → ℤ) (hf : ∀ i, f i ≤ 0) (x : Fin 10 → ℤ) :
    x ∈ lattice10 p A (fun i => Nat.ceil
      (JSP000334.qThreshold p Q (normalizedFinite10 p Q (f i)))) ↔
      ∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ (p : ℚ)^(f i) := by
  rw [lattice10_spec]
  simp_rw [normalized_threshold_exact10 p hp Q hQ _,
    Int.toNat_of_nonneg (neg_nonneg.mpr (hf _)),neg_neg]

theorem normalized_balance10 (Q : ℝ) (A : Fin 10 → ℝ)
    (hA : ∀ i, 0 < A i) (f2 f3 : Fin 10 → ℤ)
    (hb : (∏ i, A i*(2 : ℝ)^(f2 i)*(3 : ℝ)^(f3 i)) = 1) :
    (∑ i, (normalizedWidth10 Q (A i)+normalizedFinite10 2 Q (f2 i)+
      normalizedFinite10 3 Q (f3 i))) = 0 := by
  have hpos (i : Fin 10) : 0 < A i*(2 : ℝ)^(f2 i)*(3 : ℝ)^(f3 i) :=
    mul_pos (mul_pos (hA i) (by positivity)) (by positivity)
  have h := congrArg Real.log hb
  rw [Real.log_prod _ _ (fun i _ => (hpos i).ne'),Real.log_one] at h
  have he (i : Fin 10) : Real.log (A i*(2 : ℝ)^(f2 i)*(3 : ℝ)^(f3 i)) =
      Real.log (A i)+(f2 i : ℝ)*Real.log 2+(f3 i : ℝ)*Real.log 3 := by
    rw [Real.log_mul (mul_pos (hA i) (by positivity)).ne' (by positivity : (3 : ℝ)^f3 i ≠ 0),
      Real.log_mul (hA i).ne' (by positivity : (2 : ℝ)^f2 i ≠ 0),Real.log_zpow,Real.log_zpow]
  simp_rw [he] at h
  simp only [normalizedWidth10,normalizedFinite10,← add_div,← Finset.sum_div,Nat.cast_ofNat,h,zero_div]

theorem normalized_finite_bounds10 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (f : ℤ) (hf : f ≤ 0) (hsize : (p : ℝ)^(-f) < Q) :
    -1 < normalizedFinite10 p Q f ∧ normalizedFinite10 p Q f ≤ 0 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (p : ℝ)^(-f)) hsize
  rw [Real.log_zpow,Int.cast_neg] at hlog
  have hfR : (f : ℝ) ≤ 0 := by exact_mod_cast hf
  constructor
  · apply (lt_div_iff₀ (Real.log_pos hQ)).mpr
    linarith
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hfR (Real.log_pos hpR).le) (Real.log_pos hQ).le

theorem normalized_source_group_exact10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (f2 f3 : Fin 10 → ℤ) (hf2 : ∀ i, f2 i ≤ 0) (hf3 : ∀ i, f3 i ≤ 0)
    (x : Fin 10 → ℤ) :
    x ∈ originalSourceGroup10 A2 A3 Q
      (fun i => normalizedFinite10 2 Q (f2 i)) (fun i => normalizedFinite10 3 Q (f3 i)) ↔
      (∀ i, padicNorm 2 ((A2 *ᵥ (fun j => (x j : ℚ))) i) ≤ (2 : ℚ)^(f2 i)) ∧
      (∀ i, padicNorm 3 ((A3 *ᵥ (fun j => (x j : ℚ))) i) ≤ (3 : ℚ)^(f3 i)) := by
  change (x ∈ lattice10 2 A2 _ ∧ x ∈ lattice10 3 A3 _) ↔ _
  rw [normalized_lattice_exact10 2 (by decide) A2 Q hQ f2 hf2,
    normalized_lattice_exact10 3 (by decide) A3 Q hQ f3 hf3]
  norm_num only [Nat.cast_ofNat]

end
end CompoundFeasibility.SourceOriginalVariable10
