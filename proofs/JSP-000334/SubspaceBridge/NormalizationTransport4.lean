import SubspaceBridge.DetNormalization4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.NormalizationTransport4
open DetNormalization4 OriginalVariableGap4
noncomputable section

theorem common_integer4 (lambda2 lambda3 : Fin 4 → ℚ) :
    ∃ m : ℤ, m ≠ 0 ∧
      (∀ i, ∃ z : ℤ, (m : ℚ)*lambda2 i = z) ∧
      (∀ i, ∃ z : ℤ, (m : ℚ)*lambda3 i = z) := by
  obtain ⟨m,hm⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun s : Bool × Fin 4 => if s.1 then lambda2 s.2 else lambda3 s.2)
  refine ⟨m.val,mem_nonZeroDivisors_iff_ne_zero.mp m.property,?_,?_⟩
  · intro i
    obtain ⟨z,hz⟩ := hm (true,i)
    exact ⟨z,by simpa using hz.symm⟩
  · intro i
    obtain ⟨z,hz⟩ := hm (false,i)
    exact ⟨z,by simpa using hz.symm⟩

theorem integer_padic_bound4 (p : ℕ) [Fact p.Prime] (a q : ℚ)
    (ha : ∃ z : ℤ, a = z) (R : ℝ) (hq : (padicNorm p q : ℝ) ≤ R) :
    (padicNorm p (a*q) : ℝ) ≤ R := by
  obtain ⟨z,rfl⟩ := ha
  rw [padicNorm.mul,Rat.cast_mul]
  have hz : (padicNorm p (z : ℚ) : ℝ) ≤ 1 := by exact_mod_cast padicNorm.of_int (p := p) z
  have hpos : 0 ≤ (padicNorm p q : ℝ) := by exact_mod_cast padicNorm.nonneg (p := p) q
  exact (mul_le_of_le_one_left hpos hz).trans hq

theorem normalizedDet4_integer_mulVec {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (m : ℤ) (x : Fin 4 → ℤ) (i : Fin 4) :
    (normalizedDet4 A *ᵥ (fun j => ((m*x j : ℤ) : K))) i =
      ((m : K)*detRowMultiplier4 A i) * (A *ᵥ (fun j => (x j : K))) i := by
  rw [normalizedDet4_mulVec]
  simp only [Matrix.mulVec,dotProduct,Int.cast_mul]
  simp_rw [mul_left_comm (A i _) (m : K)]
  rw [← Finset.mul_sum]
  ring

theorem real_multiplier_bound4 (L : Matrix (Fin 4) (Fin 4) ℝ) (m : ℤ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, |(m : ℝ)*detRowMultiplier4 L i| ≤ M := by
  refine ⟨1+∑ i, |(m : ℝ)*detRowMultiplier4 L i|,by positivity,?_⟩
  intro i
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    abs_nonneg ((m : ℝ)*detRowMultiplier4 L j)) (Finset.mem_univ i)
  linarith

theorem real_slack_cutoff4 (M epsilon : ℝ) (he : 0 < epsilon) :
    ∃ B : ℝ, 1 < B ∧ ∀ Q : ℝ, B < Q → M ≤ Q^(epsilon/2) := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (half_pos he)).eventually (Filter.eventually_ge_atTop M))
  refine ⟨max B 2,lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _),?_⟩
  intro Q hQ
  exact hB Q ((le_max_left B 2).trans hQ.le)


theorem source_solution_normalized4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (m : ℤ) (hm : m ≠ 0)
    (h₂ : ∀ i, ∃ z : ℤ, (m : ℚ)*detRowMultiplier4 A₂ i = z)
    (h₃ : ∀ i, ∃ z : ℤ, (m : ℚ)*detRowMultiplier4 A₃ i = z)
    (Q epsilon : ℝ) (x : Fin 4 → ℤ)
    (hscale : ∀ i, |(m : ℝ)*detRowMultiplier4 L i| ≤ Q^(epsilon/2))
    (hs : originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x) :
    originalSourceSolution4 (normalizedDet4 A₂) (normalizedDet4 A₃) (normalizedDet4 L)
      c₀ c₂ c₃ Q (epsilon/2) (m • x) := by
  have hy : m • x ≠ 0 := by
    intro hz
    apply hs.1
    ext i
    have hi : m*x i = 0 := by simpa only [Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using congrFun hz i
    exact (mul_eq_zero.mp hi).resolve_left hm
  refine ⟨hy,hs.2.1,half_pos hs.2.2.1,?_,?_,?_⟩
  · intro i
    change |(normalizedDet4 L *ᵥ (fun j => ((m*x j : ℤ) : ℝ))) i| ≤ _
    rw [normalizedDet4_integer_mulVec,abs_mul]
    have hi : |(L *ᵥ (fun j => (x j : ℝ))) i| ≤ Q^(c₀ i-epsilon) := hs.2.2.2.1 i
    calc
      |(m : ℝ)*detRowMultiplier4 L i| * |(L *ᵥ (fun j => (x j : ℝ))) i| ≤
          Q^(epsilon/2)*Q^(c₀ i-epsilon) :=
        mul_le_mul (hscale i) hi (abs_nonneg _) (Real.rpow_nonneg (by linarith [hs.2.1]) _)
      _ = Q^(c₀ i-epsilon/2) := by
        rw [← Real.rpow_add (by linarith [hs.2.1] : 0 < Q)]
        congr 1
        ring
  · intro i
    change (padicNorm 2 ((normalizedDet4 A₂ *ᵥ (fun j => ((m*x j : ℤ) : ℚ))) i) : ℝ) ≤ _
    rw [normalizedDet4_integer_mulVec]
    exact integer_padic_bound4 2 _ _ (h₂ i) _ (hs.2.2.2.2.1 i)
  · intro i
    change (padicNorm 3 ((normalizedDet4 A₃ *ᵥ (fun j => ((m*x j : ℤ) : ℚ))) i) : ℝ) ≤ _
    rw [normalizedDet4_integer_mulVec]
    exact integer_padic_bound4 3 _ _ (h₃ i) _ (hs.2.2.2.2.2 i)

theorem originalRothProperty4_of_normalized (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hR : originalRothProperty4 (normalizedDet4 A₂) (normalizedDet4 A₃)
      (normalizedDet4 L) c₀ c₂ c₃) :
    originalRothProperty4 A₂ A₃ L c₀ c₂ c₃ := by
  obtain ⟨m,hm,hm₂,hm₃⟩ := common_integer4 (detRowMultiplier4 A₂) (detRowMultiplier4 A₃)
  obtain ⟨M,hM,hbound⟩ := real_multiplier_bound4 L m
  intro delta hd
  obtain ⟨B₁,hB₁⟩ := hR (delta/2) (half_pos hd)
  obtain ⟨B₂,hB₂,hcut⟩ := real_slack_cutoff4 M delta hd
  refine ⟨max B₁ B₂,?_⟩
  intro Q hQ hsol
  obtain ⟨x,hx⟩ := hsol
  apply hB₁ Q ((le_max_left _ _).trans_lt hQ)
  refine ⟨m • x,source_solution_normalized4 A₂ A₃ L c₀ c₂ c₃ m hm hm₂ hm₃ Q delta x ?_ hx⟩
  intro i
  exact (hbound i).trans (hcut Q ((le_max_right _ _).trans_lt hQ))

end
end CompoundFeasibility.NormalizationTransport4
