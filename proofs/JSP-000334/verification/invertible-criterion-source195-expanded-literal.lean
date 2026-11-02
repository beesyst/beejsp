import SubspaceBridge.SourceCriterion4
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing

open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M195LiteralDetNormalization4
noncomputable section

def detRowMultiplier4 {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) : K :=
  if i = 0 then A.det⁻¹ else 1

def normalizedDet4 {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  A.updateRow 0 (A.det⁻¹ • A 0)

theorem detRowMultiplier4_ne_zero {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0) (i : Fin 4) :
    detRowMultiplier4 A i ≠ 0 := by
  simp only [detRowMultiplier4]
  split_ifs <;> simp [hA]

theorem normalizedDet4_det {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.det ≠ 0) :
    (normalizedDet4 A).det = 1 := by
  rw [normalizedDet4,Matrix.det_updateRow_smul,Matrix.updateRow_eq_self]
  exact inv_mul_cancel₀ hA

theorem normalizedDet4_apply {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    normalizedDet4 A i j = detRowMultiplier4 A i * A i j := by
  by_cases hi : i = 0
  · subst i
    simp [normalizedDet4,detRowMultiplier4]
  · simp [normalizedDet4,detRowMultiplier4,hi,Ne.symm hi]

theorem normalizedDet4_mulVec {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (x : Fin 4 → K) (i : Fin 4) :
    (normalizedDet4 A *ᵥ x) i = detRowMultiplier4 A i * (A *ᵥ x) i := by
  simp only [Matrix.mulVec, dotProduct,normalizedDet4_apply,mul_assoc,Finset.mul_sum]

theorem algebraic_det4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) : IsAlgebraic ℚ L.det := by
  rw [Matrix.det_apply]
  apply isAlgebraic_iff_isIntegral.mpr
  apply IsIntegral.sum
  intro s hs
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ]
  exact (IsIntegral.prod _ (fun i _ => (hAlg (s i) i).isIntegral)).smul _

theorem algebraic_inv_det4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) : IsAlgebraic ℚ L.det⁻¹ :=
  (algebraic_det4 L hAlg).inv

theorem normalizedDet4_algebraic (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ i j, IsAlgebraic ℚ (normalizedDet4 L i j) := by
  intro i j
  rw [normalizedDet4_apply]
  have hs : IsAlgebraic ℚ (detRowMultiplier4 L i) := by
    unfold detRowMultiplier4
    split_ifs
    · exact algebraic_inv_det4 L hAlg
    · exact isAlgebraic_one
  exact hs.mul (hAlg i j)

end
end CompoundFeasibility.M195LiteralDetNormalization4

open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M195LiteralRowScaleSelection4
open RestrictedGreedyRows4 RestrictedRows4 SelectedRestriction4 RestrictedWeightOrder4
noncomputable section

theorem rowPrefix4_span_scale {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rows rows' : Fin 4 → V) (lambda : Fin 4 → K) (hn : ∀ i, lambda i ≠ 0)
    (hr : ∀ i, rows' i = lambda i • rows i) (n : ℕ) :
    Submodule.span K (rowPrefix4 rows' n) = Submodule.span K (rowPrefix4 rows n) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    rw [hr i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    have h : rows' i ∈ Submodule.span K (rowPrefix4 rows' n) :=
      Submodule.subset_span ⟨i,hi,rfl⟩
    rw [hr i] at h
    exact (Submodule.smul_mem_iff _ (hn i)).mp h

theorem greedyPivot4_scale_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rows rows' : Fin 4 → V) (lambda : Fin 4 → K) (hn : ∀ i, lambda i ≠ 0)
    (hr : ∀ i, rows' i = lambda i • rows i) (i : Fin 4) :
    greedyPivot4 (K := K) rows' i ↔ greedyPivot4 (K := K) rows i := by
  unfold greedyPivot4
  rw [rowPrefix4_span_scale rows rows' lambda hn hr,hr i]
  exact not_congr (Submodule.smul_mem_iff _ (hn i))

theorem greedyFinset4_scale {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rows rows' : Fin 4 → V) (lambda : Fin 4 → K) (hn : ∀ i, lambda i ≠ 0)
    (hr : ∀ i, rows' i = lambda i • rows i) :
    greedyFinset4 (K := K) rows' = greedyFinset4 (K := K) rows := by
  ext i
  simp only [greedyFinset4,Finset.mem_filter,Finset.mem_univ,true_and]
  exact greedyPivot4_scale_iff rows rows' lambda hn hr i

theorem greedyIndex4_scale {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (rows rows' : Fin 4 → V) (lambda : Fin 4 → K)
    (hn : ∀ i, lambda i ≠ 0) (hr : ∀ i, rows' i = lambda i • rows i)
    (hf : Submodule.span K (Set.range rows) = ⊤)
    (hf' : Submodule.span K (Set.range rows') = ⊤)
    (d : ℕ) (hd : Module.finrank K V = d) :
    greedyIndex4 rows' hf' d hd = greedyIndex4 rows hf d hd := by
  have hs := greedyFinset4_scale rows rows' lambda hn hr
  simp only [greedyIndex4,hs]

theorem selectedIndex4_scale {K : Type*} [Field K] {d : ℕ}
    (M N : Matrix (Fin 4) (Fin d) K) (lambda : Fin 4 → K)
    (hn : ∀ i, lambda i ≠ 0) (hr : ∀ i, N i = lambda i • M i)
    (c : Fin 4 → ℝ) (hf : Submodule.span K (Set.range M.row) = ⊤)
    (hf' : Submodule.span K (Set.range N.row) = ⊤) :
    selectedIndex4 N c hf' = selectedIndex4 M c hf := by
  exact greedyIndex4_scale (sortedRows4 M c) (sortedRows4 N c)
    (fun i => lambda (weightOrder4 c i)) (fun i => hn _) (fun i => hr _)
    (sortedRows4_span M c hf) (sortedRows4_span N c hf') d (by simp)

theorem rowCoordinates4_normalized {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    rowCoordinates4 P b (M195LiteralDetNormalization4.normalizedDet4 A) i =
      M195LiteralDetNormalization4.detRowMultiplier4 A i • rowCoordinates4 P b A i := by
  ext k
  exact M195LiteralDetNormalization4.normalizedDet4_mulVec A (b k) i

end
end CompoundFeasibility.M195LiteralRowScaleSelection4

open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M195LiteralNormalizationTransport4
open M195LiteralDetNormalization4 OriginalVariableGap4
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
end CompoundFeasibility.M195LiteralNormalizationTransport4

open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M195LiteralInvertibleExponent4
open M195LiteralDetNormalization4 M195LiteralRowScaleSelection4 SelectedRestriction4 RestrictedRows4 RestrictedWeightOrder4
noncomputable section

theorem matrixUnit4 {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : A.det ≠ 0) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)

theorem rationalRestriction_span4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det ≠ 0) :
    Submodule.span ℚ (Set.range (rationalRowCoordinates4 P A).row) = ⊤ :=
  rowCoordinates4_span P _ A (matrixUnit4 A hA)

theorem realRestriction_span4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det ≠ 0) :
    Submodule.span ℝ (Set.range (realRestrictionCoordinates4 P hP L).row) = ⊤ :=
  rowCoordinates4_span _ _ L (matrixUnit4 L hL)

def invertibleSelectedExponent4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (c₀ c₂ c₃ : Fin 4 → ℝ) : ℝ :=
  (∑ k : Fin (Module.finrank ℚ P), c₀ (weightOrder4 c₀
    (selectedIndex4 (realRestrictionCoordinates4 P hP L) c₀ (realRestriction_span4 P hP L hL) k))) +
  (∑ k : Fin (Module.finrank ℚ P), c₂ (weightOrder4 c₂
    (selectedIndex4 (rationalRowCoordinates4 P A₂) c₂ (rationalRestriction_span4 P A₂ h₂) k))) +
  (∑ k : Fin (Module.finrank ℚ P), c₃ (weightOrder4 c₃
    (selectedIndex4 (rationalRowCoordinates4 P A₃) c₃ (rationalRestriction_span4 P A₃ h₃) k)))

theorem invertibleSelectedExponent4_eq_source (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) :
    invertibleSelectedExponent4 P hP A₂ A₃ L (by rw [h₂];norm_num)
      (by rw [h₃];norm_num) (by rw [hL];norm_num) c₀ c₂ c₃ =
      sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ := rfl

theorem invertibleSelectedExponent4_normalized (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (c₀ c₂ c₃ : Fin 4 → ℝ) :
    invertibleSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ =
      sourceSelectedExponent4 P hP (normalizedDet4 A₂) (normalizedDet4 A₃) (normalizedDet4 L)
        (normalizedDet4_det A₂ h₂) (normalizedDet4_det A₃ h₃) (normalizedDet4_det L hL)
        c₀ c₂ c₃ := by
  have e₀ := selectedIndex4_scale (realRestrictionCoordinates4 P hP L)
    (realRestrictionCoordinates4 P hP (normalizedDet4 L)) (detRowMultiplier4 L)
    (detRowMultiplier4_ne_zero L hL)
    (rowCoordinates4_normalized _ _ L) c₀ (realRestriction_span4 P hP L hL)
    (realRestrictionCoordinates4_span P hP (normalizedDet4 L) (normalizedDet4_det L hL))
  have e₂ := selectedIndex4_scale (rationalRowCoordinates4 P A₂)
    (rationalRowCoordinates4 P (normalizedDet4 A₂)) (detRowMultiplier4 A₂)
    (detRowMultiplier4_ne_zero A₂ h₂)
    (rowCoordinates4_normalized _ _ A₂) c₂ (rationalRestriction_span4 P A₂ h₂)
    (rationalRowCoordinates4_span P (normalizedDet4 A₂) (normalizedDet4_det A₂ h₂))
  have e₃ := selectedIndex4_scale (rationalRowCoordinates4 P A₃)
    (rationalRowCoordinates4 P (normalizedDet4 A₃)) (detRowMultiplier4 A₃)
    (detRowMultiplier4_ne_zero A₃ h₃)
    (rowCoordinates4_normalized _ _ A₃) c₃ (rationalRestriction_span4 P A₃ h₃)
    (rationalRowCoordinates4_span P (normalizedDet4 A₃) (normalizedDet4_det A₃ h₃))
  unfold invertibleSelectedExponent4 sourceSelectedExponent4
  rw [e₀,e₂,e₃]

end
end CompoundFeasibility.M195LiteralInvertibleExponent4

open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M195LiteralInvertibleCriterion4
open M195LiteralDetNormalization4 M195LiteralInvertibleExponent4 SourceCriterion4 M195LiteralNormalizationTransport4
noncomputable section

def sourceInvertibleNonpositiveCriterion4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (c₀ c₂ c₃ : Fin 4 → ℝ) : Prop :=
  ∀ P : Submodule ℚ (Fin 4 → ℚ), 1 ≤ Module.finrank ℚ P →
    ∀ hP : Module.finrank ℚ P ≤ 3,
      invertibleSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ ≤ 0

theorem sourceInvertibleNonpositiveCriterion4_iff_normalized
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    sourceInvertibleNonpositiveCriterion4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ ↔
      sourceNonpositiveCriterion4 (normalizedDet4 A₂) (normalizedDet4 A₃) (normalizedDet4 L)
        (normalizedDet4_det A₂ h₂) (normalizedDet4_det A₃ h₃) (normalizedDet4_det L hL)
        c₀ c₂ c₃ := by
  unfold sourceInvertibleNonpositiveCriterion4 sourceNonpositiveCriterion4
  simp_rw [invertibleSelectedExponent4_normalized]

theorem source_invertible_fin4_criterion_implies_roth4
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hCriterion : sourceInvertibleNonpositiveCriterion4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) :
    OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃ := by
  have hn := source_fin4_criterion_implies_roth4 (normalizedDet4 A₂) (normalizedDet4 A₃)
    (normalizedDet4 L) (normalizedDet4_det A₂ h₂) (normalizedDet4_det A₃ h₃)
    (normalizedDet4_det L hL) (normalizedDet4_algebraic L hAlg) c₀ c₂ c₃ hc₂ hc₃ hb
    ((sourceInvertibleNonpositiveCriterion4_iff_normalized A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃).mp hCriterion)
  exact originalRothProperty4_of_normalized A₂ A₃ L c₀ c₂ c₃ hn

end
end CompoundFeasibility.M195LiteralInvertibleCriterion4

namespace CompoundFeasibility.M195LiteralInvertibleCriterion4
open SelectedRestriction4 RestrictedRows4 RestrictedWeightOrder4 M195LiteralInvertibleExponent4
theorem literal_source_contract
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det ≠ 0) (h₃ : A₃.det ≠ 0) (hL : L.det ≠ 0)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hCriterion : ∀ P : Submodule ℚ (Fin 4 → ℚ), 1 ≤ Module.finrank ℚ P → ∀ hP : Module.finrank ℚ P ≤ 3,
      (∑ k : Fin (Module.finrank ℚ P), c₀ (weightOrder4 c₀
    (selectedIndex4 (realRestrictionCoordinates4 P hP L) c₀ (realRestriction_span4 P hP L hL) k))) +
  (∑ k : Fin (Module.finrank ℚ P), c₂ (weightOrder4 c₂
    (selectedIndex4 (rationalRowCoordinates4 P A₂) c₂ (rationalRestriction_span4 P A₂ h₂) k))) +
  (∑ k : Fin (Module.finrank ℚ P), c₃ (weightOrder4 c₃
    (selectedIndex4 (rationalRowCoordinates4 P A₃) c₃ (rationalRestriction_span4 P A₃ h₃) k))) ≤ 0) :
    ∀ delta : ℝ, 0 < delta → ∃ B : ℝ, ∀ Q : ℝ, B < Q → ¬ ∃ x : Fin 4 → ℤ, x ≠ 0 ∧ 1 < Q ∧ 0 < delta ∧ (∀ i, |(L *ᵥ integerReal x) i| ≤ Q^(c₀ i-delta)) ∧ (∀ i, (padicNorm 2 ((A₂ *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c₂ i)) ∧ (∀ i, (padicNorm 3 ((A₃ *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c₃ i)) := by
  exact source_invertible_fin4_criterion_implies_roth4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb hCriterion
end CompoundFeasibility.M195LiteralInvertibleCriterion4

#check CompoundFeasibility.M195LiteralDetNormalization4.detRowMultiplier4
#print CompoundFeasibility.M195LiteralDetNormalization4.detRowMultiplier4
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.detRowMultiplier4

#check CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4
#print CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4

#check CompoundFeasibility.M195LiteralDetNormalization4.detRowMultiplier4_ne_zero
#print CompoundFeasibility.M195LiteralDetNormalization4.detRowMultiplier4_ne_zero
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.detRowMultiplier4_ne_zero

#check CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_det
#print CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_det
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_det

#check CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_apply
#print CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_apply
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_apply

#check CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_mulVec
#print CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_mulVec
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_mulVec

#check CompoundFeasibility.M195LiteralDetNormalization4.algebraic_det4
#print CompoundFeasibility.M195LiteralDetNormalization4.algebraic_det4
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.algebraic_det4

#check CompoundFeasibility.M195LiteralDetNormalization4.algebraic_inv_det4
#print CompoundFeasibility.M195LiteralDetNormalization4.algebraic_inv_det4
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.algebraic_inv_det4

#check CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_algebraic
#print CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_algebraic
#print axioms CompoundFeasibility.M195LiteralDetNormalization4.normalizedDet4_algebraic

#check CompoundFeasibility.M195LiteralRowScaleSelection4.rowPrefix4_span_scale
#print CompoundFeasibility.M195LiteralRowScaleSelection4.rowPrefix4_span_scale
#print axioms CompoundFeasibility.M195LiteralRowScaleSelection4.rowPrefix4_span_scale

#check CompoundFeasibility.M195LiteralRowScaleSelection4.greedyPivot4_scale_iff
#print CompoundFeasibility.M195LiteralRowScaleSelection4.greedyPivot4_scale_iff
#print axioms CompoundFeasibility.M195LiteralRowScaleSelection4.greedyPivot4_scale_iff

#check CompoundFeasibility.M195LiteralRowScaleSelection4.greedyFinset4_scale
#print CompoundFeasibility.M195LiteralRowScaleSelection4.greedyFinset4_scale
#print axioms CompoundFeasibility.M195LiteralRowScaleSelection4.greedyFinset4_scale

#check CompoundFeasibility.M195LiteralRowScaleSelection4.greedyIndex4_scale
#print CompoundFeasibility.M195LiteralRowScaleSelection4.greedyIndex4_scale
#print axioms CompoundFeasibility.M195LiteralRowScaleSelection4.greedyIndex4_scale

#check CompoundFeasibility.M195LiteralRowScaleSelection4.selectedIndex4_scale
#print CompoundFeasibility.M195LiteralRowScaleSelection4.selectedIndex4_scale
#print axioms CompoundFeasibility.M195LiteralRowScaleSelection4.selectedIndex4_scale

#check CompoundFeasibility.M195LiteralRowScaleSelection4.rowCoordinates4_normalized
#print CompoundFeasibility.M195LiteralRowScaleSelection4.rowCoordinates4_normalized
#print axioms CompoundFeasibility.M195LiteralRowScaleSelection4.rowCoordinates4_normalized

#check CompoundFeasibility.M195LiteralNormalizationTransport4.common_integer4
#print CompoundFeasibility.M195LiteralNormalizationTransport4.common_integer4
#print axioms CompoundFeasibility.M195LiteralNormalizationTransport4.common_integer4

#check CompoundFeasibility.M195LiteralNormalizationTransport4.integer_padic_bound4
#print CompoundFeasibility.M195LiteralNormalizationTransport4.integer_padic_bound4
#print axioms CompoundFeasibility.M195LiteralNormalizationTransport4.integer_padic_bound4

#check CompoundFeasibility.M195LiteralNormalizationTransport4.normalizedDet4_integer_mulVec
#print CompoundFeasibility.M195LiteralNormalizationTransport4.normalizedDet4_integer_mulVec
#print axioms CompoundFeasibility.M195LiteralNormalizationTransport4.normalizedDet4_integer_mulVec

#check CompoundFeasibility.M195LiteralNormalizationTransport4.real_multiplier_bound4
#print CompoundFeasibility.M195LiteralNormalizationTransport4.real_multiplier_bound4
#print axioms CompoundFeasibility.M195LiteralNormalizationTransport4.real_multiplier_bound4

#check CompoundFeasibility.M195LiteralNormalizationTransport4.real_slack_cutoff4
#print CompoundFeasibility.M195LiteralNormalizationTransport4.real_slack_cutoff4
#print axioms CompoundFeasibility.M195LiteralNormalizationTransport4.real_slack_cutoff4

#check CompoundFeasibility.M195LiteralNormalizationTransport4.source_solution_normalized4
#print CompoundFeasibility.M195LiteralNormalizationTransport4.source_solution_normalized4
#print axioms CompoundFeasibility.M195LiteralNormalizationTransport4.source_solution_normalized4

#check CompoundFeasibility.M195LiteralNormalizationTransport4.originalRothProperty4_of_normalized
#print CompoundFeasibility.M195LiteralNormalizationTransport4.originalRothProperty4_of_normalized
#print axioms CompoundFeasibility.M195LiteralNormalizationTransport4.originalRothProperty4_of_normalized

#check CompoundFeasibility.M195LiteralInvertibleExponent4.matrixUnit4
#print CompoundFeasibility.M195LiteralInvertibleExponent4.matrixUnit4
#print axioms CompoundFeasibility.M195LiteralInvertibleExponent4.matrixUnit4

#check CompoundFeasibility.M195LiteralInvertibleExponent4.rationalRestriction_span4
#print CompoundFeasibility.M195LiteralInvertibleExponent4.rationalRestriction_span4
#print axioms CompoundFeasibility.M195LiteralInvertibleExponent4.rationalRestriction_span4

#check CompoundFeasibility.M195LiteralInvertibleExponent4.realRestriction_span4
#print CompoundFeasibility.M195LiteralInvertibleExponent4.realRestriction_span4
#print axioms CompoundFeasibility.M195LiteralInvertibleExponent4.realRestriction_span4

#check CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4
#print CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4
#print axioms CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4

#check CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4_eq_source
#print CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4_eq_source
#print axioms CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4_eq_source

#check CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4_normalized
#print CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4_normalized
#print axioms CompoundFeasibility.M195LiteralInvertibleExponent4.invertibleSelectedExponent4_normalized

#check CompoundFeasibility.M195LiteralInvertibleCriterion4.sourceInvertibleNonpositiveCriterion4
#print CompoundFeasibility.M195LiteralInvertibleCriterion4.sourceInvertibleNonpositiveCriterion4
#print axioms CompoundFeasibility.M195LiteralInvertibleCriterion4.sourceInvertibleNonpositiveCriterion4

#check CompoundFeasibility.M195LiteralInvertibleCriterion4.sourceInvertibleNonpositiveCriterion4_iff_normalized
#print CompoundFeasibility.M195LiteralInvertibleCriterion4.sourceInvertibleNonpositiveCriterion4_iff_normalized
#print axioms CompoundFeasibility.M195LiteralInvertibleCriterion4.sourceInvertibleNonpositiveCriterion4_iff_normalized

#check CompoundFeasibility.M195LiteralInvertibleCriterion4.source_invertible_fin4_criterion_implies_roth4
#print CompoundFeasibility.M195LiteralInvertibleCriterion4.source_invertible_fin4_criterion_implies_roth4
#print axioms CompoundFeasibility.M195LiteralInvertibleCriterion4.source_invertible_fin4_criterion_implies_roth4

#check CompoundFeasibility.M195LiteralInvertibleCriterion4.literal_source_contract
#print axioms CompoundFeasibility.M195LiteralInvertibleCriterion4.literal_source_contract
