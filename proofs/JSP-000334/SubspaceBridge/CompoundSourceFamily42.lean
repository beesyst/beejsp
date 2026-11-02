import SubspaceBridge.CompoundDualLine42
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Block
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

def pairWeights42 (c : Fin 4 → ℝ) : Fin 6 → ℝ := fun s => c (lo s) + c (hi s)

theorem pairWeights42_sum (c : Fin 4 → ℝ) :
    ∑ s, pairWeights42 c s = 3 * ∑ i, c i := by
  simp [pairWeights42,lo,hi,Fin.sum_univ_succ]
  ring

theorem pairWeights42_bounds (c₀ c₂ c₃ : Fin 4 → ℝ)
    (h₀ : ∀ i, |c₀ i| ≤ 1) (h₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0)
    (h₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) :
    (∀ s, |pairWeights42 c₀ s| ≤ 2) ∧
    (∀ s, -2 ≤ pairWeights42 c₂ s ∧ pairWeights42 c₂ s ≤ 0) ∧
    (∀ s, -2 ≤ pairWeights42 c₃ s ∧ pairWeights42 c₃ s ≤ 0) := by
  refine ⟨fun s => (abs_add _ _).trans ?_,?_,?_⟩
  · linarith [h₀ (lo s),h₀ (hi s)]
  · intro s
    dsimp [pairWeights42]
    constructor <;> linarith [(h₂ (lo s)).1,(h₂ (hi s)).1,(h₂ (lo s)).2,(h₂ (hi s)).2]
  · intro s
    dsimp [pairWeights42]
    constructor <;> linarith [(h₃ (lo s)).1,(h₃ (hi s)).1,(h₃ (lo s)).2,(h₃ (hi s)).2]

theorem pairWeights42_balance (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∑ s, (pairWeights42 c₀ s + pairWeights42 c₂ s + pairWeights42 c₃ s) = 0 := by
  calc
    _ = ∑ s, pairWeights42 (fun i => c₀ i + c₂ i + c₃ i) s := by
      apply Finset.sum_congr rfl
      intro s _
      dsimp [pairWeights42]
      ring
    _ = 3 * ∑ i, (c₀ i + c₂ i + c₃ i) := pairWeights42_sum _
    _ = 0 := by rw [hb,mul_zero]

theorem compound42_algebraic (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ s t, IsAlgebraic ℚ (compound L s t) := by
  intro s t
  exact ((hL _ _).mul (hL _ _)).sub ((hL _ _).mul (hL _ _))

theorem compound42_map {K : Type*} [Field K] [Algebra ℚ K]
    (A : Matrix (Fin 4) (Fin 4) ℚ) :
    compound (A.map (algebraMap ℚ K)) = (compound A).map (algebraMap ℚ K) := by
  ext s t
  simp only [compound,Matrix.map_apply,map_sub,map_mul]

theorem compound42_local_algebraic {K : Type*} [Field K] [Algebra ℚ K]
    (A : Matrix (Fin 4) (Fin 4) ℚ) :
    ∀ s t, IsAlgebraic ℚ (compound (A.map (algebraMap ℚ K)) s t) := by
  intro s t
  rw [compound42_map]
  exact isAlgebraic_algebraMap _

theorem compound42_source_body (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) (r : ℝ) :
    coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) x ≤ r ↔
      ∀ s, |(compound L *ᵥ x) s| ≤ r * Q ^ pairWeights42 c₀ s := by
  change ‖compoundCoordinates42 L hL Q hQ c₀ x‖ ≤ r ↔ _
  rw [compoundCoordinates42_bounds]
  simp only [pairWeights42,Real.rpow_add (lt_trans zero_lt_one hQ),mul_assoc]

theorem compound42_source_lattice (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (z : Fin 6 → ℤ) :
    z ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃ ↔
      (∀ s, (padicNorm 2 ((compound A₂ *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤
        Q ^ pairWeights42 c₂ s) ∧
      (∀ s, (padicNorm 3 ((compound A₃ *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤
        Q ^ pairWeights42 c₃ s) :=
  directCompoundGroup42_raw A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z


theorem sourceUnit42 {K : Type*} [Field K] (M : Matrix (Fin 4) (Fin 4) K)
    (h : M.det = 1) : IsUnit M := by
  apply (Matrix.isUnit_iff_isUnit_det M).mpr
  rw [h]
  exact isUnit_one

theorem source_compound_unbounded_family42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    (∀ s t, IsAlgebraic ℚ (compound L s t)) ∧
    IsUnit (compound A₂) ∧ IsUnit (compound A₃) ∧ IsUnit (compound L) ∧
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s, |pairWeights42 c₀ s| ≤ 2) ∧
        (∀ s, -2 ≤ pairWeights42 c₂ s ∧ pairWeights42 c₂ s ≤ 0) ∧
        (∀ s, -2 ≤ pairWeights42 c₃ s ∧ pairWeights42 c₃ s ≤ 0) ∧
        (∑ s, (pairWeights42 c₀ s + pairWeights42 c₂ s + pairWeights42 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hUb : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hmem : Q ∈ U),
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 1 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 2 * Q ^ (-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧
            ∃ (u : (t : V) → Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃)
              (v : (t : V) → Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃),
              ∀ t : V, T < t.val ∧
                sourceHyperplane42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property))
                  c₀ c₂ c₃ κ (u t) (v t) ∧
                rationalDualLine42 (fun i => (u t i : Fin 4 → ℤ)) (fun j => (v t j : Fin 6 → ℤ))
                  (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃) ∧
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 4 <
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 5 *
                  t.val ^ (-delta / 2) := by
  classical
  have h₂u := sourceUnit42 A₂ h₂
  have h₃u := sourceUnit42 A₃ h₃
  have hLu := sourceUnit42 L hL
  obtain ⟨κ,T₁,hk,hT₁,hcut,hdual⟩ := source_uniform_dual_line42 A₂ A₃ L h₂u h₃u hLu delta hd
  obtain ⟨_,T₂,_,hT₂,_,hgap⟩ := source_uniform_direct_gap42 A₂ A₃ L h₂u h₃u hLu delta hd
  let T := max T₁ T₂
  refine ⟨compound42_algebraic L hAlg,compound_unit A₂ h₂u,compound_unit A₃ h₃u,
    compound_unit L hLu,κ,T,hk,hT₁.trans_le (le_max_left _ _),?_,?_⟩
  · intro Q hTQ
    exact hcut Q ((le_max_left _ _).trans_lt hTQ)
  · intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
    obtain ⟨hb₀,hb₂,hb₃⟩ := pairWeights42_bounds c₀ c₂ c₃ hc₀ hc₂ hc₃
    refine ⟨hb₀,hb₂,hb₃,pairWeights42_balance c₀ c₂ c₃ hb,?_⟩
    intro U hUb hQU horiginal
    let V := {Q : ℝ | Q ∈ U ∧ T < Q}
    have hVU : V ⊆ U := fun _ h => h.1
    have hVb : ¬ BddAbove V := JSP000334.sourceDual_unbounded_tail3 U hUb T
    have spec (t : V) :
        ∃ (u : Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃)
          (v : Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃),
          sourceHyperplane42 A₂ A₃ L hLu t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ κ u v ∧
          rationalDualLine42 (fun i => (u i : Fin 4 → ℤ)) (fun j => (v j : Fin 6 → ℤ))
            (sourceMinima4 A₂ A₃ L hLu t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃) :=
      hdual t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ (fun i => (hc₂ i).2) (fun i => (hc₃ i).2)
        hb ((le_max_left _ _).trans_lt t.property.2) (horiginal t.val (hVU t.property))
    choose u v huv using spec
    refine ⟨V,hVU,hVb,u,v,?_⟩
    intro t
    refine ⟨t.property.2,(huv t).1,(huv t).2,?_⟩
    exact (hgap t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ (fun i => (hc₂ i).2)
      (fun i => (hc₃ i).2) hb ((le_max_right _ _).trans_lt t.property.2)
      (horiginal t.val (hVU t.property))).2


theorem pair_indices42 : ∀ s : Fin 6, lo s < hi s := by decide

theorem pair_order42 : ∀ s t : Fin 6, t < s →
    (lo t < lo s ∨ hi t < hi s) ∧ lo t < hi s := by decide

theorem compound42_upper {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : A.BlockTriangular id) : (compound A).BlockTriangular id := by
  intro s t h
  obtain ⟨hor,hcross⟩ := pair_order42 s t h
  change A (lo s) (lo t) * A (hi s) (hi t) - A (lo s) (hi t) * A (hi s) (lo t) = 0
  have hzero : A (hi s) (lo t) = 0 := hA hcross
  rw [hzero,mul_zero,sub_zero]
  rcases hor with hleft | hright
  · have hz : A (lo s) (lo t) = 0 := hA hleft
    rw [hz,zero_mul]
  · have hz : A (hi s) (hi t) = 0 := hA hright
    rw [hz,mul_zero]

theorem compound42_upper_det {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : A.BlockTriangular id) : (compound A).det = A.det ^ (3 : ℕ) := by
  rw [Matrix.det_of_upperTriangular (compound42_upper A hA),Matrix.det_of_upperTriangular hA]
  have he (s : Fin 6) : compound A s s = A (lo s) (lo s) * A (hi s) (hi s) := by
    have hz : A (hi s) (lo s) = 0 := hA (pair_indices42 s)
    simp only [compound,hz,mul_zero,sub_zero]
  simp_rw [he]
  simp [lo,hi,Fin.prod_univ_succ]
  ring

theorem compound42_transpose {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K) :
    compound A.transpose = (compound A).transpose := by
  ext s t
  simp only [compound,Matrix.transpose_apply]
  ring

theorem compound42_transvection_det {K : Type*} [Field K] (i j : Fin 4)
    (hij : i ≠ j) (c : K) : (compound (Matrix.transvection i j c)).det = 1 := by
  have upper (a b : Fin 4) (hab : a < b) :
      (Matrix.transvection a b c : Matrix (Fin 4) (Fin 4) K).BlockTriangular id := by
    intro s t hts
    have hne : s ≠ t := ne_of_gt hts
    have hentry : ¬ (a = s ∧ b = t) := by
      rintro ⟨rfl,rfl⟩
      exact (not_lt_of_ge hab.le) hts
    simp [Matrix.transvection,Matrix.stdBasisMatrix,Matrix.one_apply,hne,hentry]
  by_cases h : i < j
  · rw [compound42_upper_det _ (upper i j h),Matrix.det_transvection_of_ne _ _ hij,one_pow]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)
    have ht : (Matrix.transvection j i c : Matrix (Fin 4) (Fin 4) K).transpose =
        Matrix.transvection i j c := by
      simp [Matrix.transvection,Matrix.transpose_add,Matrix.transpose_stdBasisMatrix]
    rw [← ht,compound42_transpose,Matrix.det_transpose,
      compound42_upper_det _ (upper j i hji),Matrix.det_transvection_of_ne _ _ (Ne.symm hij),one_pow]

private def compoundDet42Property {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) : Prop :=
  (compound A).det = A.det ^ (3 : ℕ)

attribute [local irreducible] compoundDet42Property

private theorem compoundDet42Property_diagonal {K : Type*} [Field K] (D : Fin 4 → K) :
    compoundDet42Property (Matrix.diagonal D) := by
  unfold compoundDet42Property
  exact compound42_upper_det (Matrix.diagonal D) (Matrix.blockTriangular_diagonal D)

private theorem compoundDet42Property_transvection {K : Type*} [Field K]
    (t : Matrix.TransvectionStruct (Fin 4) K) : compoundDet42Property t.toMatrix := by
  unfold compoundDet42Property
  have hc := @compound42_transvection_det K _ t.i t.j t.hij t.c
  rw [t.det, one_pow]
  simpa only [Matrix.TransvectionStruct.toMatrix] using hc

private theorem compoundDet42Property_mul {K : Type*} [Field K]
    (M N : Matrix (Fin 4) (Fin 4) K)
    (hM : compoundDet42Property M) (hN : compoundDet42Property N) :
    compoundDet42Property (M * N) := by
  unfold compoundDet42Property at hM hN ⊢
  rw [compound_mul, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]

private theorem compoundDet42Property_all {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) : compoundDet42Property A := by
  apply Matrix.diagonal_transvection_induction compoundDet42Property A
  · intro D _
    exact compoundDet42Property_diagonal D
  · exact compoundDet42Property_transvection
  · exact compoundDet42Property_mul

theorem compound42_det {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K) :
    (compound A).det = A.det ^ (3 : ℕ) := by
  have h := compoundDet42Property_all A
  unfold compoundDet42Property at h
  exact h

theorem compound42_det_one {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : A.det = 1) : (compound A).det = 1 := by
  rw [compound42_det, hA, one_pow]

theorem source_compound_determinant_one42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) :
    (compound A₂).det = 1 ∧ (compound A₃).det = 1 ∧ (compound L).det = 1 := by
  constructor
  · rw [compound42_det, h₂, one_pow]
  constructor
  · rw [compound42_det, h₃, one_pow]
  · rw [compound42_det, hL, one_pow]

theorem source_compound_admissible42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    (compound A₂).det = 1 ∧ (compound A₃).det = 1 ∧ (compound L).det = 1 ∧
      (∀ s t, IsAlgebraic ℚ (compound L s t)) := by
  obtain ⟨h₂c, h₃c, hLc⟩ := source_compound_determinant_one42 A₂ A₃ L h₂ h₃ hL
  exact ⟨h₂c, h₃c, hLc, compound42_algebraic L hAlg⟩

end
end CompoundFeasibility
