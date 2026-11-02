import SubspaceBridge.SourceExterior52_237
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior52_238
open Exterior52_237

theorem pair_bijective238 : Function.Bijective pair237 := by
  constructor
  · intro s t he
    have hh : ({lo237 s,hi237 s} : Finset (Fin 5)) = {lo237 t,hi237 t} :=
      congrArg Subtype.val he
    have hset : ({lo237 s,hi237 s} : Set (Fin 5)) = {lo237 t,hi237 t} := by
      simpa only [Finset.coe_pair] using congrArg (fun a : Finset (Fin 5) => (a : Set (Fin 5))) hh
    obtain h | h := Set.pair_eq_pair_iff.mp hset
    · exact pair_unique237 s t h.1 h.2
    · have hlt := pair_lt237 s
      rw [h.1,h.2] at hlt
      exact False.elim (lt_asymm hlt (pair_lt237 t))
  · intro a
    obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp a.property
    rcases lt_or_gt_of_ne hij with h | h
    · obtain ⟨s,hs,ht⟩ := pair_exists237 i j h
      refine ⟨s,Subtype.ext ?_⟩
      simpa only [pair237,hs,ht] using he.symm
    · obtain ⟨s,hs,ht⟩ := pair_exists237 j i h
      refine ⟨s,Subtype.ext ?_⟩
      simpa only [pair237,hs,ht,Finset.pair_comm] using he.symm

def pairEquiv238 : Fin 10 ≃ {a : Finset (Fin 5) // a.card = 2} :=
  Equiv.ofBijective pair237 pair_bijective238

theorem integer_wedge_casts238 (x y : Fin 5 → ℤ) (s : Fin 10) :
    (wedge237 (R := ℤ) x y s : ℚ) = (x (lo237 s) : ℚ)*(y (hi237 s) : ℚ)-
      (x (hi237 s) : ℚ)*(y (lo237 s) : ℚ) ∧
    (wedge237 (R := ℤ) x y s : ℝ) = (x (lo237 s) : ℝ)*(y (hi237 s) : ℝ)-
      (x (hi237 s) : ℝ)*(y (lo237 s) : ℝ) := by
  constructor <;> simp only [wedge237,Int.cast_sub,Int.cast_mul]

theorem pair_order238 : ∀ s t : Fin 10, t < s →
    (lo237 t < lo237 s ∨ hi237 t < hi237 s) ∧ lo237 t < hi237 s := by decide

theorem compound_upper238 {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.BlockTriangular id) : (compound237 A).BlockTriangular id := by
  intro s t h
  obtain ⟨hor,hcross⟩ := pair_order238 s t h
  change A (lo237 s) (lo237 t) * A (hi237 s) (hi237 t) - A (lo237 s) (hi237 t) * A (hi237 s) (lo237 t) = 0
  have hzero : A (hi237 s) (lo237 t) = 0 := hA hcross
  rw [hzero,mul_zero,sub_zero]
  rcases hor with hleft | hright
  · have hz : A (lo237 s) (lo237 t) = 0 := hA hleft
    rw [hz,zero_mul]
  · have hz : A (hi237 s) (hi237 t) = 0 := hA hright
    rw [hz,mul_zero]

theorem compound_upper238_det {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.BlockTriangular id) : (compound237 A).det = A.det ^ (4 : ℕ) := by
  rw [Matrix.det_of_upperTriangular (compound_upper238 A hA),Matrix.det_of_upperTriangular hA]
  have he (s : Fin 10) : compound237 A s s = A (lo237 s) (lo237 s) * A (hi237 s) (hi237 s) := by
    have hz : A (hi237 s) (lo237 s) = 0 := hA (pair_lt237 s)
    simp only [compound237,hz,mul_zero,sub_zero]
  simp_rw [he]
  simp [lo237,hi237,Fin.prod_univ_succ]
  ring

theorem compound_transpose238 {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K) :
    compound237 A.transpose = (compound237 A).transpose := by
  ext s t
  simp only [compound237,Matrix.transpose_apply]
  ring

theorem compound_transvection_det238 {K : Type*} [Field K] (i j : Fin 5)
    (hij : i ≠ j) (c : K) : (compound237 (Matrix.transvection i j c)).det = 1 := by
  have upper (a b : Fin 5) (hab : a < b) :
      (Matrix.transvection a b c : Matrix (Fin 5) (Fin 5) K).BlockTriangular id := by
    intro s t hts
    have hne : s ≠ t := ne_of_gt hts
    have hentry : ¬ (a = s ∧ b = t) := by
      rintro ⟨rfl,rfl⟩
      exact (not_lt_of_ge hab.le) hts
    simp [Matrix.transvection,Matrix.stdBasisMatrix,Matrix.one_apply,hne,hentry]
  by_cases h : i < j
  · rw [compound_upper238_det _ (upper i j h),Matrix.det_transvection_of_ne _ _ hij,one_pow]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)
    have ht : (Matrix.transvection j i c : Matrix (Fin 5) (Fin 5) K).transpose =
        Matrix.transvection i j c := by
      simp [Matrix.transvection,Matrix.transpose_add,Matrix.transpose_stdBasisMatrix]
    rw [← ht,compound_transpose238,Matrix.det_transpose,
      compound_upper238_det _ (upper j i hji),Matrix.det_transvection_of_ne _ _ (Ne.symm hij),one_pow]

def compoundDet238Property {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) : Prop :=
  (compound237 A).det = A.det ^ (4 : ℕ)

attribute [local irreducible] compoundDet238Property

theorem compoundDet238Property_diagonal {K : Type*} [Field K] (D : Fin 5 → K) :
    compoundDet238Property (Matrix.diagonal D) := by
  unfold compoundDet238Property
  exact compound_upper238_det (Matrix.diagonal D) (Matrix.blockTriangular_diagonal D)

theorem compoundDet238Property_transvection {K : Type*} [Field K]
    (t : Matrix.TransvectionStruct (Fin 5) K) : compoundDet238Property t.toMatrix := by
  unfold compoundDet238Property
  have hc := @compound_transvection_det238 K _ t.i t.j t.hij t.c
  rw [t.det, one_pow]
  simpa only [Matrix.TransvectionStruct.toMatrix] using hc

theorem compoundDet238Property_mul {K : Type*} [Field K]
    (M N : Matrix (Fin 5) (Fin 5) K)
    (hM : compoundDet238Property M) (hN : compoundDet238Property N) :
    compoundDet238Property (M * N) := by
  unfold compoundDet238Property at hM hN ⊢
  rw [compound_mul237, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]

theorem compoundDet238Property_all {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) : compoundDet238Property A := by
  apply Matrix.diagonal_transvection_induction compoundDet238Property A
  · intro D _
    exact compoundDet238Property_diagonal D
  · exact compoundDet238Property_transvection
  · exact compoundDet238Property_mul

theorem compound_det238 {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K) :
    (compound237 A).det = A.det ^ (4 : ℕ) := by
  have h := compoundDet238Property_all A
  unfold compoundDet238Property at h
  exact h

theorem compound_det238_one {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.det = 1) : (compound237 A).det = 1 := by
  rw [compound_det238, hA, one_pow]

theorem compound_algebraic238 (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ s t, IsAlgebraic ℚ (compound237 L s t) := by
  intro s t
  exact ((hL _ _).mul (hL _ _)).sub ((hL _ _).mul (hL _ _))

theorem compound_unit238 {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA : IsUnit A) : IsUnit (compound237 A) := by
  obtain ⟨u,rfl⟩ := hA
  apply isUnit_iff_exists.mpr
  refine ⟨compound237 (↑u⁻¹),?_,?_⟩
  · rw [← compound_mul237,Units.mul_inv,compound_one237]
  · rw [← compound_mul237,Units.inv_mul,compound_one237]

theorem compoundFrame_independent238 (u : Fin 5 → Fin 5 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) :
    LinearIndependent ℝ (fun s => integerReal (wedge237 (u (lo237 s)) (u (hi237 s)))) := by
  have he : (fun s => integerReal (wedge237 (u (lo237 s)) (u (hi237 s)))) =
      compound237 (fun j i => (u j i : ℝ)) := by
    funext s t
    change ((u (lo237 s) (lo237 t)*u (hi237 s) (hi237 t)-
      u (lo237 s) (hi237 t)*u (hi237 s) (lo237 t) : ℤ) : ℝ) = _
    simp only [Int.cast_sub,Int.cast_mul,compound237]
  rw [he]
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr
    (compound_unit238 _ (Matrix.linearIndependent_rows_iff_isUnit.mp hu))

end CompoundFeasibility.Exterior52_238
