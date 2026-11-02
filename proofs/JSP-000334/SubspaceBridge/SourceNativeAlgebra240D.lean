import SubspaceBridge.SourceNativeMap240D
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundNative240D
open Exterior52_237

theorem compound_upper240D {K : Type*} [CommRing K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.BlockTriangular id) : (compound237 A).BlockTriangular id := by
  intro s t h
  obtain ⟨hor,hcross⟩ := Exterior52_238.pair_order238 s t h
  change A (lo237 s) (lo237 t) * A (hi237 s) (hi237 t) - A (lo237 s) (hi237 t) * A (hi237 s) (lo237 t) = 0
  have hzero : A (hi237 s) (lo237 t) = 0 := hA hcross
  rw [hzero,mul_zero,sub_zero]
  rcases hor with hleft | hright
  · have hz : A (lo237 s) (lo237 t) = 0 := hA hleft
    rw [hz,zero_mul]
  · have hz : A (hi237 s) (hi237 t) = 0 := hA hright
    rw [hz,mul_zero]

theorem compound_upper240D_det {K : Type*} [CommRing K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.BlockTriangular id) : (compound237 A).det = A.det ^ (4 : ℕ) := by
  rw [Matrix.det_of_upperTriangular (compound_upper240D A hA),Matrix.det_of_upperTriangular hA]
  have he (s : Fin 10) : compound237 A s s = A (lo237 s) (lo237 s) * A (hi237 s) (hi237 s) := by
    have hz : A (hi237 s) (lo237 s) = 0 := hA (pair_lt237 s)
    simp only [compound237,hz,mul_zero,sub_zero]
  simp_rw [he]
  simp [lo237,hi237,Fin.prod_univ_succ]
  ring

theorem compound_transpose240D {K : Type*} [CommRing K] (A : Matrix (Fin 5) (Fin 5) K) :
    compound237 A.transpose = (compound237 A).transpose := by
  ext s t
  simp only [compound237,Matrix.transpose_apply]
  ring

theorem compound_transvection_det240D {K : Type*} [CommRing K] (i j : Fin 5)
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
  · rw [compound_upper240D_det _ (upper i j h),Matrix.det_transvection_of_ne _ _ hij,one_pow]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)
    have ht : (Matrix.transvection j i c : Matrix (Fin 5) (Fin 5) K).transpose =
        Matrix.transvection i j c := by
      simp [Matrix.transvection,Matrix.transpose_add,Matrix.transpose_stdBasisMatrix]
    rw [← ht,compound_transpose240D,Matrix.det_transpose,
      compound_upper240D_det _ (upper j i hji),Matrix.det_transvection_of_ne _ _ (Ne.symm hij),one_pow]

def compoundDet240DProperty {K : Type*} [CommRing K]
    (A : Matrix (Fin 5) (Fin 5) K) : Prop :=
  (compound237 A).det = A.det ^ (4 : ℕ)

attribute [local irreducible] compoundDet240DProperty

theorem compoundDet240DProperty_diagonal {K : Type*} [CommRing K] (D : Fin 5 → K) :
    compoundDet240DProperty (Matrix.diagonal D) := by
  unfold compoundDet240DProperty
  exact compound_upper240D_det (Matrix.diagonal D) (Matrix.blockTriangular_diagonal D)

theorem compoundDet240DProperty_transvection {K : Type*} [CommRing K]
    (t : Matrix.TransvectionStruct (Fin 5) K) : compoundDet240DProperty t.toMatrix := by
  unfold compoundDet240DProperty
  have hc := @compound_transvection_det240D K _ t.i t.j t.hij t.c
  rw [t.det, one_pow]
  simpa only [Matrix.TransvectionStruct.toMatrix] using hc

theorem compoundDet240DProperty_mul {K : Type*} [CommRing K]
    (M N : Matrix (Fin 5) (Fin 5) K)
    (hM : compoundDet240DProperty M) (hN : compoundDet240DProperty N) :
    compoundDet240DProperty (M * N) := by
  unfold compoundDet240DProperty at hM hN ⊢
  rw [compound_mul237, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]


end CompoundFeasibility.CompoundNative240D
