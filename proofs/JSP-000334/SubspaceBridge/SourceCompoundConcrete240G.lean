import SubspaceBridge.SourceNativeAlgebra240D
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundConcrete240G
open Exterior52_237 CompoundNative240D

theorem compound_rat_property240G (A : Matrix (Fin 5) (Fin 5) ℚ) :
    compoundDet240DProperty A := by
  apply Matrix.diagonal_transvection_induction compoundDet240DProperty
  · intro D _
    exact compoundDet240DProperty_diagonal D
  · exact compoundDet240DProperty_transvection
  · exact compoundDet240DProperty_mul

theorem compound_rat_det_one240G (A : Matrix (Fin 5) (Fin 5) ℚ)
    (hA : A.det = 1) : (compound237 A).det = 1 := by
  have h := compound_rat_property240G A
  unfold compoundDet240DProperty at h
  rw [h,hA,one_pow]

theorem compound_real_property240G (A : Matrix (Fin 5) (Fin 5) ℝ) :
    compoundDet240DProperty A := by
  apply Matrix.diagonal_transvection_induction compoundDet240DProperty
  · intro D _
    exact compoundDet240DProperty_diagonal D
  · exact compoundDet240DProperty_transvection
  · exact compoundDet240DProperty_mul

theorem compound_real_det_one240G (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A.det = 1) : (compound237 A).det = 1 := by
  have h := compound_real_property240G A
  unfold compoundDet240DProperty at h
  rw [h,hA,one_pow]

end CompoundFeasibility.CompoundConcrete240G
