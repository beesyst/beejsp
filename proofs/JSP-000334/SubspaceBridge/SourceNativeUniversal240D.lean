import SubspaceBridge.SourceNativeAlgebra240D
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundNative240D
open Exterior52_237

def universalMatrix240D : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 5 × Fin 5) ℤ) :=
  fun i j => MvPolynomial.X (i,j)

def universalEval240D {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    MvPolynomial (Fin 5 × Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ij => A ij.1 ij.2)

theorem universal_eval_matrix240D {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    (universalEval240D A).mapMatrix universalMatrix240D = A := by
  ext i j
  simp only [universalEval240D,universalMatrix240D,RingHom.mapMatrix_apply,Matrix.map_apply,
    MvPolynomial.eval₂Hom_X']

theorem universal_fraction240D :
    compoundDet240DProperty ((algebraMap (MvPolynomial (Fin 5 × Fin 5) ℤ)
      (FractionRing (MvPolynomial (Fin 5 × Fin 5) ℤ))).mapMatrix universalMatrix240D) := by
  apply Matrix.diagonal_transvection_induction compoundDet240DProperty
  · intro D _
    exact compoundDet240DProperty_diagonal D
  · exact compoundDet240DProperty_transvection
  · exact compoundDet240DProperty_mul


end CompoundFeasibility.CompoundNative240D
