import SubspaceBridge.SourceExterior52Algebra238
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundExterior240E
open Exterior52_237 Exterior52_238

variable {R : Type*} [CommRing R]

def pairVector240E (s : Fin 10) : ⋀[R]^2 (Fin 5 → R) :=
  exteriorPower.ιMulti R 2 ![Pi.single (lo237 s) 1,Pi.single (hi237 s) 1]

def coordinate240E (s : Fin 10) : Module.Dual R (⋀[R]^2 (Fin 5 → R)) :=
  exteriorPower.alternatingMapToDual R (Fin 5 → R) 2
    ![LinearMap.proj (lo237 s),LinearMap.proj (hi237 s)]

theorem exterior_minor240E (A : Matrix (Fin 5) (Fin 5) R) (s t : Fin 10) :
    coordinate240E s ((exteriorPower.map 2 A.mulVecLin) (pairVector240E t)) = compound237 A s t := by
  simp [coordinate240E,pairVector240E,exteriorPower.map_apply_ιMulti,
    exteriorPower.alternatingMapToDual_apply_ιMulti,Matrix.det_fin_two,compound237,
    Matrix.mulVec_single]
  ring

end CompoundFeasibility.CompoundExterior240E
