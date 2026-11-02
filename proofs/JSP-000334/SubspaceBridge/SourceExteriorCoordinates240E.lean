import SubspaceBridge.SourceExteriorMinor240E
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundExterior240E
open Exterior52_237 Exterior52_238
variable {R : Type*} [CommRing R]

theorem coordinate_pair240E (s t : Fin 10) :
    coordinate240E (R := R) s (pairVector240E t) = if s = t then 1 else 0 := by
  have hm : (1 : Matrix (Fin 5) (Fin 5) R).mulVecLin = LinearMap.id := by
    ext x i
    simp
  have h := exterior_minor240E (1 : Matrix (Fin 5) (Fin 5) R) s t
  simpa only [hm,exteriorPower.map_id,LinearMap.id_apply,compound_one237,Matrix.one_apply] using h

def coordinates240E : (⋀[R]^2 (Fin 5 → R)) →ₗ[R] (Fin 10 → R) :=
  LinearMap.pi coordinate240E

def fromCoordinates240E : (Fin 10 → R) →ₗ[R] (⋀[R]^2 (Fin 5 → R)) :=
  (Pi.basisFun R (Fin 10)).constr R pairVector240E

theorem coordinates_from240E (x : Fin 10 → R) :
    coordinates240E (fromCoordinates240E x) = x := by
  ext s
  simp [coordinates240E,fromCoordinates240E,Basis.constr_apply,coordinate_pair240E]

end CompoundFeasibility.CompoundExterior240E
