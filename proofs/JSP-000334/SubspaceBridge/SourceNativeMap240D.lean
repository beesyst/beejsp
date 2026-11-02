import SubspaceBridge.SourceCompoundFixedLine240C
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.FractionRing
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundNative240D
open Exterior52_237

theorem compound_mapMatrix240D {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 5) (Fin 5) R) :
    compound237 (f.mapMatrix A) = f.mapMatrix (compound237 A) := by
  ext s t
  simp only [compound237,RingHom.mapMatrix_apply,Matrix.map_apply,map_sub,map_mul]

theorem compound_det_image240D {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 5) (Fin 5) R)
    (hA : (compound237 A).det = A.det^4) :
    (compound237 (f.mapMatrix A)).det = (f.mapMatrix A).det^4 := by
  have hm : f (compound237 A).det = (compound237 (f.mapMatrix A)).det :=
    (f.map_det (compound237 A)).trans
      (congrArg (fun M : Matrix (Fin 10) (Fin 10) S => M.det) (compound_mapMatrix240D f A).symm)
  have hp : f (A.det^4) = (f.mapMatrix A).det^4 :=
    (map_pow f A.det 4).trans (congrArg (fun x : S => x^4) (f.map_det A))
  exact hm.symm.trans ((congrArg f hA).trans hp)

theorem compound_det_injective240D {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (A : Matrix (Fin 5) (Fin 5) R)
    (hA : (compound237 (f.mapMatrix A)).det = (f.mapMatrix A).det^4) :
    (compound237 A).det = A.det^4 := by
  apply hf
  calc
    _ = (f.mapMatrix (compound237 A)).det := f.map_det _
    _ = (compound237 (f.mapMatrix A)).det := congrArg Matrix.det (compound_mapMatrix240D f A).symm
    _ = (f.mapMatrix A).det^4 := hA
    _ = (f A.det)^4 := congrArg (fun x : S => x^4) (f.map_det A).symm
    _ = _ := (map_pow f _ _).symm

end CompoundFeasibility.CompoundNative240D
