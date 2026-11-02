import SubspaceBridge.SourceCompoundFields52_240
import Mathlib.Algebra.Equiv.TransferInstance
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundNaturality240N
open Exterior52_237 Exterior52_238

theorem compound_map240N {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin 5) (Fin 5) R) :
    compound237 (A.map f) = (compound237 A).map f := compound_map237 f A

structure SourceCarrier240N (K : Type*) where
  down : K

def carrierEquiv240N (K : Type*) : SourceCarrier240N K ≃ K where
  toFun := SourceCarrier240N.down
  invFun := SourceCarrier240N.mk
  left_inv := fun ⟨x⟩ => rfl
  right_inv := fun _ => rfl

instance carrierField240N (K : Type*) [Field K] : Field (SourceCarrier240N K) :=
  (carrierEquiv240N K).field

def carrierRingEquiv240N (K : Type*) [Field K] : SourceCarrier240N K ≃+* K where
  toEquiv := carrierEquiv240N K
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def ratSourceEquiv240N : SourceCarrier240N ℚ ≃+* ℚ := carrierRingEquiv240N ℚ

def realSourceEquiv240N : SourceCarrier240N ℝ ≃+* ℝ := carrierRingEquiv240N ℝ

end CompoundFeasibility.CompoundNaturality240N
