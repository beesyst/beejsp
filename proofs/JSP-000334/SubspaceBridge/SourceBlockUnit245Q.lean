import SubspaceBridge.SourceBlockWeights245P
import SubspaceBridge.SourceProjection245P
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245Q
open BlockReduction245P

def first245Q {R : Type*} (z : Fin 10 → R) (i : Fin 5) : R := z (blockIndex245P (Sum.inl i))
def second245Q {R : Type*} (z : Fin 10 → R) (i : Fin 5) : R := z (blockIndex245P (Sum.inr i))
def join245Q {R : Type*} (x y : Fin 5 → R) (i : Fin 10) : R :=
  Sum.elim x y (blockIndex245P.symm i)

theorem block_mulVec_left245Q {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) (z : Fin 10 → R) (i : Fin 5) :
    (block245P A *ᵥ z) (blockIndex245P (Sum.inl i)) = (A *ᵥ first245Q z) i := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [← Equiv.sum_comp blockIndex245P]
  simp [block245P,Matrix.reindex_apply,Fintype.sum_sum_type,first245Q]

theorem block_mulVec_right245Q {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) (z : Fin 10 → R) (i : Fin 5) :
    (block245P A *ᵥ z) (blockIndex245P (Sum.inr i)) = second245Q z i := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [← Equiv.sum_comp blockIndex245P]
  simp [block245P,Matrix.reindex_apply,Fintype.sum_sum_type,second245Q,Matrix.one_apply]

theorem block_unit245Q (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) :
    IsUnit (block245P L) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hfirst : L *ᵥ first245Q x = L *ᵥ first245Q y := by
    ext i
    have hi := congrFun hxy (blockIndex245P (Sum.inl i))
    simpa only [block_mulVec_left245Q] using hi
  have hp := Matrix.mulVec_injective_iff_isUnit.mpr hL hfirst
  funext j
  obtain ⟨s,rfl⟩ := blockIndex245P.surjective j
  cases s with
  | inl i => exact congrFun hp i
  | inr i =>
    have hi := congrFun hxy (blockIndex245P (Sum.inr i))
    simpa only [block_mulVec_right245Q,second245Q] using hi

end CompoundFeasibility.BlockReduction245Q
