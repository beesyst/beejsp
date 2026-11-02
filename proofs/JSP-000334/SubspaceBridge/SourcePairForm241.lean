import SubspaceBridge.SourceExterior52Algebra238
import SubspaceBridge.CompoundDualLine42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open Exterior52_237

def pairForm241 (b : Fin 10 → ℤ) : (Fin 5 → ℚ) →ₗ[ℚ] Module.Dual ℚ (Fin 5 → ℚ) where
  toFun x :=
    { toFun := fun y => ∑ s, (b s : ℚ)*(x (lo237 s)*y (hi237 s)-x (hi237 s)*y (lo237 s))
      map_add' := by
        intro y z
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s _
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c y
        change (∑ s, _) = c*(∑ s, _)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        simp only [Pi.smul_apply,smul_eq_mul]
        ring }
  map_add' := by
    intro x z
    apply LinearMap.ext
    intro y
    change (∑ s : Fin 10, (b s : ℚ)*((x+z) (lo237 s)*y (hi237 s)-(x+z) (hi237 s)*y (lo237 s))) =
      (∑ s : Fin 10, (b s : ℚ)*(x (lo237 s)*y (hi237 s)-x (hi237 s)*y (lo237 s)))+
      (∑ s : Fin 10, (b s : ℚ)*(z (lo237 s)*y (hi237 s)-z (hi237 s)*y (lo237 s)))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change (∑ s : Fin 10, (b s : ℚ)*((c*x (lo237 s))*y (hi237 s)-(c*x (hi237 s))*y (lo237 s))) =
      c*(∑ s : Fin 10, (b s : ℚ)*(x (lo237 s)*y (hi237 s)-x (hi237 s)*y (lo237 s)))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring

def radical241 (b : Fin 10 → ℤ) : Submodule ℚ (Fin 5 → ℚ) := LinearMap.ker (pairForm241 b)

theorem pairForm_apply241 (b : Fin 10 → ℤ) (x y : Fin 5 → ℚ) :
    pairForm241 b x y = ∑ s, (b s : ℚ)*wedge237 x y s := rfl

theorem pairForm_self241 (b : Fin 10 → ℤ) (x : Fin 5 → ℚ) : pairForm241 b x x = 0 := by
  simp [pairForm_apply241,wedge237,mul_comm]

theorem pairForm_swap241 (b : Fin 10 → ℤ) (x y : Fin 5 → ℚ) :
    pairForm241 b x y = -pairForm241 b y x := by
  rw [pairForm_apply241,pairForm_apply241,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge237]
  ring

end CompoundFeasibility.SourceFlag241
