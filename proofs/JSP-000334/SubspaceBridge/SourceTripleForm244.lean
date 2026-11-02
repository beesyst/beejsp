import SubspaceBridge.SourceExterior53_242
import SubspaceBridge.SourceExceptionalPair241
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag244
open Exterior53_242 SchmidtNormal10

def tripleForm244 (b : Fin 10 → ℤ) (x y z : Fin 5 → ℚ) : ℚ :=
  ∑ s, (b s : ℚ)*wedge3242 x y z s

theorem tripleForm_add1_244 (b : Fin 10 → ℤ) (x y z w : Fin 5 → ℚ) :
    tripleForm244 b (x+w) y z = tripleForm244 b x y z+tripleForm244 b w y z := by
  simp only [tripleForm244]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242,Pi.add_apply]
  ring

theorem tripleForm_smul1_244 (b : Fin 10 → ℤ) (c : ℚ) (x y z : Fin 5 → ℚ) :
    tripleForm244 b (c • x) y z = c*tripleForm244 b x y z := by
  simp only [tripleForm244]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242,Pi.smul_apply,smul_eq_mul]
  ring

theorem tripleForm_add2_244 (b : Fin 10 → ℤ) (x y z w : Fin 5 → ℚ) :
    tripleForm244 b x (y+w) z = tripleForm244 b x y z+tripleForm244 b x w z := by
  simp only [tripleForm244]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242,Pi.add_apply]
  ring

theorem tripleForm_smul2_244 (b : Fin 10 → ℤ) (c : ℚ) (x y z : Fin 5 → ℚ) :
    tripleForm244 b x (c • y) z = c*tripleForm244 b x y z := by
  simp only [tripleForm244]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242,Pi.smul_apply,smul_eq_mul]
  ring

theorem tripleForm_add3_244 (b : Fin 10 → ℤ) (x y z w : Fin 5 → ℚ) :
    tripleForm244 b x y (z+w) = tripleForm244 b x y z+tripleForm244 b x y w := by
  simp only [tripleForm244]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242,Pi.add_apply]
  ring

theorem tripleForm_smul3_244 (b : Fin 10 → ℤ) (c : ℚ) (x y z : Fin 5 → ℚ) :
    tripleForm244 b x y (c • z) = c*tripleForm244 b x y z := by
  simp only [tripleForm244]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242,Pi.smul_apply,smul_eq_mul]
  ring

theorem tripleForm_swap12_244 (b : Fin 10 → ℤ) (x y z : Fin 5 → ℚ) :
    tripleForm244 b x y z = -tripleForm244 b y x z := by
  simp only [tripleForm244]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242]
  ring

theorem tripleForm_swap23_244 (b : Fin 10 → ℤ) (x y z : Fin 5 → ℚ) :
    tripleForm244 b x y z = -tripleForm244 b x z y := by
  simp only [tripleForm244]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [wedge3242,det3242]
  ring

theorem tripleForm_12_244 (b : Fin 10 → ℤ) (x y : Fin 5 → ℚ) :
    tripleForm244 b x x y = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  simp only [wedge3242,det3242,Pi.zero_apply]
  ring

theorem tripleForm_23_244 (b : Fin 10 → ℤ) (x y : Fin 5 → ℚ) :
    tripleForm244 b y x x = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  simp only [wedge3242,det3242,Pi.zero_apply]
  ring

theorem tripleForm_13_244 (b : Fin 10 → ℤ) (x y : Fin 5 → ℚ) :
    tripleForm244 b x y x = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  simp only [wedge3242,det3242,Pi.zero_apply]
  ring

theorem tripleForm_zero_244 (b : Fin 10 → ℤ) (x y : Fin 5 → ℚ) :
    tripleForm244 b 0 x y = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  simp only [wedge3242,det3242,Pi.zero_apply]
  ring

def radical244 (b : Fin 10 → ℤ) : Submodule ℚ (Fin 5 → ℚ) where
  carrier := {x | ∀ y z, tripleForm244 b x y z = 0}
  zero_mem' := tripleForm_zero_244 b
  add_mem' := by
    intro x y hx hy z w
    rw [tripleForm_add1_244,hx,hy,add_zero]
  smul_mem' := by
    intro c x hx y z
    rw [tripleForm_smul1_244,hx,mul_zero]

theorem tripleForm_integer_cast244 (b : Fin 10 → ℤ) (x y z : Fin 5 → ℤ) :
    tripleForm244 b (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) (fun i => (z i : ℚ)) =
      normalForm10 b (fun s => (wedge3242 (R := ℤ) x y z s : ℚ)) := by
  simp only [tripleForm244,normalForm10_apply,wedge3242,det3242,Int.cast_sub,Int.cast_add,Int.cast_mul]

end CompoundFeasibility.SourceFlag244
