import SubspaceBridge.SourceSelectedSet10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedSelector10
open SourceSelectedSet10

theorem balanced_widths_do_not_preserve_selector10 :
    let A : Fin 10 → ℝ := ![1/8,8,1,1,1,1,1,1,1,1]
    (∏ i, A i) = 1 ∧ (∀ i, 0 < A i ∧ A i < 16 ∧ (A i)⁻¹ < 16) ∧
      (fun _ : Fin 3 => (0 : Fin 10)) ∈
        roundedSelector10 16 1 (fun _ => 1) (fun _ => 0) (fun _ => 0) ∧
      (fun _ : Fin 3 => (0 : Fin 10)) ∉
        roundedSelector10 16 1 A (fun _ => 0) (fun _ => 0) := by
  have hp : (16 : ℝ)^((1 : ℝ)/2) = 4 := by
    rw [← Real.sqrt_eq_rpow]
    rw [show (16 : ℝ) = 4^2 by norm_num,Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  dsimp
  constructor
  · norm_num [Fin.prod_univ_succ]
  constructor
  · intro i
    fin_cases i <;> norm_num
  constructor <;> norm_num [roundedSelector10,roundedRadius10,JSP000334.qThreshold,hp]

end CompoundFeasibility.SourceFixedSelector10
