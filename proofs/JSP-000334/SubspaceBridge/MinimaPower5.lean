import SubspaceBridge.OriginalSource5
open scoped BigOperators
namespace CompoundFeasibility.MinimaPower5
noncomputable section

def prefixProduct5 (j : Fin 4) (lam : Fin 5 → ℝ) : ℝ :=
  ∏ i : Fin (j.val+1), lam ⟨i.val, by omega⟩

def tailProduct5 (j : Fin 4) (lam : Fin 5 → ℝ) : ℝ :=
  ∏ i : Fin (4-j.val), lam ⟨j.val+1+i.val, by omega⟩

def decayExponent5 (j : Fin 4) (delta : ℝ) : ℝ :=
  delta * (j.val+1) * (5-(j.val+1)) / 5

theorem selectedDimension5_cases (j : Fin 4) :
    j.val+1 = 1 ∨ j.val+1 = 2 ∨ j.val+1 = 3 ∨ j.val+1 = 4 := by
  omega

theorem decayExponent5_pos (j : Fin 4) (delta : ℝ) (hd : 0 < delta) :
    0 < decayExponent5 j delta := by
  unfold decayExponent5
  have hj : (j.val : ℝ) < 4 := by exact_mod_cast j.isLt
  have hx : 0 < 5 - ((j.val : ℝ)+1) := by linarith
  exact div_pos (mul_pos (mul_pos hd (by positivity)) hx) (by norm_num)

end
end CompoundFeasibility.MinimaPower5
