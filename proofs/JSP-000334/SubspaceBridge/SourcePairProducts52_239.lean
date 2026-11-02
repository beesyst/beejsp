import SubspaceBridge.SourceExterior52Normalize238
import Mathlib.Data.Fin.Tuple.Sort
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.ExteriorGap52_239
open Exterior52_237 Exterior52_238

def pairOrder239 (a : Fin 5 → ℝ) : Equiv.Perm (Fin 10) :=
  Tuple.sort (fun s => a (lo237 s)*a (hi237 s))

def pairProducts239 (a : Fin 5 → ℝ) : Fin 10 → ℝ :=
  fun j => a (lo237 (pairOrder239 a j))*a (hi237 (pairOrder239 a j))

theorem pairProducts_pos239 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ j, 0 < pairProducts239 a j := fun _ => mul_pos (ha _) (ha _)

theorem pairProducts_mono239 (a : Fin 5 → ℝ) : Monotone (pairProducts239 a) :=
  Tuple.monotone_sort (fun s => a (lo237 s)*a (hi237 s))

theorem pair_width_product239 (a : Fin 5 → ℝ) :
    (∏ s, a (lo237 s)*a (hi237 s)) = (∏ i, a i)^4 := by
  simp [lo237,hi237,Fin.prod_univ_succ]
  ring

theorem pairProducts_product239 (a : Fin 5 → ℝ) :
    (∏ j, pairProducts239 a j) = (∏ i, a i)^4 := by
  rw [show (∏ j, pairProducts239 a j) = ∏ s, a (lo237 s)*a (hi237 s) from
    Equiv.prod_comp (pairOrder239 a) (fun s => a (lo237 s)*a (hi237 s))]
  exact pair_width_product239 a

theorem pairProducts_top239 (a : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) (hm : Monotone a) :
    pairProducts239 a 8 = a 2*a 4 ∧ pairProducts239 a 9 = a 3*a 4 := by
  classical
  let f : Fin 10 → ℝ := fun s => a (lo237 s)*a (hi237 s)
  let sigma := pairOrder239 a
  have hs : Monotone (fun j => f (sigma j)) := pairProducts_mono239 a
  have htop : ∀ s, f s ≤ a 3*a 4 := by
    intro s
    have hi : lo237 s ≤ (3 : Fin 5) ∧ hi237 s ≤ (4 : Fin 5) := by
      have hh : ∀ s : Fin 10, lo237 s ≤ (3 : Fin 5) ∧ hi237 s ≤ (4 : Fin 5) := by decide
      exact hh s
    exact mul_le_mul (hm hi.1) (hm hi.2) (ha _).le (ha _).le
  have hpen : ∀ s, s ≠ (9 : Fin 10) → f s ≤ a 2*a 4 := by
    intro s hne
    have hh : ∀ s : Fin 10, s ≠ (9 : Fin 10) → lo237 s ≤ (2 : Fin 5) ∧ hi237 s ≤ (4 : Fin 5) := by decide
    exact mul_le_mul (hm (hh s hne).1) (hm (hh s hne).2) (ha _).le (ha _).le
  have h8 : f 8 = a 2*a 4 := rfl
  have h9 : f 9 = a 3*a 4 := rfl
  have he8 : f (sigma (sigma.symm 8)) = a 2*a 4 := by rw [sigma.apply_symm_apply,h8]
  have he9 : f (sigma (sigma.symm 9)) = a 3*a 4 := by rw [sigma.apply_symm_apply,h9]
  constructor
  · apply le_antisymm
    · by_cases he : sigma 8 = 9
      · have hne : sigma 9 ≠ 9 := by
          intro h
          have hh := sigma.injective (he.trans h.symm)
          exact (by decide : (8 : Fin 10) ≠ 9) hh
        exact (hs (show (8 : Fin 10) ≤ 9 by decide)).trans (hpen _ hne)
      · exact hpen _ he
    · by_cases hi : sigma.symm 8 ≤ (8 : Fin 10)
      · exact he8.symm.trans_le (hs hi)
      · have hj : sigma.symm 9 ≤ (8 : Fin 10) := by
          by_contra hj
          have e8 : sigma.symm 8 = (9 : Fin 10) := Fin.ext (by
            have := (sigma.symm 8).isLt
            change (sigma.symm 8).val = 9
            change ¬ (sigma.symm 8).val ≤ 8 at hi
            omega)
          have e9 : sigma.symm 9 = (9 : Fin 10) := Fin.ext (by
            have := (sigma.symm 9).isLt
            change (sigma.symm 9).val = 9
            change ¬ (sigma.symm 9).val ≤ 8 at hj
            omega)
          have hh := sigma.symm.injective (e8.trans e9.symm)
          exact (by decide : (8 : Fin 10) ≠ 9) hh
        exact (mul_le_mul_of_nonneg_right (hm (show (2 : Fin 5) ≤ 3 by decide)) (ha 4).le).trans
          (he9.symm.trans_le (hs hj))
  · exact le_antisymm (htop _) (he9.symm.trans_le (hs (Fin.le_last _)))

end CompoundFeasibility.ExteriorGap52_239
