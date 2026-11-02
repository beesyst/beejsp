import SubspaceBridge.AllPointPrimitive3
import SubspaceBridge.AllPointShortExtraction3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_pair_proper3 (v w : Fin 3 → ℚ) :
    Submodule.span ℚ {v,w} ≠ ⊤ := by
  classical
  have hr : Set.range (![v,w] : Fin 2 → Fin 3 → ℚ) = {v,w} := by
    ext x
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  intro h
  have hh : Submodule.span ℚ (Set.range (![v,w] : Fin 2 → Fin 3 → ℚ)) = ⊤ := by rw [hr,h]
  have hf := finrank_le_of_span_eq_top (R := ℚ) hh
  norm_num at hf

theorem allpoint_bounded_height_finite3 (M : ℝ) :
    {z : IntegerTriple | (archTripleHeight z : ℝ) ≤ M}.Finite := by
  classical
  let N := Nat.ceil (max 0 M)
  have hM : M ≤ (N : ℝ) := (le_max_right 0 M).trans (Nat.le_ceil _)
  have hbox : {z : IntegerTriple | ∀ i, -(N : ℤ) ≤ z i ∧ z i ≤ (N : ℤ)}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  apply hbox.subset
  intro z hz i
  have hcoord : |(z i : ℚ)| ≤ archTripleHeight z := by
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hR : |(z i : ℝ)| ≤ (archTripleHeight z : ℝ) := by exact_mod_cast hcoord
  have hh := abs_le.mp (hR.trans (hz.trans hM))
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

end JSP000334
