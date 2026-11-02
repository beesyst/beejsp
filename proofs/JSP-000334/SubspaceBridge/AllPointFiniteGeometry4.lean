import SubspaceBridge.AllPointActualValues4
namespace JSP000334
open scoped BigOperators Matrix

theorem allpoint_triple_proper4 (a b c : Fin 4 → ℚ) : Submodule.span ℚ {a,b,c}≠⊤ := by
  classical
  have hr : Set.range (![a,b,c] : Fin 3 → Fin 4 → ℚ)={a,b,c} := by
    ext x
    simp [Fin.exists_fin_succ,or_comm,or_left_comm,or_assoc,eq_comm]
  intro he
  have hh : Submodule.span ℚ (Set.range (![a,b,c] : Fin 3 → Fin 4 → ℚ))=⊤ := by rw [hr,he]
  have hf := finrank_le_of_span_eq_top (R := ℚ) hh
  norm_num at hf

theorem allpoint_bounded_height_finite4 (M : ℝ) :
    {z : Fin 4 → ℤ | (archFourHeight z : ℝ)≤M}.Finite := by
  let N := Nat.ceil (max 0 M)
  have hM : M≤(N : ℝ) := (le_max_right 0 M).trans (Nat.le_ceil _)
  have hb : {z : Fin 4 → ℤ | ∀ i,-(N : ℤ)≤z i ∧ z i≤(N : ℤ)}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  apply hb.subset
  intro z hz i
  have hc : |(z i : ℚ)|≤archFourHeight z := four_local_coordinate_le 0 (fun j => (z j : ℚ)) i
  have hr : |(z i : ℝ)|≤(archFourHeight z : ℝ) := by exact_mod_cast hc
  have hh := abs_le.mp (hr.trans (hz.trans hM))
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

end JSP000334
