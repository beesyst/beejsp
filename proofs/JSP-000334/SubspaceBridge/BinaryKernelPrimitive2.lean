import SubspaceBridge.BinaryAuxSourceIndex2
open scoped BigOperators Classical
namespace JSP000334

def binaryNormalHeight (V : Fin 2 → ℤ) : ℕ := max (V 0).natAbs (V 1).natAbs

theorem binary_primitive_gcd (V : Fin 2 → ℤ)
    (hV : Ideal.span (Set.range V) = ⊤) : Int.gcd (V 0) (V 1) = 1 := by
  let d := Int.gcd (V 0) (V 1)
  have hspan : Ideal.span (Set.range V) ≤ Ideal.span ({(d : ℤ)} : Set ℤ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    fin_cases i
    · exact Int.gcd_dvd_left
    · exact Int.gcd_dvd_right
  have hone : (1 : ℤ) ∈ Ideal.span ({(d : ℤ)} : Set ℤ) := by
    apply hspan
    rw [hV]
    trivial
  have hu : IsUnit (d : ℤ) := isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hone)
  simpa using Int.isUnit_iff_natAbs_eq.mp hu

theorem binary_primitive_parameters (V : Fin 2 → ℤ)
    (hnz : ∃ i, V i ≠ 0) (hV : Ideal.span (Set.range V) = ⊤) :
    ∃ k : Fin 2, V k ≠ 0 ∧ Int.gcd (-(V k.rev)) (V k) = 1 ∧
      (V k).natAbs = binaryNormalHeight V := by
  have hg := binary_primitive_gcd V hV
  have hmax : ∃ k : Fin 2, (V k).natAbs = binaryNormalHeight V := by
    by_cases h : (V 0).natAbs ≤ (V 1).natAbs
    · exact ⟨1, (max_eq_right h).symm⟩
    · exact ⟨0, (max_eq_left (le_of_not_ge h)).symm⟩
  obtain ⟨k,hk⟩ := hmax
  refine ⟨k,?_,?_,hk⟩
  · intro hz
    obtain ⟨i,hi⟩ := hnz
    have hh : (V i).natAbs ≤ binaryNormalHeight V := by
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    rw [← hk,hz,Int.natAbs_zero] at hh
    exact hi (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hh))
  · fin_cases k
    · simpa [Int.gcd_comm] using hg
    · simpa using hg
end JSP000334
