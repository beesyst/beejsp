import SubspaceBridge.WeightedDiagonalReduction4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_coefficient_denominator4 (B : Fin 4 → ℚ) (hB : ∀ i,B i≠0) :
    ∃ L : ℕ,0<L ∧ ∃ t : Fin 4 → ℤ,(∀ i,t i≠0) ∧
      ∀ i,(t i : ℚ)=(L : ℚ)*B i := by
  let L := (B 0).den*(B 1).den*(B 2).den*(B 3).den
  let t : Fin 4 → ℤ := ![(B 0).num*(B 1).den*(B 2).den*(B 3).den,(B 1).num*(B 0).den*(B 2).den*(B 3).den,(B 2).num*(B 0).den*(B 1).den*(B 3).den,(B 3).num*(B 0).den*(B 1).den*(B 2).den]
  have hL : 0<L := mul_pos (mul_pos (mul_pos (B 0).den_pos (B 1).den_pos) (B 2).den_pos) (B 3).den_pos
  have hn (x : ℚ) : (x.num : ℚ)=(x.den : ℚ)*x := integralPair_scale x 1
  have he (i : Fin 4) : (t i : ℚ)=(L : ℚ)*B i := by
    fin_cases i
    · change (((B 0).num*(B 1).den*(B 2).den*(B 3).den : ℤ) : ℚ)=(L : ℚ)*B 0
      push_cast
      rw [hn]
      dsimp [L]
      push_cast
      ring
    · change (((B 1).num*(B 0).den*(B 2).den*(B 3).den : ℤ) : ℚ)=(L : ℚ)*B 1
      push_cast
      rw [hn]
      dsimp [L]
      push_cast
      ring
    · change (((B 2).num*(B 0).den*(B 1).den*(B 3).den : ℤ) : ℚ)=(L : ℚ)*B 2
      push_cast
      rw [hn]
      dsimp [L]
      push_cast
      ring
    · change (((B 3).num*(B 0).den*(B 1).den*(B 2).den : ℤ) : ℚ)=(L : ℚ)*B 3
      push_cast
      rw [hn]
      dsimp [L]
      push_cast
      ring
  refine ⟨L,hL,t,?_,he⟩
  intro i hi
  have hh := he i
  rw [hi,Int.cast_zero] at hh
  exact (mul_ne_zero (by exact_mod_cast ne_of_gt hL : (L : ℚ)≠0) (hB i)) hh.symm

end JSP000334
