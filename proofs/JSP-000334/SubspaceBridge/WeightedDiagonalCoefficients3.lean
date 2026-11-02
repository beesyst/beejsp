import SubspaceBridge.WeightedDiagonalPrimitive3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_coefficient_denominator3 (B C D : ℚ) (hB : B≠0) (hC : C≠0) (hD : D≠0) :
    ∃ L : ℕ,0<L ∧ ∃ t : Fin 3 → ℤ,(∀ i,t i≠0) ∧
      ∀ i,(t i : ℚ)=(L : ℚ)*(![B,C,D] i) := by
  let L := B.den*C.den*D.den
  let t : Fin 3 → ℤ := ![B.num*C.den*D.den,C.num*B.den*D.den,D.num*B.den*C.den]
  have hL : 0<L := mul_pos (mul_pos B.den_pos C.den_pos) D.den_pos
  have hn (x : ℚ) : (x.num : ℚ)=(x.den : ℚ)*x := integralPair_scale x 1
  have he (i : Fin 3) : (t i : ℚ)=(L : ℚ)*(![B,C,D] i) := by
    fin_cases i
    · change (((B.num*C.den*D.den : ℤ)) : ℚ)=(L : ℚ)*B
      push_cast
      rw [hn]
      dsimp [L]
      push_cast
      ring
    · change (((C.num*B.den*D.den : ℤ)) : ℚ)=(L : ℚ)*C
      push_cast
      rw [hn]
      dsimp [L]
      push_cast
      ring
    · change (((D.num*B.den*C.den : ℤ)) : ℚ)=(L : ℚ)*D
      push_cast
      rw [hn]
      dsimp [L]
      push_cast
      ring
  have hcn (i : Fin 3) : (![B,C,D] i)≠0 := by fin_cases i <;> assumption
  refine ⟨L,hL,t,?_,he⟩
  intro i hi
  have hh := he i
  rw [hi,Int.cast_zero] at hh
  exact (mul_ne_zero (by exact_mod_cast ne_of_gt hL : (L : ℚ)≠0) (hcn i)) hh.symm

end JSP000334
