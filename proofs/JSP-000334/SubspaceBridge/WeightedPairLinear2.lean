import SubspaceBridge.WeightedTernaryProduct2
namespace JSP000334

theorem binary_proper_annihilator (P : Submodule ℚ (Fin 2 → ℚ)) (hP : P ≠ ⊤) :
    ∃ b0 b1 : ℚ, (b0 ≠ 0 ∨ b1 ≠ 0) ∧ ∀ x ∈ P, b0*x 0+b1*x 1=0 := by
  obtain ⟨f,hf,hker⟩ := P.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hP)
  have heval (x : Fin 2 → ℚ) : f x = f ![1,0]*x 0+f ![0,1]*x 1 := by
    have hx : x = x 0 • ![(1 : ℚ),0]+x 1 • ![0,(1 : ℚ)] := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hx]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  refine ⟨f ![1,0],f ![0,1],?_,?_⟩
  · by_contra hn
    push_neg at hn
    apply hf
    apply LinearMap.ext
    intro x
    simpa [hn.1,hn.2] using heval x
  · intro x hx
    have hk : f x=0 := hker hx
    rw [heval] at hk
    exact hk

theorem weighted_pair_exact_values (A B C b0 b1 u v : ℚ)
    (hd : B*b1-C*b0 ≠ 0) (he : A+B*u+C*v=0) (hl : b0*u+b1*v=0) :
    u = -A*b1/(B*b1-C*b0) ∧ v = A*b0/(B*b1-C*b0) := by
  constructor
  · apply (eq_div_iff hd).mpr
    nlinarith [congrArg (fun t : ℚ => t*b1) he, congrArg (fun t : ℚ => t*C) hl]
  · apply (eq_div_iff hd).mpr
    nlinarith [congrArg (fun t : ℚ => t*b0) he, congrArg (fun t : ℚ => t*B) hl]

theorem weighted_pair_determinant (A B C b0 b1 u v : ℚ) (hA : A ≠ 0) (hC : C ≠ 0)
    (hb : b0 ≠ 0 ∨ b1 ≠ 0) (he : A+B*u+C*v=0) (hl : b0*u+b1*v=0) :
    B*b1-C*b0 ≠ 0 := by
  intro hd
  have hid : A*b1 = (A+B*u+C*v)*b1-(b0*u+b1*v)*C-(B*b1-C*b0)*u := by ring
  rw [he,hl,hd] at hid
  have hb1 : b1=0 := (mul_eq_zero.mp (by simpa using hid)).resolve_left hA
  have hb0 : b0=0 := by
    have hc : C*b0=0 := by simpa only [hb1,mul_zero,zero_sub,neg_eq_zero] using hd
    exact (mul_eq_zero.mp hc).resolve_left hC
  exact hb.elim (fun h => h hb0) (fun h => h hb1)

end JSP000334
