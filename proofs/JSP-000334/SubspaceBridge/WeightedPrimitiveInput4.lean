import SubspaceBridge.WeightedFixedProductCover4
import SubspaceBridge.WeightedDiagonalPrimitive3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_primitive_sunit_normalized4 (x : Fin 4 → ℚ) (h0 : x 0=1)
    (u1 u2 u3 : fixedSUnitGroup)
    (hu1 : ((u1 : ℚˣ) : ℚ)=x 1) (hu2 : ((u2 : ℚˣ) : ℚ)=x 2)
    (hu3 : ((u3 : ℚˣ) : ℚ)=x 3) :
    ∃ z : Fin 4 → ℤ,∃ s : fixedSUnitGroup,PrimitiveFour z ∧ z≠0 ∧
      ∀ i : Fin 4,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i := by
  obtain ⟨s1,hs1⟩ := sunit_denominator u1
  obtain ⟨s2,hs2⟩ := sunit_denominator u2
  obtain ⟨s3,hs3⟩ := sunit_denominator u3
  have hd1 : ((s1 : ℚˣ) : ℚ)=((x 1).den : ℚ) := by simpa [hu1] using hs1
  have hd2 : ((s2 : ℚˣ) : ℚ)=((x 2).den : ℚ) := by simpa [hu2] using hs2
  have hd3 : ((s3 : ℚˣ) : ℚ)=((x 3).den : ℚ) := by simpa [hu3] using hs3
  let D : ℕ := (x 1).den*(x 2).den*(x 3).den
  let s0 : fixedSUnitGroup := s1*s2*s3
  let w : Fin 4 → ℤ := ![(D : ℤ),
    (x 1).num*(x 2).den*(x 3).den,
    (x 2).num*(x 1).den*(x 3).den,
    (x 3).num*(x 1).den*(x 2).den]
  have hs0 : ((s0 : ℚˣ) : ℚ)=(D : ℚ) := by simp [s0,D,hd1,hd2,hd3]
  have hnum (i : Fin 4) : ((x i).num : ℚ)=((x i).den : ℚ)*x i := integralPair_scale (x i) 1
  have hw (i : Fin 4) : (w i : ℚ)=((s0 : ℚˣ) : ℚ)*x i := by
    rw [hs0]
    fin_cases i
    · simp [w,h0]
    · change (((x 1).num*(x 2).den*(x 3).den : ℤ) : ℚ)=(D : ℚ)*x 1
      push_cast
      rw [hnum]
      dsimp [D]
      push_cast
      ring
    · change (((x 2).num*(x 1).den*(x 3).den : ℤ) : ℚ)=(D : ℚ)*x 2
      push_cast
      rw [hnum]
      dsimp [D]
      push_cast
      ring
    · change (((x 3).num*(x 1).den*(x 2).den : ℤ) : ℚ)=(D : ℚ)*x 3
      push_cast
      rw [hnum]
      dsimp [D]
      push_cast
      ring
  have hD : D≠0 := mul_ne_zero (mul_ne_zero (Rat.den_ne_zero _) (Rat.den_ne_zero _)) (Rat.den_ne_zero _)
  have hw0 : w 0≠0 := by change (D : ℤ)≠0; exact_mod_cast hD
  obtain ⟨g,hg,hgdvd,z,hz,hscale⟩ := primitive_four_integer_reduction w hw0
  have hgD : g∣D := Int.natCast_dvd_natCast.mp hgdvd
  have hgsmooth : Smooth23 g := by
    intro p hp hpg
    rcases hp.dvd_mul.mp (hpg.trans hgD) with hp12|hp3
    · rcases hp.dvd_mul.mp hp12 with hp1|hp2
      · apply sunit_den_prime_support u1 p hp
        simpa [hu1] using hp1
      · apply sunit_den_prime_support u2 p hp
        simpa [hu2] using hp2
    · apply sunit_den_prime_support u3 p hp
      simpa [hu3] using hp3
  obtain ⟨ug,hug⟩ := positive_smooth23_sunit4 (ne_of_gt hg) hgsmooth
  let s := s0/ug
  have hzscale (i : Fin 4) : (z i : ℚ)=((s : ℚˣ) : ℚ)*x i := by
    have hc := congrArg ((↑) : ℤ → ℚ) (hscale i)
    push_cast at hc
    have hsval : ((s : ℚˣ) : ℚ)=((s0 : ℚˣ) : ℚ)/(g : ℚ) := by simp [s,hug]
    rw [hsval,div_mul_eq_mul_div]
    apply (eq_div_iff (by exact_mod_cast (ne_of_gt hg) : (g : ℚ)≠0)).mpr
    have hh := hw i
    rw [hc] at hh
    nlinarith only [hh]
  have hnz : z≠0 := by
    intro he
    have hh := hzscale 0
    simp [he,h0] at hh
    exact Units.ne_zero _ hh.symm
  exact ⟨z,s,hz,hnz,hzscale⟩

theorem weighted_primitive_sunit_coordinates4 (u : Fin 4 → fixedSUnitGroup) :
    ∃ z : Fin 4 → ℤ,∃ s : fixedSUnitGroup,PrimitiveFour z ∧ (∀ i,z i≠0) ∧
      ∀ i,(z i : ℚ)=((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ) := by
  let x (i : Fin 4) : ℚ := (((u i/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)
  have h0 : x 0=1 := by simp [x]
  obtain ⟨z,s,hz,_,he⟩ := weighted_primitive_sunit_normalized4 x h0 (u 1/u 0) (u 2/u 0) (u 3/u 0) rfl rfl rfl
  let s' := s/u 0
  have hh (i : Fin 4) : (z i : ℚ)=((s' : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ) := by
    simpa [x,s',div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using he i
  refine ⟨z,s',hz,?_,hh⟩
  intro i hi
  have h := hh i
  rw [hi,Int.cast_zero] at h
  exact (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) h.symm

end JSP000334
