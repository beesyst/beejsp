import SubspaceBridge.WeightedDiagonalProducts3
import SubspaceBridge.AllPointPrimitive4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_primitive_triple_reduction3 (z : Fin 3 → ℤ) (hz0 : z 0 ≠ 0) :
    ∃ g : ℕ, 0 < g ∧ (g : ℤ) ∣ z 0 ∧ ∃ y : Fin 3 → ℤ,
      PrimitiveTriple y ∧ ∀ i, z i = (g : ℤ) * y i := by
  let k := Int.gcd (z 1) (z 2)
  let g := Int.gcd (z 0) (k : ℤ)
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left _ hz0
  have hg0 : (g : ℤ) ∣ z 0 := Int.gcd_dvd_left
  have hgk : (g : ℤ) ∣ (k : ℤ) := Int.gcd_dvd_right
  have hg1 : (g : ℤ) ∣ z 1 := hgk.trans (Int.gcd_dvd_left)
  have hg2 : (g : ℤ) ∣ z 2 := hgk.trans (Int.gcd_dvd_right)
  obtain ⟨y0, hy0⟩ := hg0
  obtain ⟨y1, hy1⟩ := hg1
  obtain ⟨y2, hy2⟩ := hg2
  let y : Fin 3 → ℤ := ![y0, y1, y2]
  have hscale (i : Fin 3) : z i = (g : ℤ) * y i := by
    fin_cases i <;> assumption
  let a := Int.gcdA (z 0) (k : ℤ)
  let b := Int.gcdB (z 0) (k : ℤ)
  let c := Int.gcdA (z 1) (z 2)
  let d := Int.gcdB (z 1) (z 2)
  have hgbez : (g : ℤ) = z 0 * a + (k : ℤ) * b := Int.gcd_eq_gcd_ab _ _
  have hkbez : (k : ℤ) = z 1 * c + z 2 * d := Int.gcd_eq_gcd_ab _ _
  have hcoeff : (g : ℤ) * (a * y0 + (b * c) * y1 + (b * d) * y2) = (g : ℤ) * 1 := by
    calc
      _ = z 0 * a + (k : ℤ) * b := by rw [hkbez, hy0, hy1, hy2]; ring
      _ = _ := by rw [← hgbez]; ring
  have hgneq : (g : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
  have hprimitive : PrimitiveTriple y := by
    refine ⟨![a, b * c, b * d], ?_⟩
    simpa [y, Fin.sum_univ_succ, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
      add_assoc] using mul_left_cancel₀ hgneq hcoeff
  exact ⟨g, hg, Int.gcd_dvd_left, y, hprimitive, hscale⟩


theorem weighted_primitive_sunit_normalized3 (x : Fin 3 → ℚ) (h0 : x 0=1)
    (u1 u2 : fixedSUnitGroup) (hu1 : ((u1 : ℚˣ) : ℚ)=x 1) (hu2 : ((u2 : ℚˣ) : ℚ)=x 2) :
    ∃ z : Fin 3 → ℤ,∃ s : fixedSUnitGroup,PrimitiveTriple z ∧ z≠0 ∧
      ∀ i : Fin 3,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i := by
  obtain ⟨s1, hs1⟩ := sunit_denominator u1
  obtain ⟨s2, hs2⟩ := sunit_denominator u2
  have hd1 : ((s1 : ℚˣ) : ℚ) = ((x 1).den : ℚ) := by simpa [hu1] using hs1
  have hd2 : ((s2 : ℚˣ) : ℚ) = ((x 2).den : ℚ) := by simpa [hu2] using hs2
  let D : ℕ := (x 1).den * (x 2).den
  let s0 : fixedSUnitGroup := s1 * s2
  let w : Fin 3 → ℤ := ![(D : ℤ), (x 1).num * (x 2).den, (x 2).num * (x 1).den]
  have hs0 : ((s0 : ℚˣ) : ℚ) = (D : ℚ) := by simp [s0, D, hd1, hd2]
  have hnum1 : ((x 1).num : ℚ) = ((x 1).den : ℚ) * x 1 := by
    have h := integralPair_scale (x 1) (1 : Fin 2)
    exact h
  have hnum2 : ((x 2).num : ℚ) = ((x 2).den : ℚ) * x 2 := by
    have h := integralPair_scale (x 2) (1 : Fin 2)
    exact h
  have hw (i : Fin 3) : (w i : ℚ) = ((s0 : ℚˣ) : ℚ) * x i := by
    rw [hs0]
    fin_cases i
    · simp [w, h0]
    · change (((x 1).num * ((x 2).den : ℤ) : ℤ) : ℚ) = (D : ℚ) * x 1
      push_cast
      rw [hnum1]
      dsimp [D]
      push_cast
      ring
    · change (((x 2).num * ((x 1).den : ℤ) : ℤ) : ℚ) = (D : ℚ) * x 2
      push_cast
      rw [hnum2]
      dsimp [D]
      push_cast
      ring
  have hD : D ≠ 0 := mul_ne_zero (Rat.den_ne_zero _) (Rat.den_ne_zero _)
  have hw0 : w 0 ≠ 0 := by
    change (D : ℤ) ≠ 0
    exact_mod_cast hD
  obtain ⟨g, hg, hgdvd, z, hz, hscale⟩ := weighted_primitive_triple_reduction3 w hw0
  have hgD : g ∣ D := Int.natCast_dvd_natCast.mp hgdvd
  have hgsmooth : Smooth23 g := by
    intro p hp hpg
    rcases hp.dvd_mul.mp (hpg.trans hgD) with hp1 | hp2
    · apply sunit_den_prime_support u1 p hp
      simpa [hu1] using hp1
    · apply sunit_den_prime_support u2 p hp
      simpa [hu2] using hp2
  obtain ⟨ug, hug⟩ := positive_smooth23_sunit4 (ne_of_gt hg) hgsmooth
  let s := s0 / ug
  have hzscale (i : Fin 3) : (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i := by
    have hc := congrArg ((↑) : ℤ → ℚ) (hscale i)
    push_cast at hc
    have hsval : ((s : ℚˣ) : ℚ) = ((s0 : ℚˣ) : ℚ) / (g : ℚ) := by simp [s, hug]
    rw [hsval]
    have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hg0).mpr
    have hwi := hw i
    rw [hc] at hwi
    nlinarith [hwi]
  have hnz : z ≠ 0 := by
    intro heq
    have hh := hzscale 0
    simp only [heq,Pi.zero_apply,Int.cast_zero,h0,mul_one] at hh
    exact Units.ne_zero (s : ℚˣ) hh.symm
  exact ⟨z, s, hz, hnz, hzscale⟩

theorem weighted_primitive_sunit_coordinates3 (u : Fin 3 → fixedSUnitGroup) :
    ∃ z : Fin 3 → ℤ,∃ s : fixedSUnitGroup,PrimitiveTriple z ∧ (∀ i,z i≠0) ∧
      ∀ i,(z i : ℚ)=((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ) := by
  let x (i : Fin 3) : ℚ := (((u i/u 0 : fixedSUnitGroup) : ℚˣ) : ℚ)
  have h0 : x 0=1 := by simp [x]
  obtain ⟨z,s,hz,_,he⟩ := weighted_primitive_sunit_normalized3 x h0 (u 1/u 0) (u 2/u 0) rfl rfl
  let s' := s/u 0
  have hh (i : Fin 3) : (z i : ℚ)=((s' : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ) := by
    simpa [x,s',div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using he i
  refine ⟨z,s',hz,?_,hh⟩
  intro i hi
  have h := hh i
  rw [hi,Int.cast_zero] at h
  exact (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) h.symm

theorem weighted_diagonal_primitive3 (t z : Fin 3 → ℤ) (ht : ∀ i,t i≠0)
    (hz : PrimitiveTriple z) (hzn : ∀ i,z i≠0) :
    ∃ g : ℕ,0<g ∧ (g : ℤ)∣t 0*t 1*t 2 ∧ ∃ y : Fin 3 → ℤ,
      PrimitiveTriple y ∧ (∀ i,y i≠0) ∧ ∀ i,t i*z i=(g : ℤ)*y i := by
  obtain ⟨g,hg,_,y,hy,he⟩ := weighted_primitive_triple_reduction3 (fun i => t i*z i) (mul_ne_zero (ht 0) (hzn 0))
  refine ⟨g,hg,weighted_diagonal_gcd_divides3 t z hz (g : ℤ) (fun i => ⟨y i,he i⟩),y,hy,?_,he⟩
  intro i hi
  have hh := he i
  rw [hi,mul_zero] at hh
  exact (mul_ne_zero (ht i) (hzn i)) hh

end JSP000334
