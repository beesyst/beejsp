import SubspaceBridge.AllPointFixedSourceFamily5
import SubspaceBridge.AllPointPrimitive4
namespace JSP000334
open scoped BigOperators Matrix

def PrimitiveFive (z : Fin 5 → ℤ) : Prop := ∃ c : Fin 5 → ℤ,∑ i,c i*z i=1

theorem primitive_five_integer_reduction (w : Fin 5 → ℤ) (hw0 : w 0≠0) :
    ∃ g : ℕ,0<g ∧ (g : ℤ)∣w 0 ∧ ∃ z : Fin 5 → ℤ,
      PrimitiveFive z ∧ ∀ i,w i=(g : ℤ)*z i := by
  let k := Int.gcd (w 3) (w 4)
  let l := Int.gcd (w 2) (k : ℤ)
  let m := Int.gcd (w 1) (l : ℤ)
  let g := Int.gcd (w 0) (m : ℤ)
  have hg : 0<g := Int.gcd_pos_of_ne_zero_left _ hw0
  have hg0 : (g : ℤ)∣w 0 := Int.gcd_dvd_left
  have hgm : (g : ℤ)∣(m : ℤ) := Int.gcd_dvd_right
  have hm1 : (m : ℤ)∣w 1 := Int.gcd_dvd_left
  have hml : (m : ℤ)∣(l : ℤ) := Int.gcd_dvd_right
  have hl2 : (l : ℤ)∣w 2 := Int.gcd_dvd_left
  have hlk : (l : ℤ)∣(k : ℤ) := Int.gcd_dvd_right
  have hk3 : (k : ℤ)∣w 3 := Int.gcd_dvd_left
  have hk4 : (k : ℤ)∣w 4 := Int.gcd_dvd_right
  obtain ⟨z0,h0⟩ := hg0
  obtain ⟨z1,h1⟩ := hgm.trans hm1
  obtain ⟨z2,h2⟩ := (hgm.trans hml).trans hl2
  obtain ⟨z3,h3⟩ := ((hgm.trans hml).trans hlk).trans hk3
  obtain ⟨z4,h4⟩ := ((hgm.trans hml).trans hlk).trans hk4
  let z : Fin 5 → ℤ := ![z0,z1,z2,z3,z4]
  have hscale : ∀ i,w i=(g : ℤ)*z i := by intro i; fin_cases i <;> assumption
  let a := Int.gcdA (w 0) (m : ℤ)
  let b := Int.gcdB (w 0) (m : ℤ)
  let c := Int.gcdA (w 1) (l : ℤ)
  let d := Int.gcdB (w 1) (l : ℤ)
  let e := Int.gcdA (w 2) (k : ℤ)
  let f := Int.gcdB (w 2) (k : ℤ)
  let h := Int.gcdA (w 3) (w 4)
  let j := Int.gcdB (w 3) (w 4)
  have hb0 : (g : ℤ)=w 0*a+(m : ℤ)*b := Int.gcd_eq_gcd_ab _ _
  have hb1 : (m : ℤ)=w 1*c+(l : ℤ)*d := Int.gcd_eq_gcd_ab _ _
  have hb2 : (l : ℤ)=w 2*e+(k : ℤ)*f := Int.gcd_eq_gcd_ab _ _
  have hb3 : (k : ℤ)=w 3*h+w 4*j := Int.gcd_eq_gcd_ab _ _
  have heq : (g : ℤ)*(a*z0+(b*c)*z1+(b*d*e)*z2+(b*d*f*h)*z3+(b*d*f*j)*z4)=(g : ℤ)*1 := by
    calc
      _=w 0*a+(m : ℤ)*b := by rw [hb1,hb2,hb3,h0,h1,h2,h3,h4]; ring
      _=_ := by rw [← hb0]; ring
  have hgn : (g : ℤ)≠0 := by exact_mod_cast ne_of_gt hg
  refine ⟨g,hg,Int.gcd_dvd_left,z,?_,hscale⟩
  refine ⟨![a,b*c,b*d*e,b*d*f*h,b*d*f*j],?_⟩
  simpa [z,Fin.sum_univ_succ,add_assoc] using mul_left_cancel₀ hgn heq

theorem exists_primitive_sunit_five {x : Fin 6 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 5) :
    ∃ z : Fin 5 → ℤ,∃ s : fixedSUnitGroup,PrimitiveFive z ∧ z≠0 ∧
      ∀ i : Fin 5,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc := by
  obtain ⟨u1,hu1⟩ := hx.2.1 1
  obtain ⟨s1,hs1⟩ := sunit_denominator u1
  have hd1 : ((s1 : ℚˣ) : ℚ)=((x 1).den : ℚ) := by simpa [hu1] using hs1
  obtain ⟨u2,hu2⟩ := hx.2.1 2
  obtain ⟨s2,hs2⟩ := sunit_denominator u2
  have hd2 : ((s2 : ℚˣ) : ℚ)=((x 2).den : ℚ) := by simpa [hu2] using hs2
  obtain ⟨u3,hu3⟩ := hx.2.1 3
  obtain ⟨s3,hs3⟩ := sunit_denominator u3
  have hd3 : ((s3 : ℚˣ) : ℚ)=((x 3).den : ℚ) := by simpa [hu3] using hs3
  obtain ⟨u4,hu4⟩ := hx.2.1 4
  obtain ⟨s4,hs4⟩ := sunit_denominator u4
  have hd4 : ((s4 : ℚˣ) : ℚ)=((x 4).den : ℚ) := by simpa [hu4] using hs4
  let D : ℕ := (x 1).den*(x 2).den*(x 3).den*(x 4).den
  let s0 : fixedSUnitGroup := s1*s2*s3*s4
  let w : Fin 5 → ℤ := ![(D : ℤ),(x 1).num*(x 2).den*(x 3).den*(x 4).den,(x 2).num*(x 1).den*(x 3).den*(x 4).den,(x 3).num*(x 1).den*(x 2).den*(x 4).den,(x 4).num*(x 1).den*(x 2).den*(x 3).den]
  have hs0 : ((s0 : ℚˣ) : ℚ)=(D : ℚ) := by simp [s0,D,hd1,hd2,hd3,hd4]
  have hnum (i : Fin 6) : ((x i).num : ℚ)=((x i).den : ℚ)*x i := integralPair_scale (x i) 1
  have hw (i : Fin 5) : (w i : ℚ)=((s0 : ℚˣ) : ℚ)*x i.castSucc := by
    rw [hs0]
    fin_cases i
    · simp [w,hx.1]
    · change (((x 1).num*(x 2).den*(x 3).den*(x 4).den : ℤ) : ℚ)=(D : ℚ)*x 1
      push_cast
      rw [hnum]
      dsimp [D]
      push_cast
      ring
    · change (((x 2).num*(x 1).den*(x 3).den*(x 4).den : ℤ) : ℚ)=(D : ℚ)*x 2
      push_cast
      rw [hnum]
      dsimp [D]
      push_cast
      ring
    · change (((x 3).num*(x 1).den*(x 2).den*(x 4).den : ℤ) : ℚ)=(D : ℚ)*x 3
      push_cast
      rw [hnum]
      dsimp [D]
      push_cast
      ring
    · change (((x 4).num*(x 1).den*(x 2).den*(x 3).den : ℤ) : ℚ)=(D : ℚ)*x 4
      push_cast
      rw [hnum]
      dsimp [D]
      push_cast
      ring
  have hD : D≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (Rat.den_ne_zero _) (Rat.den_ne_zero _)) (Rat.den_ne_zero _)) (Rat.den_ne_zero _)
  have hw0 : w 0≠0 := by change (D : ℤ)≠0; exact_mod_cast hD
  obtain ⟨g,hg,hgdvd,z,hz,hscale⟩ := primitive_five_integer_reduction w hw0
  have hgD : g∣D := Int.natCast_dvd_natCast.mp hgdvd
  have hgsmooth : Smooth23 g := by
    intro p hp hpg
    rcases hp.dvd_mul.mp (hpg.trans hgD) with hp123|hp4
    · rcases hp.dvd_mul.mp hp123 with hp12|hp3
      · rcases hp.dvd_mul.mp hp12 with hp1|hp2
        · apply sunit_den_prime_support u1 p hp
          simpa [hu1] using hp1
        · apply sunit_den_prime_support u2 p hp
          simpa [hu2] using hp2
      · apply sunit_den_prime_support u3 p hp
        simpa [hu3] using hp3
    · apply sunit_den_prime_support u4 p hp
      simpa [hu4] using hp4
  obtain ⟨ug,hug⟩ := positive_smooth23_sunit4 (ne_of_gt hg) hgsmooth
  let s := s0/ug
  have hzscale (i : Fin 5) : (z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc := by
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
    simp [he,hx.1] at hh
    exact Units.ne_zero _ hh.symm
  exact ⟨z,s,hz,hnz,hzscale⟩

theorem exists_primitive_six_term_relation {x : Fin 6 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 5) :
    ∃ w : Fin 6 → ℤ,∃ s : fixedSUnitGroup,
      PrimitiveFive (fun i => w i.castSucc) ∧ (∀ i,w i≠0) ∧ (∑ i,w i=0) ∧
      Nondegenerate (fun i => (w i : ℚ)) ∧
      (∀ i,(w i : ℚ)=((s : ℚˣ) : ℚ)*x i) ∧
      (∀ i,x i=(w i : ℚ)/(w 0 : ℚ)) := by
  obtain ⟨z,s,hz,_,hscale⟩ := exists_primitive_sunit_five hx
  let w : Fin 6 → ℤ := ![z 0,z 1,z 2,z 3,z 4,-z 0-z 1-z 2-z 3-z 4]
  have hsum : x 0+x 1+x 2+x 3+x 4+x 5=0 := by simpa [Fin.sum_univ_succ,add_assoc] using hx.2.2.1
  have hw (i : Fin 6) : (w i : ℚ)=((s : ℚˣ) : ℚ)*x i := by
    have h0 := hscale 0
    have h1 := hscale 1
    have h2 := hscale 2
    have h3 := hscale 3
    change (z 0 : ℚ)=((s : ℚˣ) : ℚ)*x 0 at h0
    change (z 1 : ℚ)=((s : ℚˣ) : ℚ)*x 1 at h1
    change (z 2 : ℚ)=((s : ℚˣ) : ℚ)*x 2 at h2
    change (z 3 : ℚ)=((s : ℚˣ) : ℚ)*x 3 at h3
    have h4 := hscale 4
    change (z 4 : ℚ)=((s : ℚˣ) : ℚ)*x 4 at h4
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · change ((-z 0-z 1-z 2-z 3-z 4 : ℤ) : ℚ)=((s : ℚˣ) : ℚ)*x 5
      push_cast
      have hs : ((s : ℚˣ) : ℚ)*(x 0+x 1+x 2+x 3+x 4+x 5)=0 := by rw [hsum,mul_zero]
      nlinarith only [h0,h1,h2,h3,h4,hs]
  have he : (fun i : Fin 5 => w i.castSucc)=z := by ext i; fin_cases i <;> rfl
  refine ⟨w,s,he.symm ▸ hz,?_,?_,?_,hw,?_⟩
  · intro i hi
    obtain ⟨u,hu⟩ := hx.2.1 i
    have hn : x i≠0 := by rw [← hu]; exact Units.ne_zero _
    have hh := hw i
    rw [hi,Int.cast_zero] at hh
    exact (mul_ne_zero (Units.ne_zero _) hn) hh.symm
  · simp [w,Fin.sum_univ_succ]
  · intro I hI hproper hzero
    have hs : (∑ i∈I,(w i : ℚ))=((s : ℚˣ) : ℚ)*∑ i∈I,x i := by
      simp_rw [hw]
      rw [Finset.mul_sum]
    rw [hzero] at hs
    exact hx.2.2.2 I hI hproper ((mul_eq_zero.mp hs.symm).resolve_left (Units.ne_zero _))
  · intro i
    have h0 : (w 0 : ℚ)=((s : ℚˣ) : ℚ) := by simpa only [hx.1,mul_one] using hw 0
    rw [hw,h0]
    exact (mul_div_cancel_left₀ (x i) (Units.ne_zero _)).symm

end JSP000334
