import ElementaryThreeTerm
import SubspaceBridge.AllPointSourceExtraction4
namespace JSP000334
open scoped BigOperators

def PrimitiveFour (z : Fin 4 → ℤ) : Prop := ∃ c : Fin 4 → ℤ,∑ i,c i*z i=1

theorem primitive_four_integer_reduction (w : Fin 4 → ℤ) (hw0 : w 0≠0) :
    ∃ g : ℕ,0<g ∧ (g : ℤ)∣w 0 ∧ ∃ z : Fin 4 → ℤ,
      PrimitiveFour z ∧ ∀ i,w i=(g : ℤ)*z i := by
  let k := Int.gcd (w 2) (w 3)
  let l := Int.gcd (w 1) (k : ℤ)
  let g := Int.gcd (w 0) (l : ℤ)
  have hg : 0<g := Int.gcd_pos_of_ne_zero_left _ hw0
  have hg0 : (g : ℤ)∣w 0 := Int.gcd_dvd_left
  have hgl : (g : ℤ)∣(l : ℤ) := Int.gcd_dvd_right
  have hl1 : (l : ℤ)∣w 1 := Int.gcd_dvd_left
  have hlk : (l : ℤ)∣(k : ℤ) := Int.gcd_dvd_right
  have hk2 : (k : ℤ)∣w 2 := Int.gcd_dvd_left
  have hk3 : (k : ℤ)∣w 3 := Int.gcd_dvd_right
  obtain ⟨z0,h0⟩ := hg0
  obtain ⟨z1,h1⟩ := hgl.trans hl1
  obtain ⟨z2,h2⟩ := (hgl.trans hlk).trans hk2
  obtain ⟨z3,h3⟩ := (hgl.trans hlk).trans hk3
  let z : Fin 4 → ℤ := ![z0,z1,z2,z3]
  have hscale : ∀ i,w i=(g : ℤ)*z i := by intro i; fin_cases i <;> assumption
  let a := Int.gcdA (w 0) (l : ℤ)
  let b := Int.gcdB (w 0) (l : ℤ)
  let c := Int.gcdA (w 1) (k : ℤ)
  let d := Int.gcdB (w 1) (k : ℤ)
  let e := Int.gcdA (w 2) (w 3)
  let f := Int.gcdB (w 2) (w 3)
  have hb0 : (g : ℤ)=w 0*a+(l : ℤ)*b := Int.gcd_eq_gcd_ab _ _
  have hb1 : (l : ℤ)=w 1*c+(k : ℤ)*d := Int.gcd_eq_gcd_ab _ _
  have hb2 : (k : ℤ)=w 2*e+w 3*f := Int.gcd_eq_gcd_ab _ _
  have heq : (g : ℤ)*(a*z0+(b*c)*z1+(b*d*e)*z2+(b*d*f)*z3)=(g : ℤ)*1 := by
    calc
      _=w 0*a+(l : ℤ)*b := by rw [hb1,hb2,h0,h1,h2,h3]; ring
      _=_ := by rw [← hb0]; ring
  have hgn : (g : ℤ)≠0 := by exact_mod_cast ne_of_gt hg
  refine ⟨g,hg,Int.gcd_dvd_left,z,?_,hscale⟩
  refine ⟨![a,b*c,b*d*e,b*d*f],?_⟩
  simpa [z,Fin.sum_univ_succ,add_assoc] using mul_left_cancel₀ hgn heq

theorem positive_smooth23_sunit4 {g : ℕ} (hg : g≠0) (hs : Smooth23 g) :
    ∃ u : fixedSUnitGroup,((u : ℚˣ) : ℚ)=(g : ℚ) := by
  have htwo : twoUnit∈fixedSUnitGroup := Subgroup.subset_closure (by simp)
  have hthree : threeUnit∈fixedSUnitGroup := Subgroup.subset_closure (by simp)
  refine ⟨⟨twoUnit^g.factorization 2*threeUnit^g.factorization 3,
    fixedSUnitGroup.mul_mem (fixedSUnitGroup.pow_mem htwo _) (fixedSUnitGroup.pow_mem hthree _)⟩,?_⟩
  simpa [twoUnit,threeUnit] using congrArg ((↑) : ℕ → ℚ) (smooth23_factorization hg hs).symm

theorem exists_primitive_sunit_four {x : Fin 5 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 4) :
    ∃ z : Fin 4 → ℤ,∃ s : fixedSUnitGroup,PrimitiveFour z ∧ z≠0 ∧
      ∀ i : Fin 4,(z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc := by
  obtain ⟨u1,hu1⟩ := hx.2.1 1
  obtain ⟨u2,hu2⟩ := hx.2.1 2
  obtain ⟨u3,hu3⟩ := hx.2.1 3
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
  have hnum (i : Fin 5) : ((x i).num : ℚ)=((x i).den : ℚ)*x i := integralPair_scale (x i) 1
  have hw (i : Fin 4) : (w i : ℚ)=((s0 : ℚˣ) : ℚ)*x i.castSucc := by
    rw [hs0]
    fin_cases i
    · simp [w,hx.1]
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
  have hzscale (i : Fin 4) : (z i : ℚ)=((s : ℚˣ) : ℚ)*x i.castSucc := by
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

theorem exists_primitive_five_term_relation {x : Fin 5 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 4) :
    ∃ w : Fin 5 → ℤ,∃ s : fixedSUnitGroup,
      PrimitiveFour (fun i => w i.castSucc) ∧ (∀ i,w i≠0) ∧ (∑ i,w i=0) ∧
      Nondegenerate (fun i => (w i : ℚ)) ∧
      (∀ i,(w i : ℚ)=((s : ℚˣ) : ℚ)*x i) ∧
      (∀ i,x i=(w i : ℚ)/(w 0 : ℚ)) := by
  obtain ⟨z,s,hz,_,hscale⟩ := exists_primitive_sunit_four hx
  let w : Fin 5 → ℤ := ![z 0,z 1,z 2,z 3,-z 0-z 1-z 2-z 3]
  have hsum : x 0+x 1+x 2+x 3+x 4=0 := by simpa [Fin.sum_univ_succ,add_assoc] using hx.2.2.1
  have hw (i : Fin 5) : (w i : ℚ)=((s : ℚˣ) : ℚ)*x i := by
    have h0 := hscale 0
    have h1 := hscale 1
    have h2 := hscale 2
    have h3 := hscale 3
    change (z 0 : ℚ)=((s : ℚˣ) : ℚ)*x 0 at h0
    change (z 1 : ℚ)=((s : ℚˣ) : ℚ)*x 1 at h1
    change (z 2 : ℚ)=((s : ℚˣ) : ℚ)*x 2 at h2
    change (z 3 : ℚ)=((s : ℚˣ) : ℚ)*x 3 at h3
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · change ((-z 0-z 1-z 2-z 3 : ℤ) : ℚ)=((s : ℚˣ) : ℚ)*x 4
      push_cast
      have hs : ((s : ℚˣ) : ℚ)*(x 0+x 1+x 2+x 3+x 4)=0 := by rw [hsum,mul_zero]
      nlinarith only [h0,h1,h2,h3,hs]
  have he : (fun i : Fin 4 => w i.castSucc)=z := by ext i; fin_cases i <;> rfl
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
