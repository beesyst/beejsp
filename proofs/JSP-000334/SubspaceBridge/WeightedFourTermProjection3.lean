import SubspaceBridge.WeightedFourTermCover3
import SubspaceBridge.FourTermSource3
namespace JSP000334
open scoped BigOperators Matrix

def weightedFourTermValues3 (p : fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup) : Fin 3 → ℚ :=
  ![((p.1 : ℚˣ) : ℚ),((p.2.1 : ℚˣ) : ℚ),((p.2.2 : ℚˣ) : ℚ)]

def weightedFourTermCoefficientFiber3 (A B C D b0 b1 b2 : ℚ) :
    Set (fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup) :=
  {p | p∈WeightedFourTermSolutions A B C D ∧
    b0*((p.1 : ℚˣ) : ℚ)+b1*((p.2.1 : ℚˣ) : ℚ)+b2*((p.2.2 : ℚˣ) : ℚ)=0}

theorem weighted_four_term_values_injective3 : Function.Injective weightedFourTermValues3 := by
  intro p q he
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    exact congrFun he 0
  · apply Prod.ext
    · apply Subtype.ext
      apply Units.ext
      exact congrFun he 1
    · apply Subtype.ext
      apply Units.ext
      exact congrFun he 2

theorem weighted_four_term_pair_sums3 {A B C D : ℚ}
    {p : fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup}
    (hp : p∈WeightedFourTermSolutions A B C D) :
    B*((p.1 : ℚˣ) : ℚ)+C*((p.2.1 : ℚˣ) : ℚ)≠0 ∧
    B*((p.1 : ℚˣ) : ℚ)+D*((p.2.2 : ℚˣ) : ℚ)≠0 ∧
    C*((p.2.1 : ℚˣ) : ℚ)+D*((p.2.2 : ℚˣ) : ℚ)≠0 := by
  refine ⟨?_,?_,?_⟩
  · simpa using hp.2 ({1,2} : Finset (Fin 4)) (by decide) (by decide)
  · simpa using hp.2 ({1,3} : Finset (Fin 4)) (by decide) (by decide)
  · simpa using hp.2 ({2,3} : Finset (Fin 4)) (by decide) (by decide)

theorem weighted_four_term_projection_finite3
    (S : Set (fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup))
    (A B C : ℚ) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (f : (fixedSUnitGroup × fixedSUnitGroup × fixedSUnitGroup) → fixedSUnitGroup × fixedSUnitGroup)
    (recover : ℚ → ℚ → Fin 3 → ℚ)
    (heq : ∀ p∈S,A+B*(((f p).1 : ℚˣ) : ℚ)+C*(((f p).2 : ℚˣ) : ℚ)=0)
    (hrec : ∀ p∈S,recover (((f p).1 : ℚˣ) : ℚ) (((f p).2 : ℚˣ) : ℚ)=weightedFourTermValues3 p) :
    S.Finite := by
  have hf : (weightedFourTermValues3 '' S).Finite := by
    apply ((weighted_fixed_sunit_pair_finite A B C hA hB hC).image
      (fun q : fixedSUnitGroup × fixedSUnitGroup => recover ((q.1 : ℚˣ) : ℚ) ((q.2 : ℚˣ) : ℚ))).subset
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨f p,heq p hp,hrec p hp⟩
  exact hf.of_finite_image weighted_four_term_values_injective3.injOn

theorem weighted_four_term_ratio_values3 (A B C D u v w : ℚ)
    (hA : A≠0) (hu : u≠0) (he : A+B*u+C*v+D*w=0) :
    B+C*(v/u)+D*(w/u)≠0 ∧
    u=-A/(B+C*(v/u)+D*(w/u)) ∧ v=(v/u)*u ∧ w=(w/u)*u := by
  have hv : v=(v/u)*u := by field_simp
  have hw : w=(w/u)*u := by field_simp
  have hscale : A+(B+C*(v/u)+D*(w/u))*u=0 := by
    rw [hv,hw] at he
    linear_combination he
  have hd : B+C*(v/u)+D*(w/u)≠0 := by
    intro h
    rw [h,zero_mul,add_zero] at hscale
    exact hA hscale
  refine ⟨hd,?_,hv,hw⟩
  apply (eq_div_iff hd).mpr
  nlinarith only [hscale]

end JSP000334
