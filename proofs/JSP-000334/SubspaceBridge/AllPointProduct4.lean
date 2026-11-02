import SubspaceBridge.AllPointForms4
import SubspaceBridge.AllPointPrimitive4
open scoped BigOperators Matrix
namespace JSP000334

def fourRetainedForm (k i : Fin 4) (y : Fin 4 → ℚ) : ℚ := if i=k then ∑ j,y j else y i

def localFourHeight (tau : Fin 3) (y : Fin 4 → ℚ) : ℚ :=
  max (rationalPlaceNorm tau (y 0)) (max (rationalPlaceNorm tau (y 1))
    (max (rationalPlaceNorm tau (y 2)) (rationalPlaceNorm tau (y 3))))

def fourHeight (y : Fin 4 → ℚ) : ℚ := ∏ tau : Fin 3,localFourHeight tau y

def archFourHeight (z : Fin 4 → ℤ) : ℚ :=
  max |(z 0 : ℚ)| (max |(z 1 : ℚ)| (max |(z 2 : ℚ)| |(z 3 : ℚ)|))

def fourRetainedProduct (choice : Fin 3 → Fin 4) (y : Fin 4 → ℚ) : ℚ :=
  ∏ tau : Fin 3,∏ i : Fin 4,rationalPlaceNorm tau (fourRetainedForm (choice tau) i y)

theorem four_local_coordinate_le (tau : Fin 3) (y : Fin 4 → ℚ) (i : Fin 4) :
    rationalPlaceNorm tau (y i)≤localFourHeight tau y := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem primitive_four_local_height (z : Fin 4 → ℤ) (hz : PrimitiveFour z)
    (p : ℕ) [Fact p.Prime] :
    max (padicNorm p (z 0 : ℚ)) (max (padicNorm p (z 1 : ℚ))
      (max (padicNorm p (z 2 : ℚ)) (padicNorm p (z 3 : ℚ))))=1 := by
  obtain ⟨c,hc⟩ := hz
  obtain ⟨i,hi⟩ : ∃ i : Fin 4,¬(p : ℤ)∣z i := by
    by_contra hn
    push_neg at hn
    have hd : (p : ℤ)∣∑ i,c i*z i := Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hn i) _)
    rw [hc] at hd
    exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp hd)
  have he := (padicNorm.int_eq_one_iff (p := p) (z i)).mpr hi
  apply le_antisymm
  · exact max_le (padicNorm.of_int _) (max_le (padicNorm.of_int _)
      (max_le (padicNorm.of_int _) (padicNorm.of_int _)))
  · rw [← he]
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem primitive_four_height (z : Fin 4 → ℤ) (hz : PrimitiveFour z) :
    fourHeight (fun i => (z i : ℚ))=archFourHeight z := by
  simp only [fourHeight,Fin.prod_univ_three]
  change archFourHeight z *
    (max (padicNorm 2 (z 0 : ℚ)) (max (padicNorm 2 (z 1 : ℚ))
      (max (padicNorm 2 (z 2 : ℚ)) (padicNorm 2 (z 3 : ℚ))))) *
    (max (padicNorm 3 (z 0 : ℚ)) (max (padicNorm 3 (z 1 : ℚ))
      (max (padicNorm 3 (z 2 : ℚ)) (padicNorm 3 (z 3 : ℚ)))))=_
  rw [primitive_four_local_height z hz 2,primitive_four_local_height z hz 3]
  ring

theorem exists_four_maximal_coordinate (tau : Fin 3) (y : Fin 4 → ℚ) :
    ∃ k : Fin 4,rationalPlaceNorm tau (y k)=localFourHeight tau y := by
  let f := fun i => rationalPlaceNorm tau (y i)
  have hex : ∃ k : Fin 4,f k=max (f 0) (max (f 1) (max (f 2) (f 3))) := by
    rcases le_total (f 2) (f 3) with h|h
    · rw [max_eq_right h]
      rcases le_total (f 1) (f 3) with h|h
      · rw [max_eq_right h]
        rcases le_total (f 0) (f 3) with h|h
        · exact ⟨3,(max_eq_right h).symm⟩
        · exact ⟨0,(max_eq_left h).symm⟩
      · rw [max_eq_left h]
        rcases le_total (f 0) (f 1) with h|h
        · exact ⟨1,(max_eq_right h).symm⟩
        · exact ⟨0,(max_eq_left h).symm⟩
    · rw [max_eq_left h]
      rcases le_total (f 1) (f 2) with h|h
      · rw [max_eq_right h]
        rcases le_total (f 0) (f 2) with h|h
        · exact ⟨2,(max_eq_right h).symm⟩
        · exact ⟨0,(max_eq_left h).symm⟩
      · rw [max_eq_left h]
        rcases le_total (f 0) (f 1) with h|h
        · exact ⟨1,(max_eq_right h).symm⟩
        · exact ⟨0,(max_eq_left h).symm⟩
  exact hex

theorem four_retained_product_height (choice : Fin 3 → Fin 4) (y : Fin 4 → ℚ)
    (hchoice : ∀ tau,rationalPlaceNorm tau (y (choice tau))=localFourHeight tau y) :
    fourRetainedProduct choice y*fourHeight y=
      (∏ i : Fin 4,threePlaceProduct (y i))*threePlaceProduct (∑ i,y i) := by
  have hlocal (tau : Fin 3) : (∏ i : Fin 4,rationalPlaceNorm tau (fourRetainedForm (choice tau) i y))*
      localFourHeight tau y=(∏ i : Fin 4,rationalPlaceNorm tau (y i))*rationalPlaceNorm tau (∑ i,y i) := by
    rw [← hchoice tau]
    generalize choice tau=k
    fin_cases k <;> simp [fourRetainedForm,Fin.prod_univ_succ] <;> ring
  unfold fourRetainedProduct fourHeight
  rw [← Finset.prod_mul_distrib]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib,Finset.prod_comm]
  simp_rw [rationalPlaceNorm_product]

end JSP000334
