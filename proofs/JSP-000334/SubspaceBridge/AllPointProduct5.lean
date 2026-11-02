import SubspaceBridge.AllPointForms5
import SubspaceBridge.AllPointPrimitive5
open scoped BigOperators Matrix
namespace JSP000334

def fiveRetainedForm (k i : Fin 5) (y : Fin 5 → ℚ) : ℚ := if i=k then ∑ j,y j else y i

def localFiveHeight (tau : Fin 3) (y : Fin 5 → ℚ) : ℚ :=
  max (rationalPlaceNorm tau (y 0)) (max (rationalPlaceNorm tau (y 1))
    (max (rationalPlaceNorm tau (y 2)) (max (rationalPlaceNorm tau (y 3)) (rationalPlaceNorm tau (y 4)))))

def fiveHeight (y : Fin 5 → ℚ) : ℚ := ∏ tau : Fin 3,localFiveHeight tau y

def archFiveHeight (z : Fin 5 → ℤ) : ℚ :=
  max |(z 0 : ℚ)| (max |(z 1 : ℚ)| (max |(z 2 : ℚ)| (max |(z 3 : ℚ)| |(z 4 : ℚ)|)))

def fiveRetainedProduct (choice : Fin 3 → Fin 5) (y : Fin 5 → ℚ) : ℚ :=
  ∏ tau : Fin 3,∏ i : Fin 5,rationalPlaceNorm tau (fiveRetainedForm (choice tau) i y)

theorem five_local_coordinate_le (tau : Fin 3) (y : Fin 5 → ℚ) (i : Fin 5) :
    rationalPlaceNorm tau (y i)≤localFiveHeight tau y := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem primitive_five_local_height (z : Fin 5 → ℤ) (hz : PrimitiveFive z)
    (p : ℕ) [Fact p.Prime] :
    max (padicNorm p (z 0 : ℚ)) (max (padicNorm p (z 1 : ℚ))
      (max (padicNorm p (z 2 : ℚ)) (max (padicNorm p (z 3 : ℚ)) (padicNorm p (z 4 : ℚ)))))=1 := by
  obtain ⟨c,hc⟩ := hz
  obtain ⟨i,hi⟩ : ∃ i : Fin 5,¬(p : ℤ)∣z i := by
    by_contra hn
    push_neg at hn
    have hd : (p : ℤ)∣∑ i,c i*z i := Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hn i) _)
    rw [hc] at hd
    exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp hd)
  have he := (padicNorm.int_eq_one_iff (p := p) (z i)).mpr hi
  apply le_antisymm
  · exact max_le (padicNorm.of_int _) (max_le (padicNorm.of_int _)
      (max_le (padicNorm.of_int _) (max_le (padicNorm.of_int _) (padicNorm.of_int _))))
  · rw [← he]
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem primitive_five_height (z : Fin 5 → ℤ) (hz : PrimitiveFive z) :
    fiveHeight (fun i => (z i : ℚ))=archFiveHeight z := by
  simp only [fiveHeight,Fin.prod_univ_three]
  change archFiveHeight z *
    (max (padicNorm 2 (z 0 : ℚ)) (max (padicNorm 2 (z 1 : ℚ))
      (max (padicNorm 2 (z 2 : ℚ)) (max (padicNorm 2 (z 3 : ℚ)) (padicNorm 2 (z 4 : ℚ)))))) *
    (max (padicNorm 3 (z 0 : ℚ)) (max (padicNorm 3 (z 1 : ℚ))
      (max (padicNorm 3 (z 2 : ℚ)) (max (padicNorm 3 (z 3 : ℚ)) (padicNorm 3 (z 4 : ℚ))))))=_
  rw [primitive_five_local_height z hz 2,primitive_five_local_height z hz 3]
  ring

theorem exists_five_maximal_coordinate (tau : Fin 3) (y : Fin 5 → ℚ) :
    ∃ k : Fin 5,rationalPlaceNorm tau (y k)=localFiveHeight tau y := by
  obtain ⟨k,_,hk⟩ := Finset.exists_max_image Finset.univ (fun i => rationalPlaceNorm tau (y i)) Finset.univ_nonempty
  refine ⟨k,le_antisymm (five_local_coordinate_le tau y k) ?_⟩
  exact max_le (hk 0 (Finset.mem_univ _)) (max_le (hk 1 (Finset.mem_univ _))
    (max_le (hk 2 (Finset.mem_univ _)) (max_le (hk 3 (Finset.mem_univ _)) (hk 4 (Finset.mem_univ _)))))

theorem five_retained_product_height (choice : Fin 3 → Fin 5) (y : Fin 5 → ℚ)
    (hchoice : ∀ tau,rationalPlaceNorm tau (y (choice tau))=localFiveHeight tau y) :
    fiveRetainedProduct choice y*fiveHeight y=
      (∏ i : Fin 5,threePlaceProduct (y i))*threePlaceProduct (∑ i,y i) := by
  have hlocal (tau : Fin 3) : (∏ i : Fin 5,rationalPlaceNorm tau (fiveRetainedForm (choice tau) i y))*
      localFiveHeight tau y=(∏ i : Fin 5,rationalPlaceNorm tau (y i))*rationalPlaceNorm tau (∑ i,y i) := by
    rw [← hchoice tau]
    generalize choice tau=k
    fin_cases k <;> simp [fiveRetainedForm,Fin.prod_univ_succ] <;> ring
  unfold fiveRetainedProduct fiveHeight
  rw [← Finset.prod_mul_distrib]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib,Finset.prod_comm]
  simp_rw [rationalPlaceNorm_product]

end JSP000334
