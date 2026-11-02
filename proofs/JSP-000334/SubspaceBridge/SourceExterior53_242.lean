import SubspaceBridge.SourceCompoundConcrete240G
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior53_242

def lo242 : Fin 10 → Fin 5 := ![0,0,0,0,0,0,1,1,1,2]
def mid242 : Fin 10 → Fin 5 := ![1,1,1,2,2,3,2,2,3,3]
def hi242 : Fin 10 → Fin 5 := ![2,3,4,3,4,4,3,4,4,4]

theorem triple_lt242 : ∀ s, lo242 s < mid242 s ∧ mid242 s < hi242 s := by decide

def triple242 (s : Fin 10) : {a : Finset (Fin 5) // a.card = 3} :=
  ⟨{lo242 s,mid242 s,hi242 s},by
    have h : ∀ s : Fin 10, ({lo242 s,mid242 s,hi242 s} : Finset (Fin 5)).card = 3 := by decide
    exact h s⟩

theorem triple_bijective242 : Function.Bijective triple242 := by decide

def tripleIndex242 (s : Fin 10) : Fin 3 → Fin 5 := ![lo242 s,mid242 s,hi242 s]

def det3242 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*e*i+b*f*g+c*d*h-c*e*g-b*d*i-a*f*h

def wedge3242 {R : Type*} [CommRing R] (x y z : Fin 5 → R) : Fin 10 → R := fun s =>
  det3242 (x (lo242 s)) (y (lo242 s)) (z (lo242 s))
    (x (mid242 s)) (y (mid242 s)) (z (mid242 s)) (x (hi242 s)) (y (hi242 s)) (z (hi242 s))

def compound3242 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    Matrix (Fin 10) (Fin 10) R := fun s t =>
  det3242 (A (lo242 s) (lo242 t)) (A (lo242 s) (mid242 t)) (A (lo242 s) (hi242 t))
    (A (mid242 s) (lo242 t)) (A (mid242 s) (mid242 t)) (A (mid242 s) (hi242 t))
    (A (hi242 s) (lo242 t)) (A (hi242 s) (mid242 t)) (A (hi242 s) (hi242 t))

theorem compound_minor3242 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) (s t : Fin 10) :
    compound3242 A s t = (A.submatrix (tripleIndex242 s) (tripleIndex242 t)).det := by
  simp [compound3242,det3242,Matrix.det_fin_three,tripleIndex242,Matrix.submatrix_apply]
  ring

theorem wedge_transform3242 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R)
    (x y z : Fin 5 → R) :
    compound3242 A *ᵥ wedge3242 x y z = wedge3242 (A *ᵥ x) (A *ᵥ y) (A *ᵥ z) := by
  ext s
  simp [compound3242,wedge3242,det3242,lo242,mid242,hi242,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem compound_mul3242 {R : Type*} [CommRing R] (A B : Matrix (Fin 5) (Fin 5) R) :
    compound3242 (A*B) = compound3242 A*compound3242 B := by
  ext s t
  simp [compound3242,det3242,lo242,mid242,hi242,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

theorem compound_upper3242 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R)
    (hA : A.BlockTriangular id) : (compound3242 A).BlockTriangular id := by
  have term (a b c d e f : Fin 5) (h : d<a ∨ e<b ∨ f<c) : A a d*A b e*A c f=0 := by
    rcases h with h | h | h <;> simp [hA h]
  have order : ∀ s t : Fin 10, t<s →
      (lo242 t<lo242 s ∨ mid242 t<mid242 s ∨ hi242 t<hi242 s) ∧
      (mid242 t<lo242 s ∨ hi242 t<mid242 s ∨ lo242 t<hi242 s) ∧
      (hi242 t<lo242 s ∨ lo242 t<mid242 s ∨ mid242 t<hi242 s) ∧
      (hi242 t<lo242 s ∨ mid242 t<mid242 s ∨ lo242 t<hi242 s) ∧
      (mid242 t<lo242 s ∨ lo242 t<mid242 s ∨ hi242 t<hi242 s) ∧
      (lo242 t<lo242 s ∨ hi242 t<mid242 s ∨ mid242 t<hi242 s) := by decide
  intro s t h
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := order s t h
  change _+_+_-_-_-_=0
  rw [term _ _ _ _ _ _ h1,term _ _ _ _ _ _ h2,term _ _ _ _ _ _ h3,
    term _ _ _ _ _ _ h4,term _ _ _ _ _ _ h5,term _ _ _ _ _ _ h6]
  ring

theorem compound_upper_det3242 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R)
    (hA : A.BlockTriangular id) : (compound3242 A).det = A.det^6 := by
  rw [Matrix.det_of_upperTriangular (compound_upper3242 A hA),Matrix.det_of_upperTriangular hA]
  have he (s : Fin 10) : compound3242 A s s =
      A (lo242 s) (lo242 s)*A (mid242 s) (mid242 s)*A (hi242 s) (hi242 s) := by
    have h1 := hA (triple_lt242 s).1
    have h2 := hA (lt_trans (triple_lt242 s).1 (triple_lt242 s).2)
    have h3 := hA (triple_lt242 s).2
    change A (mid242 s) (lo242 s) = 0 at h1
    change A (hi242 s) (lo242 s) = 0 at h2
    change A (hi242 s) (mid242 s) = 0 at h3
    simp only [compound3242,det3242,h1,h2,h3,mul_zero,zero_mul,add_zero,sub_zero]
  simp_rw [he]
  simp [lo242,mid242,hi242,Fin.prod_univ_succ]
  ring

theorem compound_transpose3242 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    compound3242 A.transpose = (compound3242 A).transpose := by
  ext s t
  simp only [compound3242,det3242,Matrix.transpose_apply]
  ring

theorem compound_transvection_det3242 {R : Type*} [CommRing R] (i j : Fin 5)
    (hij : i ≠ j) (c : R) : (compound3242 (Matrix.transvection i j c)).det = 1 := by
  have upper (a b : Fin 5) (hab : a < b) :
      (Matrix.transvection a b c : Matrix (Fin 5) (Fin 5) R).BlockTriangular id := by
    intro s t hts
    have hne : s ≠ t := ne_of_gt hts
    have hentry : ¬ (a = s ∧ b = t) := by
      rintro ⟨rfl,rfl⟩
      exact (not_lt_of_ge hab.le) hts
    simp [Matrix.transvection,Matrix.stdBasisMatrix,Matrix.one_apply,hne,hentry]
  by_cases h : i < j
  · rw [compound_upper_det3242 _ (upper i j h),Matrix.det_transvection_of_ne _ _ hij,one_pow]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij)
    have ht : (Matrix.transvection j i c : Matrix (Fin 5) (Fin 5) R).transpose =
        Matrix.transvection i j c := by
      simp [Matrix.transvection,Matrix.transpose_add,Matrix.transpose_stdBasisMatrix]
    rw [← ht,compound_transpose3242,Matrix.det_transpose,
      compound_upper_det3242 _ (upper j i hji),Matrix.det_transvection_of_ne _ _ (Ne.symm hij),one_pow]

def compoundDet3242Property {R : Type*} [CommRing R]
    (A : Matrix (Fin 5) (Fin 5) R) : Prop := (compound3242 A).det = A.det^6

attribute [local irreducible] compoundDet3242Property

theorem compoundDet3242Property_diagonal {R : Type*} [CommRing R] (D : Fin 5 → R) :
    compoundDet3242Property (Matrix.diagonal D) := by
  unfold compoundDet3242Property
  exact compound_upper_det3242 (Matrix.diagonal D) (Matrix.blockTriangular_diagonal D)

theorem compoundDet3242Property_transvection {R : Type*} [CommRing R]
    (t : Matrix.TransvectionStruct (Fin 5) R) : compoundDet3242Property t.toMatrix := by
  unfold compoundDet3242Property
  have hc := @compound_transvection_det3242 R _ t.i t.j t.hij t.c
  rw [t.det,one_pow]
  simpa only [Matrix.TransvectionStruct.toMatrix] using hc

theorem compoundDet3242Property_mul {R : Type*} [CommRing R]
    (M N : Matrix (Fin 5) (Fin 5) R)
    (hM : compoundDet3242Property M) (hN : compoundDet3242Property N) :
    compoundDet3242Property (M*N) := by
  unfold compoundDet3242Property at hM hN ⊢
  rw [compound_mul3242,Matrix.det_mul,hM,hN,Matrix.det_mul,mul_pow]

theorem compound_rat_property3242 (A : Matrix (Fin 5) (Fin 5) ℚ) : compoundDet3242Property A := by
  apply Matrix.diagonal_transvection_induction compoundDet3242Property
  · intro D _
    exact compoundDet3242Property_diagonal D
  · exact compoundDet3242Property_transvection
  · exact compoundDet3242Property_mul

theorem compound_rat_det_one3242 (A : Matrix (Fin 5) (Fin 5) ℚ) (hA : A.det=1) :
    (compound3242 A).det=1 := by
  have h := compound_rat_property3242 A
  unfold compoundDet3242Property at h
  rw [h,hA,one_pow]

theorem compound_real_property3242 (A : Matrix (Fin 5) (Fin 5) ℝ) : compoundDet3242Property A := by
  apply Matrix.diagonal_transvection_induction compoundDet3242Property
  · intro D _
    exact compoundDet3242Property_diagonal D
  · exact compoundDet3242Property_transvection
  · exact compoundDet3242Property_mul

theorem compound_real_det_one3242 (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.det=1) :
    (compound3242 A).det=1 := by
  have h := compound_real_property3242 A
  unfold compoundDet3242Property at h
  rw [h,hA,one_pow]

def tripleEquiv242 : Fin 10 ≃ {a : Finset (Fin 5) // a.card=3} :=
  Equiv.ofBijective triple242 triple_bijective242

theorem wedge_cast3242 {R : Type*} [CommRing R] (x y z : Fin 5 → ℤ) :
    (fun s => (wedge3242 (R := ℤ) x y z s : R)) =
      wedge3242 (fun i => (x i : R)) (fun i => (y i : R)) (fun i => (z i : R)) := by
  ext s
  simp only [wedge3242,det3242,Int.cast_sub,Int.cast_add,Int.cast_mul]

theorem compound_algebraic3242 (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : ∀ i j, IsAlgebraic ℚ (L i j)) : ∀ s t, IsAlgebraic ℚ (compound3242 L s t) := by
  intro s t
  unfold compound3242 det3242
  exact (((((hL _ _).mul (hL _ _)).mul (hL _ _)).add
    (((hL _ _).mul (hL _ _)).mul (hL _ _))).add
    (((hL _ _).mul (hL _ _)).mul (hL _ _))).sub
    (((hL _ _).mul (hL _ _)).mul (hL _ _)) |>.sub
    (((hL _ _).mul (hL _ _)).mul (hL _ _)) |>.sub
    (((hL _ _).mul (hL _ _)).mul (hL _ _))

theorem compound_rat_unit3242 (A : Matrix (Fin 5) (Fin 5) ℚ) (hA : IsUnit A) :
    IsUnit (compound3242 A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h := compound_rat_property3242 A
  unfold compoundDet3242Property at h
  rw [h]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA).pow 6

theorem compound_real_unit3242 (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : IsUnit A) :
    IsUnit (compound3242 A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h := compound_real_property3242 A
  unfold compoundDet3242Property at h
  rw [h]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA).pow 6

theorem compoundFrame_independent3242 (u : Fin 5 → Fin 5 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) :
    LinearIndependent ℝ (fun s => integerReal
      (wedge3242 (u (lo242 s)) (u (mid242 s)) (u (hi242 s)))) := by
  have he : (fun s => integerReal (wedge3242 (u (lo242 s)) (u (mid242 s)) (u (hi242 s)))) =
      compound3242 (fun j i => (u j i : ℝ)) := by
    funext s t
    change ((wedge3242 (R := ℤ) (u (lo242 s)) (u (mid242 s)) (u (hi242 s)) t : ℤ) : ℝ) = _
    simp only [wedge3242,det3242,Int.cast_sub,Int.cast_add,Int.cast_mul,compound3242]
    ring
  rw [he]
  have hU : IsUnit (show Matrix (Fin 5) (Fin 5) ℝ from fun j i => (u j i : ℝ)) := Matrix.linearIndependent_rows_iff_isUnit.mp hu
  have hC := compound_real_unit3242 (fun j i => (u j i : ℝ)) hU
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hC

end CompoundFeasibility.Exterior53_242
