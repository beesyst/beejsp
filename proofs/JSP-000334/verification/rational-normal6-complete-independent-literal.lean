import SubspaceBridge.SchmidtScalarDehomogenization6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtRationalNormalization6Literal
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SchmidtNormalSubstitution6 SchmidtExcessElimination6
open SchmidtScalarDehomogenization6 SourceSchmidtParameters6 SourceReadiness6

def rootNumerator6 (a b : ℤ) : ℤ := (-b)/(Int.gcd a b : ℤ)

def rootDenominator6 (a b : ℤ) : ℤ := a/(Int.gcd a b : ℤ)

theorem integer_normalization6 (a b : ℤ) (ha : a ≠ 0) :
    0 < Int.gcd a b ∧ (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b ∧
      a = (Int.gcd a b : ℤ)*rootDenominator6 a b ∧
      b = -((Int.gcd a b : ℤ)*rootNumerator6 a b) ∧
      rootDenominator6 a b ≠ 0 ∧ Int.gcd (rootNumerator6 a b) (rootDenominator6 a b) = 1 := by
  have hp := Int.gcd_pos_of_ne_zero_left b ha
  have heq : (Int.gcd a b : ℤ)*rootDenominator6 a b = a := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel Int.gcd_dvd_left
  have hneg : (Int.gcd a b : ℤ)*rootNumerator6 a b = -b := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (dvd_neg.mpr Int.gcd_dvd_right)
  have hn : rootDenominator6 a b ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at heq
    exact ha heq.symm
  have hg : Int.gcd (-b) a = Int.gcd a b := by simp [Int.gcd,Nat.gcd_comm]
  have hc := Int.gcd_div_gcd_div_gcd (i := -b) (j := a) (hg.symm ▸ hp)
  rw [hg] at hc
  exact ⟨hp,Int.gcd_dvd_left,Int.gcd_dvd_right,heq.symm,by rw [hneg,neg_neg],hn,hc⟩

theorem negative_denominator6 (a b : ℤ) (ha : a < 0) : rootDenominator6 a b < 0 := by
  obtain ⟨hg,_,_,heq,_,_,_⟩ := integer_normalization6 a b (ne_of_lt ha)
  have hgz : 0 < (Int.gcd a b : ℤ) := by exact_mod_cast hg
  by_contra! hq
  have hp := mul_nonneg hgz.le hq
  linarith

theorem root_ratio6 {K : Type*} [Field K] [CharZero K] (a b : ℤ) (ha : a ≠ 0) :
    (rootNumerator6 a b : K)/(rootDenominator6 a b : K) = -(b : K)/(a : K) := by
  obtain ⟨hg,_,_,heq,hbeq,hqn,_⟩ := integer_normalization6 a b ha
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  have hqK : (rootDenominator6 a b : K) ≠ 0 := by exact_mod_cast hqn
  have heqK : (a : K) = (Int.gcd a b : K)*(rootDenominator6 a b : K) := by exact_mod_cast heq
  have hbeqK : (b : K) = -((Int.gcd a b : K)*(rootNumerator6 a b : K)) := by exact_mod_cast hbeq
  apply (div_eq_div_iff hqK haK).mpr
  rw [heqK,hbeqK]
  ring

theorem monic_generator6 {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (a b : ℤ) (ha : a ≠ 0) (h : Fin m) :
    (MvPolynomial.C (a : K)*MvPolynomial.X h + MvPolynomial.C (b : K) : MvPolynomial (Fin m) K) =
      MvPolynomial.C (a : K)*(MvPolynomial.X h -
        MvPolynomial.C ((rootNumerator6 a b : K)/(rootDenominator6 a b : K))) := by
  rw [root_ratio6 a b ha,mul_sub,← MvPolynomial.C_mul]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  have hc : (a : K)*(-(b : K)/(a : K)) = -(b : K) := by field_simp; ring
  rw [hc,map_neg,sub_neg_eq_add]

theorem denominator_nat_bounds6 (a b : ℤ) (ha : a ≠ 0)
    (hb : Int.gcd a b^5 ≤ a.natAbs^4) :
    a.natAbs ≤ (rootDenominator6 a b).natAbs^5 ∧
      (rootDenominator6 a b).natAbs ≤ a.natAbs := by
  obtain ⟨hg,_,_,heq,_,_,_⟩ := integer_normalization6 a b ha
  have hA : a.natAbs = Int.gcd a b*(rootDenominator6 a b).natAbs := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs heq
  have hmul : (Int.gcd a b)^4*Int.gcd a b ≤
      (Int.gcd a b)^4*(rootDenominator6 a b).natAbs^4 := by
    calc
      (Int.gcd a b)^4*Int.gcd a b = (Int.gcd a b)^5 := by ring
      _ ≤ a.natAbs^4 := hb
      _ = (Int.gcd a b*(rootDenominator6 a b).natAbs)^4 := congrArg (fun n : ℕ => n^4) hA
      _ = _ := by ring
  have hc : Int.gcd a b ≤ (rootDenominator6 a b).natAbs^4 :=
    Nat.le_of_mul_le_mul_left hmul (pow_pos hg 4)
  constructor
  · calc
      a.natAbs = Int.gcd a b*(rootDenominator6 a b).natAbs := hA
      _ ≤ (rootDenominator6 a b).natAbs^4*(rootDenominator6 a b).natAbs := Nat.mul_le_mul_right _ hc
      _ = (rootDenominator6 a b).natAbs^5 := by ring
  · calc
      (rootDenominator6 a b).natAbs = 1*(rootDenominator6 a b).natAbs := (one_mul _).symm
      _ ≤ Int.gcd a b*(rootDenominator6 a b).natAbs := Nat.mul_le_mul_right _ (by omega)
      _ = a.natAbs := hA.symm

theorem denominator_real_bounds6 (a b : ℤ) (ha : a ≠ 0)
    (hb : Int.gcd a b^5 ≤ a.natAbs^4) :
    |(a : ℝ)|^(1/5 : ℝ) ≤ |(rootDenominator6 a b : ℝ)| ∧
      |(rootDenominator6 a b : ℝ)| ≤ |(a : ℝ)| := by
  obtain ⟨hl,hu⟩ := denominator_nat_bounds6 a b ha hb
  have hlR : (a.natAbs : ℝ) ≤ ((rootDenominator6 a b).natAbs : ℝ)^5 := by exact_mod_cast hl
  have huR : ((rootDenominator6 a b).natAbs : ℝ) ≤ (a.natAbs : ℝ) := by exact_mod_cast hu
  have hp : |(a : ℝ)| ≤ |(rootDenominator6 a b : ℝ)|^5 := by
    simpa only [Int.cast_natAbs,Int.cast_abs] using hlR
  constructor
  · rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos (abs_nonneg _) (abs_nonneg _) (by norm_num : (0 : ℝ) < 5)).mpr
    exact hp.trans_eq (Real.rpow_natCast _ 5).symm
  · simpa only [Int.cast_natAbs,Int.cast_abs] using huR

def monicNormal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) : MvPolynomial (Fin m) ℝ :=
  MvPolynomial.X h - MvPolynomial.C
    ((rootNumerator6 (M h 0) (M h 1) : ℝ)/(rootDenominator6 (M h 0) (M h 1) : ℝ))

theorem scalarNormal6_monic {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (h : Fin m) :
    scalarNormal6 M h = MvPolynomial.C (M h 0 : ℝ)*monicNormal6 M h :=
  monic_generator6 (M h 0) (M h 1) (hM h) h

theorem normal_constant_unit6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (h : Fin m) :
    IsUnit (MvPolynomial.C (M h 0 : ℝ) : MvPolynomial (Fin m) ℝ) := by
  have ha : (M h 0 : ℝ) ≠ 0 := by exact_mod_cast hM h
  exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C

theorem scalar_products_scaling6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (i : Fin m → ℕ) :
    (∏ h, scalarNormal6 M h^(i h)) =
      MvPolynomial.C (∏ h, (M h 0 : ℝ)^(i h))*(∏ h, monicNormal6 M h^(i h)) := by
  simp only [scalarNormal6_monic M hM,mul_pow,Finset.prod_mul_distrib,map_prod,map_pow]

theorem scalar_products_membership6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (i : Fin m → ℕ) (I : Ideal (MvPolynomial (Fin m) ℝ)) :
    (∏ h, scalarNormal6 M h^(i h)) ∈ I ↔ (∏ h, monicNormal6 M h^(i h)) ∈ I := by
  have hn : (∏ h, (M h 0 : ℝ)^(i h)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro h _
    exact pow_ne_zero _ (by exact_mod_cast hM h)
  have hi : MvPolynomial.C ((∏ h, (M h 0 : ℝ)^(i h))⁻¹)*
      (∏ h, scalarNormal6 M h^(i h)) = ∏ h, monicNormal6 M h^(i h) := by
    rw [scalar_products_scaling6 M hM i,← mul_assoc,← MvPolynomial.C_mul,
      inv_mul_cancel₀ hn,map_one,one_mul]
  constructor
  · intro hp
    rw [← hi]
    exact I.mul_mem_left _ hp
  · intro hp
    rw [scalar_products_scaling6 M hM i]
    exact I.mul_mem_left _ hp

def monicIdeal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, monicNormal6 M h^(i h)}

def monicStrictIdeal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c < ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, monicNormal6 M h^(i h)}

theorem scalarIdeal6_eq_monic {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ) :
    scalarIdeal6 M r c = monicIdeal6 M r c := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨i,hi,rfl⟩
    apply (scalar_products_membership6 M hM i _).mpr
    exact Ideal.subset_span ⟨i,hi,rfl⟩
  · apply Ideal.span_le.mpr
    rintro P ⟨i,hi,rfl⟩
    apply (scalar_products_membership6 M hM i _).mp
    exact Ideal.subset_span ⟨i,hi,rfl⟩

theorem scalarStrictIdeal6_eq_monic {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ) :
    scalarStrictIdeal6 M r c = monicStrictIdeal6 M r c := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨i,hi,rfl⟩
    apply (scalar_products_membership6 M hM i _).mpr
    exact Ideal.subset_span ⟨i,hi,rfl⟩
  · apply Ideal.span_le.mpr
    rintro P ⟨i,hi,rfl⟩
    apply (scalar_products_membership6 M hM i _).mp
    exact Ideal.subset_span ⟨i,hi,rfl⟩

theorem selected_height6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (C : (h : Fin m) → SchmidtHilfssatz13.NormalCoordinateChoice6 (M h)) (h : Fin m) :
    SourceNormalHeight.normalHeight6 (M h) =
        (permutedNormals6 M (fun g => (C g).e) h 0).natAbs ∧
      SourceNormalHeight.normalHeight6 (permutedNormals6 M (fun g => (C g).e) h) =
        SourceNormalHeight.normalHeight6 (M h) := by
  constructor
  · change SourceNormalHeight.normalHeight6 (M h) = (M h ((C h).e 0)).natAbs
    rw [(C h).e_zero]
    exact (C h).height_attains
  · exact SchmidtHilfssatz13.permuted_height6 (M h) (C h).e

theorem schmidtPackage6_rational_normalization
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) :
    ∃ (C : (h : Fin S.m) → SchmidtHilfssatz13.NormalCoordinateChoice6 (R.M (S.t h)))
      (P' : MvPolynomial (Vars6 S.m) ℤ) (PN : MvPolynomial (Vars6 S.m) ℚ)
      (F : MvPolynomial (Vars6 S.m) ℤ) (G : MvPolynomial (Fin S.m) ℤ)
      (p q : Fin S.m → ℤ),
      let e := fun h => (C h).e
      let M' := permutedNormals6 (fun h => R.M (S.t h)) e
      P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
      PN = normalPolynomialQ6 M' P' ∧ PN ≠ 0 ∧
      (∀ h k, M' h ((C h).e.symm k) = R.M (S.t h) k) ∧
      F = reducedPolynomial6 P' ∧ F ≠ 0 ∧ homogeneous6 (blockDegree6 F) F ∧
      G = scalar6 F ∧ G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height6 S.P ∧
      (∀ h, G.degreeOf h ≤ S.r h) ∧
      (∀ h, p h = rootNumerator6 (M' h 0) (M' h 1) ∧
        q h = rootDenominator6 (M' h 0) (M' h 1)) ∧
      (∀ h, let a := M' h 0
        let b := M' h 1
        let g := Int.gcd a b
        a ≠ 0 ∧ 0 < g ∧ (g : ℤ) ∣ a ∧ (g : ℤ) ∣ b ∧
        a = (g : ℤ)*q h ∧ b = -((g : ℤ)*p h) ∧ q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1 ∧
        (p h : ℚ)/(q h : ℚ) = -(b : ℚ)/(a : ℚ) ∧
        (p h : ℝ)/(q h : ℝ) = -(b : ℝ)/(a : ℝ) ∧
        g^5 ≤ a.natAbs^4 ∧ a.natAbs ≤ (q h).natAbs^5 ∧ (q h).natAbs ≤ a.natAbs ∧
        |(a : ℝ)|^(1/5 : ℝ) ≤ |(q h : ℝ)| ∧ |(q h : ℝ)| ≤ |(a : ℝ)|) ∧
      (∀ h, SourceNormalHeight.normalHeight6 (R.M (S.t h)) = (M' h 0).natAbs ∧
        SourceNormalHeight.normalHeight6 (M' h) = SourceNormalHeight.normalHeight6 (R.M (S.t h)) ∧
        (SourceNormalHeight.normalHeight6 (R.M (S.t h)) : ℝ)^(1/5 : ℝ) ≤ |(q h : ℝ)| ∧
        |(q h : ℝ)| ≤ (SourceNormalHeight.normalHeight6 (R.M (S.t h)) : ℝ)) ∧
      (∀ h, monicNormal6 M' h = MvPolynomial.X h - MvPolynomial.C ((p h : ℝ)/(q h : ℝ)) ∧
        scalarNormal6 M' h = MvPolynomial.C (M' h 0 : ℝ)*monicNormal6 M' h ∧
        IsUnit (MvPolynomial.C (M' h 0 : ℝ) : MvPolynomial (Fin S.m) ℝ)) ∧
      (∀ c, scalarIdeal6 M' S.r c = monicIdeal6 M' S.r c) ∧
      (∀ c, scalarStrictIdeal6 M' S.r c = monicStrictIdeal6 M' S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        G.map (Int.castRingHom ℝ) ∈ monicIdeal6 M' S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceStrictNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 M' S.r c) ∧
      G.map (Int.castRingHom ℝ) ∈ monicIdeal6 M' S.r ((S.m : ℝ)*S.eta) ∧
      G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 M' S.r S.theta := by
  obtain ⟨C,P',PN,F,G,heq,hinv,hPN,hPNn,hrecover,hF,hFn,hbinary,hdegrees,hhom,hdeg,
    hG,hGn,hcoeff,hsupport,hinj,hheightEq,hheight,hGsupportDegree,hGdegree,hfirsttwo,
    hnormal,hnormalDef,hclosed,hstrict,hhigh,hstrictTheta⟩ := schmidtPackage6_scalar_dehomogenization S
  let e := fun h => (C h).e
  let M' := permutedNormals6 (fun h => R.M (S.t h)) e
  let p := fun h => rootNumerator6 (M' h 0) (M' h 1)
  let q := fun h => rootDenominator6 (M' h 0) (M' h 1)
  have hM (h) : M' h 0 ≠ 0 := by
    change R.M (S.t h) ((C h).e 0) ≠ 0
    rw [(C h).e_zero]
    exact (C h).first_nonzero
  have hb (h) : Int.gcd (M' h 0) (M' h 1)^5 ≤ (M' h 0).natAbs^4 := by
    simpa only [(hfirsttwo h).1,(hfirsttwo h).2.1] using (hfirsttwo h).2.2.2
  refine ⟨C,P',PN,F,G,p,q,heq,hinv,hPN,hPNn,hrecover,hF,hFn,hhom,hG,hGn,hheight,
    fun h => (hGdegree h).2,fun _ => ⟨rfl,rfl⟩,?_,?_,?_,scalarIdeal6_eq_monic M' hM S.r,
    scalarStrictIdeal6_eq_monic M' hM S.r,?_,?_,?_,?_⟩
  · intro h
    obtain ⟨hg,hga,hgb,ha,hb',hqn,hcop⟩ := integer_normalization6 (M' h 0) (M' h 1) (hM h)
    obtain ⟨hl,hu⟩ := denominator_nat_bounds6 (M' h 0) (M' h 1) (hM h) (hb h)
    obtain ⟨hlR,huR⟩ := denominator_real_bounds6 (M' h 0) (M' h 1) (hM h) (hb h)
    exact ⟨hM h,hg,hga,hgb,ha,hb',hqn,hcop,root_ratio6 _ _ (hM h),root_ratio6 _ _ (hM h),
      hb h,hl,hu,hlR,huR⟩
  · intro h
    obtain ⟨hh,hperm⟩ := selected_height6 (fun h => R.M (S.t h)) C h
    refine ⟨hh,hperm,?_⟩
    have hr := denominator_real_bounds6 (M' h 0) (M' h 1) (hM h) (hb h)
    rw [hh]
    simpa only [Int.cast_natAbs,Int.cast_abs] using hr
  · intro h
    exact ⟨rfl,scalarNormal6_monic M' hM h,normal_constant_unit6 M' hM h⟩
  · intro c hP
    rw [← scalarIdeal6_eq_monic M' hM S.r c]
    exact hclosed c hP
  · intro c hP
    rw [← scalarStrictIdeal6_eq_monic M' hM S.r c]
    exact hstrict c hP
  · rw [← scalarIdeal6_eq_monic M' hM S.r]
    exact hhigh
  · rw [← scalarStrictIdeal6_eq_monic M' hM S.r]
    exact hstrictTheta

end CompoundFeasibility.SchmidtRationalNormalization6Literal

#check CompoundFeasibility.SchmidtRationalNormalization6Literal.rootNumerator6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.rootNumerator6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.rootDenominator6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.rootDenominator6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.integer_normalization6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.integer_normalization6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.negative_denominator6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.negative_denominator6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.root_ratio6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.root_ratio6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.monic_generator6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.monic_generator6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.denominator_nat_bounds6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.denominator_nat_bounds6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.denominator_real_bounds6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.denominator_real_bounds6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.monicNormal6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.monicNormal6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.scalarNormal6_monic
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.scalarNormal6_monic
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.normal_constant_unit6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.normal_constant_unit6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.scalar_products_scaling6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.scalar_products_scaling6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.scalar_products_membership6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.scalar_products_membership6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.monicIdeal6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.monicIdeal6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.monicStrictIdeal6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.monicStrictIdeal6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.scalarIdeal6_eq_monic
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.scalarIdeal6_eq_monic
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.scalarStrictIdeal6_eq_monic
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.scalarStrictIdeal6_eq_monic
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.selected_height6
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.selected_height6
#check CompoundFeasibility.SchmidtRationalNormalization6Literal.schmidtPackage6_rational_normalization
#print axioms CompoundFeasibility.SchmidtRationalNormalization6Literal.schmidtPackage6_rational_normalization
