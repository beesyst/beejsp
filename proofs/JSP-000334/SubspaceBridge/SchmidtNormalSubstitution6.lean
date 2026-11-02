import SubspaceBridge.SchmidtCoordinateTransport6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtNormalSubstitution6
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SourceSchmidtParameters6 SourceReadiness6 SchmidtHilfssatz13 SourceNormalHeight
variable {K : Type*} [Field K] [CharZero K]

def linearNormal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    MvPolynomial (Vars6 m) K :=
  ∑ j, MvPolynomial.C (M h j : K)*MvPolynomial.X (h,j)

def forward6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6) :
    MvPolynomial (Vars6 m) K →+* MvPolynomial (Vars6 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = k u.1 then linearNormal6 M u.1 else MvPolynomial.X u)

def inverse6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6) :
    MvPolynomial (Vars6 m) K →+* MvPolynomial (Vars6 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then
    MvPolynomial.C ((M u.1 (k u.1) : K)⁻¹) *
      (MvPolynomial.X u - ∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (M u.1 j : K) * MvPolynomial.X (u.1,j))
    else MvPolynomial.X u)

theorem forward6_inverse6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars6 m) K) :
    forward6 M k (inverse6 M k P) = P := by
  classical
  have he : (forward6 (K := K) M k).comp (inverse6 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [forward6,inverse6]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C ((M h (k h) : K)⁻¹) : MvPolynomial (Vars6 m) K) *
            MvPolynomial.C (M h (k h) : K) = 1 := by
          rw [← MvPolynomial.C_mul,inv_mul_cancel₀ (by exact_mod_cast hk h),map_one]
        have hs : linearNormal6 M h =
            (∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : K) * MvPolynomial.X (h,j)) +
              MvPolynomial.C (M h (k h) : K) * MvPolynomial.X (h,k h) := by
          exact (Finset.sum_erase_add _ _ (Finset.mem_univ (k h))).symm
        simp only [RingHom.comp_apply,inverse6,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,map_mul,map_sub,map_sum,forward6,
          MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',RingHom.id_apply]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : K) *
              (if j = k h then linearNormal6 M h else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : K) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,hs,add_sub_cancel_left,← mul_assoc,hc,one_mul]
      · simp [forward6,inverse6,hi]
  exact congrArg (fun f => f P) he

theorem inverse6_forward6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars6 m) K) :
    inverse6 M k (forward6 M k P) = P := by
  classical
  have he : (inverse6 (K := K) M k).comp (forward6 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [forward6,inverse6]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C (M h (k h) : K) : MvPolynomial (Vars6 m) K) *
            MvPolynomial.C ((M h (k h) : K)⁻¹) = 1 := by
          rw [← MvPolynomial.C_mul,mul_inv_cancel₀ (by exact_mod_cast hk h),map_one]
        simp only [RingHom.comp_apply,forward6,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,RingHom.id_apply]
        change inverse6 M k (linearNormal6 M h) = MvPolynomial.X (h,k h)
        rw [linearNormal6,← Finset.sum_erase_add _ _ (Finset.mem_univ (k h))]
        simp only [map_add,map_sum,map_mul,inverse6,MvPolynomial.eval₂Hom_C,
          MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : K) *
              (if j = k h then MvPolynomial.C ((M h (k h) : K)⁻¹) *
                (MvPolynomial.X (h,j) - ∑ l ∈ Finset.univ.erase (k h),
                  MvPolynomial.C (M h l : K) * MvPolynomial.X (h,l))
               else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : K) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,← mul_assoc,hc,one_mul]
        ring
      · simp [forward6,inverse6,hi]
  exact congrArg (fun f => f P) he



def normalEquiv6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6)
    (hk : ∀ h, M h (k h) ≠ 0) :
    MvPolynomial (Vars6 m) K ≃+* MvPolynomial (Vars6 m) K where
  toFun := forward6 M k
  invFun := inverse6 M k
  left_inv := inverse6_forward6 M k hk
  right_inv := forward6_inverse6 M k hk
  map_mul' := map_mul (forward6 M k)
  map_add' := map_add (forward6 M k)

theorem inverse6_normal {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0) (h : Fin m) :
    inverse6 (K := K) M k (linearNormal6 M h) = MvPolynomial.X (h,k h) := by
  simpa only [forward6,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true]
    using inverse6_forward6 (K := K) M k hk (MvPolynomial.X (h,k h))

theorem linearNormal6_map {F : Type*} [Field F] [CharZero F] (f : K →+* F)
    {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    (linearNormal6 (K := K) M h).map f = linearNormal6 M h := by
  simp [linearNormal6]

theorem inverse6_map {F : Type*} [Field F] [CharZero F] (f : K →+* F)
    {m : ℕ} (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6)
    (P : MvPolynomial (Vars6 m) K) :
    (inverse6 M k P).map f = inverse6 M k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [inverse6]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X]
    by_cases hu : u.2 = k u.1 <;> simp [inverse6,hu]

theorem forward6_map {F : Type*} [Field F] [CharZero F] (f : K →+* F)
    {m : ℕ} (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6)
    (P : MvPolynomial (Vars6 m) K) :
    (forward6 M k P).map f = forward6 M k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [forward6]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X]
    by_cases hu : u.2 = k u.1 <;> simp [forward6,hu,linearNormal6_map]

def normalPolynomialQ6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (P : MvPolynomial (Vars6 m) ℤ) : MvPolynomial (Vars6 m) ℚ :=
  inverse6 M (fun _ => 0) (P.map (Int.castRingHom ℚ))

theorem normalPolynomialQ6_forward {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (P : MvPolynomial (Vars6 m) ℤ) :
    forward6 M (fun _ => 0) (normalPolynomialQ6 M P) = P.map (Int.castRingHom ℚ) :=
  forward6_inverse6 M (fun _ => 0) hM _

theorem normalPolynomialQ6_nonzero {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (P : MvPolynomial (Vars6 m) ℤ) (hP : P ≠ 0) :
    normalPolynomialQ6 M P ≠ 0 := by
  intro hz
  have he := normalPolynomialQ6_forward M hM P
  rw [hz,map_zero] at he
  exact hP ((MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
    (he.symm.trans (map_zero _).symm))

theorem normalPolynomialQ6_real {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (P : MvPolynomial (Vars6 m) ℤ) :
    (normalPolynomialQ6 M P).map (Rat.castHom ℝ) =
      normalInverse6 M (fun _ => 0) (P.map (Int.castRingHom ℝ)) := by
  rw [normalPolynomialQ6,inverse6_map,MvPolynomial.map_map]
  rfl


theorem inverse6_normal_products {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (i : Fin m → ℕ) :
    inverse6 (K := K) M (fun _ => 0) (∏ h, linearNormal6 M h^(i h)) =
      ∏ h, MvPolynomial.X (h,0)^(i h) := by
  simp only [map_prod,map_pow,inverse6_normal M (fun _ => 0) hM]

def coordinateIdeal6 {m : ℕ} (r : Fin m → ℕ) (c : ℝ) :
    Ideal (MvPolynomial (Vars6 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, MvPolynomial.X (h,0)^(i h)}

def coordinateStrictIdeal6 {m : ℕ} (r : Fin m → ℕ) (c : ℝ) :
    Ideal (MvPolynomial (Vars6 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c < ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, MvPolynomial.X (h,0)^(i h)}

theorem inverse6_ideal_map {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (inverse6 M (fun _ => 0)) (sourceNormalIdeal6 M r c) = coordinateIdeal6 r c := by
  unfold sourceNormalIdeal6 coordinateIdeal6
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,inverse6_normal_products M hM i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,inverse6_normal_products M hM i⟩

theorem inverse6_strictIdeal_map {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (inverse6 M (fun _ => 0)) (sourceStrictNormalIdeal6 M r c) =
      coordinateStrictIdeal6 r c := by
  unfold sourceStrictNormalIdeal6 coordinateStrictIdeal6
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,inverse6_normal_products M hM i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,inverse6_normal_products M hM i⟩

theorem inverse6_ideal_iff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceNormalIdeal6 M r c ↔ inverse6 M (fun _ => 0) P ∈ coordinateIdeal6 r c := by
  rw [← inverse6_ideal_map M hM r c]
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro hP
    obtain ⟨Q,hQ,he⟩ := (Ideal.mem_map_iff_of_surjective
      (inverse6 M (fun _ => 0)) (normalEquiv6 M (fun _ => 0) hM).symm.surjective).mp hP
    exact (normalEquiv6 M (fun _ => 0) hM).symm.injective he ▸ hQ

theorem inverse6_strictIdeal_iff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceStrictNormalIdeal6 M r c ↔
      inverse6 M (fun _ => 0) P ∈ coordinateStrictIdeal6 r c := by
  rw [← inverse6_strictIdeal_map M hM r c]
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro hP
    obtain ⟨Q,hQ,he⟩ := (Ideal.mem_map_iff_of_surjective
      (inverse6 M (fun _ => 0)) (normalEquiv6 M (fun _ => 0) hM).symm.surjective).mp hP
    exact (normalEquiv6 M (fun _ => 0) hM).symm.injective he ▸ hQ

theorem homogeneous6_scale {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) K) (hP : homogeneous6 r P)
    (b : Fin m → K) (f : Vars6 m → MvPolynomial (Vars6 m) K) :
    MvPolynomial.eval₂Hom MvPolynomial.C (fun u => MvPolynomial.C (b u.1)*f u) P =
      MvPolynomial.C (∏ h, b h^(r h))*MvPolynomial.eval₂Hom MvPolynomial.C f P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial,MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype d (fun u n => (MvPolynomial.C (b u.1)*f u)^n)
    (fun _ => pow_zero _),Finsupp.prod_fintype d (fun u n => f u^n) (fun _ => pow_zero _)]
  simp only [mul_pow,Finset.prod_mul_distrib]
  have he : (∏ u : Vars6 m, (MvPolynomial.C (b u.1) : MvPolynomial (Vars6 m) K)^d u) =
      MvPolynomial.C (∏ h, b h^(r h)) := by
    rw [Fintype.prod_prod_type]
    simp only [Finset.prod_pow_eq_pow_sum,hP d hd,map_prod,map_pow]
  rw [he]
  ring

def numerator6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) :
    MvPolynomial (Vars6 m) ℤ →+* MvPolynomial (Vars6 m) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = 0 then
    MvPolynomial.X u - ∑ j ∈ Finset.univ.erase 0,
      MvPolynomial.C (M u.1 j)*MvPolynomial.X (u.1,j)
    else MvPolynomial.C (M u.1 0)*MvPolynomial.X u)

theorem numerator6_map {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (P : MvPolynomial (Vars6 m) ℤ) :
    (numerator6 M P).map (Int.castRingHom ℚ) =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun u => MvPolynomial.C (M u.1 0 : ℚ)*
          inverse6 M (fun _ => 0) (MvPolynomial.X u)) (P.map (Int.castRingHom ℚ)) := by
  have hgen (u : Vars6 m) :
      (numerator6 M (MvPolynomial.X u)).map (Int.castRingHom ℚ) =
        MvPolynomial.C (M u.1 0 : ℚ)*inverse6 M (fun _ => 0) (MvPolynomial.X u) := by
    simp only [numerator6,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd]
    by_cases hu : u.2 = 0
    · rw [if_pos hu]
      have hn : (M u.1 0 : ℚ) ≠ 0 := by exact_mod_cast hM u.1
      have hc : (MvPolynomial.C (M u.1 0 : ℚ) : MvPolynomial (Vars6 m) ℚ)*
          MvPolynomial.C ((M u.1 0 : ℚ)⁻¹) = 1 := by
        rw [← MvPolynomial.C_mul,mul_inv_cancel₀ hn,map_one]
      simp only [map_sub,map_sum,map_mul,MvPolynomial.map_X,MvPolynomial.map_C,
        inverse6,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,if_pos hu]
      rw [← mul_assoc,hc,one_mul]
      rfl
    · simp only [if_neg hu,map_mul,MvPolynomial.map_C,MvPolynomial.map_X,
        inverse6,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,if_neg hu]
      rfl
  induction P using MvPolynomial.induction_on with
  | C c => simp [numerator6]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X,hgen,MvPolynomial.eval₂Hom_X']

def denominator6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (r : Fin m → ℕ) : ℕ :=
  ∏ h, (M h 0).natAbs^(r h)

theorem denominator6_ne_zero {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) : denominator6 M r ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun h _ => pow_ne_zero _ (Int.natAbs_ne_zero.mpr (hM h)))

theorem numerator6_homogeneous {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) :
    (numerator6 M P).map (Int.castRingHom ℚ) =
      MvPolynomial.C ((∏ h, M h 0^(r h) : ℤ) : ℚ)*normalPolynomialQ6 M P := by
  rw [numerator6_map M hM]
  have hhom := homogeneous6_map (Int.castRingHom ℚ) r P hP
  rw [homogeneous6_scale r _ hhom (fun h => (M h 0 : ℚ))
    (fun u => inverse6 M (fun _ => 0) (MvPolynomial.X u))]
  congr 1
  · simp
  · rw [normalPolynomialQ6]
    have he : MvPolynomial.eval₂Hom MvPolynomial.C
        (fun u => inverse6 (K := ℚ) M (fun _ => 0) (MvPolynomial.X u)) =
        inverse6 M (fun _ => 0) := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [inverse6]
      · intro u; simp
    exact congrArg (fun f => f (P.map (Int.castRingHom ℚ))) he

theorem normalPolynomialQ6_integral_multiple {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) :
    ∃ Q : MvPolynomial (Vars6 m) ℤ,
      Q.map (Int.castRingHom ℚ) = MvPolynomial.C (denominator6 M r : ℚ)*normalPolynomialQ6 M P := by
  let A : ℤ := ∏ h, M h 0^(r h)
  refine ⟨MvPolynomial.C (Int.sign A)*numerator6 M P,?_⟩
  rw [map_mul,MvPolynomial.map_C,numerator6_homogeneous M hM r P hP,← mul_assoc,
    ← MvPolynomial.C_mul]
  have he : (Int.sign A : ℚ)*(A : ℚ) = (denominator6 M r : ℚ) := by
    have hsign := Int.sign_mul_self_eq_natAbs A
    have habs : A.natAbs = denominator6 M r := by
      change Int.natAbsHom (∏ h, M h 0^r h) = _
      rw [map_prod]
      simp only [map_pow]
      rfl
    rw [habs] at hsign
    exact_mod_cast hsign
  change MvPolynomial.C ((Int.sign A : ℚ)*(A : ℚ))*normalPolynomialQ6 M P = _
  rw [he]

theorem inverse6_X_weight {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (h : Fin m) (u : Vars6 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars6 m => if v.1 = h then 1 else 0)
      (inverse6 (K := K) M k (MvPolynomial.X u)) (if u.1 = h then 1 else 0) := by
  let w := fun v : Vars6 m => if v.1 = h then 1 else 0
  have hs : MvPolynomial.IsWeightedHomogeneous w
      (∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (M u.1 j : K)*MvPolynomial.X (u.1,j)) (w u) := by
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j _
    simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w (M u.1 j : K)).mul
      (MvPolynomial.isWeightedHomogeneous_X K w (u.1,j))
  by_cases hu : u.2 = k u.1
  · simp only [inverse6,MvPolynomial.eval₂Hom_X',if_pos hu]
    simpa only [zero_add,sub_eq_add_neg] using
      (MvPolynomial.isWeightedHomogeneous_C w ((M u.1 (k u.1) : K)⁻¹)).mul
        ((MvPolynomial.isWeightedHomogeneous_X K w u).add (rothAux_weighted_neg w _ _ hs))
  · simpa only [inverse6,MvPolynomial.eval₂Hom_X',if_neg hu] using
      MvPolynomial.isWeightedHomogeneous_X K w u

theorem homogeneous6_substitution {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) K) (hP : homogeneous6 r P)
    (f : MvPolynomial (Vars6 m) K →+* MvPolynomial (Vars6 m) K)
    (hC : ∀ c, f (MvPolynomial.C c) = MvPolynomial.C c)
    (hX : ∀ h u, MvPolynomial.IsWeightedHomogeneous
      (fun v : Vars6 m => if v.1 = h then 1 else 0) (f (MvPolynomial.X u))
      (if u.1 = h then 1 else 0)) : homogeneous6 r (f P) := by
  have hall (h : Fin m) : MvPolynomial.IsWeightedHomogeneous
      (fun v : Vars6 m => if v.1 = h then 1 else 0) (f P) (r h) := by
    let w := fun v : Vars6 m => if v.1 = h then 1 else 0
    conv => arg 2; rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro d hd
    rw [MvPolynomial.monomial_eq,map_mul,hC]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),map_prod]
    simp only [map_pow]
    have hw := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun u => f (MvPolynomial.X u)^d u) (fun u => d u*w u)
      (fun u _ => by simpa only [nsmul_eq_mul] using (hX h u).pow (d u))
    have he : (∑ u : Vars6 m, d u*w u) = r h := by
      rw [← hP d hd h,← rothAux_weight_block]
      rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)]
      rfl
    rw [he] at hw
    simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w (P.coeff d)).mul hw
  intro d hd h
  rw [← rothAux_weight_block]
  exact hall h (MvPolynomial.mem_support_iff.mp hd)

theorem inverse6_homogeneous {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) K) (hP : homogeneous6 r P) :
    homogeneous6 r (inverse6 M k P) :=
  homogeneous6_substitution r P hP (inverse6 M k) (by intro c; simp [inverse6])
    (inverse6_X_weight M k)

theorem homogeneous6_blockDegree {A : Type*} [CommRing A] {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) A) (hP : homogeneous6 r P) (hn : P ≠ 0) (h : Fin m) :
    blockDegree6 P h = r h := by
  unfold blockDegree6
  apply le_antisymm
  · exact Finset.sup_le (fun d hd => (hP d hd h).le)
  · obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hn
    rw [← hP d hd h]
    exact Finset.le_sup (f := fun d => ∑ j : Fin 6, d (h,j)) hd

theorem normalPolynomialQ6_degrees {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) (hn : P ≠ 0) :
    homogeneous6 r (normalPolynomialQ6 M P) ∧
      (∀ h, blockDegree6 (normalPolynomialQ6 M P) h = r h) := by
  have hh := inverse6_homogeneous M (fun _ => 0) r (P.map (Int.castRingHom ℚ))
    (homogeneous6_map (Int.castRingHom ℚ) r P hP)
  exact ⟨hh,homogeneous6_blockDegree r _ hh (normalPolynomialQ6_nonzero M hM P hn)⟩

theorem normalPolynomialQ6_blockDegree {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) (hn : P ≠ 0) (h : Fin m) :
    blockDegree6 (normalPolynomialQ6 M P) h = blockDegree6 P h := by
  rw [(normalPolynomialQ6_degrees M hM r P hP hn).2 h,homogeneous6_blockDegree r P hP hn h]

theorem schmidtPackage6_normal_substitution
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) :
    ∃ (C : (h : Fin S.m) → NormalCoordinateChoice6 (R.M (S.t h)))
      (P' : MvPolynomial (Vars6 S.m) ℤ) (PN : MvPolynomial (Vars6 S.m) ℚ),
      let e := fun h => (C h).e
      let M' := permutedNormals6 (fun h => R.M (S.t h)) e
      P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
      P' ≠ 0 ∧ height6 P' = height6 S.P ∧ homogeneous6 S.r P' ∧
      (∀ h, blockDegree6 P' h = blockDegree6 S.P h) ∧
      (∀ h, M' h 0 ≠ 0 ∧ (M' h 0).natAbs = normalHeight6 (M' h) ∧
        Int.gcd (M' h 0) (M' h 1)^5 ≤ (M' h 0).natAbs^4) ∧
      (∀ h k, M' h ((C h).e.symm k) = R.M (S.t h) k) ∧
      PN = normalPolynomialQ6 M' P' ∧ PN ≠ 0 ∧
      (∀ Q : MvPolynomial (Vars6 S.m) ℚ,
        forward6 M' (fun _ => 0) (inverse6 M' (fun _ => 0) Q) = Q ∧
        inverse6 M' (fun _ => 0) (forward6 M' (fun _ => 0) Q) = Q) ∧
      forward6 M' (fun _ => 0) PN = P'.map (Int.castRingHom ℚ) ∧
      inverse6 M' (fun _ => 0) (forward6 M' (fun _ => 0) PN) = PN ∧
      denominator6 M' S.r ≠ 0 ∧
      (∃ Q : MvPolynomial (Vars6 S.m) ℤ,
        Q.map (Int.castRingHom ℚ) = MvPolynomial.C (denominator6 M' S.r : ℚ)*PN) ∧
      homogeneous6 S.r PN ∧ (∀ h, blockDegree6 PN h = S.r h) ∧
      (∀ h, blockDegree6 PN h = blockDegree6 S.P h) ∧
      (∀ h, inverse6 (K := ℚ) M' (fun _ => 0) (linearNormal6 M' h) = MvPolynomial.X (h,0)) ∧
      (∀ h, forward6 (K := ℚ) M' (fun _ => 0) (MvPolynomial.X (h,0)) = linearNormal6 M' h) ∧
      (∀ h, (linearNormal6 (K := ℚ) M' h).map (Rat.castHom ℝ) = normalPolynomial6 M' h) ∧
      PN.map (Rat.castHom ℝ) = normalInverse6 M' (fun _ => 0) (P'.map (Int.castRingHom ℝ)) ∧
      (∀ c : ℝ, P'.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M' S.r c ↔
        PN.map (Rat.castHom ℝ) ∈ coordinateIdeal6 S.r c) ∧
      (∀ c : ℝ, P'.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M' S.r c ↔
        PN.map (Rat.castHom ℝ) ∈ coordinateStrictIdeal6 S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c ↔
        PN.map (Rat.castHom ℝ) ∈ coordinateIdeal6 S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceStrictNormalIdeal6 (fun h => R.M (S.t h)) S.r c ↔
        PN.map (Rat.castHom ℝ) ∈ coordinateStrictIdeal6 S.r c) ∧
      PN.map (Rat.castHom ℝ) ∈ coordinateIdeal6 S.r ((S.m : ℝ)*S.eta) := by
  obtain ⟨C,P',heq,hinv,hn,hheight,hhom,hdeg,hdata,hbez,hnorm,hmap,hiff,hstrict,hhigh⟩ :=
    schmidtPackage6_transport S
  let e := fun h => (C h).e
  let M' := permutedNormals6 (fun h => R.M (S.t h)) e
  have hM : ∀ h, M' h 0 ≠ 0 := fun h => (hdata h).2.2.2.1
  let PN := normalPolynomialQ6 M' P'
  have hreal := normalPolynomialQ6_real M' P'
  have hc (c : ℝ) : P'.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M' S.r c ↔
      PN.map (Rat.castHom ℝ) ∈ coordinateIdeal6 S.r c := by
    rw [hreal]
    exact inverse6_ideal_iff M' hM S.r c _
  have hs (c : ℝ) : P'.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M' S.r c ↔
      PN.map (Rat.castHom ℝ) ∈ coordinateStrictIdeal6 S.r c := by
    rw [hreal]
    exact inverse6_strictIdeal_iff M' hM S.r c _
  refine ⟨C,P',PN,heq,hinv,hn,hheight,hhom,hdeg,?_,?_,rfl,
    normalPolynomialQ6_nonzero M' hM P' hn,?_,normalPolynomialQ6_forward M' hM P',
    inverse6_forward6 M' (fun _ => 0) hM PN,denominator6_ne_zero M' hM S.r,
    normalPolynomialQ6_integral_multiple M' hM S.r P' hhom,
    (normalPolynomialQ6_degrees M' hM S.r P' hhom hn).1,
    (normalPolynomialQ6_degrees M' hM S.r P' hhom hn).2,
    fun h => (normalPolynomialQ6_blockDegree M' hM S.r P' hhom hn h).trans (hdeg h),
    inverse6_normal M' (fun _ => 0) hM,?_,?_,hreal,hc,hs,
    fun c => (hiff c).trans (hc c),fun c => (hstrict c).trans (hs c),(hc _).mp hhigh⟩
  · intro h
    refine ⟨hM h,(hdata h).2.2.2.2.1.symm,?_⟩
    rw [← (hdata h).2.2.2.2.1]
    exact (hdata h).2.2.2.2.2.2.1
  · intro h k
    exact (hdata h).2.2.2.2.2.2.2 k
  · intro Q
    exact ⟨forward6_inverse6 M' (fun _ => 0) hM Q,inverse6_forward6 M' (fun _ => 0) hM Q⟩
  · intro h
    simp [forward6]
  · intro h
    exact linearNormal6_map (Rat.castHom ℝ) M' h

end CompoundFeasibility.SchmidtNormalSubstitution6
