import SubspaceBridge.SchmidtHilfssatz13
import Mathlib.Data.Nat.Factorization.Basic
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtNormal10
def normalHeight10 (M : Fin 10 → ℤ) : ℕ := Finset.univ.sup (fun i => (M i).natAbs)

theorem normalHeight10_le_iff (M : Fin 10 → ℤ) (b : ℕ) :
    normalHeight10 M ≤ b ↔ ∀ i, (M i).natAbs ≤ b := by
  simp only [normalHeight10,Finset.sup_le_iff,Finset.mem_univ,true_implies]



theorem primitive_common_divisor10 (M : Fin 10 → ℤ)
    (hM : Ideal.span (Set.range M) = ⊤) (d : ℕ)
    (hd : ∀ i, d ∣ (M i).natAbs) : d = 1 := by
  have hspan : Ideal.span (Set.range M) ≤ Ideal.span ({(d : ℤ)} : Set ℤ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.mem_span_singleton.mpr (Int.natCast_dvd.mpr (hd i))
  have hone : (1 : ℤ) ∈ Ideal.span ({(d : ℤ)} : Set ℤ) := by
    apply hspan
    rw [hM]
    trivial
  simpa using Int.isUnit_iff_natAbs_eq.mp
    (isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hone))

theorem height_attaining10 (M : Fin 10 → ℤ) (hM : M ≠ 0) :
    ∃ i : Fin 10, M i ≠ 0 ∧ (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧
      normalHeight10 M = (M i).natAbs := by
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun k : Fin 10 => (M k).natAbs)
  have hmax (k) : (M k).natAbs ≤ (M i).natAbs := by
    rw [← he]
    exact Finset.le_sup (f := fun k : Fin 10 => (M k).natAbs) (Finset.mem_univ k)
  have hi : M i ≠ 0 := by
    intro hz
    apply hM
    funext k
    have hk := hmax k
    rw [hz,Int.natAbs_zero] at hk
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
  exact ⟨i,hi,hmax,he⟩

theorem nine_gcd_product_dvd10 (M : Fin 10 → ℤ)
    (hM : Ideal.span (Set.range M) = ⊤) (i : Fin 10) (hi : M i ≠ 0) :
    (∏ j ∈ Finset.univ.erase i, Nat.gcd (M i).natAbs (M j).natAbs) ∣
      (M i).natAbs^8 := by
  let A := (M i).natAbs
  let d := fun j : Fin 10 => Nat.gcd A (M j).natAbs
  let S := Finset.univ.erase i
  have hA : A ≠ 0 := Int.natAbs_ne_zero.mpr hi
  have hd (j : Fin 10) : d j ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hA)).ne'
  have hS : S.card = 9 := by simp [S]
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  change (∏ j ∈ S, d j) ∣ A^8
  apply (Nat.factorization_prime_le_iff_dvd (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))
    (pow_ne_zero 8 hA)).mp
  intro p hp
  have hbound (j : Fin 10) : (d j).factorization p ≤ A.factorization p :=
    (Nat.factorization_le_iff_dvd (hd j) hA).mpr (Nat.gcd_dvd_left _ _) p
  have hsome : ∃ j ∈ S, ¬p ∣ d j := by
    by_contra! hall
    have hone : p = 1 := primitive_common_divisor10 M hM p (by
      intro k
      by_cases hk : k = i
      · subst k
        obtain ⟨j,hj⟩ := hSn
        exact (hall j hj).trans (Nat.gcd_dvd_left _ _)
      · exact (hall k (by simpa [S] using hk)).trans (Nat.gcd_dvd_right _ _))
    exact hp.ne_one hone
  obtain ⟨j,hj,hjp⟩ := hsome
  have hz : (d j).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hjp
  rw [Nat.factorization_prod (fun j _ => hd j),Nat.factorization_pow]
  simp only [Finsupp.finset_sum_apply,Finsupp.smul_apply,smul_eq_mul]
  calc
    (∑ k ∈ S, (d k).factorization p) = ∑ k ∈ S.erase j, (d k).factorization p := by
      rw [← Finset.sum_erase_add S (fun k => (d k).factorization p) hj,hz,add_zero]
    _ ≤ ∑ k ∈ S.erase j, A.factorization p := Finset.sum_le_sum (fun k _ => hbound k)
    _ = 8*A.factorization p := by
      simp [Finset.card_erase_of_mem hj,hS]

theorem minimum_secondary_gcd10 (M : Fin 10 → ℤ) (i : Fin 10) :
    ∃ j : Fin 10, j ≠ i ∧
      (∀ k : Fin 10, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)) ∧
      Int.gcd (M i) (M j)^9 ≤
        ∏ k ∈ Finset.univ.erase i, Nat.gcd (M i).natAbs (M k).natAbs := by
  let S := Finset.univ.erase i
  let d := fun k : Fin 10 => Int.gcd (M i) (M k)
  have hS : S.card = 9 := by simp [S]
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S d (Finset.card_pos.mp (by omega))
  have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
  refine ⟨j,hjne,fun k hk => hmin k (by simpa [S] using hk),?_⟩
  have hp := Finset.prod_le_prod' hmin
  simpa [d,hS] using hp

theorem primitive_nonzero10 (M : Fin 10 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) : M ≠ 0 := by
  intro hz
  have h := primitive_common_divisor10 M hM 0 (by intro k; rw [hz]; simp)
  omega

theorem select_minimum_pair10 (M : Fin 10 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) :
    ∃ i j : Fin 10, i ≠ j ∧ M i ≠ 0 ∧
      (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧ normalHeight10 M = (M i).natAbs ∧
      (∀ k : Fin 10, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)) ∧
      Int.gcd (M i) (M j)^9 ≤ (M i).natAbs^8 := by
  obtain ⟨i,hi,hmax,hheight⟩ := height_attaining10 M (primitive_nonzero10 M hM)
  obtain ⟨j,hji,hmin,hpow⟩ := minimum_secondary_gcd10 M i
  have hprod := nine_gcd_product_dvd10 M hM i hi
  exact ⟨i,j,Ne.symm hji,hi,hmax,hheight,hmin,hpow.trans
    (Nat.le_of_dvd (pow_pos (Int.natAbs_pos.mpr hi) 8) hprod)⟩

theorem select_pair10 (M : Fin 10 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) :
    ∃ i j : Fin 10, i ≠ j ∧ M i ≠ 0 ∧
      (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧
      Int.gcd (M i) (M j)^9 ≤ (M i).natAbs^8 := by
  obtain ⟨i,j,hij,hi,hmax,_,_,hpow⟩ := select_minimum_pair10 M hM
  exact ⟨i,j,hij,hi,hmax,hpow⟩

def pairPermutation10 (i j : Fin 10) : Equiv.Perm (Fin 10) :=
  (Equiv.swap 1 (Equiv.swap 0 i j)).trans (Equiv.swap 0 i)

theorem pairPermutation6_coordinates (i j : Fin 10) (hij : i ≠ j) :
    pairPermutation10 i j 0 = i ∧ pairPermutation10 i j 1 = j := by
  have hk : Equiv.swap 0 i j ≠ 0 := by
    intro hz
    have he : Equiv.swap 0 i j = Equiv.swap 0 i i := by simpa using hz
    exact hij ((Equiv.swap 0 i).injective he).symm
  constructor
  · simp only [pairPermutation10,Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 10) ≠ 1) (Ne.symm hk),
      Equiv.swap_apply_left]
  · simp [pairPermutation10,Equiv.trans_apply]

def coefficientMultiset10 (M : Fin 10 → ℤ) : Multiset ℤ := ∑ k, ({M k} : Multiset ℤ)

theorem permuted_coefficients10 (M : Fin 10 → ℤ) (e : Equiv.Perm (Fin 10)) :
    coefficientMultiset10 (fun k => M (e k)) = coefficientMultiset10 M := by
  exact e.sum_comp Finset.univ (fun k => ({M k} : Multiset ℤ)) (by intro k _; simp)

theorem permuted_range10 (M : Fin 10 → ℤ) (e : Equiv.Perm (Fin 10)) :
    Set.range (fun k => M (e k)) = Set.range M := by
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨e k,rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨e.symm k,by simp⟩

theorem permuted_primitive10 (M : Fin 10 → ℤ) (e : Equiv.Perm (Fin 10))
    (hM : Ideal.span (Set.range M) = ⊤) :
    Ideal.span (Set.range (fun k => M (e k))) = ⊤ := by
  rw [permuted_range10 M e,hM]

theorem permuted_height10 (M : Fin 10 → ℤ) (e : Equiv.Perm (Fin 10)) :
    normalHeight10 (fun k => M (e k)) = normalHeight10 M := by
  apply le_antisymm
  · apply (normalHeight10_le_iff _ _).mpr
    intro k
    exact Finset.le_sup (f := fun j => (M j).natAbs) (Finset.mem_univ (e k))
  · apply (normalHeight10_le_iff _ _).mpr
    intro k
    simpa using Finset.le_sup (f := fun j => (M (e j)).natAbs) (Finset.mem_univ (e.symm k))

theorem permuted_bezout10 (M a : Fin 10 → ℤ) (e : Equiv.Perm (Fin 10))
    (ha : (∑ k, a k*M k) = 1) : (∑ k, a (e k)*M (e k)) = 1 := by
  rw [e.sum_comp Finset.univ (fun k => a k*M k) (by intro k _; simp),ha]

structure NormalCoordinateChoice10 (M : Fin 10 → ℤ) where
  i : Fin 10
  j : Fin 10
  distinct : i ≠ j
  primitive : Ideal.span (Set.range M) = ⊤
  first_nonzero : M i ≠ 0
  maximal : ∀ k, (M k).natAbs ≤ (M i).natAbs
  height_attains : normalHeight10 M = (M i).natAbs
  minimum : ∀ k : Fin 10, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)
  gcd_bound : Int.gcd (M i) (M j)^9 ≤ (M i).natAbs^8
  e : Equiv.Perm (Fin 10)
  e_zero : e 0 = i
  e_one : e 1 = j

theorem normal_coordinate_choice10 (M : Fin 10 → ℤ)
    (hM : Ideal.span (Set.range M) = ⊤) : Nonempty (NormalCoordinateChoice10 M) := by
  obtain ⟨i,j,hij,hi,hmax,hheight,hmin,hpow⟩ := select_minimum_pair10 M hM
  obtain ⟨he0,he1⟩ := pairPermutation6_coordinates i j hij
  exact ⟨{
    i := i, j := j, distinct := hij, primitive := hM, first_nonzero := hi,
    maximal := hmax, height_attains := hheight, minimum := hmin, gcd_bound := hpow,
    e := pairPermutation10 i j, e_zero := he0, e_one := he1 }⟩

theorem NormalCoordinateChoice10.permuted_data {M : Fin 10 → ℤ} (C : NormalCoordinateChoice10 M) :
    coefficientMultiset10 (fun k => M (C.e k)) = coefficientMultiset10 M ∧
    Ideal.span (Set.range (fun k => M (C.e k))) = ⊤ ∧
    normalHeight10 (fun k => M (C.e k)) = normalHeight10 M ∧
    M (C.e 0) ≠ 0 ∧
    Int.gcd (M (C.e 0)) (M (C.e 1))^9 ≤ normalHeight10 (fun k => M (C.e k))^8 ∧
    (∀ k, C.e.symm (C.e k) = k) ∧ (∀ k, C.e (C.e.symm k) = k) ∧
    (∀ k, (fun j => M (C.e j)) (C.e.symm k) = M k) := by
  refine ⟨permuted_coefficients10 M C.e,permuted_primitive10 M C.e C.primitive,
    permuted_height10 M C.e,?_,?_,C.e.symm_apply_apply,C.e.apply_symm_apply,?_⟩
  · rw [C.e_zero]
    exact C.first_nonzero
  · rw [C.e_zero,C.e_one,permuted_height10 M C.e,C.height_attains]
    exact C.gcd_bound
  · intro k
    simp


variable {K : Type*} [Field K] [CharZero K]

abbrev Vars10 (m : ℕ) := Fin m × Fin 10

def linearNormal10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    MvPolynomial (Vars10 m) K :=
  ∑ j, MvPolynomial.C (M h j : K)*MvPolynomial.X (h,j)

def sourceNormalIdeal10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Vars10 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, linearNormal10 M h^(i h)}

def sourceStrictNormalIdeal10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Vars10 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c < ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, linearNormal10 M h^(i h)}

def forward10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) (k : Fin m → Fin 10) :
    MvPolynomial (Vars10 m) K →+* MvPolynomial (Vars10 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = k u.1 then linearNormal10 M u.1 else MvPolynomial.X u)

def inverse10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) (k : Fin m → Fin 10) :
    MvPolynomial (Vars10 m) K →+* MvPolynomial (Vars10 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then
    MvPolynomial.C ((M u.1 (k u.1) : K)⁻¹) *
      (MvPolynomial.X u - ∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (M u.1 j : K) * MvPolynomial.X (u.1,j))
    else MvPolynomial.X u)

theorem forward6_inverse10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars10 m) K) :
    forward10 M k (inverse10 M k P) = P := by
  classical
  have he : (forward10 (K := K) M k).comp (inverse10 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [forward10,inverse10]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C ((M h (k h) : K)⁻¹) : MvPolynomial (Vars10 m) K) *
            MvPolynomial.C (M h (k h) : K) = 1 := by
          rw [← MvPolynomial.C_mul,inv_mul_cancel₀ (by exact_mod_cast hk h),map_one]
        have hs : linearNormal10 M h =
            (∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : K) * MvPolynomial.X (h,j)) +
              MvPolynomial.C (M h (k h) : K) * MvPolynomial.X (h,k h) := by
          exact (Finset.sum_erase_add _ _ (Finset.mem_univ (k h))).symm
        simp only [RingHom.comp_apply,inverse10,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,map_mul,map_sub,map_sum,forward10,
          MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',RingHom.id_apply]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : K) *
              (if j = k h then linearNormal10 M h else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : K) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,hs,add_sub_cancel_left,← mul_assoc,hc,one_mul]
      · simp [forward10,inverse10,hi]
  exact congrArg (fun f => f P) he

theorem inverse6_forward10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars10 m) K) :
    inverse10 M k (forward10 M k P) = P := by
  classical
  have he : (inverse10 (K := K) M k).comp (forward10 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [forward10,inverse10]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C (M h (k h) : K) : MvPolynomial (Vars10 m) K) *
            MvPolynomial.C ((M h (k h) : K)⁻¹) = 1 := by
          rw [← MvPolynomial.C_mul,mul_inv_cancel₀ (by exact_mod_cast hk h),map_one]
        simp only [RingHom.comp_apply,forward10,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,RingHom.id_apply]
        change inverse10 M k (linearNormal10 M h) = MvPolynomial.X (h,k h)
        rw [linearNormal10,← Finset.sum_erase_add _ _ (Finset.mem_univ (k h))]
        simp only [map_add,map_sum,map_mul,inverse10,MvPolynomial.eval₂Hom_C,
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
      · simp [forward10,inverse10,hi]
  exact congrArg (fun f => f P) he



def normalEquiv10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) (k : Fin m → Fin 10)
    (hk : ∀ h, M h (k h) ≠ 0) :
    MvPolynomial (Vars10 m) K ≃+* MvPolynomial (Vars10 m) K where
  toFun := forward10 M k
  invFun := inverse10 M k
  left_inv := inverse6_forward10 M k hk
  right_inv := forward6_inverse10 M k hk
  map_mul' := map_mul (forward10 M k)
  map_add' := map_add (forward10 M k)

theorem inverse10_normal {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0) (h : Fin m) :
    inverse10 (K := K) M k (linearNormal10 M h) = MvPolynomial.X (h,k h) := by
  simpa only [forward10,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true]
    using inverse6_forward10 (K := K) M k hk (MvPolynomial.X (h,k h))

theorem linearNormal10_map {F : Type*} [Field F] [CharZero F] (f : K →+* F)
    {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    (linearNormal10 (K := K) M h).map f = linearNormal10 M h := by
  simp [linearNormal10]

theorem inverse10_map {F : Type*} [Field F] [CharZero F] (f : K →+* F)
    {m : ℕ} (M : Fin m → Fin 10 → ℤ) (k : Fin m → Fin 10)
    (P : MvPolynomial (Vars10 m) K) :
    (inverse10 M k P).map f = inverse10 M k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [inverse10]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X]
    by_cases hu : u.2 = k u.1 <;> simp [inverse10,hu]

theorem forward10_map {F : Type*} [Field F] [CharZero F] (f : K →+* F)
    {m : ℕ} (M : Fin m → Fin 10 → ℤ) (k : Fin m → Fin 10)
    (P : MvPolynomial (Vars10 m) K) :
    (forward10 M k P).map f = forward10 M k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [forward10]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X]
    by_cases hu : u.2 = k u.1 <;> simp [forward10,hu,linearNormal10_map]

def normalPolynomialQ10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (P : MvPolynomial (Vars10 m) ℤ) : MvPolynomial (Vars10 m) ℚ :=
  inverse10 M (fun _ => 0) (P.map (Int.castRingHom ℚ))

theorem normalPolynomialQ10_forward {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (P : MvPolynomial (Vars10 m) ℤ) :
    forward10 M (fun _ => 0) (normalPolynomialQ10 M P) = P.map (Int.castRingHom ℚ) :=
  forward6_inverse10 M (fun _ => 0) hM _

theorem normalPolynomialQ10_nonzero {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (P : MvPolynomial (Vars10 m) ℤ) (hP : P ≠ 0) :
    normalPolynomialQ10 M P ≠ 0 := by
  intro hz
  have he := normalPolynomialQ10_forward M hM P
  rw [hz,map_zero] at he
  exact hP ((MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
    (he.symm.trans (map_zero _).symm))

theorem normalPolynomialQ10_real {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (P : MvPolynomial (Vars10 m) ℤ) :
    (normalPolynomialQ10 M P).map (Rat.castHom ℝ) =
      inverse10 (K := ℝ) M (fun _ => 0) (P.map (Int.castRingHom ℝ)) := by
  rw [normalPolynomialQ10,inverse10_map,MvPolynomial.map_map]
  rfl


theorem inverse10_normal_products {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (i : Fin m → ℕ) :
    inverse10 (K := K) M (fun _ => 0) (∏ h, linearNormal10 M h^(i h)) =
      ∏ h, MvPolynomial.X (h,0)^(i h) := by
  simp only [map_prod,map_pow,inverse10_normal M (fun _ => 0) hM]

def coordinateIdeal10 {m : ℕ} (r : Fin m → ℕ) (c : ℝ) :
    Ideal (MvPolynomial (Vars10 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, MvPolynomial.X (h,0)^(i h)}

def coordinateStrictIdeal10 {m : ℕ} (r : Fin m → ℕ) (c : ℝ) :
    Ideal (MvPolynomial (Vars10 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c < ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, MvPolynomial.X (h,0)^(i h)}

theorem inverse10_ideal_map {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (inverse10 M (fun _ => 0)) (sourceNormalIdeal10 M r c) = coordinateIdeal10 r c := by
  unfold sourceNormalIdeal10 coordinateIdeal10
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,inverse10_normal_products M hM i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,inverse10_normal_products M hM i⟩

theorem inverse10_strictIdeal_map {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (inverse10 M (fun _ => 0)) (sourceStrictNormalIdeal10 M r c) =
      coordinateStrictIdeal10 r c := by
  unfold sourceStrictNormalIdeal10 coordinateStrictIdeal10
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,inverse10_normal_products M hM i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,inverse10_normal_products M hM i⟩

theorem inverse10_ideal_iff {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars10 m) ℝ) :
    P ∈ sourceNormalIdeal10 M r c ↔ inverse10 M (fun _ => 0) P ∈ coordinateIdeal10 r c := by
  rw [← inverse10_ideal_map M hM r c]
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro hP
    obtain ⟨Q,hQ,he⟩ := (Ideal.mem_map_iff_of_surjective
      (inverse10 M (fun _ => 0)) (normalEquiv10 M (fun _ => 0) hM).symm.surjective).mp hP
    exact (normalEquiv10 M (fun _ => 0) hM).symm.injective he ▸ hQ

theorem inverse10_strictIdeal_iff {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars10 m) ℝ) :
    P ∈ sourceStrictNormalIdeal10 M r c ↔
      inverse10 M (fun _ => 0) P ∈ coordinateStrictIdeal10 r c := by
  rw [← inverse10_strictIdeal_map M hM r c]
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro hP
    obtain ⟨Q,hQ,he⟩ := (Ideal.mem_map_iff_of_surjective
      (inverse10 M (fun _ => 0)) (normalEquiv10 M (fun _ => 0) hM).symm.surjective).mp hP
    exact (normalEquiv10 M (fun _ => 0) hM).symm.injective he ▸ hQ

theorem selected_normal_substitution10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, Ideal.span (Set.range (M h)) = ⊤)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : P ≠ 0) :
    ∃ (e : Fin m → Equiv.Perm (Fin 10)) (N : Fin m → Fin 10 → ℤ)
      (PN : MvPolynomial (Vars10 m) ℚ),
      (∀ h k, N h k = M h (e h k)) ∧
      (∀ h, N h 0 ≠ 0 ∧ (N h 0).natAbs = normalHeight10 (M h) ∧
        Int.gcd (N h 0) (N h 1)^9 ≤ (N h 0).natAbs^8) ∧
      PN = normalPolynomialQ10 N P ∧ PN ≠ 0 ∧
      forward10 N (fun _ => 0) PN = P.map (Int.castRingHom ℚ) ∧
      (∀ (r : Fin m → ℕ) (c : ℝ),
        P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 N r c ↔
          PN.map (Rat.castHom ℝ) ∈ coordinateIdeal10 r c) ∧
      (∀ (r : Fin m → ℕ) (c : ℝ),
        P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 N r c ↔
          PN.map (Rat.castHom ℝ) ∈ coordinateStrictIdeal10 r c) := by
  let C := fun h => Classical.choice (normal_coordinate_choice10 (M h) (hM h))
  let e := fun h => (C h).e
  let N := fun h k => M h (e h k)
  have hn : ∀ h, N h 0 ≠ 0 := by
    intro h
    change M h ((C h).e 0) ≠ 0
    rw [(C h).e_zero]
    exact (C h).first_nonzero
  let PN := normalPolynomialQ10 N P
  refine ⟨e,N,PN,fun _ _ => rfl,?_,rfl,normalPolynomialQ10_nonzero N hn P hP,
    normalPolynomialQ10_forward N hn P,?_,?_⟩
  · intro h
    refine ⟨hn h,?_,?_⟩
    · change (M h ((C h).e 0)).natAbs = _
      rw [(C h).e_zero]
      exact (C h).height_attains.symm
    · change Int.gcd (M h ((C h).e 0)) (M h ((C h).e 1))^9 ≤ (M h ((C h).e 0)).natAbs^8
      rw [(C h).e_zero,(C h).e_one]
      exact (C h).gcd_bound
  · intro r c
    rw [show PN.map (Rat.castHom ℝ) = inverse10 N (fun _ => 0)
      (P.map (Int.castRingHom ℝ)) from normalPolynomialQ10_real N P]
    exact inverse10_ideal_iff N hn r c _
  · intro r c
    rw [show PN.map (Rat.castHom ℝ) = inverse10 N (fun _ => 0)
      (P.map (Int.castRingHom ℝ)) from normalPolynomialQ10_real N P]
    exact inverse10_strictIdeal_iff N hn r c _

def firstNineSpan10 {K : Type*} [Field K] (v : Fin 10 → Fin 10 → K) :
    Submodule K (Fin 10 → K) := Submodule.span K (Set.range (fun j : Fin 9 => v j.castSucc))

theorem lastDual10_kernel (v : Fin 10 → Fin 10 → ℚ) (hv : LinearIndependent ℚ v) :
    LinearMap.ker (rationalFrameDual42 v hv 9) = firstNineSpan10 v := by
  apply le_antisymm
  · intro x hx
    have hz : (rationalFrameBasis42 v hv).repr x 9 = 0 := by
      rw [← Basis.dualBasis_apply]
      exact (show rationalFrameDual42 v hv 9 x = 0 from hx)
    have he := (rationalFrameBasis42 v hv).sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 9 = (9 : Fin 10) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [rationalFrameBasis42_apply]
    exact Submodule.subset_span ⟨i,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change rationalFrameDual42 v hv 9 (v i.castSucc) = 0
    rw [rationalFrameDual42_pairing,if_neg]
    exact fun h => by have := congrArg Fin.val h; simp at this; omega

def normalForm10 (M : Fin 10 → ℤ) : Module.Dual ℚ (Fin 10 → ℚ) :=
  ∑ i, (M i : ℚ) • LinearMap.proj i

theorem normalForm10_apply (M : Fin 10 → ℤ) (x : Fin 10 → ℚ) :
    normalForm10 M x = ∑ i, (M i : ℚ)*x i := by
  simp [normalForm10]

theorem functional_coordinates10 (f : Module.Dual ℚ (Fin 10 → ℚ)) (x : Fin 10 → ℚ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  have hx : x = ∑ i : Fin 10, x i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  conv_lhs => rw [hx]
  simp

theorem primitive_integer10 (z : Fin 10 → ℤ) (hz : z ≠ 0) :
    ∃ (g : ℤ) (M a : Fin 10 → ℤ), g ≠ 0 ∧ M ≠ 0 ∧
      (∀ i, z i = g*M i) ∧ (∑ i, a i*M i) = 1 ∧ Ideal.span (Set.range M) = ⊤ := by
  let I : Ideal ℤ := Ideal.span (Set.range z)
  let g := Submodule.IsPrincipal.generator I
  have hdiv (i : Fin 10) : g ∣ z i :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_range_self i))
  choose M hM using hdiv
  have hg : g ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hM i,he,zero_mul]
    rfl
  have hgm : g ∈ Submodule.span ℤ (Set.range z) := by
    rw [Ideal.submodule_span_eq]
    exact Submodule.IsPrincipal.generator_mem I
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hgm
  simp only [smul_eq_mul] at ha
  have hsum : ∑ i, a i*M i = 1 := by
    apply mul_left_cancel₀ hg
    calc
      g*(∑ i, a i*M i) = ∑ i, a i*z i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hM i]
        ring
      _ = g*1 := by simpa using ha
  have hspan : Ideal.span (Set.range M) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hsum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  have hMn : M ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hM i,he]
    simp
  exact ⟨g,M,a,hg,hMn,hM,hsum,hspan⟩

theorem primitive_normal10 (v : Fin 10 → Fin 10 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) :
    ∃ M a : Fin 10 → ℤ, M ≠ 0 ∧ (∑ i, a i*M i) = 1 ∧
      Ideal.span (Set.range M) = ⊤ ∧
      (∀ j : Fin 9, (∑ i, M i*v j.castSucc i) = 0) ∧
      LinearMap.ker (normalForm10 M) =
        Submodule.span ℚ (Set.range (fun j : Fin 9 => fun i => (v j.castSucc i : ℚ))) := by
  let u : Fin 10 → Fin 10 → ℚ := fun j i => (v j i : ℚ)
  let f := rationalFrameDual42 u hv 9
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun i : Fin 10 => f (Pi.single i 1))
  have hDn : (D : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp D.property
  have hDQ : ((D : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hDn
  have hcoords : ∀ i : Fin 10, ∃ z : ℤ, (z : ℚ) = ((D : ℤ) : ℚ)*f (Pi.single i 1) := by
    intro i
    obtain ⟨z,hz⟩ := hD i
    exact ⟨z,by simpa only [Algebra.smul_def,map_intCast] using hz⟩
  choose z hz using hcoords
  have hzf : normalForm10 z = ((D : ℤ) : ℚ) • f := by
    apply LinearMap.ext
    intro x
    rw [normalForm10_apply,LinearMap.smul_apply,smul_eq_mul,functional_coordinates10 f x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hz i]
    ring
  have hzn : z ≠ 0 := by
    intro he
    have heq := congrArg (fun F : Module.Dual ℚ (Fin 10 → ℚ) => F (u 9)) hzf
    have hp : f (u 9) = 1 := by simpa using rationalFrameDual42_pairing u hv 9 9
    rw [he] at heq
    simp only [normalForm10_apply,Pi.zero_apply,Int.cast_zero,zero_mul,
      Finset.sum_const_zero,LinearMap.smul_apply,smul_eq_mul,hp,if_pos rfl,mul_one] at heq
    exact hDQ heq.symm
  obtain ⟨g,M,a,hg,hMn,hscale,ha,hprimitive⟩ := primitive_integer10 z hzn
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hzM : normalForm10 z = (g : ℚ) • normalForm10 M := by
    apply LinearMap.ext
    intro x
    rw [normalForm10_apply,LinearMap.smul_apply,normalForm10_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i]
    push_cast
    ring
  have hker : LinearMap.ker (normalForm10 M) = LinearMap.ker f := by
    calc
      _ = LinearMap.ker (normalForm10 z) := by rw [hzM,LinearMap.ker_smul _ _ hgQ]
      _ = _ := by rw [hzf,LinearMap.ker_smul _ _ hDQ]
  have hk : LinearMap.ker (normalForm10 M) = firstNineSpan10 u :=
    hker.trans (lastDual10_kernel u hv)
  refine ⟨M,a,hMn,ha,hprimitive,?_,hk⟩
  intro j
  have hm : u j.castSucc ∈ LinearMap.ker (normalForm10 M) := by
    rw [hk]
    exact Submodule.subset_span (Set.mem_range_self j)
  have hmQ : (∑ i, (M i : ℚ)*(v j.castSucc i : ℚ)) = 0 := by
    exact (normalForm10_apply M (u j.castSucc)).symm.trans hm
  exact_mod_cast hmQ


theorem original_frame_normal_substitution10
    (v : Fin 10 → Fin 10 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (P : MvPolynomial (Vars10 1) ℤ) (hP : P ≠ 0) :
    ∃ M : Fin 10 → ℤ, M ≠ 0 ∧ Ideal.span (Set.range M) = ⊤ ∧
      LinearMap.ker (normalForm10 M) = firstNineSpan10 (fun j i => (v j i : ℚ)) ∧
      ∃ (e : Equiv.Perm (Fin 10)) (N : Fin 10 → ℤ)
        (PN : MvPolynomial (Vars10 1) ℚ),
        (∀ k, N k = M (e k)) ∧ N 0 ≠ 0 ∧
        Int.gcd (N 0) (N 1)^9 ≤ (N 0).natAbs^8 ∧ PN ≠ 0 ∧
        forward10 (fun _ => N) (fun _ => 0) PN = P.map (Int.castRingHom ℚ) := by
  obtain ⟨M,a,hn,ha,hp,hann,hker⟩ := primitive_normal10 v hv
  obtain ⟨e,N,PN,he,hdata,hPN,hne,hforward,hclosed,hstrict⟩ :=
    selected_normal_substitution10 (fun _ : Fin 1 => M) (fun _ => hp) P hP
  have hN : N = fun _ : Fin 1 => N 0 := by
    funext h
    have hh : h = 0 := Subsingleton.elim _ _
    subst h
    rfl
  rw [hN] at hforward
  exact ⟨M,hn,hp,hker,e 0,N 0,PN,he 0,(hdata 0).1,(hdata 0).2.2,hne,hforward⟩

end CompoundFeasibility.SchmidtNormal10
