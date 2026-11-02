import SubspaceBridge.SchmidtScalarReduction4
import Mathlib.Data.Nat.Factorization.Basic
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtNormalCoordinates4
open SourceMultiblock4 SourceNormalIndex4 Auxiliary4 SchmidtScalarReduction4
open SchmidtRationalNormalization6 (rootDenominator6 integer_normalization6)

def normalHeight4 (M : Fin 4 → ℤ) : ℕ := Finset.univ.sup (fun i => (M i).natAbs)

theorem normalHeight4_coord (M : Fin 4 → ℤ) (i : Fin 4) :
    |(M i : ℝ)| ≤ (normalHeight4 M : ℝ) := by
  have hi := Finset.le_sup (f := fun i => (M i).natAbs) (Finset.mem_univ i)
  have he : ((M i).natAbs : ℝ) = |(M i : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [← he]
  exact_mod_cast hi

theorem normalHeight4_pos (M : Fin 4 → ℤ) (hM : M ≠ 0) : 0 < normalHeight4 M := by
  by_contra hn
  have hz : normalHeight4 M = 0 := by omega
  apply hM
  funext i
  have hi : (M i).natAbs ≤ normalHeight4 M := Finset.le_sup (f := fun j => (M j).natAbs) (Finset.mem_univ i)
  rw [hz] at hi
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)

theorem normalHeight4_neg (M : Fin 4 → ℤ) : normalHeight4 (-M) = normalHeight4 M := by
  simp [normalHeight4]

theorem normalHeight4_le_iff (M : Fin 4 → ℤ) (H : ℕ) :
    normalHeight4 M ≤ H ↔ ∀ i, (M i).natAbs ≤ H := by
  simp [normalHeight4,Finset.sup_le_iff]

theorem normalHeight4_normalization_bound (z M : Fin 4 → ℤ) (g : ℤ)
    (hg : g ≠ 0) (hz : ∀ i, z i = g*M i) : normalHeight4 M ≤ normalHeight4 z := by
  apply (normalHeight4_le_iff _ _).mpr
  intro i
  have hg1 : 1 ≤ g.natAbs := Int.natAbs_pos.mpr hg
  have hi := (normalHeight4_le_iff z _).mp le_rfl i
  rw [hz i,Int.natAbs_mul] at hi
  exact (show (M i).natAbs ≤ g.natAbs*(M i).natAbs by
    simpa only [one_mul] using Nat.mul_le_mul_right (M i).natAbs hg1).trans hi

theorem primitive_common_divisor4 (M : Fin 4 → ℤ)
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

theorem height_attaining4 (M : Fin 4 → ℤ) (hM : M ≠ 0) :
    ∃ i : Fin 4, M i ≠ 0 ∧ (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧
      normalHeight4 M = (M i).natAbs := by
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun k : Fin 4 => (M k).natAbs)
  have hmax (k) : (M k).natAbs ≤ (M i).natAbs := by
    rw [← he]
    exact Finset.le_sup (f := fun k : Fin 4 => (M k).natAbs) (Finset.mem_univ k)
  have hi : M i ≠ 0 := by
    intro hz
    apply hM
    funext k
    have hk := hmax k
    rw [hz,Int.natAbs_zero] at hk
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
  exact ⟨i,hi,hmax,he⟩

theorem three_gcd_product_dvd4 (M : Fin 4 → ℤ)
    (hM : Ideal.span (Set.range M) = ⊤) (i : Fin 4) (hi : M i ≠ 0) :
    (∏ j ∈ Finset.univ.erase i, Nat.gcd (M i).natAbs (M j).natAbs) ∣
      (M i).natAbs^2 := by
  let A := (M i).natAbs
  let d := fun j : Fin 4 => Nat.gcd A (M j).natAbs
  let S := Finset.univ.erase i
  have hA : A ≠ 0 := Int.natAbs_ne_zero.mpr hi
  have hd (j : Fin 4) : d j ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hA)).ne'
  have hS : S.card = 3 := by simp [S]
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  change (∏ j ∈ S, d j) ∣ A^2
  apply (Nat.factorization_prime_le_iff_dvd (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))
    (pow_ne_zero 2 hA)).mp
  intro p hp
  have hbound (j : Fin 4) : (d j).factorization p ≤ A.factorization p :=
    (Nat.factorization_le_iff_dvd (hd j) hA).mpr (Nat.gcd_dvd_left _ _) p
  have hsome : ∃ j ∈ S, ¬p ∣ d j := by
    by_contra! hall
    have hone : p = 1 := primitive_common_divisor4 M hM p (by
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
    _ = 2*A.factorization p := by
      simp [Finset.card_erase_of_mem hj,hS]

theorem minimum_secondary_gcd4 (M : Fin 4 → ℤ) (i : Fin 4) :
    ∃ j : Fin 4, j ≠ i ∧
      (∀ k : Fin 4, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)) ∧
      Int.gcd (M i) (M j)^3 ≤
        ∏ k ∈ Finset.univ.erase i, Nat.gcd (M i).natAbs (M k).natAbs := by
  let S := Finset.univ.erase i
  let d := fun k : Fin 4 => Int.gcd (M i) (M k)
  have hS : S.card = 3 := by simp [S]
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S d (Finset.card_pos.mp (by omega))
  have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
  refine ⟨j,hjne,fun k hk => hmin k (by simpa [S] using hk),?_⟩
  have hp := Finset.prod_le_prod' hmin
  simpa [d,hS] using hp

theorem primitive_nonzero4 (M : Fin 4 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) : M ≠ 0 := by
  intro hz
  have h := primitive_common_divisor4 M hM 0 (by intro k; rw [hz]; simp)
  omega

theorem select_minimum_pair4 (M : Fin 4 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) :
    ∃ i j : Fin 4, i ≠ j ∧ M i ≠ 0 ∧
      (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧ normalHeight4 M = (M i).natAbs ∧
      (∀ k : Fin 4, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)) ∧
      Int.gcd (M i) (M j)^3 ≤ (M i).natAbs^2 := by
  obtain ⟨i,hi,hmax,hheight⟩ := height_attaining4 M (primitive_nonzero4 M hM)
  obtain ⟨j,hji,hmin,hpow⟩ := minimum_secondary_gcd4 M i
  have hprod := three_gcd_product_dvd4 M hM i hi
  exact ⟨i,j,Ne.symm hji,hi,hmax,hheight,hmin,hpow.trans
    (Nat.le_of_dvd (pow_pos (Int.natAbs_pos.mpr hi) 2) hprod)⟩

theorem select_pair4 (M : Fin 4 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) :
    ∃ i j : Fin 4, i ≠ j ∧ M i ≠ 0 ∧
      (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧
      Int.gcd (M i) (M j)^3 ≤ (M i).natAbs^2 := by
  obtain ⟨i,j,hij,hi,hmax,_,_,hpow⟩ := select_minimum_pair4 M hM
  exact ⟨i,j,hij,hi,hmax,hpow⟩

def pairPermutation4 (i j : Fin 4) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 1 (Equiv.swap 0 i j)).trans (Equiv.swap 0 i)

theorem pairPermutation4_coordinates (i j : Fin 4) (hij : i ≠ j) :
    pairPermutation4 i j 0 = i ∧ pairPermutation4 i j 1 = j := by
  have hk : Equiv.swap 0 i j ≠ 0 := by
    intro hz
    have he : Equiv.swap 0 i j = Equiv.swap 0 i i := by simpa using hz
    exact hij ((Equiv.swap 0 i).injective he).symm
  constructor
  · simp only [pairPermutation4,Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) (Ne.symm hk),
      Equiv.swap_apply_left]
  · simp [pairPermutation4,Equiv.trans_apply]

def coefficientMultiset4 (M : Fin 4 → ℤ) : Multiset ℤ := ∑ k, ({M k} : Multiset ℤ)

theorem permuted_coefficients4 (M : Fin 4 → ℤ) (e : Equiv.Perm (Fin 4)) :
    coefficientMultiset4 (fun k => M (e k)) = coefficientMultiset4 M := by
  exact e.sum_comp Finset.univ (fun k => ({M k} : Multiset ℤ)) (by intro k _; simp)

theorem permuted_range4 (M : Fin 4 → ℤ) (e : Equiv.Perm (Fin 4)) :
    Set.range (fun k => M (e k)) = Set.range M := by
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨e k,rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨e.symm k,by simp⟩

theorem permuted_primitive4 (M : Fin 4 → ℤ) (e : Equiv.Perm (Fin 4))
    (hM : Ideal.span (Set.range M) = ⊤) :
    Ideal.span (Set.range (fun k => M (e k))) = ⊤ := by
  rw [permuted_range4 M e,hM]

theorem permuted_height4 (M : Fin 4 → ℤ) (e : Equiv.Perm (Fin 4)) :
    normalHeight4 (fun k => M (e k)) = normalHeight4 M := by
  apply le_antisymm
  · apply (normalHeight4_le_iff _ _).mpr
    intro k
    exact Finset.le_sup (f := fun j => (M j).natAbs) (Finset.mem_univ (e k))
  · apply (normalHeight4_le_iff _ _).mpr
    intro k
    simpa using Finset.le_sup (f := fun j => (M (e j)).natAbs) (Finset.mem_univ (e.symm k))

theorem permuted_bezout4 (M a : Fin 4 → ℤ) (e : Equiv.Perm (Fin 4))
    (ha : (∑ k, a k*M k) = 1) : (∑ k, a (e k)*M (e k)) = 1 := by
  rw [e.sum_comp Finset.univ (fun k => a k*M k) (by intro k _; simp),ha]

structure NormalCoordinateChoice4 (M : Fin 4 → ℤ) where
  i : Fin 4
  j : Fin 4
  distinct : i ≠ j
  primitive : Ideal.span (Set.range M) = ⊤
  first_nonzero : M i ≠ 0
  maximal : ∀ k, (M k).natAbs ≤ (M i).natAbs
  height_attains : normalHeight4 M = (M i).natAbs
  minimum : ∀ k : Fin 4, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)
  gcd_bound : Int.gcd (M i) (M j)^3 ≤ (M i).natAbs^2
  e : Equiv.Perm (Fin 4)
  e_zero : e 0 = i
  e_one : e 1 = j

theorem normal_coordinate_choice4 (M : Fin 4 → ℤ)
    (hM : Ideal.span (Set.range M) = ⊤) : Nonempty (NormalCoordinateChoice4 M) := by
  obtain ⟨i,j,hij,hi,hmax,hheight,hmin,hpow⟩ := select_minimum_pair4 M hM
  obtain ⟨he0,he1⟩ := pairPermutation4_coordinates i j hij
  exact ⟨{
    i := i, j := j, distinct := hij, primitive := hM, first_nonzero := hi,
    maximal := hmax, height_attains := hheight, minimum := hmin, gcd_bound := hpow,
    e := pairPermutation4 i j, e_zero := he0, e_one := he1 }⟩

theorem NormalCoordinateChoice4.permuted_data {M : Fin 4 → ℤ} (C : NormalCoordinateChoice4 M) :
    coefficientMultiset4 (fun k => M (C.e k)) = coefficientMultiset4 M ∧
    Ideal.span (Set.range (fun k => M (C.e k))) = ⊤ ∧
    normalHeight4 (fun k => M (C.e k)) = normalHeight4 M ∧
    M (C.e 0) ≠ 0 ∧
    Int.gcd (M (C.e 0)) (M (C.e 1))^3 ≤ normalHeight4 (fun k => M (C.e k))^2 ∧
    (∀ k, C.e.symm (C.e k) = k) ∧ (∀ k, C.e (C.e.symm k) = k) ∧
    (∀ k, (fun j => M (C.e j)) (C.e.symm k) = M k) := by
  refine ⟨permuted_coefficients4 M C.e,permuted_primitive4 M C.e C.primitive,
    permuted_height4 M C.e,?_,?_,C.e.symm_apply_apply,C.e.apply_symm_apply,?_⟩
  · rw [C.e_zero]
    exact C.first_nonzero
  · rw [C.e_zero,C.e_one,permuted_height4 M C.e,C.height_attains]
    exact C.gcd_bound
  · intro k
    simp

def variablePermutation4 {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4)) :
    Equiv.Perm (Vars4 m) where
  toFun u := (u.1,(e u.1).symm u.2)
  invFun u := (u.1,e u.1 u.2)
  left_inv u := by rcases u with ⟨h,j⟩; simp
  right_inv u := by rcases u with ⟨h,j⟩; simp

theorem variablePermutation4_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (h : Fin m) (j : Fin 4) : variablePermutation4 e (h,j) = (h,(e h).symm j) := rfl

theorem variablePermutation4_symm_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (h : Fin m) (k : Fin 4) : (variablePermutation4 e).symm (h,k) = (h,e h k) := rfl

theorem variablePermutation4_inverses {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4)) :
    (∀ u, (variablePermutation4 e).symm (variablePermutation4 e u) = u) ∧
    (∀ u, variablePermutation4 e ((variablePermutation4 e).symm u) = u) :=
  ⟨(variablePermutation4 e).symm_apply_apply,(variablePermutation4 e).apply_symm_apply⟩

def transport4 (A : Type*) [CommRing A] {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4)) :
    MvPolynomial (Vars4 m) A ≃+* MvPolynomial (Vars4 m) A :=
  (MvPolynomial.renameEquiv A (variablePermutation4 e)).toRingEquiv

theorem transport4_inverse {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (P : MvPolynomial (Vars4 m) A) :
    (transport4 A e).symm (transport4 A e P) = P ∧
      transport4 A e ((transport4 A e).symm P) = P :=
  ⟨(transport4 A e).symm_apply_apply P,(transport4 A e).apply_symm_apply P⟩

theorem transport4_nonzero {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (P : MvPolynomial (Vars4 m) A) :
    transport4 A e P ≠ 0 ↔ P ≠ 0 := (transport4 A e).map_ne_zero_iff

def exponentPermutation4 {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4)) :
    Equiv.Perm (Vars4 m →₀ ℕ) := Finsupp.equivCongrLeft (variablePermutation4 e)

theorem exponentPermutation4_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (d : Vars4 m →₀ ℕ) (h : Fin m) (k : Fin 4) :
    exponentPermutation4 e d (h,k) = d (h,e h k) := rfl

theorem transport4_coeff {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (P : MvPolynomial (Vars4 m) A)
    (d : Vars4 m →₀ ℕ) : (transport4 A e P).coeff (exponentPermutation4 e d) = P.coeff d := by
  change (MvPolynomial.rename (variablePermutation4 e) P).coeff
    (Finsupp.equivMapDomain (variablePermutation4 e) d) = P.coeff d
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact MvPolynomial.coeff_rename_mapDomain (variablePermutation4 e)
    (variablePermutation4 e).injective P d

theorem transport4_coeff_all {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (P : MvPolynomial (Vars4 m) A)
    (d : Vars4 m →₀ ℕ) :
    (transport4 A e P).coeff d = P.coeff ((exponentPermutation4 e).symm d) := by
  simpa using transport4_coeff e P ((exponentPermutation4 e).symm d)

theorem transport4_support {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (P : MvPolynomial (Vars4 m) A) :
    (transport4 A e P).support = P.support.image (exponentPermutation4 e) := by
  have he : (exponentPermutation4 e : (Vars4 m →₀ ℕ) → (Vars4 m →₀ ℕ)) =
      Finsupp.mapDomain (variablePermutation4 e) := by
    funext d
    exact Finsupp.equivMapDomain_eq_mapDomain (variablePermutation4 e) d
  rw [he]
  exact MvPolynomial.support_rename_of_injective (variablePermutation4 e).injective

theorem transport4_height {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (P : MvPolynomial (Vars4 m) ℤ) : height4 (transport4 ℤ e P) = height4 P := by
  unfold height4
  rw [transport4_support,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d _
  change ((transport4 ℤ e P).coeff (exponentPermutation4 e d)).natAbs = (P.coeff d).natAbs
  rw [transport4_coeff]

theorem exponentPermutation4_block_sum {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (d : Vars4 m →₀ ℕ) (h : Fin m) :
    (∑ k : Fin 4, exponentPermutation4 e d (h,k)) = ∑ j : Fin 4, d (h,j) := by
  exact (e h).sum_comp Finset.univ (fun j => d (h,j)) (by intro j _; simp)

theorem transport4_blockDegree {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (P : MvPolynomial (Vars4 m) A) (h : Fin m) :
    blockDegree4 (transport4 A e P) h = blockDegree4 P h := by
  unfold blockDegree4
  rw [transport4_support,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d _
  exact exponentPermutation4_block_sum e d h

theorem transport4_homogeneous {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A) :
    homogeneous4 r (transport4 A e P) ↔ homogeneous4 r P := by
  constructor
  · intro hP d hd h
    have hm : exponentPermutation4 e d ∈ (transport4 A e P).support := by
      rw [transport4_support]
      exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
    exact (exponentPermutation4_block_sum e d h).symm.trans (hP _ hm h)
  · intro hP d hd h
    rw [transport4_support] at hd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hd
    exact (exponentPermutation4_block_sum e a h).trans (hP a ha h)


theorem transport4_X {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (u : Vars4 m) :
    transport4 A e (MvPolynomial.X u) = MvPolynomial.X (variablePermutation4 e u) :=
  MvPolynomial.rename_X (variablePermutation4 e) u

theorem transport4_C {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (a : A) :
    transport4 A e (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.rename_C (variablePermutation4 e) a

theorem transport4_map {A B : Type*} [CommRing A] [CommRing B] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 4)) (f : A →+* B) (P : MvPolynomial (Vars4 m) A) :
    (transport4 A e P).map f = transport4 B e (P.map f) :=
  MvPolynomial.map_rename f (variablePermutation4 e) P

def permutedNormals4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (e : Fin m → Equiv.Perm (Fin 4)) (h : Fin m) (k : Fin 4) : ℤ := M h (e h k)

theorem transport4_normalPolynomial {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    transport4 ℝ e (normalPolynomial4 M h) = normalPolynomial4 (permutedNormals4 M e) h := by
  simp only [normalPolynomial4,map_sum,map_mul,transport4_C,transport4_X,
    variablePermutation4_apply]
  simpa [permutedNormals4] using
    ((e h).sum_comp Finset.univ
      (fun j => MvPolynomial.C (M h j : ℝ)*MvPolynomial.X (h,(e h).symm j))
      (by intro j _; simp)).symm

theorem transport4_normal_products {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (M : Fin m → Fin 4 → ℤ) (i : Fin m → ℕ) :
    transport4 ℝ e (∏ h, normalPolynomial4 M h^(i h)) =
      ∏ h, normalPolynomial4 (permutedNormals4 M e) h^(i h) := by
  simp only [map_prod,map_pow,transport4_normalPolynomial]

theorem transport4_normalIdeal_map {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (M : Fin m → Fin 4 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (transport4 ℝ e).toRingHom (sourceNormalIdeal4 M r c) =
      sourceNormalIdeal4 (permutedNormals4 M e) r c := by
  unfold sourceNormalIdeal4
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,transport4_normal_products e M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,transport4_normal_products e M i⟩

theorem transport4_normalIdeal_iff {m : ℕ} (e : Fin m → Equiv.Perm (Fin 4))
    (M : Fin m → Fin 4 → ℤ) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars4 m) ℝ) :
    P ∈ sourceNormalIdeal4 M r c ↔
      transport4 ℝ e P ∈ sourceNormalIdeal4 (permutedNormals4 M e) r c := by
  rw [← transport4_normalIdeal_map e M r c]
  constructor
  · exact Ideal.mem_map_of_mem (transport4 ℝ e).toRingHom
  · intro hP
    obtain ⟨Q,hQ,he⟩ := (Ideal.mem_map_iff_of_surjective
      (transport4 ℝ e).toRingHom (transport4 ℝ e).surjective).mp hP
    exact (transport4 ℝ e).injective he ▸ hQ

theorem denominator_nat_bounds4 (a b : ℤ) (ha : a ≠ 0)
    (hb : Int.gcd a b^3 ≤ a.natAbs^2) :
    a.natAbs ≤ (rootDenominator6 a b).natAbs^3 ∧
      (rootDenominator6 a b).natAbs ≤ a.natAbs := by
  obtain ⟨hg,_,_,heq,_,_,_⟩ := integer_normalization6 a b ha
  have hA : a.natAbs = Int.gcd a b*(rootDenominator6 a b).natAbs := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs heq
  have hmul : (Int.gcd a b)^2*Int.gcd a b ≤
      (Int.gcd a b)^2*(rootDenominator6 a b).natAbs^2 := by
    calc
      (Int.gcd a b)^2*Int.gcd a b = (Int.gcd a b)^3 := by ring
      _ ≤ a.natAbs^2 := hb
      _ = (Int.gcd a b*(rootDenominator6 a b).natAbs)^2 := congrArg (fun n : ℕ => n^2) hA
      _ = _ := by ring
  have hc : Int.gcd a b ≤ (rootDenominator6 a b).natAbs^2 :=
    Nat.le_of_mul_le_mul_left hmul (pow_pos hg 2)
  constructor
  · calc
      a.natAbs = Int.gcd a b*(rootDenominator6 a b).natAbs := hA
      _ ≤ (rootDenominator6 a b).natAbs^2*(rootDenominator6 a b).natAbs := Nat.mul_le_mul_right _ hc
      _ = (rootDenominator6 a b).natAbs^3 := by ring
  · calc
      (rootDenominator6 a b).natAbs = 1*(rootDenominator6 a b).natAbs := (one_mul _).symm
      _ ≤ Int.gcd a b*(rootDenominator6 a b).natAbs := Nat.mul_le_mul_right _ (by omega)
      _ = a.natAbs := hA.symm

theorem denominator_real_bounds4 (a b : ℤ) (ha : a ≠ 0)
    (hb : Int.gcd a b^3 ≤ a.natAbs^2) :
    |(a : ℝ)|^(1/3 : ℝ) ≤ |(rootDenominator6 a b : ℝ)| ∧
      |(rootDenominator6 a b : ℝ)| ≤ |(a : ℝ)| := by
  obtain ⟨hl,hu⟩ := denominator_nat_bounds4 a b ha hb
  have hlR : (a.natAbs : ℝ) ≤ ((rootDenominator6 a b).natAbs : ℝ)^3 := by exact_mod_cast hl
  have huR : ((rootDenominator6 a b).natAbs : ℝ) ≤ (a.natAbs : ℝ) := by exact_mod_cast hu
  have hp : |(a : ℝ)| ≤ |(rootDenominator6 a b : ℝ)|^3 := by
    simpa only [Int.cast_natAbs,Int.cast_abs] using hlR
  constructor
  · rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos (abs_nonneg _) (abs_nonneg _) (by norm_num : (0 : ℝ) < 3)).mpr
    exact hp.trans_eq (Real.rpow_natCast _ 3).symm
  · simpa only [Int.cast_natAbs,Int.cast_abs] using huR


end CompoundFeasibility.SchmidtNormalCoordinates4
