import SubspaceBridge.SourceSchmidtParameters6
import Mathlib.Data.Nat.Factorization.Basic
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtHilfssatz13
open SourceNormalHeight SourceReadiness6 SourceSchmidtParameters6

theorem primitive_common_divisor6 (M : Fin 6 → ℤ)
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

theorem height_attaining6 (M : Fin 6 → ℤ) (hM : M ≠ 0) :
    ∃ i : Fin 6, M i ≠ 0 ∧ (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧
      normalHeight6 M = (M i).natAbs := by
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun k : Fin 6 => (M k).natAbs)
  have hmax (k) : (M k).natAbs ≤ (M i).natAbs := by
    rw [← he]
    exact Finset.le_sup (f := fun k : Fin 6 => (M k).natAbs) (Finset.mem_univ k)
  have hi : M i ≠ 0 := by
    intro hz
    apply hM
    funext k
    have hk := hmax k
    rw [hz,Int.natAbs_zero] at hk
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
  exact ⟨i,hi,hmax,he⟩

theorem five_gcd_product_dvd6 (M : Fin 6 → ℤ)
    (hM : Ideal.span (Set.range M) = ⊤) (i : Fin 6) (hi : M i ≠ 0) :
    (∏ j ∈ Finset.univ.erase i, Nat.gcd (M i).natAbs (M j).natAbs) ∣
      (M i).natAbs^4 := by
  let A := (M i).natAbs
  let d := fun j : Fin 6 => Nat.gcd A (M j).natAbs
  let S := Finset.univ.erase i
  have hA : A ≠ 0 := Int.natAbs_ne_zero.mpr hi
  have hd (j : Fin 6) : d j ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hA)).ne'
  have hS : S.card = 5 := by simp [S]
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  change (∏ j ∈ S, d j) ∣ A^4
  apply (Nat.factorization_prime_le_iff_dvd (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))
    (pow_ne_zero 4 hA)).mp
  intro p hp
  have hbound (j : Fin 6) : (d j).factorization p ≤ A.factorization p :=
    (Nat.factorization_le_iff_dvd (hd j) hA).mpr (Nat.gcd_dvd_left _ _) p
  have hsome : ∃ j ∈ S, ¬p ∣ d j := by
    by_contra! hall
    have hone : p = 1 := primitive_common_divisor6 M hM p (by
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
    _ = 4*A.factorization p := by
      simp [Finset.card_erase_of_mem hj,hS]

theorem minimum_secondary_gcd6 (M : Fin 6 → ℤ) (i : Fin 6) :
    ∃ j : Fin 6, j ≠ i ∧
      (∀ k : Fin 6, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)) ∧
      Int.gcd (M i) (M j)^5 ≤
        ∏ k ∈ Finset.univ.erase i, Nat.gcd (M i).natAbs (M k).natAbs := by
  let S := Finset.univ.erase i
  let d := fun k : Fin 6 => Int.gcd (M i) (M k)
  have hS : S.card = 5 := by simp [S]
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S d (Finset.card_pos.mp (by omega))
  have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
  refine ⟨j,hjne,fun k hk => hmin k (by simpa [S] using hk),?_⟩
  have hp := Finset.prod_le_prod' hmin
  simpa [d,hS] using hp

theorem primitive_nonzero6 (M : Fin 6 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) : M ≠ 0 := by
  intro hz
  have h := primitive_common_divisor6 M hM 0 (by intro k; rw [hz]; simp)
  omega

theorem select_minimum_pair6 (M : Fin 6 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) :
    ∃ i j : Fin 6, i ≠ j ∧ M i ≠ 0 ∧
      (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧ normalHeight6 M = (M i).natAbs ∧
      (∀ k : Fin 6, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)) ∧
      Int.gcd (M i) (M j)^5 ≤ (M i).natAbs^4 := by
  obtain ⟨i,hi,hmax,hheight⟩ := height_attaining6 M (primitive_nonzero6 M hM)
  obtain ⟨j,hji,hmin,hpow⟩ := minimum_secondary_gcd6 M i
  have hprod := five_gcd_product_dvd6 M hM i hi
  exact ⟨i,j,Ne.symm hji,hi,hmax,hheight,hmin,hpow.trans
    (Nat.le_of_dvd (pow_pos (Int.natAbs_pos.mpr hi) 4) hprod)⟩

theorem select_pair6 (M : Fin 6 → ℤ) (hM : Ideal.span (Set.range M) = ⊤) :
    ∃ i j : Fin 6, i ≠ j ∧ M i ≠ 0 ∧
      (∀ k, (M k).natAbs ≤ (M i).natAbs) ∧
      Int.gcd (M i) (M j)^5 ≤ (M i).natAbs^4 := by
  obtain ⟨i,j,hij,hi,hmax,_,_,hpow⟩ := select_minimum_pair6 M hM
  exact ⟨i,j,hij,hi,hmax,hpow⟩

def pairPermutation6 (i j : Fin 6) : Equiv.Perm (Fin 6) :=
  (Equiv.swap 1 (Equiv.swap 0 i j)).trans (Equiv.swap 0 i)

theorem pairPermutation6_coordinates (i j : Fin 6) (hij : i ≠ j) :
    pairPermutation6 i j 0 = i ∧ pairPermutation6 i j 1 = j := by
  have hk : Equiv.swap 0 i j ≠ 0 := by
    intro hz
    have he : Equiv.swap 0 i j = Equiv.swap 0 i i := by simpa using hz
    exact hij ((Equiv.swap 0 i).injective he).symm
  constructor
  · simp only [pairPermutation6,Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 6) ≠ 1) (Ne.symm hk),
      Equiv.swap_apply_left]
  · simp [pairPermutation6,Equiv.trans_apply]

def coefficientMultiset6 (M : Fin 6 → ℤ) : Multiset ℤ := ∑ k, ({M k} : Multiset ℤ)

theorem permuted_coefficients6 (M : Fin 6 → ℤ) (e : Equiv.Perm (Fin 6)) :
    coefficientMultiset6 (fun k => M (e k)) = coefficientMultiset6 M := by
  exact e.sum_comp Finset.univ (fun k => ({M k} : Multiset ℤ)) (by intro k _; simp)

theorem permuted_range6 (M : Fin 6 → ℤ) (e : Equiv.Perm (Fin 6)) :
    Set.range (fun k => M (e k)) = Set.range M := by
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨e k,rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨e.symm k,by simp⟩

theorem permuted_primitive6 (M : Fin 6 → ℤ) (e : Equiv.Perm (Fin 6))
    (hM : Ideal.span (Set.range M) = ⊤) :
    Ideal.span (Set.range (fun k => M (e k))) = ⊤ := by
  rw [permuted_range6 M e,hM]

theorem permuted_height6 (M : Fin 6 → ℤ) (e : Equiv.Perm (Fin 6)) :
    normalHeight6 (fun k => M (e k)) = normalHeight6 M := by
  apply le_antisymm
  · apply (normalHeight6_le_iff _ _).mpr
    intro k
    exact Finset.le_sup (f := fun j => (M j).natAbs) (Finset.mem_univ (e k))
  · apply (normalHeight6_le_iff _ _).mpr
    intro k
    simpa using Finset.le_sup (f := fun j => (M (e j)).natAbs) (Finset.mem_univ (e.symm k))

theorem permuted_bezout6 (M a : Fin 6 → ℤ) (e : Equiv.Perm (Fin 6))
    (ha : (∑ k, a k*M k) = 1) : (∑ k, a (e k)*M (e k)) = 1 := by
  rw [e.sum_comp Finset.univ (fun k => a k*M k) (by intro k _; simp),ha]

structure NormalCoordinateChoice6 (M : Fin 6 → ℤ) where
  i : Fin 6
  j : Fin 6
  distinct : i ≠ j
  primitive : Ideal.span (Set.range M) = ⊤
  first_nonzero : M i ≠ 0
  maximal : ∀ k, (M k).natAbs ≤ (M i).natAbs
  height_attains : normalHeight6 M = (M i).natAbs
  minimum : ∀ k : Fin 6, k ≠ i → Int.gcd (M i) (M j) ≤ Int.gcd (M i) (M k)
  gcd_bound : Int.gcd (M i) (M j)^5 ≤ (M i).natAbs^4
  e : Equiv.Perm (Fin 6)
  e_zero : e 0 = i
  e_one : e 1 = j

theorem normal_coordinate_choice6 (M : Fin 6 → ℤ)
    (hM : Ideal.span (Set.range M) = ⊤) : Nonempty (NormalCoordinateChoice6 M) := by
  obtain ⟨i,j,hij,hi,hmax,hheight,hmin,hpow⟩ := select_minimum_pair6 M hM
  obtain ⟨he0,he1⟩ := pairPermutation6_coordinates i j hij
  exact ⟨{
    i := i, j := j, distinct := hij, primitive := hM, first_nonzero := hi,
    maximal := hmax, height_attains := hheight, minimum := hmin, gcd_bound := hpow,
    e := pairPermutation6 i j, e_zero := he0, e_one := he1 }⟩

theorem NormalCoordinateChoice6.permuted_data {M : Fin 6 → ℤ} (C : NormalCoordinateChoice6 M) :
    coefficientMultiset6 (fun k => M (C.e k)) = coefficientMultiset6 M ∧
    Ideal.span (Set.range (fun k => M (C.e k))) = ⊤ ∧
    normalHeight6 (fun k => M (C.e k)) = normalHeight6 M ∧
    M (C.e 0) ≠ 0 ∧
    Int.gcd (M (C.e 0)) (M (C.e 1))^5 ≤ normalHeight6 (fun k => M (C.e k))^4 ∧
    (∀ k, C.e.symm (C.e k) = k) ∧ (∀ k, C.e (C.e.symm k) = k) ∧
    (∀ k, (fun j => M (C.e j)) (C.e.symm k) = M k) := by
  refine ⟨permuted_coefficients6 M C.e,permuted_primitive6 M C.e C.primitive,
    permuted_height6 M C.e,?_,?_,C.e.symm_apply_apply,C.e.apply_symm_apply,?_⟩
  · rw [C.e_zero]
    exact C.first_nonzero
  · rw [C.e_zero,C.e_one,permuted_height6 M C.e,C.height_attains]
    exact C.gcd_bound
  · intro k
    simp

theorem schmidtPackage6_coordinate_choices
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) :
    ∃ C : (h : Fin S.m) → NormalCoordinateChoice6 (R.M (S.t h)),
      ∀ h, (∑ k, R.a (S.t h) ((C h).e k)*R.M (S.t h) ((C h).e k)) = 1 := by
  let C : (h : Fin S.m) → NormalCoordinateChoice6 (R.M (S.t h)) := fun h =>
    Classical.choice (normal_coordinate_choice6 (R.M (S.t h)) (R.normals (S.t h)).2.2.1)
  exact ⟨C,fun h => permuted_bezout6 (R.M (S.t h)) (R.a (S.t h)) (C h).e
    (R.normals (S.t h)).2.1⟩

end CompoundFeasibility.SchmidtHilfssatz13
