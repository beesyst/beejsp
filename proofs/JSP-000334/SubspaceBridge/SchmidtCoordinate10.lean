import SubspaceBridge.SchmidtPolynomial10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SchmidtCoordinate10
open SchmidtNormal10 SchmidtPolynomial10 SourceNormalHighIndex10
noncomputable section

def variablePermutation10 {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10)) :
    Equiv.Perm (SourceMultiblock10.Vars10 m) where
  toFun u := (u.1,(e u.1).symm u.2)
  invFun u := (u.1,e u.1 u.2)
  left_inv u := by rcases u with ⟨h,j⟩; simp
  right_inv u := by rcases u with ⟨h,j⟩; simp

theorem variablePermutation10_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (h : Fin m) (j : Fin 10) : variablePermutation10 e (h,j) = (h,(e h).symm j) := rfl

theorem variablePermutation10_symm_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (h : Fin m) (k : Fin 10) : (variablePermutation10 e).symm (h,k) = (h,e h k) := rfl

theorem variablePermutation10_inverses {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10)) :
    (∀ u, (variablePermutation10 e).symm (variablePermutation10 e u) = u) ∧
    (∀ u, variablePermutation10 e ((variablePermutation10 e).symm u) = u) :=
  ⟨(variablePermutation10 e).symm_apply_apply,(variablePermutation10 e).apply_symm_apply⟩

def transport10 (A : Type*) [CommRing A] {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10)) :
    MvPolynomial (SourceMultiblock10.Vars10 m) A ≃+* MvPolynomial (SourceMultiblock10.Vars10 m) A :=
  (MvPolynomial.renameEquiv A (variablePermutation10 e)).toRingEquiv

theorem transport10_inverse {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) :
    (transport10 A e).symm (transport10 A e P) = P ∧
      transport10 A e ((transport10 A e).symm P) = P :=
  ⟨(transport10 A e).symm_apply_apply P,(transport10 A e).apply_symm_apply P⟩

theorem transport10_nonzero {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) :
    transport10 A e P ≠ 0 ↔ P ≠ 0 := (transport10 A e).map_ne_zero_iff

def exponentPermutation10 {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10)) :
    Equiv.Perm (SourceMultiblock10.Vars10 m →₀ ℕ) := Finsupp.equivCongrLeft (variablePermutation10 e)

theorem exponentPermutation10_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) (h : Fin m) (k : Fin 10) :
    exponentPermutation10 e d (h,k) = d (h,e h k) := rfl

theorem transport10_coeff {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) : (transport10 A e P).coeff (exponentPermutation10 e d) = P.coeff d := by
  change (MvPolynomial.rename (variablePermutation10 e) P).coeff
    (Finsupp.equivMapDomain (variablePermutation10 e) d) = P.coeff d
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact MvPolynomial.coeff_rename_mapDomain (variablePermutation10 e)
    (variablePermutation10 e).injective P d

theorem transport10_coeff_all {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) :
    (transport10 A e P).coeff d = P.coeff ((exponentPermutation10 e).symm d) := by
  simpa using transport10_coeff e P ((exponentPermutation10 e).symm d)

theorem transport10_support {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) :
    (transport10 A e P).support = P.support.image (exponentPermutation10 e) := by
  have he : (exponentPermutation10 e : (SourceMultiblock10.Vars10 m →₀ ℕ) → (SourceMultiblock10.Vars10 m →₀ ℕ)) =
      Finsupp.mapDomain (variablePermutation10 e) := by
    funext d
    exact Finsupp.equivMapDomain_eq_mapDomain (variablePermutation10 e) d
  rw [he]
  exact MvPolynomial.support_rename_of_injective (variablePermutation10 e).injective

theorem transport10_height {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) : height10 (transport10 ℤ e P) = height10 P := by
  unfold height10
  rw [transport10_support,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d _
  change ((transport10 ℤ e P).coeff (exponentPermutation10 e d)).natAbs = (P.coeff d).natAbs
  rw [transport10_coeff]

theorem exponentPermutation10_block_sum {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) (h : Fin m) :
    (∑ k : Fin 10, exponentPermutation10 e d (h,k)) = ∑ j : Fin 10, d (h,j) := by
  exact (e h).sum_comp Finset.univ (fun j => d (h,j)) (by intro j _; simp)

def blockDegree10 {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) (h : Fin m) : ℕ :=
  P.support.sup (fun d => ∑ j : Fin 10, d (h,j))

theorem transport10_blockDegree {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) (h : Fin m) :
    blockDegree10 (transport10 A e P) h = blockDegree10 P h := by
  unfold blockDegree10
  rw [transport10_support,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d _
  exact exponentPermutation10_block_sum e d h

theorem transport10_homogeneous {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) :
    homogeneous10 r (transport10 A e P) ↔ homogeneous10 r P := by
  constructor
  · intro hP d hd h
    have hm : exponentPermutation10 e d ∈ (transport10 A e P).support := by
      rw [transport10_support]
      exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
    exact (exponentPermutation10_block_sum e d h).symm.trans (hP _ hm h)
  · intro hP d hd h
    rw [transport10_support] at hd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hd
    exact (exponentPermutation10_block_sum e a h).trans (hP a ha h)


theorem transport10_X {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (u : SourceMultiblock10.Vars10 m) :
    transport10 A e (MvPolynomial.X u) = MvPolynomial.X (variablePermutation10 e u) :=
  MvPolynomial.rename_X (variablePermutation10 e) u

theorem transport10_C {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (a : A) :
    transport10 A e (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.rename_C (variablePermutation10 e) a

theorem transport10_map {A B : Type*} [CommRing A] [CommRing B] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 10)) (f : A →+* B) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) :
    (transport10 A e P).map f = transport10 B e (P.map f) :=
  MvPolynomial.map_rename f (variablePermutation10 e) P

def permutedNormals10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (e : Fin m → Equiv.Perm (Fin 10)) (h : Fin m) (k : Fin 10) : ℤ := M h (e h k)

theorem transport10_normalPolynomial {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    transport10 ℝ e (linearNormal10 M h) = linearNormal10 (permutedNormals10 M e) h := by
  simp only [linearNormal10,map_sum,map_mul,transport10_C,transport10_X,
    variablePermutation10_apply]
  simpa [permutedNormals10] using
    ((e h).sum_comp Finset.univ
      (fun j => MvPolynomial.C (M h j : ℝ)*MvPolynomial.X (h,(e h).symm j))
      (by intro j _; simp)).symm

theorem transport10_normal_products {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (M : Fin m → Fin 10 → ℤ) (i : Fin m → ℕ) :
    transport10 ℝ e (∏ h, linearNormal10 M h^(i h)) =
      ∏ h, linearNormal10 (permutedNormals10 M e) h^(i h) := by
  simp only [map_prod,map_pow,transport10_normalPolynomial]

theorem transport10_normalIdeal_map {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (M : Fin m → Fin 10 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (transport10 ℝ e).toRingHom (sourceNormalIdeal10 M r c) =
      sourceNormalIdeal10 (permutedNormals10 M e) r c := by
  unfold sourceNormalIdeal10
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,transport10_normal_products e M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,transport10_normal_products e M i⟩

theorem transport10_normalIdeal_iff {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (M : Fin m → Fin 10 → ℤ) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    P ∈ sourceNormalIdeal10 M r c ↔
      transport10 ℝ e P ∈ sourceNormalIdeal10 (permutedNormals10 M e) r c := by
  rw [← transport10_normalIdeal_map e M r c]
  constructor
  · exact Ideal.mem_map_of_mem (transport10 ℝ e).toRingHom
  · intro hP
    obtain ⟨Q,hQ,he⟩ := (Ideal.mem_map_iff_of_surjective
      (transport10 ℝ e).toRingHom (transport10 ℝ e).surjective).mp hP
    exact (transport10 ℝ e).injective he ▸ hQ

theorem transport10_strictIdeal_iff {m : ℕ} (e : Fin m → Equiv.Perm (Fin 10))
    (M : Fin m → Fin 10 → ℤ) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    P ∈ sourceStrictNormalIdeal10 M r c ↔
      transport10 ℝ e P ∈ sourceStrictNormalIdeal10 (permutedNormals10 M e) r c := by
  rw [sourceStrictNormalIdeal10_iff,sourceStrictNormalIdeal10_iff]
  constructor
  · rintro ⟨d,hd,hP⟩
    exact ⟨d,hd,(transport10_normalIdeal_iff e M r d P).mp hP⟩
  · rintro ⟨d,hd,hP⟩
    exact ⟨d,hd,(transport10_normalIdeal_iff e M r d P).mpr hP⟩


theorem choice_normal_data10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (C : (h : Fin m) → NormalCoordinateChoice10 (M h)) :
    ∀ h, let M' := permutedNormals10 M (fun g => (C g).e) h
      coefficientMultiset10 M' = coefficientMultiset10 (M h) ∧
      Ideal.span (Set.range M') = ⊤ ∧ normalHeight10 M' = normalHeight10 (M h) ∧
      M' 0 ≠ 0 ∧ normalHeight10 M' = (M' 0).natAbs ∧
      (∀ k, (M' k).natAbs ≤ (M' 0).natAbs) ∧
      Int.gcd (M' 0) (M' 1)^9 ≤ normalHeight10 M'^8 ∧
      (∀ k, M' ((C h).e.symm k) = M h k) := by
  intro h
  obtain ⟨hcoeff,hprim,hheight,hfirst,hgcd,_,_,hinv⟩ := (C h).permuted_data
  refine ⟨hcoeff,hprim,hheight,hfirst,?_,?_,hgcd,hinv⟩
  · change normalHeight10 (fun k => M h ((C h).e k)) = (M h ((C h).e 0)).natAbs
    rw [hheight,(C h).e_zero,(C h).height_attains]
  · intro k
    change (M h ((C h).e k)).natAbs ≤ (M h ((C h).e 0)).natAbs
    rw [(C h).e_zero]
    exact (C h).maximal _


end
end CompoundFeasibility.SchmidtCoordinate10
