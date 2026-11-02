import SubspaceBridge.SchmidtHilfssatz13
import SubspaceBridge.SchmidtIndexSemantics6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtCoordinateTransport6
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtHilfssatz13 SourceNormalHeight SourceReadiness6 SourceSchmidtParameters6

def variablePermutation6 {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6)) :
    Equiv.Perm (Vars6 m) where
  toFun u := (u.1,(e u.1).symm u.2)
  invFun u := (u.1,e u.1 u.2)
  left_inv u := by rcases u with ⟨h,j⟩; simp
  right_inv u := by rcases u with ⟨h,j⟩; simp

theorem variablePermutation6_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (h : Fin m) (j : Fin 6) : variablePermutation6 e (h,j) = (h,(e h).symm j) := rfl

theorem variablePermutation6_symm_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (h : Fin m) (k : Fin 6) : (variablePermutation6 e).symm (h,k) = (h,e h k) := rfl

theorem variablePermutation6_inverses {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6)) :
    (∀ u, (variablePermutation6 e).symm (variablePermutation6 e u) = u) ∧
    (∀ u, variablePermutation6 e ((variablePermutation6 e).symm u) = u) :=
  ⟨(variablePermutation6 e).symm_apply_apply,(variablePermutation6 e).apply_symm_apply⟩

def transport6 (A : Type*) [CommRing A] {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6)) :
    MvPolynomial (Vars6 m) A ≃+* MvPolynomial (Vars6 m) A :=
  (MvPolynomial.renameEquiv A (variablePermutation6 e)).toRingEquiv

theorem transport6_inverse {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (P : MvPolynomial (Vars6 m) A) :
    (transport6 A e).symm (transport6 A e P) = P ∧
      transport6 A e ((transport6 A e).symm P) = P :=
  ⟨(transport6 A e).symm_apply_apply P,(transport6 A e).apply_symm_apply P⟩

theorem transport6_nonzero {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (P : MvPolynomial (Vars6 m) A) :
    transport6 A e P ≠ 0 ↔ P ≠ 0 := (transport6 A e).map_ne_zero_iff

def exponentPermutation6 {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6)) :
    Equiv.Perm (Vars6 m →₀ ℕ) := Finsupp.equivCongrLeft (variablePermutation6 e)

theorem exponentPermutation6_apply {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (d : Vars6 m →₀ ℕ) (h : Fin m) (k : Fin 6) :
    exponentPermutation6 e d (h,k) = d (h,e h k) := rfl

theorem transport6_coeff {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (P : MvPolynomial (Vars6 m) A)
    (d : Vars6 m →₀ ℕ) : (transport6 A e P).coeff (exponentPermutation6 e d) = P.coeff d := by
  change (MvPolynomial.rename (variablePermutation6 e) P).coeff
    (Finsupp.equivMapDomain (variablePermutation6 e) d) = P.coeff d
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact MvPolynomial.coeff_rename_mapDomain (variablePermutation6 e)
    (variablePermutation6 e).injective P d

theorem transport6_coeff_all {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (P : MvPolynomial (Vars6 m) A)
    (d : Vars6 m →₀ ℕ) :
    (transport6 A e P).coeff d = P.coeff ((exponentPermutation6 e).symm d) := by
  simpa using transport6_coeff e P ((exponentPermutation6 e).symm d)

theorem transport6_support {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (P : MvPolynomial (Vars6 m) A) :
    (transport6 A e P).support = P.support.image (exponentPermutation6 e) := by
  have he : (exponentPermutation6 e : (Vars6 m →₀ ℕ) → (Vars6 m →₀ ℕ)) =
      Finsupp.mapDomain (variablePermutation6 e) := by
    funext d
    exact Finsupp.equivMapDomain_eq_mapDomain (variablePermutation6 e) d
  rw [he]
  exact MvPolynomial.support_rename_of_injective (variablePermutation6 e).injective

theorem transport6_height {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (P : MvPolynomial (Vars6 m) ℤ) : height6 (transport6 ℤ e P) = height6 P := by
  unfold height6
  rw [transport6_support,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d _
  change ((transport6 ℤ e P).coeff (exponentPermutation6 e d)).natAbs = (P.coeff d).natAbs
  rw [transport6_coeff]

theorem exponentPermutation6_block_sum {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (d : Vars6 m →₀ ℕ) (h : Fin m) :
    (∑ k : Fin 6, exponentPermutation6 e d (h,k)) = ∑ j : Fin 6, d (h,j) := by
  exact (e h).sum_comp Finset.univ (fun j => d (h,j)) (by intro j _; simp)

def blockDegree6 {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (Vars6 m) A) (h : Fin m) : ℕ :=
  P.support.sup (fun d => ∑ j : Fin 6, d (h,j))

theorem transport6_blockDegree {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (P : MvPolynomial (Vars6 m) A) (h : Fin m) :
    blockDegree6 (transport6 A e P) h = blockDegree6 P h := by
  unfold blockDegree6
  rw [transport6_support,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d _
  exact exponentPermutation6_block_sum e d h

theorem transport6_homogeneous {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A) :
    homogeneous6 r (transport6 A e P) ↔ homogeneous6 r P := by
  constructor
  · intro hP d hd h
    have hm : exponentPermutation6 e d ∈ (transport6 A e P).support := by
      rw [transport6_support]
      exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
    exact (exponentPermutation6_block_sum e d h).symm.trans (hP _ hm h)
  · intro hP d hd h
    rw [transport6_support] at hd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hd
    exact (exponentPermutation6_block_sum e a h).trans (hP a ha h)


theorem transport6_X {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (u : Vars6 m) :
    transport6 A e (MvPolynomial.X u) = MvPolynomial.X (variablePermutation6 e u) :=
  MvPolynomial.rename_X (variablePermutation6 e) u

theorem transport6_C {A : Type*} [CommRing A] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (a : A) :
    transport6 A e (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.rename_C (variablePermutation6 e) a

theorem transport6_map {A B : Type*} [CommRing A] [CommRing B] {m : ℕ}
    (e : Fin m → Equiv.Perm (Fin 6)) (f : A →+* B) (P : MvPolynomial (Vars6 m) A) :
    (transport6 A e P).map f = transport6 B e (P.map f) :=
  MvPolynomial.map_rename f (variablePermutation6 e) P

def permutedNormals6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (e : Fin m → Equiv.Perm (Fin 6)) (h : Fin m) (k : Fin 6) : ℤ := M h (e h k)

theorem transport6_normalPolynomial {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    transport6 ℝ e (normalPolynomial6 M h) = normalPolynomial6 (permutedNormals6 M e) h := by
  simp only [normalPolynomial6,map_sum,map_mul,transport6_C,transport6_X,
    variablePermutation6_apply]
  simpa [permutedNormals6] using
    ((e h).sum_comp Finset.univ
      (fun j => MvPolynomial.C (M h j : ℝ)*MvPolynomial.X (h,(e h).symm j))
      (by intro j _; simp)).symm

theorem transport6_normal_products {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (M : Fin m → Fin 6 → ℤ) (i : Fin m → ℕ) :
    transport6 ℝ e (∏ h, normalPolynomial6 M h^(i h)) =
      ∏ h, normalPolynomial6 (permutedNormals6 M e) h^(i h) := by
  simp only [map_prod,map_pow,transport6_normalPolynomial]

theorem transport6_normalIdeal_map {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (M : Fin m → Fin 6 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (transport6 ℝ e).toRingHom (sourceNormalIdeal6 M r c) =
      sourceNormalIdeal6 (permutedNormals6 M e) r c := by
  unfold sourceNormalIdeal6
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,transport6_normal_products e M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,transport6_normal_products e M i⟩

theorem transport6_normalIdeal_iff {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (M : Fin m → Fin 6 → ℤ) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceNormalIdeal6 M r c ↔
      transport6 ℝ e P ∈ sourceNormalIdeal6 (permutedNormals6 M e) r c := by
  rw [← transport6_normalIdeal_map e M r c]
  constructor
  · exact Ideal.mem_map_of_mem (transport6 ℝ e).toRingHom
  · intro hP
    obtain ⟨Q,hQ,he⟩ := (Ideal.mem_map_iff_of_surjective
      (transport6 ℝ e).toRingHom (transport6 ℝ e).surjective).mp hP
    exact (transport6 ℝ e).injective he ▸ hQ

theorem transport6_strictIdeal_iff {m : ℕ} (e : Fin m → Equiv.Perm (Fin 6))
    (M : Fin m → Fin 6 → ℤ) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceStrictNormalIdeal6 M r c ↔
      transport6 ℝ e P ∈ sourceStrictNormalIdeal6 (permutedNormals6 M e) r c := by
  rw [sourceStrictNormalIdeal6_iff,sourceStrictNormalIdeal6_iff]
  constructor
  · rintro ⟨d,hd,hP⟩
    exact ⟨d,hd,(transport6_normalIdeal_iff e M r d P).mp hP⟩
  · rintro ⟨d,hd,hP⟩
    exact ⟨d,hd,(transport6_normalIdeal_iff e M r d P).mpr hP⟩


theorem choice_normal_data6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (C : (h : Fin m) → NormalCoordinateChoice6 (M h)) :
    ∀ h, let M' := permutedNormals6 M (fun g => (C g).e) h
      coefficientMultiset6 M' = coefficientMultiset6 (M h) ∧
      Ideal.span (Set.range M') = ⊤ ∧ normalHeight6 M' = normalHeight6 (M h) ∧
      M' 0 ≠ 0 ∧ normalHeight6 M' = (M' 0).natAbs ∧
      (∀ k, (M' k).natAbs ≤ (M' 0).natAbs) ∧
      Int.gcd (M' 0) (M' 1)^5 ≤ normalHeight6 M'^4 ∧
      (∀ k, M' ((C h).e.symm k) = M h k) := by
  intro h
  obtain ⟨hcoeff,hprim,hheight,hfirst,hgcd,_,_,hinv⟩ := (C h).permuted_data
  refine ⟨hcoeff,hprim,hheight,hfirst,?_,?_,hgcd,hinv⟩
  · change normalHeight6 (fun k => M h ((C h).e k)) = (M h ((C h).e 0)).natAbs
    rw [hheight,(C h).e_zero,(C h).height_attains]
  · intro k
    change (M h ((C h).e k)).natAbs ≤ (M h ((C h).e 0)).natAbs
    rw [(C h).e_zero]
    exact (C h).maximal _

theorem schmidtPackage6_transport
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) :
    ∃ (C : (h : Fin S.m) → NormalCoordinateChoice6 (R.M (S.t h)))
      (P' : MvPolynomial (Vars6 S.m) ℤ),
      let e := fun h => (C h).e
      let M' := permutedNormals6 (fun h => R.M (S.t h)) e
      P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧ P' ≠ 0 ∧
      height6 P' = height6 S.P ∧ homogeneous6 S.r P' ∧
      (∀ h, blockDegree6 P' h = blockDegree6 S.P h) ∧
      (∀ h, coefficientMultiset6 (M' h) = coefficientMultiset6 (R.M (S.t h)) ∧
        Ideal.span (Set.range (M' h)) = ⊤ ∧
        normalHeight6 (M' h) = normalHeight6 (R.M (S.t h)) ∧
        M' h 0 ≠ 0 ∧ normalHeight6 (M' h) = (M' h 0).natAbs ∧
        (∀ k, (M' h k).natAbs ≤ (M' h 0).natAbs) ∧
        Int.gcd (M' h 0) (M' h 1)^5 ≤ normalHeight6 (M' h)^4 ∧
        (∀ k, M' h ((C h).e.symm k) = R.M (S.t h) k)) ∧
      (∀ h, (∑ k, R.a (S.t h) (e h k)*M' h k) = 1) ∧
      (∀ h, transport6 ℝ e (normalPolynomial6 (fun g => R.M (S.t g)) h) =
        normalPolynomial6 M' h) ∧
      P'.map (Int.castRingHom ℝ) = transport6 ℝ e (S.P.map (Int.castRingHom ℝ)) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c ↔
        P'.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M' S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceStrictNormalIdeal6 (fun h => R.M (S.t h)) S.r c ↔
        P'.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M' S.r c) ∧
      P'.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M' S.r ((S.m : ℝ)*S.eta) := by
  obtain ⟨C,hC⟩ := schmidtPackage6_coordinate_choices S
  let e := fun h => (C h).e
  let M' := permutedNormals6 (fun h => R.M (S.t h)) e
  let P' := transport6 ℤ e S.P
  refine ⟨C,P',rfl,(transport6_inverse e S.P).1,
    (transport6_nonzero e S.P).mpr S.auxiliary.1,transport6_height e S.P,
    (transport6_homogeneous e S.r S.P).mpr S.auxiliary.2.1,
    transport6_blockDegree e S.P,choice_normal_data6 (fun h => R.M (S.t h)) C,
    hC,transport6_normalPolynomial e (fun h => R.M (S.t h)),
    transport6_map e (Int.castRingHom ℝ) S.P,?_,?_,?_⟩
  · intro c
    rw [transport6_map]
    exact transport6_normalIdeal_iff e (fun h => R.M (S.t h)) S.r c _
  · intro c
    rw [transport6_map]
    exact transport6_strictIdeal_iff e (fun h => R.M (S.t h)) S.r c _
  · rw [transport6_map]
    exact (transport6_normalIdeal_iff e (fun h => R.M (S.t h)) S.r
      ((S.m : ℝ)*S.eta) _).mp S.high_index

end CompoundFeasibility.SchmidtCoordinateTransport6
