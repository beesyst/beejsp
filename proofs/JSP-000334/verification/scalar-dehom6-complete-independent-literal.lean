import SubspaceBridge.SchmidtExcessElimination6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtScalarDehomogenization6Literal
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SchmidtNormalSubstitution6 SchmidtExcessElimination6
open SourceSchmidtParameters6 SourceReadiness6

def eliminatedDegrees6 {m : ℕ} : List (Vars6 m) → MvPolynomial (Vars6 m) ℤ →
    (Fin m → ℕ) → Fin m → ℕ
  | [],_,r => r
  | u::us,P,r => eliminatedDegrees6 us (eliminate6 u P)
      (fun h => r h - if u.1 = h then minimumExponent6 u P else 0)

theorem eliminateList6_homogeneous {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) (r : Fin m → ℕ) (hP : homogeneous6 r P) :
    homogeneous6 (eliminatedDegrees6 us P r) (eliminateList6 us P) := by
  induction us generalizing P r with
  | nil => exact hP
  | cons u us ih => exact ih _ _ (eliminate6_homogeneous u P r hP)

theorem eliminatedDegrees6_le {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) (r : Fin m → ℕ) (h : Fin m) :
    eliminatedDegrees6 us P r h ≤ r h := by
  induction us generalizing P r with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _ _).trans (Nat.sub_le _ _)

theorem eliminatedDegrees6_actual {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) (r : Fin m → ℕ) (hP : homogeneous6 r P)
    (hn : P ≠ 0) (h : Fin m) :
    eliminatedDegrees6 us P r h = blockDegree6 (eliminateList6 us P) h :=
  (homogeneous6_blockDegree _ _ (eliminateList6_homogeneous us P r hP)
    (eliminateList6_nonzero us P hn) h).symm

theorem reducedPolynomial6_homogeneous {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ)
    (r : Fin m → ℕ) (hP : homogeneous6 r P) (hn : P ≠ 0) :
    homogeneous6 (blockDegree6 (reducedPolynomial6 P)) (reducedPolynomial6 P) ∧
      (∀ h, blockDegree6 (reducedPolynomial6 P) h ≤ r h) := by
  have he : eliminatedDegrees6 (excessVariables6 m).toList P r =
      blockDegree6 (reducedPolynomial6 P) := by
    funext h
    exact eliminatedDegrees6_actual _ P r hP hn h
  constructor
  · rw [← he]
    exact eliminateList6_homogeneous _ P r hP
  · intro h
    rw [← he]
    exact eliminatedDegrees6_le _ P r h

def scalar6 {A : Type*} [CommRing A] {m : ℕ} :
    MvPolynomial (Vars6 m) A →+* MvPolynomial (Fin m) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = 0 then MvPolynomial.X u.1 else if u.2 = 1 then 1 else 0)

theorem scalar6_generators {A : Type*} [CommRing A] {m : ℕ} :
    (∀ c : A, scalar6 (MvPolynomial.C c : MvPolynomial (Vars6 m) A) = MvPolynomial.C c) ∧
      (∀ u : Vars6 m, scalar6 (MvPolynomial.X u : MvPolynomial (Vars6 m) A) =
        if u.2 = 0 then MvPolynomial.X u.1 else if u.2 = 1 then 1 else 0) := by
  constructor <;> intro x <;> simp [scalar6]

theorem scalar6_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {m : ℕ} (P : MvPolynomial (Vars6 m) A) :
    (scalar6 P).map f = scalar6 (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [scalar6]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F u hF =>
    simp only [map_mul,hF,MvPolynomial.map_X]
    by_cases h0 : u.2 = 0 <;> by_cases h1 : u.2 = 1 <;> simp [scalar6,h0,h1]

def scalarExponent6 {m : ℕ} (d : Vars6 m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun h => d (h,0))

def binarySupport6 {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (Vars6 m) A) : Prop :=
  ∀ d ∈ P.support, ∀ u : Vars6 m, 2 ≤ u.2.val → d u = 0

theorem binary_block_sum6 {m : ℕ} (d : Vars6 m →₀ ℕ)
    (hd : ∀ u : Vars6 m, 2 ≤ u.2.val → d u = 0) (h : Fin m) :
    (∑ j : Fin 6, d (h,j)) = d (h,0)+d (h,1) := by
  have hs : (∑ j ∈ ({0,1} : Finset (Fin 6)), d (h,j)) = ∑ j : Fin 6, d (h,j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply hd (h,j)
    fin_cases j <;> simp_all
  exact hs.symm.trans (by simp)

theorem scalar6_monomial {A : Type*} [CommRing A] {m : ℕ}
    (d : Vars6 m →₀ ℕ) (hd : ∀ u : Vars6 m, 2 ≤ u.2.val → d u = 0) (c : A) :
    scalar6 (MvPolynomial.monomial d c) = MvPolynomial.monomial (scalarExponent6 d) c := by
  rw [scalar6,MvPolynomial.eval₂Hom_monomial,MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [Finset.prod_eq_single (0 : Fin 6)]
  · simp [scalarExponent6]
  · intro j _ hj0
    by_cases hj1 : j = 1
    · simp [hj1]
    · have hz := hd (h,j) (by fin_cases j <;> simp_all)
      simp [hz]
  · simp

theorem scalarExponent6_inj {m : ℕ} (r : Fin m → ℕ) (d e : Vars6 m →₀ ℕ)
    (hd : ∀ u : Vars6 m, 2 ≤ u.2.val → d u = 0)
    (he : ∀ u : Vars6 m, 2 ≤ u.2.val → e u = 0)
    (hdr : ∀ h, (∑ j : Fin 6, d (h,j)) = r h)
    (her : ∀ h, (∑ j : Fin 6, e (h,j)) = r h)
    (hp : scalarExponent6 d = scalarExponent6 e) : d = e := by
  apply Finsupp.ext
  rintro ⟨h,j⟩
  have h0 : d (h,0) = e (h,0) := congrArg (fun b => b h) hp
  have hd' := hdr h
  have he' := her h
  rw [binary_block_sum6 d hd h] at hd'
  rw [binary_block_sum6 e he h] at he'
  by_cases hj0 : j = 0
  · subst j; exact h0
  by_cases hj1 : j = 1
  · subst j; omega
  have hj : 2 ≤ j.val := by fin_cases j <;> simp_all
  rw [hd (h,j) hj,he (h,j) hj]

theorem scalarExponent6_injOn {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A)
    (hh : homogeneous6 r P) (hb : binarySupport6 P) :
    Set.InjOn scalarExponent6 (↑P.support : Set (Vars6 m →₀ ℕ)) := by
  intro d hd e he hp
  exact scalarExponent6_inj r d e (hb d hd) (hb e he) (hh d hd) (hh e he) hp

theorem scalar6_as_sum {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (Vars6 m) A) (hb : binarySupport6 P) :
    scalar6 P = ∑ d ∈ P.support, MvPolynomial.monomial (scalarExponent6 d) (P.coeff d) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact scalar6_monomial d (hb d hd) (P.coeff d)

theorem scalar6_coeff {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A)
    (hh : homogeneous6 r P) (hb : binarySupport6 P)
    (d : Vars6 m →₀ ℕ) (hd : d ∈ P.support) :
    (scalar6 P).coeff (scalarExponent6 d) = P.coeff d := by
  rw [scalar6_as_sum P hb,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hed
    rw [MvPolynomial.coeff_monomial,if_neg]
    intro hp
    exact hed (scalarExponent6_injOn r P hh hb he hd hp)
  · intro hn
    exact False.elim (hn hd)

theorem scalar6_support {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A)
    (hh : homogeneous6 r P) (hb : binarySupport6 P) :
    (scalar6 P).support = P.support.image scalarExponent6 := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [scalar6_as_sum P hb] at he
    obtain ⟨d,hd,hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
    have heq : e = scalarExponent6 d := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (R := A) hm)
    exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
  · intro e he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
    rw [MvPolynomial.mem_support_iff,scalar6_coeff r P hh hb d hd]
    exact MvPolynomial.mem_support_iff.mp hd

def scalarSupportEquiv6 {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A)
    (hh : homogeneous6 r P) (hb : binarySupport6 P) :
    {d // d ∈ P.support} ≃ {e // e ∈ (scalar6 P).support} :=
  Equiv.ofBijective (fun d => ⟨scalarExponent6 d.val,
    by rw [scalar6_support r P hh hb]; exact Finset.mem_image.mpr ⟨d.val,d.property,rfl⟩⟩) (by
    constructor
    · intro d e he
      apply Subtype.ext
      exact scalarExponent6_injOn r P hh hb d.property e.property (congrArg Subtype.val he)
    · intro e
      have he : e.val ∈ P.support.image scalarExponent6 :=
        Eq.mp (congrArg (fun s : Finset (Fin m →₀ ℕ) => e.val ∈ s)
          (scalar6_support r P hh hb)) e.property
      obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp he
      exact ⟨⟨d,hd⟩,Subtype.ext hde⟩)

theorem scalar6_nonzero {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A)
    (hh : homogeneous6 r P) (hb : binarySupport6 P) (hn : P ≠ 0) : scalar6 P ≠ 0 := by
  obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hn
  apply MvPolynomial.ne_zero_iff.mpr
  refine ⟨scalarExponent6 d,?_⟩
  rw [scalar6_coeff r P hh hb d hd]
  exact MvPolynomial.mem_support_iff.mp hd

theorem scalar6_height {m : ℕ} (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) ℤ)
    (hh : homogeneous6 r P) (hb : binarySupport6 P) :
    JSP000334.rothIntegerHeight (scalar6 P) = height6 P := by
  unfold JSP000334.rothIntegerHeight height6
  rw [scalar6_support r P hh hb,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d hd
  change ((scalar6 P).coeff (scalarExponent6 d)).natAbs = (P.coeff d).natAbs
  rw [scalar6_coeff r P hh hb d hd]

theorem scalar6_support_degree {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A)
    (hh : homogeneous6 r P) (hb : binarySupport6 P) :
    ∀ e ∈ (scalar6 P).support, ∀ h, e h ≤ r h := by
  intro e he h
  rw [scalar6_support r P hh hb] at he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
  change d (h,0) ≤ r h
  rw [← hh d hd h,binary_block_sum6 d (hb d hd) h]
  exact Nat.le_add_right _ _

theorem scalar6_degree {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) A)
    (hh : homogeneous6 r P) (hb : binarySupport6 P) (h : Fin m) :
    (scalar6 P).degreeOf h ≤ r h :=
  MvPolynomial.degreeOf_le_iff.mpr (fun e he => scalar6_support_degree r P hh hb e he h)

def scalarNormal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    MvPolynomial (Fin m) ℝ :=
  MvPolynomial.C (M h 0 : ℝ)*MvPolynomial.X h + MvPolynomial.C (M h 1 : ℝ)

theorem scalar6_normal {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    scalar6 (normalPolynomial6 (reducedNormals6 M) h) = scalarNormal6 M h := by
  simp only [reducedNormals6_polynomial,map_add,map_mul,
    (scalar6_generators (A := ℝ)).1,(scalar6_generators (A := ℝ)).2]
  simp [scalarNormal6]

theorem scalar6_normal_products {m : ℕ} (M : Fin m → Fin 6 → ℤ) (i : Fin m → ℕ) :
    scalar6 (∏ h, normalPolynomial6 (reducedNormals6 M) h^(i h)) =
      ∏ h, scalarNormal6 M h^(i h) := by
  simp only [map_prod,map_pow,scalar6_normal]

def scalarIdeal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, scalarNormal6 M h^(i h)}

def scalarStrictIdeal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c < ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, scalarNormal6 M h^(i h)}

theorem scalar6_ideal_map {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map scalar6 (sourceNormalIdeal6 (reducedNormals6 M) r c) = scalarIdeal6 M r c := by
  unfold sourceNormalIdeal6 scalarIdeal6
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,scalar6_normal_products M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,scalar6_normal_products M i⟩

theorem scalar6_strictIdeal_map {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map scalar6 (sourceStrictNormalIdeal6 (reducedNormals6 M) r c) = scalarStrictIdeal6 M r c := by
  unfold sourceStrictNormalIdeal6 scalarStrictIdeal6
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,scalar6_normal_products M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,scalar6_normal_products M i⟩

theorem scalar6_closed {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℤ)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (reducedNormals6 M) r c) :
    (scalar6 P).map (Int.castRingHom ℝ) ∈ scalarIdeal6 M r c := by
  rw [scalar6_map,← scalar6_ideal_map M r c]
  exact Ideal.mem_map_of_mem scalar6 hP

theorem scalar6_strict {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℤ)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (reducedNormals6 M) r c) :
    (scalar6 P).map (Int.castRingHom ℝ) ∈ scalarStrictIdeal6 M r c := by
  rw [scalar6_map,← scalar6_strictIdeal_map M r c]
  exact Ideal.mem_map_of_mem scalar6 hP

theorem schmidtPackage6_scalar_dehomogenization
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) :
    ∃ (C : (h : Fin S.m) → SchmidtHilfssatz13.NormalCoordinateChoice6 (R.M (S.t h)))
      (P' : MvPolynomial (Vars6 S.m) ℤ) (PN : MvPolynomial (Vars6 S.m) ℚ)
      (F : MvPolynomial (Vars6 S.m) ℤ) (G : MvPolynomial (Fin S.m) ℤ),
      let e := fun h => (C h).e
      let M' := permutedNormals6 (fun h => R.M (S.t h)) e
      let r_reduced := blockDegree6 F
      P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
      PN = normalPolynomialQ6 M' P' ∧ PN ≠ 0 ∧
      (∀ h k, M' h ((C h).e.symm k) = R.M (S.t h) k) ∧
      F = reducedPolynomial6 P' ∧ F ≠ 0 ∧ binarySupport6 F ∧
      r_reduced = eliminatedDegrees6 (excessVariables6 S.m).toList P' S.r ∧
      homogeneous6 r_reduced F ∧ (∀ h, r_reduced h ≤ S.r h) ∧
      G = scalar6 F ∧ G ≠ 0 ∧
      (∀ d ∈ F.support, G.coeff (scalarExponent6 d) = F.coeff d) ∧
      G.support = F.support.image scalarExponent6 ∧
      Set.InjOn scalarExponent6 (↑F.support : Set (Vars6 S.m →₀ ℕ)) ∧
      JSP000334.rothIntegerHeight G = height6 F ∧
      JSP000334.rothIntegerHeight G ≤ height6 S.P ∧
      (∀ b ∈ G.support, ∀ h, b h ≤ r_reduced h) ∧
      (∀ h, G.degreeOf h ≤ r_reduced h ∧ G.degreeOf h ≤ S.r h) ∧
      (∀ h, reducedNormals6 M' h 0 = M' h 0 ∧ reducedNormals6 M' h 1 = M' h 1 ∧
        reducedNormals6 M' h 0 ≠ 0 ∧
        Int.gcd (reducedNormals6 M' h 0) (reducedNormals6 M' h 1)^5 ≤ (M' h 0).natAbs^4) ∧
      (∀ h, scalar6 (normalPolynomial6 (reducedNormals6 M') h) = scalarNormal6 M' h) ∧
      (∀ h, scalarNormal6 M' h =
        MvPolynomial.C (M' h 0 : ℝ)*MvPolynomial.X h + MvPolynomial.C (M' h 1 : ℝ)) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        G.map (Int.castRingHom ℝ) ∈ scalarIdeal6 M' S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceStrictNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        G.map (Int.castRingHom ℝ) ∈ scalarStrictIdeal6 M' S.r c) ∧
      G.map (Int.castRingHom ℝ) ∈ scalarIdeal6 M' S.r ((S.m : ℝ)*S.eta) ∧
      G.map (Int.castRingHom ℝ) ∈ scalarStrictIdeal6 M' S.r S.theta := by
  obtain ⟨C,P',PN,F,heq,hinv,hPN,hPNn,hrecover,hF,hFn,hcard,hbinary,hheight,hdeg,
    hnormcoeff,hfirsttwo,hnormal,hclosed,hstrict,hhigh,hstrictTheta⟩ :=
    schmidtPackage6_excess_elimination S
  let e := fun h => (C h).e
  let M' := permutedNormals6 (fun h => R.M (S.t h)) e
  have hPn : P' ≠ 0 := by
    rw [heq]
    exact (transport6_nonzero e S.P).mpr S.auxiliary.1
  have hPhom : homogeneous6 S.r P' := by
    rw [heq]
    exact (transport6_homogeneous e S.r S.P).mpr S.auxiliary.2.1
  have hhom : homogeneous6 (blockDegree6 F) F := by
    rw [hF]
    exact (reducedPolynomial6_homogeneous P' S.r hPhom hPn).1
  have hdegrees : blockDegree6 F = eliminatedDegrees6 (excessVariables6 S.m).toList P' S.r := by
    funext h
    rw [hF]
    exact (eliminatedDegrees6_actual _ P' S.r hPhom hPn h).symm
  let G := scalar6 F
  have hH : JSP000334.rothIntegerHeight G = height6 F := scalar6_height _ F hhom hbinary
  refine ⟨C,P',PN,F,G,heq,hinv,hPN,hPNn,hrecover,hF,hFn,hbinary,hdegrees,hhom,hdeg,rfl,
    scalar6_nonzero _ F hhom hbinary hFn,scalar6_coeff _ F hhom hbinary,
    scalar6_support _ F hhom hbinary,scalarExponent6_injOn _ F hhom hbinary,hH,
    hH.le.trans hheight,scalar6_support_degree _ F hhom hbinary,?_,hfirsttwo,
    scalar6_normal M',fun _ => rfl,?_,?_,scalar6_closed M' S.r _ F hhigh,
    scalar6_strict M' S.r _ F hstrictTheta⟩
  · intro h
    have hd := scalar6_degree _ F hhom hbinary h
    exact ⟨hd,hd.trans (hdeg h)⟩
  · intro c hP
    exact scalar6_closed M' S.r c F (hclosed c hP)
  · intro c hP
    exact scalar6_strict M' S.r c F (hstrict c hP)

end CompoundFeasibility.SchmidtScalarDehomogenization6Literal

#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminatedDegrees6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminatedDegrees6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminateList6_homogeneous
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminateList6_homogeneous
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminatedDegrees6_le
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminatedDegrees6_le
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminatedDegrees6_actual
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.eliminatedDegrees6_actual
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.reducedPolynomial6_homogeneous
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.reducedPolynomial6_homogeneous
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_generators
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_generators
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_map
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_map
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarExponent6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarExponent6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.binarySupport6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.binarySupport6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.binary_block_sum6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.binary_block_sum6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_monomial
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_monomial
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarExponent6_inj
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarExponent6_inj
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarExponent6_injOn
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarExponent6_injOn
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_as_sum
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_as_sum
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_coeff
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_coeff
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_support
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_support
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarSupportEquiv6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarSupportEquiv6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_nonzero
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_nonzero
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_height
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_height
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_support_degree
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_support_degree
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_degree
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_degree
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarNormal6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarNormal6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_normal
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_normal
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_normal_products
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_normal_products
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarIdeal6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarIdeal6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarStrictIdeal6
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalarStrictIdeal6
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_ideal_map
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_ideal_map
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_strictIdeal_map
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_strictIdeal_map
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_closed
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_closed
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_strict
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.scalar6_strict
#check CompoundFeasibility.SchmidtScalarDehomogenization6Literal.schmidtPackage6_scalar_dehomogenization
#print axioms CompoundFeasibility.SchmidtScalarDehomogenization6Literal.schmidtPackage6_scalar_dehomogenization
