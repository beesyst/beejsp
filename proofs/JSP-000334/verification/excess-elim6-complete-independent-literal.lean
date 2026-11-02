import SubspaceBridge.SchmidtNormalSubstitution6
import Mathlib.Algebra.MvPolynomial.Division
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtExcessElimination6Literal
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SchmidtNormalSubstitution6 SourceSchmidtParameters6 SourceReadiness6

def pivotNormals6 {m : ℕ} : Fin m → Fin 6 → ℤ := fun _ j => if j = 0 then 1 else 0

theorem pivotNormals6_polynomial {m : ℕ} (h : Fin m) :
    normalPolynomial6 pivotNormals6 h = MvPolynomial.X (h,0) := by
  simp [normalPolynomial6,pivotNormals6]

theorem pivotNormals6_inverse {m : ℕ} (F : MvPolynomial (Vars6 m) ℝ) :
    normalInverse6 pivotNormals6 (fun _ => 0) F = F := by
  have he : normalInverse6 (m := m) pivotNormals6 (fun _ => 0) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [normalInverse6]
    · intro u
      by_cases hu : u.2 = 0 <;> simp [normalInverse6,pivotNormals6,hu]
  exact congrArg (fun f => f F) he

theorem coordinateIdeal6_support {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (F : MvPolynomial (Vars6 m) ℝ) :
    F ∈ coordinateIdeal6 r c ↔
      ∀ d ∈ F.support, c ≤ normalCoordinateWeight6 r (fun _ => 0) d := by
  have he : coordinateIdeal6 r c = sourceNormalIdeal6 pivotNormals6 r c := by
    simp only [coordinateIdeal6,sourceNormalIdeal6,pivotNormals6_polynomial]
  rw [he,sourceNormalIdeal6_iff_support pivotNormals6 (fun _ => 0)
    (by intro h; simp [pivotNormals6]),pivotNormals6_inverse]

theorem coordinateStrictIdeal6_support {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (F : MvPolynomial (Vars6 m) ℝ) :
    F ∈ coordinateStrictIdeal6 r c ↔
      ∀ d ∈ F.support, c < normalCoordinateWeight6 r (fun _ => 0) d := by
  have he : coordinateStrictIdeal6 r c = sourceStrictNormalIdeal6 pivotNormals6 r c := by
    simp only [coordinateStrictIdeal6,sourceStrictNormalIdeal6,pivotNormals6_polynomial]
  rw [he,sourceStrictNormalIdeal6_iff_support pivotNormals6 (fun _ => 0)
    (by intro h; simp [pivotNormals6]),pivotNormals6_inverse]

theorem support_X_pow_mul6 {A : Type*} [CommRing A] {m : ℕ}
    (u : Vars6 m) (a : ℕ) (F : MvPolynomial (Vars6 m) A) (d : Vars6 m →₀ ℕ) :
    d ∈ (MvPolynomial.X u^a*F).support ↔
      ∃ b ∈ F.support, Finsupp.single u a+b = d := by
  rw [MvPolynomial.mem_support_iff,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_monomial_mul']
  by_cases hs : Finsupp.single u a ≤ d
  · rw [if_pos hs,one_mul]
    constructor
    · intro hd
      exact ⟨d-Finsupp.single u a,MvPolynomial.mem_support_iff.mpr hd,add_tsub_cancel_of_le hs⟩
    · rintro ⟨b,hb,he⟩
      rw [← he,add_tsub_cancel_left]
      exact MvPolynomial.mem_support_iff.mp hb
  · rw [if_neg hs]
    constructor
    · intro h; exact False.elim (h rfl)
    · rintro ⟨b,hb,he⟩
      exact False.elim (hs (he ▸ le_self_add))

theorem free_weight_shift6 {m : ℕ} (r : Fin m → ℕ) (u : Vars6 m)
    (hu : u.2 ≠ 0) (a : ℕ) (d : Vars6 m →₀ ℕ) :
    normalCoordinateWeight6 r (fun _ => 0) (Finsupp.single u a+d) =
      normalCoordinateWeight6 r (fun _ => 0) d := by
  rw [normalCoordinateWeight6_add]
  have hz : normalCoordinateWeight6 r (fun _ => 0) (Finsupp.single u a) = 0 := by
    rcases u with ⟨g,k⟩
    simp [normalCoordinateWeight6,Finsupp.single_apply,Prod.mk.injEq,hu]
  rw [hz,zero_add]

theorem coordinateIdeal6_saturation {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (u : Vars6 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (Vars6 m) ℝ) :
    MvPolynomial.X u^a*F ∈ coordinateIdeal6 r c ↔ F ∈ coordinateIdeal6 r c := by
  rw [coordinateIdeal6_support,coordinateIdeal6_support]
  constructor
  · intro h d hd
    have hm := h _ ((support_X_pow_mul6 u a F _).mpr ⟨d,hd,rfl⟩)
    simpa only [free_weight_shift6 r u hu] using hm
  · intro h d hd
    obtain ⟨b,hb,rfl⟩ := (support_X_pow_mul6 u a F d).mp hd
    simpa only [free_weight_shift6 r u hu] using h b hb

theorem coordinateStrictIdeal6_saturation {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (u : Vars6 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (Vars6 m) ℝ) :
    MvPolynomial.X u^a*F ∈ coordinateStrictIdeal6 r c ↔ F ∈ coordinateStrictIdeal6 r c := by
  rw [coordinateStrictIdeal6_support,coordinateStrictIdeal6_support]
  constructor
  · intro h d hd
    have hm := h _ ((support_X_pow_mul6 u a F _).mpr ⟨d,hd,rfl⟩)
    simpa only [free_weight_shift6 r u hu] using hm
  · intro h d hd
    obtain ⟨b,hb,rfl⟩ := (support_X_pow_mul6 u a F d).mp hd
    simpa only [free_weight_shift6 r u hu] using h b hb

theorem normalEquiv6_free {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Fin m → Fin 6 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (u : Vars6 m) (hu : u.2 ≠ 0) :
    normalEquiv6 (K := K) M (fun _ => 0) hM (MvPolynomial.X u) = MvPolynomial.X u ∧
      (normalEquiv6 (K := K) M (fun _ => 0) hM).symm (MvPolynomial.X u) = MvPolynomial.X u := by
  constructor
  · change forward6 M (fun _ => 0) (MvPolynomial.X u) = _
    simp [forward6,hu]
  · change inverse6 M (fun _ => 0) (MvPolynomial.X u) = _
    simp [inverse6,hu]

theorem sourceNormalIdeal6_saturation {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (u : Vars6 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (Vars6 m) ℝ) :
    MvPolynomial.X u^a*F ∈ sourceNormalIdeal6 M r c ↔ F ∈ sourceNormalIdeal6 M r c := by
  rw [inverse6_ideal_iff M hM,inverse6_ideal_iff M hM,map_mul,map_pow]
  have hx : inverse6 (K := ℝ) M (fun _ => 0) (MvPolynomial.X u) = MvPolynomial.X u :=
    (normalEquiv6_free M hM u hu).2
  rw [hx,coordinateIdeal6_saturation r c u hu]

theorem sourceStrictNormalIdeal6_saturation {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (u : Vars6 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (Vars6 m) ℝ) :
    MvPolynomial.X u^a*F ∈ sourceStrictNormalIdeal6 M r c ↔ F ∈ sourceStrictNormalIdeal6 M r c := by
  rw [inverse6_strictIdeal_iff M hM,inverse6_strictIdeal_iff M hM,map_mul,map_pow]
  have hx : inverse6 (K := ℝ) M (fun _ => 0) (MvPolynomial.X u) = MvPolynomial.X u :=
    (normalEquiv6_free M hM u hu).2
  rw [hx,coordinateStrictIdeal6_saturation r c u hu]

def zeroSpecialize6 {A : Type*} [CommRing A] {m : ℕ} (u : Vars6 m) :
    MvPolynomial (Vars6 m) A →+* MvPolynomial (Vars6 m) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v => if v = u then 0 else MvPolynomial.X v)

theorem zeroSpecialize6_monomial {A : Type*} [CommRing A] {m : ℕ}
    (u : Vars6 m) (d : Vars6 m →₀ ℕ) (c : A) :
    zeroSpecialize6 u (MvPolynomial.monomial d c) =
      if d u = 0 then MvPolynomial.monomial d c else 0 := by
  rw [zeroSpecialize6,MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  by_cases hd : d u = 0
  · rw [if_pos hd,MvPolynomial.monomial_eq]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v = u
    · subst v; simp [hd]
    · simp [hv]
  · rw [if_neg hd]
    have hz : (∏ v : Vars6 m,
        (if v = u then 0 else MvPolynomial.X v)^d v) = (0 : MvPolynomial (Vars6 m) A) := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [hd]
    rw [hz,mul_zero]

theorem zeroSpecialize6_coeff {A : Type*} [CommRing A] {m : ℕ}
    (u : Vars6 m) (F : MvPolynomial (Vars6 m) A) (d : Vars6 m →₀ ℕ) :
    (zeroSpecialize6 u F).coeff d = if d u = 0 then F.coeff d else 0 := by
  induction F using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [zeroSpecialize6_monomial]
    by_cases hb : b u = 0
    · rw [if_pos hb]
      by_cases hd : d u = 0
      · simp [hd]
      · have hbd : b ≠ d := by intro he; subst b; exact hd hb
        simp [hd,hbd]
    · rw [if_neg hb]
      by_cases hd : d u = 0
      · have hbd : b ≠ d := by intro he; subst b; exact hb hd
        simp [hd,hbd]
      · simp [hd]
  | add F G hF hG =>
    rw [map_add,MvPolynomial.coeff_add,hF,hG,MvPolynomial.coeff_add]
    split_ifs <;> simp

def minimumExponent6 {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ) : ℕ :=
  if hn : P = 0 then 0 else
    (Classical.choose (Finset.exists_min_image P.support (fun d => d u)
      (MvPolynomial.support_nonempty.mpr hn))) u

theorem minimumExponent6_spec {m : ℕ} (u : Vars6 m)
    (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0) :
    ∃ d ∈ P.support, d u = minimumExponent6 u P ∧
      ∀ b ∈ P.support, minimumExponent6 u P ≤ b u := by
  simp only [minimumExponent6,dif_neg hn]
  have hex := Finset.exists_min_image P.support (fun d => d u) (MvPolynomial.support_nonempty.mpr hn)
  exact ⟨Classical.choose hex,(Classical.choose_spec hex).1,rfl,(Classical.choose_spec hex).2⟩

def extracted6 {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ) :
    MvPolynomial (Vars6 m) ℤ := P.divMonomial (Finsupp.single u (minimumExponent6 u P))

def eliminate6 {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ) :
    MvPolynomial (Vars6 m) ℤ := zeroSpecialize6 u (extracted6 u P)

theorem extracted6_coeff {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (d : Vars6 m →₀ ℕ) :
    (extracted6 u P).coeff d = P.coeff (Finsupp.single u (minimumExponent6 u P)+d) := rfl

theorem extracted6_factor {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (hn : P ≠ 0) : P = MvPolynomial.X u^(minimumExponent6 u P)*extracted6 u P := by
  obtain ⟨b,hb,hbe,hmin⟩ := minimumExponent6_spec u P hn
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.coeff_monomial_mul']
  by_cases hs : Finsupp.single u (minimumExponent6 u P) ≤ d
  · rw [if_pos hs,one_mul,extracted6_coeff,add_tsub_cancel_of_le hs]
  · rw [if_neg hs]
    apply MvPolynomial.not_mem_support_iff.mp
    intro hd
    exact hs (Finsupp.single_le_iff.mpr (hmin d hd))

theorem eliminate6_coeff {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (d : Vars6 m →₀ ℕ) :
    (eliminate6 u P).coeff d = if d u = 0 then
      P.coeff (Finsupp.single u (minimumExponent6 u P)+d) else 0 := by
  rw [eliminate6,zeroSpecialize6_coeff,extracted6_coeff]

theorem eliminate6_nonzero {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (hn : P ≠ 0) : eliminate6 u P ≠ 0 := by
  obtain ⟨b,hb,hbe,hmin⟩ := minimumExponent6_spec u P hn
  let s := Finsupp.single u (minimumExponent6 u P)
  have hs : s ≤ b := Finsupp.single_le_iff.mpr (hmin b hb)
  have hz : (b-s) u = 0 := by simp [s,Finsupp.tsub_apply,hbe]
  have hcoeff : (eliminate6 u P).coeff (b-s) ≠ 0 := by
    rw [eliminate6_coeff,if_pos hz,show Finsupp.single u (minimumExponent6 u P) = s from rfl,
      add_tsub_cancel_of_le hs]
    exact MvPolynomial.mem_support_iff.mp hb
  exact MvPolynomial.ne_zero_iff.mpr ⟨b-s,hcoeff⟩

theorem extracted6_nonzero {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (hn : P ≠ 0) : extracted6 u P ≠ 0 := by
  intro hz
  apply eliminate6_nonzero u P hn
  rw [eliminate6,hz,map_zero]

theorem eliminate6_support_source {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (d : Vars6 m →₀ ℕ) (hd : d ∈ (eliminate6 u P).support) :
    d u = 0 ∧ Finsupp.single u (minimumExponent6 u P)+d ∈ P.support := by
  have hn := MvPolynomial.mem_support_iff.mp hd
  rw [eliminate6_coeff] at hn
  by_cases hz : d u = 0
  · exact ⟨hz,MvPolynomial.mem_support_iff.mpr (by simpa [hz] using hn)⟩
  · simp [hz] at hn

theorem eliminate6_height {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ) :
    height6 (eliminate6 u P) ≤ height6 P := by
  apply Finset.sup_le
  intro d hd
  obtain ⟨hz,hp⟩ := eliminate6_support_source u P d hd
  change ((eliminate6 u P).coeff d).natAbs ≤ height6 P
  rw [eliminate6_coeff,if_pos hz]
  exact Finset.le_sup (f := fun b => (P.coeff b).natAbs) hp

theorem eliminate6_blockDegree {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (h : Fin m) : blockDegree6 (eliminate6 u P) h ≤ blockDegree6 P h := by
  apply Finset.sup_le
  intro d hd
  have hp := (eliminate6_support_source u P d hd).2
  calc
    (∑ j : Fin 6, d (h,j)) ≤ ∑ j : Fin 6, (Finsupp.single u (minimumExponent6 u P)+d) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.le_add_left _ _
    _ ≤ blockDegree6 P h := Finset.le_sup (f := fun b => ∑ j : Fin 6, b (h,j)) hp

theorem eliminate6_preserves_independence {m : ℕ} (u v : Vars6 m)
    (P : MvPolynomial (Vars6 m) ℤ) (hv : ∀ d ∈ P.support, d v = 0) :
    ∀ d ∈ (eliminate6 u P).support, d v = 0 := by
  intro d hd
  have he := hv _ (eliminate6_support_source u P d hd).2
  simp only [Finsupp.add_apply] at he
  omega

theorem eliminate6_homogeneous {m : ℕ} (u : Vars6 m) (P : MvPolynomial (Vars6 m) ℤ)
    (r : Fin m → ℕ) (hP : homogeneous6 r P) :
    homogeneous6 (fun h => r h - if u.1 = h then minimumExponent6 u P else 0) (eliminate6 u P) := by
  intro d hd h
  have he := hP _ (eliminate6_support_source u P d hd).2 h
  have hs : (∑ j : Fin 6, (Finsupp.single u (minimumExponent6 u P)) (h,j)) =
      if u.1 = h then minimumExponent6 u P else 0 := by
    rcases u with ⟨g,k⟩
    by_cases hg : g = h
    · subst g; simp [Finsupp.single_apply,Prod.mk.injEq,eq_comm]
    · simp [Finsupp.single_apply,Prod.mk.injEq,hg]
  simp only [Finsupp.add_apply,Finset.sum_add_distrib,hs] at he
  change (∑ j : Fin 6, d (h,j)) = r h - if u.1 = h then minimumExponent6 u P else 0
  omega

def zeroNormalCoefficient6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (u : Vars6 m)
    (h : Fin m) (j : Fin 6) : ℤ := if (h,j) = u then 0 else M h j

theorem zeroSpecialize6_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {m : ℕ} (u : Vars6 m) (F : MvPolynomial (Vars6 m) A) :
    (zeroSpecialize6 u F).map f = zeroSpecialize6 u (F.map f) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [zeroSpecialize6]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F v hF =>
    simp only [map_mul,hF,MvPolynomial.map_X]
    by_cases hv : v = u <;> simp [zeroSpecialize6,hv]

theorem zeroNormalCoefficient6_pivot {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (u : Vars6 m) (hu : u.2 ≠ 0) (h : Fin m) :
    zeroNormalCoefficient6 M u h 0 = M h 0 := by
  have he : (h,0) ≠ u := by intro he; exact hu (congrArg Prod.snd he).symm
  simp [zeroNormalCoefficient6,he]

theorem zeroSpecialize6_normal {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (u : Vars6 m) (h : Fin m) :
    zeroSpecialize6 u (normalPolynomial6 M h) = normalPolynomial6 (zeroNormalCoefficient6 M u) h := by
  simp only [normalPolynomial6,map_sum,map_mul,zeroSpecialize6,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X']
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : (h,j) = u <;> simp [zeroNormalCoefficient6,he]

theorem zeroSpecialize6_normal_products {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (u : Vars6 m) (i : Fin m → ℕ) :
    zeroSpecialize6 u (∏ h, normalPolynomial6 M h^(i h)) =
      ∏ h, normalPolynomial6 (zeroNormalCoefficient6 M u) h^(i h) := by
  simp only [map_prod,map_pow,zeroSpecialize6_normal]

theorem zeroSpecialize6_ideal_map {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (u : Vars6 m) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (zeroSpecialize6 u) (sourceNormalIdeal6 M r c) =
      sourceNormalIdeal6 (zeroNormalCoefficient6 M u) r c := by
  unfold sourceNormalIdeal6
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,zeroSpecialize6_normal_products M u i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,zeroSpecialize6_normal_products M u i⟩

theorem zeroSpecialize6_strictIdeal_map {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (u : Vars6 m) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (zeroSpecialize6 u) (sourceStrictNormalIdeal6 M r c) =
      sourceStrictNormalIdeal6 (zeroNormalCoefficient6 M u) r c := by
  unfold sourceStrictNormalIdeal6
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,zeroSpecialize6_normal_products M u i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,zeroSpecialize6_normal_products M u i⟩

theorem eliminate6_closed {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (u : Vars6 m) (hu : u.2 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M r c) :
    (eliminate6 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (zeroNormalCoefficient6 M u) r c := by
  have hQ : (extracted6 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M r c := by
    apply (sourceNormalIdeal6_saturation M hM r c u hu (minimumExponent6 u P) _).mp
    rw [extracted6_factor u P hn,map_mul,map_pow,MvPolynomial.map_X] at hP
    exact hP
  rw [eliminate6,zeroSpecialize6_map,← zeroSpecialize6_ideal_map M u r c]
  exact Ideal.mem_map_of_mem (zeroSpecialize6 u) hQ

theorem eliminate6_strict {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (u : Vars6 m) (hu : u.2 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M r c) :
    (eliminate6 u P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (zeroNormalCoefficient6 M u) r c := by
  have hQ : (extracted6 u P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M r c := by
    apply (sourceStrictNormalIdeal6_saturation M hM r c u hu (minimumExponent6 u P) _).mp
    rw [extracted6_factor u P hn,map_mul,map_pow,MvPolynomial.map_X] at hP
    exact hP
  rw [eliminate6,zeroSpecialize6_map,← zeroSpecialize6_strictIdeal_map M u r c]
  exact Ideal.mem_map_of_mem (zeroSpecialize6 u) hQ

theorem eliminate6_step {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (u : Vars6 m) (hu : u.2 ≠ 0)
    (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0) :
    P = MvPolynomial.X u^(minimumExponent6 u P)*extracted6 u P ∧
      extracted6 u P ≠ 0 ∧ eliminate6 u P ≠ 0 ∧
      height6 (eliminate6 u P) ≤ height6 P ∧
      (∀ h, blockDegree6 (eliminate6 u P) h ≤ blockDegree6 P h) ∧
      (∀ d ∈ (eliminate6 u P).support, d u = 0) ∧
      (∀ h, zeroNormalCoefficient6 M u h 0 = M h 0 ∧ zeroNormalCoefficient6 M u h 0 ≠ 0) ∧
      (∀ r c, P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M r c →
        (eliminate6 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (zeroNormalCoefficient6 M u) r c) ∧
      (∀ r c, P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M r c →
        (eliminate6 u P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (zeroNormalCoefficient6 M u) r c) := by
  refine ⟨extracted6_factor u P hn,extracted6_nonzero u P hn,eliminate6_nonzero u P hn,
    eliminate6_height u P,eliminate6_blockDegree u P,fun d hd => (eliminate6_support_source u P d hd).1,
    ?_,fun r c => eliminate6_closed M hM u hu r c P hn,fun r c => eliminate6_strict M hM u hu r c P hn⟩
  intro h
  rw [zeroNormalCoefficient6_pivot M u hu h]
  exact ⟨rfl,hM h⟩

def eliminateList6 {m : ℕ} : List (Vars6 m) → MvPolynomial (Vars6 m) ℤ → MvPolynomial (Vars6 m) ℤ
  | [],P => P
  | u::us,P => eliminateList6 us (eliminate6 u P)

def specializeNormalsList6 {m : ℕ} : List (Vars6 m) → (Fin m → Fin 6 → ℤ) → Fin m → Fin 6 → ℤ
  | [],M => M
  | u::us,M => specializeNormalsList6 us (zeroNormalCoefficient6 M u)

theorem specializeNormalsList6_coeff {m : ℕ} (us : List (Vars6 m))
    (M : Fin m → Fin 6 → ℤ) (h : Fin m) (j : Fin 6) :
    specializeNormalsList6 us M h j = if (h,j) ∈ us then 0 else M h j := by
  induction us generalizing M with
  | nil => simp [specializeNormalsList6]
  | cons u us ih =>
    rw [specializeNormalsList6,ih]
    by_cases ht : (h,j) ∈ us <;> by_cases he : (h,j) = u <;>
      simp [zeroNormalCoefficient6,ht,he]

theorem specializeNormalsList6_pivot {m : ℕ} (us : List (Vars6 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    specializeNormalsList6 us M h 0 = M h 0 := by
  rw [specializeNormalsList6_coeff,if_neg]
  intro he
  exact hus (h,0) he rfl

theorem eliminateList6_nonzero {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0) : eliminateList6 us P ≠ 0 := by
  induction us generalizing P with
  | nil => exact hn
  | cons u us ih => exact ih _ (eliminate6_nonzero u P hn)

theorem eliminateList6_height {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) : height6 (eliminateList6 us P) ≤ height6 P := by
  induction us generalizing P with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _).trans (eliminate6_height u P)

theorem eliminateList6_blockDegree {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) (h : Fin m) :
    blockDegree6 (eliminateList6 us P) h ≤ blockDegree6 P h := by
  induction us generalizing P with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _).trans (eliminate6_blockDegree u P h)

theorem eliminateList6_preserves_independence {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) (v : Vars6 m) (hv : ∀ d ∈ P.support, d v = 0) :
    ∀ d ∈ (eliminateList6 us P).support, d v = 0 := by
  induction us generalizing P with
  | nil => exact hv
  | cons u us ih => exact ih _ (eliminate6_preserves_independence u v P hv)

theorem eliminateList6_independent {m : ℕ} (us : List (Vars6 m))
    (P : MvPolynomial (Vars6 m) ℤ) :
    ∀ v ∈ us, ∀ d ∈ (eliminateList6 us P).support, d v = 0 := by
  induction us generalizing P with
  | nil => simp
  | cons u us ih =>
    intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      exact eliminateList6_preserves_independence us (eliminate6 u P) u
        (fun d hd => (eliminate6_support_source u P d hd).1)
    · exact ih _ v hv

theorem eliminateList6_closed {m : ℕ} (us : List (Vars6 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 6 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M r c) :
    (eliminateList6 us P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (specializeNormalsList6 us M) r c := by
  induction us generalizing M P with
  | nil => exact hP
  | cons u us ih =>
    have hu := hus u (by simp)
    have htail : ∀ v ∈ us, v.2 ≠ 0 := fun v hv => hus v (by simp [hv])
    exact ih htail (zeroNormalCoefficient6 M u)
      (fun h => by rw [zeroNormalCoefficient6_pivot M u hu h]; exact hM h)
      (eliminate6 u P) (eliminate6_nonzero u P hn) (eliminate6_closed M hM u hu r c P hn hP)

theorem eliminateList6_strict {m : ℕ} (us : List (Vars6 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 6 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M r c) :
    (eliminateList6 us P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (specializeNormalsList6 us M) r c := by
  induction us generalizing M P with
  | nil => exact hP
  | cons u us ih =>
    have hu := hus u (by simp)
    have htail : ∀ v ∈ us, v.2 ≠ 0 := fun v hv => hus v (by simp [hv])
    exact ih htail (zeroNormalCoefficient6 M u)
      (fun h => by rw [zeroNormalCoefficient6_pivot M u hu h]; exact hM h)
      (eliminate6 u P) (eliminate6_nonzero u P hn) (eliminate6_strict M hM u hu r c P hn hP)

def excessVariables6 (m : ℕ) : Finset (Vars6 m) :=
  Finset.univ.product ({2,3,4,5} : Finset (Fin 6))

theorem mem_excessVariables6 {m : ℕ} (u : Vars6 m) :
    u ∈ excessVariables6 m ↔ 2 ≤ u.2.val := by
  rcases u with ⟨h,k⟩
  fin_cases k <;> simp [excessVariables6]

theorem card_excessVariables6 (m : ℕ) : (excessVariables6 m).card = 4*m := by
  have hc : ({2,3,4,5} : Finset (Fin 6)).card = 4 := by decide
  simpa [excessVariables6,hc,Nat.mul_comm] using
    Finset.card_product (Finset.univ : Finset (Fin m)) ({2,3,4,5} : Finset (Fin 6))

def reducedNormals6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) : Fin m → Fin 6 → ℤ :=
  specializeNormalsList6 (excessVariables6 m).toList M

def reducedPolynomial6 {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) : MvPolynomial (Vars6 m) ℤ :=
  eliminateList6 (excessVariables6 m).toList P

theorem reducedNormals6_coeff {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) (j : Fin 6) :
    reducedNormals6 M h j = if 2 ≤ j.val then 0 else M h j := by
  simp only [reducedNormals6,specializeNormalsList6_coeff,Finset.mem_toList,mem_excessVariables6]

theorem reducedNormals6_first_two {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    reducedNormals6 M h 0 = M h 0 ∧ reducedNormals6 M h 1 = M h 1 := by
  simp [reducedNormals6_coeff]

theorem reducedNormals6_polynomial {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    normalPolynomial6 (reducedNormals6 M) h =
      MvPolynomial.C (M h 0 : ℝ)*MvPolynomial.X (h,0) +
        MvPolynomial.C (M h 1 : ℝ)*MvPolynomial.X (h,1) := by
  norm_num [normalPolynomial6,reducedNormals6_coeff,Fin.sum_univ_succ]

theorem reducedPolynomial6_support {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) :
    ∀ d ∈ (reducedPolynomial6 P).support, ∀ u : Vars6 m, 2 ≤ u.2.val → d u = 0 := by
  intro d hd u hu
  exact eliminateList6_independent (excessVariables6 m).toList P u
    (Finset.mem_toList.mpr ((mem_excessVariables6 u).mpr hu)) d hd

theorem reducedPolynomial6_nonzero {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0) :
    reducedPolynomial6 P ≠ 0 := eliminateList6_nonzero _ P hn

theorem reducedPolynomial6_height {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) :
    height6 (reducedPolynomial6 P) ≤ height6 P := eliminateList6_height _ P

theorem reducedPolynomial6_blockDegree {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) (h : Fin m) :
    blockDegree6 (reducedPolynomial6 P) h ≤ blockDegree6 P h := eliminateList6_blockDegree _ P h

theorem excessVariables6_free {m : ℕ} : ∀ u ∈ (excessVariables6 m).toList, u.2 ≠ 0 := by
  intro u hu hz
  have he := (mem_excessVariables6 u).mp (Finset.mem_toList.mp hu)
  rw [hz] at he
  norm_num at he

theorem reducedPolynomial6_closed {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M r c) :
    (reducedPolynomial6 P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (reducedNormals6 M) r c :=
  eliminateList6_closed _ excessVariables6_free M hM r c P hn hP

theorem reducedPolynomial6_strict {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars6 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 M r c) :
    (reducedPolynomial6 P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (reducedNormals6 M) r c :=
  eliminateList6_strict _ excessVariables6_free M hM r c P hn hP

theorem schmidtPackage6_excess_elimination
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) :
    ∃ (C : (h : Fin S.m) → SchmidtHilfssatz13.NormalCoordinateChoice6 (R.M (S.t h)))
      (P' : MvPolynomial (Vars6 S.m) ℤ) (PN : MvPolynomial (Vars6 S.m) ℚ)
      (F : MvPolynomial (Vars6 S.m) ℤ),
      let e := fun h => (C h).e
      let M' := permutedNormals6 (fun h => R.M (S.t h)) e
      P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
      PN = normalPolynomialQ6 M' P' ∧ PN ≠ 0 ∧
      (∀ h k, M' h ((C h).e.symm k) = R.M (S.t h) k) ∧
      F = reducedPolynomial6 P' ∧ F ≠ 0 ∧
      (excessVariables6 S.m).toList.length = 4*S.m ∧
      (∀ d ∈ F.support, ∀ u : Vars6 S.m, 2 ≤ u.2.val → d u = 0) ∧
      height6 F ≤ height6 S.P ∧ (∀ h, blockDegree6 F h ≤ S.r h) ∧
      (∀ h j, reducedNormals6 M' h j = if 2 ≤ j.val then 0 else M' h j) ∧
      (∀ h, reducedNormals6 M' h 0 = M' h 0 ∧ reducedNormals6 M' h 1 = M' h 1 ∧
        reducedNormals6 M' h 0 ≠ 0 ∧
        Int.gcd (reducedNormals6 M' h 0) (reducedNormals6 M' h 1)^5 ≤ (M' h 0).natAbs^4) ∧
      (∀ h, normalPolynomial6 (reducedNormals6 M') h =
        MvPolynomial.C (M' h 0 : ℝ)*MvPolynomial.X (h,0) +
          MvPolynomial.C (M' h 1 : ℝ)*MvPolynomial.X (h,1)) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        F.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (reducedNormals6 M') S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceStrictNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        F.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (reducedNormals6 M') S.r c) ∧
      F.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (reducedNormals6 M') S.r ((S.m : ℝ)*S.eta) ∧
      F.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (reducedNormals6 M') S.r S.theta := by
  obtain ⟨C,P',PN,heq,hinv,hn,hheight,hhom,hdeg,hlead,hrecover,hPN,hPNn,hcomp,hforward,
    hback,hden,hclear,hPNhom,hPNdeg,hPNorig,hnormInv,hnormForward,hnormReal,hreal,
    hclosed,hstrict,hclosedOrig,hstrictOrig,hhigh⟩ := schmidtPackage6_normal_substitution S
  let e := fun h => (C h).e
  let M' := permutedNormals6 (fun h => R.M (S.t h)) e
  let F := reducedPolynomial6 P'
  have hM : ∀ h, M' h 0 ≠ 0 := fun h => (hlead h).1
  have hc (c : ℝ) (hP : S.P.map (Int.castRingHom ℝ) ∈
      sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c) :
      F.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (reducedNormals6 M') S.r c := by
    exact reducedPolynomial6_closed M' hM S.r c P' hn ((hclosed c).mpr ((hclosedOrig c).mp hP))
  have hs (c : ℝ) (hP : S.P.map (Int.castRingHom ℝ) ∈
      sourceStrictNormalIdeal6 (fun h => R.M (S.t h)) S.r c) :
      F.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal6 (reducedNormals6 M') S.r c := by
    exact reducedPolynomial6_strict M' hM S.r c P' hn ((hstrict c).mpr ((hstrictOrig c).mp hP))
  have hFhigh := hc ((S.m : ℝ)*S.eta) S.high_index
  refine ⟨C,P',PN,F,heq,hinv,hPN,hPNn,hrecover,rfl,reducedPolynomial6_nonzero P' hn,
    ?_,reducedPolynomial6_support P',(reducedPolynomial6_height P').trans hheight.le,?_,
    reducedNormals6_coeff M',?_,reducedNormals6_polynomial M',hc,hs,hFhigh,?_⟩
  · simpa only [Finset.length_toList] using card_excessVariables6 S.m
  · intro h
    rw [← homogeneous6_blockDegree S.r P' hhom hn h]
    exact reducedPolynomial6_blockDegree P' h
  · intro h
    obtain ⟨h0,h1⟩ := reducedNormals6_first_two M' h
    refine ⟨h0,h1,?_,?_⟩
    · rw [h0]; exact hM h
    · rw [h0,h1]; exact (hlead h).2.2
  · exact (sourceStrictNormalIdeal6_iff (reducedNormals6 M') S.r S.theta _).mpr
      ⟨(S.m : ℝ)*S.eta,S.theta_index,hFhigh⟩

end CompoundFeasibility.SchmidtExcessElimination6Literal

#check CompoundFeasibility.SchmidtExcessElimination6Literal.pivotNormals6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.pivotNormals6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.pivotNormals6_polynomial
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.pivotNormals6_polynomial
#check CompoundFeasibility.SchmidtExcessElimination6Literal.pivotNormals6_inverse
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.pivotNormals6_inverse
#check CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateIdeal6_support
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateIdeal6_support
#check CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateStrictIdeal6_support
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateStrictIdeal6_support
#check CompoundFeasibility.SchmidtExcessElimination6Literal.support_X_pow_mul6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.support_X_pow_mul6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.free_weight_shift6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.free_weight_shift6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateIdeal6_saturation
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateIdeal6_saturation
#check CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateStrictIdeal6_saturation
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.coordinateStrictIdeal6_saturation
#check CompoundFeasibility.SchmidtExcessElimination6Literal.normalEquiv6_free
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.normalEquiv6_free
#check CompoundFeasibility.SchmidtExcessElimination6Literal.sourceNormalIdeal6_saturation
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.sourceNormalIdeal6_saturation
#check CompoundFeasibility.SchmidtExcessElimination6Literal.sourceStrictNormalIdeal6_saturation
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.sourceStrictNormalIdeal6_saturation
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_monomial
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_monomial
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_coeff
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_coeff
#check CompoundFeasibility.SchmidtExcessElimination6Literal.minimumExponent6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.minimumExponent6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.minimumExponent6_spec
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.minimumExponent6_spec
#check CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6_coeff
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6_coeff
#check CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6_factor
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6_factor
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_coeff
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_coeff
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_nonzero
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_nonzero
#check CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6_nonzero
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.extracted6_nonzero
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_support_source
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_support_source
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_height
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_height
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_blockDegree
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_blockDegree
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_preserves_independence
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_preserves_independence
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_homogeneous
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_homogeneous
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroNormalCoefficient6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroNormalCoefficient6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_map
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_map
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroNormalCoefficient6_pivot
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroNormalCoefficient6_pivot
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_normal
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_normal
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_normal_products
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_normal_products
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_ideal_map
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_ideal_map
#check CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_strictIdeal_map
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.zeroSpecialize6_strictIdeal_map
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_closed
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_closed
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_strict
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_strict
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_step
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminate6_step
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.specializeNormalsList6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.specializeNormalsList6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.specializeNormalsList6_coeff
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.specializeNormalsList6_coeff
#check CompoundFeasibility.SchmidtExcessElimination6Literal.specializeNormalsList6_pivot
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.specializeNormalsList6_pivot
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_nonzero
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_nonzero
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_height
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_height
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_blockDegree
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_blockDegree
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_preserves_independence
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_preserves_independence
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_independent
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_independent
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_closed
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_closed
#check CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_strict
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.eliminateList6_strict
#check CompoundFeasibility.SchmidtExcessElimination6Literal.excessVariables6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.excessVariables6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.mem_excessVariables6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.mem_excessVariables6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.card_excessVariables6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.card_excessVariables6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6_coeff
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6_coeff
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6_first_two
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6_first_two
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6_polynomial
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedNormals6_polynomial
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_support
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_support
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_nonzero
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_nonzero
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_height
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_height
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_blockDegree
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_blockDegree
#check CompoundFeasibility.SchmidtExcessElimination6Literal.excessVariables6_free
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.excessVariables6_free
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_closed
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_closed
#check CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_strict
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.reducedPolynomial6_strict
#check CompoundFeasibility.SchmidtExcessElimination6Literal.schmidtPackage6_excess_elimination
#print axioms CompoundFeasibility.SchmidtExcessElimination6Literal.schmidtPackage6_excess_elimination
