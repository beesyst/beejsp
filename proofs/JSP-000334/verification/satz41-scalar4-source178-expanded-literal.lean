import SubspaceBridge.SourceNormalizedHighIndex4
import SubspaceBridge.SchmidtTaylorCorrespondence6
import SubspaceBridge.SchmidtHilfssatz12
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Data.Nat.Factorization.Basic
import SubspaceBridge.SourceFieldLower6
import SubspaceBridge.SchmidtParameters6

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtScalarReduction4Literal178
open SourceMultiblock4 SourceNormalIndex4 Auxiliary4

def blockDegree4 {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (Vars4 m) A) (h : Fin m) : ℕ :=
  P.support.sup (fun d => ∑ j : Fin 4, d (h,j))

theorem homogeneous4_blockDegree {A : Type*} [CommRing A] {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars4 m) A) (hP : homogeneous4 r P) (hn : P ≠ 0) (h : Fin m) :
    blockDegree4 P h = r h := by
  unfold blockDegree4
  apply le_antisymm
  · exact Finset.sup_le (fun d hd => (hP d hd h).le)
  · obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hn
    rw [← hP d hd h]
    exact Finset.le_sup (f := fun d => ∑ j : Fin 4, d (h,j)) hd

def pivotExponent4 {m : ℕ} (k : Fin m → Fin 4) (i : Fin m → ℕ) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k u.1 then i u.1 else 0)

theorem pivotExponent4_weight {m : ℕ} (k : Fin m → Fin 4) (i r : Fin m → ℕ) :
    normalCoordinateWeight4 r k (pivotExponent4 k i) = ∑ h, (i h : ℝ)/(r h : ℝ) := by
  simp [normalCoordinateWeight4,pivotExponent4]

theorem pivotExponent4_forward {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (i : Fin m → ℕ) :
    normalForward4 M k (MvPolynomial.monomial (pivotExponent4 k i) 1) =
      ∏ h, (normalPolynomial4 M h)^(i h) := by
  rw [normalForward4_monomial]
  have hfree : (∏ h : Fin m, ∏ j ∈ Finset.univ.erase (k h),
      (MvPolynomial.X (h,j) : MvPolynomial (Vars4 m) ℝ) ^ pivotExponent4 k i (h,j)) = 1 := by
    apply Finset.prod_eq_one
    intro h _
    apply Finset.prod_eq_one
    intro j hj
    simp [pivotExponent4,(Finset.mem_erase.mp hj).1]
  simp [hfree,pivotExponent4]

theorem normalCoordinateWeight4_nonneg {m : ℕ} (r : Fin m → ℕ)
    (k : Fin m → Fin 4) (b : Vars4 m →₀ ℕ) : 0 ≤ normalCoordinateWeight4 r k b := by
  unfold normalCoordinateWeight4
  positivity

theorem sourceNormalIdeal4_support {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (Vars4 m) ℝ) (hP : P ∈ sourceNormalIdeal4 M r c) :
    ∀ b ∈ (normalInverse4 M k P).support, c ≤ normalCoordinateWeight4 r k b := by
  induction hP using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i,hi,rfl⟩ := hF
    rw [← pivotExponent4_forward M k i,normalInverse6_forward4 M k hk]
    intro b hb
    have he : b = pivotExponent4 k i := by symm; simpa using hb
    subst b
    simpa only [pivotExponent4_weight] using hi
  | zero => simp
  | add F G hF hG ihF ihG =>
    rw [map_add]
    intro b hb
    rcases Finset.mem_union.mp (MvPolynomial.support_add hb) with hb | hb
    · exact ihF b hb
    · exact ihG b hb
  | smul a F hF ih =>
    change ∀ b ∈ (normalInverse4 M k (a*F)).support, _
    rw [map_mul]
    intro b hb
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hb)
    rw [← he,normalCoordinateWeight4_add]
    exact (ih v hv).trans (le_add_of_nonneg_left (normalCoordinateWeight4_nonneg r k u))

theorem sourceNormalIdeal4_iff_support {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (Vars4 m) ℝ) :
    P ∈ sourceNormalIdeal4 M r c ↔
      ∀ b ∈ (normalInverse4 M k P).support, c ≤ normalCoordinateWeight4 r k b := by
  refine ⟨sourceNormalIdeal4_support M k hk r c P,?_⟩
  intro hP
  have hsum := congrArg (normalForward4 M k) (normalInverse4 M k P).as_sum
  rw [normalForward6_inverse4 M k hk P,map_sum] at hsum
  rw [hsum]
  apply Ideal.sum_mem
  intro b hb
  exact normalForward4_monomial_mem M k r c b _ (hP b hb)

theorem support_X_pow_mul4 {A : Type*} [CommRing A] {m : ℕ}
    (u : Vars4 m) (a : ℕ) (F : MvPolynomial (Vars4 m) A) (d : Vars4 m →₀ ℕ) :
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

theorem free_weight_shift4 {m : ℕ} (r : Fin m → ℕ) (u : Vars4 m)
    (hu : u.2 ≠ 0) (a : ℕ) (d : Vars4 m →₀ ℕ) :
    normalCoordinateWeight4 r (fun _ => 0) (Finsupp.single u a+d) =
      normalCoordinateWeight4 r (fun _ => 0) d := by
  rw [normalCoordinateWeight4_add]
  have hz : normalCoordinateWeight4 r (fun _ => 0) (Finsupp.single u a) = 0 := by
    rcases u with ⟨g,k⟩
    simp [normalCoordinateWeight4,Finsupp.single_apply,Prod.mk.injEq,hu]
  rw [hz,zero_add]

theorem sourceNormalIdeal4_saturation {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (u : Vars4 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (Vars4 m) ℝ) :
    MvPolynomial.X u^a*F ∈ sourceNormalIdeal4 M r c ↔ F ∈ sourceNormalIdeal4 M r c := by
  rw [sourceNormalIdeal4_iff_support M (fun _ => 0) hM,
    sourceNormalIdeal4_iff_support M (fun _ => 0) hM,map_mul,map_pow]
  have hx : normalInverse4 M (fun _ => 0) (MvPolynomial.X u) = MvPolynomial.X u := by
    simp [normalInverse4,hu]
  rw [hx]
  constructor
  · intro h d hd
    have hm := h _ ((support_X_pow_mul4 u a _ _).mpr ⟨d,hd,rfl⟩)
    simpa only [free_weight_shift4 r u hu] using hm
  · intro h d hd
    obtain ⟨b,hb,rfl⟩ := (support_X_pow_mul4 u a _ d).mp hd
    simpa only [free_weight_shift4 r u hu] using h b hb

def zeroSpecialize4 {A : Type*} [CommRing A] {m : ℕ} (u : Vars4 m) :
    MvPolynomial (Vars4 m) A →+* MvPolynomial (Vars4 m) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v => if v = u then 0 else MvPolynomial.X v)

theorem zeroSpecialize4_monomial {A : Type*} [CommRing A] {m : ℕ}
    (u : Vars4 m) (d : Vars4 m →₀ ℕ) (c : A) :
    zeroSpecialize4 u (MvPolynomial.monomial d c) =
      if d u = 0 then MvPolynomial.monomial d c else 0 := by
  rw [zeroSpecialize4,MvPolynomial.eval₂Hom_monomial]
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
    have hz : (∏ v : Vars4 m,
        (if v = u then 0 else MvPolynomial.X v)^d v) = (0 : MvPolynomial (Vars4 m) A) := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [hd]
    rw [hz,mul_zero]

theorem zeroSpecialize4_coeff {A : Type*} [CommRing A] {m : ℕ}
    (u : Vars4 m) (F : MvPolynomial (Vars4 m) A) (d : Vars4 m →₀ ℕ) :
    (zeroSpecialize4 u F).coeff d = if d u = 0 then F.coeff d else 0 := by
  induction F using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [zeroSpecialize4_monomial]
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

def minimumExponent4 {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ) : ℕ :=
  if hn : P = 0 then 0 else
    (Classical.choose (Finset.exists_min_image P.support (fun d => d u)
      (MvPolynomial.support_nonempty.mpr hn))) u

theorem minimumExponent4_spec {m : ℕ} (u : Vars4 m)
    (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0) :
    ∃ d ∈ P.support, d u = minimumExponent4 u P ∧
      ∀ b ∈ P.support, minimumExponent4 u P ≤ b u := by
  simp only [minimumExponent4,dif_neg hn]
  have hex := Finset.exists_min_image P.support (fun d => d u) (MvPolynomial.support_nonempty.mpr hn)
  exact ⟨Classical.choose hex,(Classical.choose_spec hex).1,rfl,(Classical.choose_spec hex).2⟩

def extracted4 {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ) :
    MvPolynomial (Vars4 m) ℤ := P.divMonomial (Finsupp.single u (minimumExponent4 u P))

def eliminate4 {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ) :
    MvPolynomial (Vars4 m) ℤ := zeroSpecialize4 u (extracted4 u P)

theorem extracted4_coeff {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (d : Vars4 m →₀ ℕ) :
    (extracted4 u P).coeff d = P.coeff (Finsupp.single u (minimumExponent4 u P)+d) := rfl

theorem extracted4_factor {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (hn : P ≠ 0) : P = MvPolynomial.X u^(minimumExponent4 u P)*extracted4 u P := by
  obtain ⟨b,hb,hbe,hmin⟩ := minimumExponent4_spec u P hn
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.coeff_monomial_mul']
  by_cases hs : Finsupp.single u (minimumExponent4 u P) ≤ d
  · rw [if_pos hs,one_mul,extracted4_coeff,add_tsub_cancel_of_le hs]
  · rw [if_neg hs]
    apply MvPolynomial.not_mem_support_iff.mp
    intro hd
    exact hs (Finsupp.single_le_iff.mpr (hmin d hd))

theorem eliminate4_coeff {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (d : Vars4 m →₀ ℕ) :
    (eliminate4 u P).coeff d = if d u = 0 then
      P.coeff (Finsupp.single u (minimumExponent4 u P)+d) else 0 := by
  rw [eliminate4,zeroSpecialize4_coeff,extracted4_coeff]

theorem eliminate4_nonzero {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (hn : P ≠ 0) : eliminate4 u P ≠ 0 := by
  obtain ⟨b,hb,hbe,hmin⟩ := minimumExponent4_spec u P hn
  let s := Finsupp.single u (minimumExponent4 u P)
  have hs : s ≤ b := Finsupp.single_le_iff.mpr (hmin b hb)
  have hz : (b-s) u = 0 := by simp [s,Finsupp.tsub_apply,hbe]
  have hcoeff : (eliminate4 u P).coeff (b-s) ≠ 0 := by
    rw [eliminate4_coeff,if_pos hz,show Finsupp.single u (minimumExponent4 u P) = s from rfl,
      add_tsub_cancel_of_le hs]
    exact MvPolynomial.mem_support_iff.mp hb
  exact MvPolynomial.ne_zero_iff.mpr ⟨b-s,hcoeff⟩

theorem extracted4_nonzero {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (hn : P ≠ 0) : extracted4 u P ≠ 0 := by
  intro hz
  apply eliminate4_nonzero u P hn
  rw [eliminate4,hz,map_zero]

theorem eliminate4_support_source {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (d : Vars4 m →₀ ℕ) (hd : d ∈ (eliminate4 u P).support) :
    d u = 0 ∧ Finsupp.single u (minimumExponent4 u P)+d ∈ P.support := by
  have hn := MvPolynomial.mem_support_iff.mp hd
  rw [eliminate4_coeff] at hn
  by_cases hz : d u = 0
  · exact ⟨hz,MvPolynomial.mem_support_iff.mpr (by simpa [hz] using hn)⟩
  · simp [hz] at hn

theorem eliminate4_height {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ) :
    height4 (eliminate4 u P) ≤ height4 P := by
  apply Finset.sup_le
  intro d hd
  obtain ⟨hz,hp⟩ := eliminate4_support_source u P d hd
  change ((eliminate4 u P).coeff d).natAbs ≤ height4 P
  rw [eliminate4_coeff,if_pos hz]
  exact Finset.le_sup (f := fun b => (P.coeff b).natAbs) hp

theorem eliminate4_blockDegree {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (h : Fin m) : blockDegree4 (eliminate4 u P) h ≤ blockDegree4 P h := by
  apply Finset.sup_le
  intro d hd
  have hp := (eliminate4_support_source u P d hd).2
  calc
    (∑ j : Fin 4, d (h,j)) ≤ ∑ j : Fin 4, (Finsupp.single u (minimumExponent4 u P)+d) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.le_add_left _ _
    _ ≤ blockDegree4 P h := Finset.le_sup (f := fun b => ∑ j : Fin 4, b (h,j)) hp

theorem eliminate4_preserves_independence {m : ℕ} (u v : Vars4 m)
    (P : MvPolynomial (Vars4 m) ℤ) (hv : ∀ d ∈ P.support, d v = 0) :
    ∀ d ∈ (eliminate4 u P).support, d v = 0 := by
  intro d hd
  have he := hv _ (eliminate4_support_source u P d hd).2
  simp only [Finsupp.add_apply] at he
  omega

theorem eliminate4_homogeneous {m : ℕ} (u : Vars4 m) (P : MvPolynomial (Vars4 m) ℤ)
    (r : Fin m → ℕ) (hP : homogeneous4 r P) :
    homogeneous4 (fun h => r h - if u.1 = h then minimumExponent4 u P else 0) (eliminate4 u P) := by
  intro d hd h
  have he := hP _ (eliminate4_support_source u P d hd).2 h
  have hs : (∑ j : Fin 4, (Finsupp.single u (minimumExponent4 u P)) (h,j)) =
      if u.1 = h then minimumExponent4 u P else 0 := by
    rcases u with ⟨g,k⟩
    by_cases hg : g = h
    · subst g; simp [Finsupp.single_apply,Prod.mk.injEq,eq_comm]
    · simp [Finsupp.single_apply,Prod.mk.injEq,hg]
  simp only [Finsupp.add_apply,Finset.sum_add_distrib,hs] at he
  change (∑ j : Fin 4, d (h,j)) = r h - if u.1 = h then minimumExponent4 u P else 0
  omega

def zeroNormalCoefficient4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (u : Vars4 m)
    (h : Fin m) (j : Fin 4) : ℤ := if (h,j) = u then 0 else M h j

theorem zeroSpecialize4_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {m : ℕ} (u : Vars4 m) (F : MvPolynomial (Vars4 m) A) :
    (zeroSpecialize4 u F).map f = zeroSpecialize4 u (F.map f) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [zeroSpecialize4]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F v hF =>
    simp only [map_mul,hF,MvPolynomial.map_X]
    by_cases hv : v = u <;> simp [zeroSpecialize4,hv]

theorem zeroNormalCoefficient4_pivot {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (u : Vars4 m) (hu : u.2 ≠ 0) (h : Fin m) :
    zeroNormalCoefficient4 M u h 0 = M h 0 := by
  have he : (h,0) ≠ u := by intro he; exact hu (congrArg Prod.snd he).symm
  simp [zeroNormalCoefficient4,he]

theorem zeroSpecialize4_normal {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (u : Vars4 m) (h : Fin m) :
    zeroSpecialize4 u (normalPolynomial4 M h) = normalPolynomial4 (zeroNormalCoefficient4 M u) h := by
  simp only [normalPolynomial4,map_sum,map_mul,zeroSpecialize4,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X']
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : (h,j) = u <;> simp [zeroNormalCoefficient4,he]

theorem zeroSpecialize4_normal_products {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (u : Vars4 m) (i : Fin m → ℕ) :
    zeroSpecialize4 u (∏ h, normalPolynomial4 M h^(i h)) =
      ∏ h, normalPolynomial4 (zeroNormalCoefficient4 M u) h^(i h) := by
  simp only [map_prod,map_pow,zeroSpecialize4_normal]

theorem zeroSpecialize4_ideal_map {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (u : Vars4 m) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (zeroSpecialize4 u) (sourceNormalIdeal4 M r c) =
      sourceNormalIdeal4 (zeroNormalCoefficient4 M u) r c := by
  unfold sourceNormalIdeal4
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,zeroSpecialize4_normal_products M u i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,zeroSpecialize4_normal_products M u i⟩

theorem eliminate4_closed {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (u : Vars4 m) (hu : u.2 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c) :
    (eliminate4 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 (zeroNormalCoefficient4 M u) r c := by
  have hQ : (extracted4 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c := by
    apply (sourceNormalIdeal4_saturation M hM r c u hu (minimumExponent4 u P) _).mp
    rw [extracted4_factor u P hn,map_mul,map_pow,MvPolynomial.map_X] at hP
    exact hP
  rw [eliminate4,zeroSpecialize4_map,← zeroSpecialize4_ideal_map M u r c]
  exact Ideal.mem_map_of_mem (zeroSpecialize4 u) hQ

def eliminateList4 {m : ℕ} : List (Vars4 m) → MvPolynomial (Vars4 m) ℤ → MvPolynomial (Vars4 m) ℤ
  | [],P => P
  | u::us,P => eliminateList4 us (eliminate4 u P)

def specializeNormalsList4 {m : ℕ} : List (Vars4 m) → (Fin m → Fin 4 → ℤ) → Fin m → Fin 4 → ℤ
  | [],M => M
  | u::us,M => specializeNormalsList4 us (zeroNormalCoefficient4 M u)

theorem specializeNormalsList4_coeff {m : ℕ} (us : List (Vars4 m))
    (M : Fin m → Fin 4 → ℤ) (h : Fin m) (j : Fin 4) :
    specializeNormalsList4 us M h j = if (h,j) ∈ us then 0 else M h j := by
  induction us generalizing M with
  | nil => simp [specializeNormalsList4]
  | cons u us ih =>
    rw [specializeNormalsList4,ih]
    by_cases ht : (h,j) ∈ us <;> by_cases he : (h,j) = u <;>
      simp [zeroNormalCoefficient4,ht,he]

theorem specializeNormalsList4_pivot {m : ℕ} (us : List (Vars4 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    specializeNormalsList4 us M h 0 = M h 0 := by
  rw [specializeNormalsList4_coeff,if_neg]
  intro he
  exact hus (h,0) he rfl

theorem eliminateList4_nonzero {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0) : eliminateList4 us P ≠ 0 := by
  induction us generalizing P with
  | nil => exact hn
  | cons u us ih => exact ih _ (eliminate4_nonzero u P hn)

theorem eliminateList4_height {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) : height4 (eliminateList4 us P) ≤ height4 P := by
  induction us generalizing P with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _).trans (eliminate4_height u P)

theorem eliminateList4_blockDegree {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) (h : Fin m) :
    blockDegree4 (eliminateList4 us P) h ≤ blockDegree4 P h := by
  induction us generalizing P with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _).trans (eliminate4_blockDegree u P h)

theorem eliminateList4_preserves_independence {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) (v : Vars4 m) (hv : ∀ d ∈ P.support, d v = 0) :
    ∀ d ∈ (eliminateList4 us P).support, d v = 0 := by
  induction us generalizing P with
  | nil => exact hv
  | cons u us ih => exact ih _ (eliminate4_preserves_independence u v P hv)

theorem eliminateList4_independent {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) :
    ∀ v ∈ us, ∀ d ∈ (eliminateList4 us P).support, d v = 0 := by
  induction us generalizing P with
  | nil => simp
  | cons u us ih =>
    intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      exact eliminateList4_preserves_independence us (eliminate4 u P) u
        (fun d hd => (eliminate4_support_source u P d hd).1)
    · exact ih _ v hv

theorem eliminateList4_closed {m : ℕ} (us : List (Vars4 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 4 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c) :
    (eliminateList4 us P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 (specializeNormalsList4 us M) r c := by
  induction us generalizing M P with
  | nil => exact hP
  | cons u us ih =>
    have hu := hus u (by simp)
    have htail : ∀ v ∈ us, v.2 ≠ 0 := fun v hv => hus v (by simp [hv])
    exact ih htail (zeroNormalCoefficient4 M u)
      (fun h => by rw [zeroNormalCoefficient4_pivot M u hu h]; exact hM h)
      (eliminate4 u P) (eliminate4_nonzero u P hn) (eliminate4_closed M hM u hu r c P hn hP)

def excessVariables4 (m : ℕ) : Finset (Vars4 m) :=
  Finset.univ.product ({2,3} : Finset (Fin 4))

theorem mem_excessVariables4 {m : ℕ} (u : Vars4 m) :
    u ∈ excessVariables4 m ↔ 2 ≤ u.2.val := by
  rcases u with ⟨h,k⟩
  fin_cases k <;> simp [excessVariables4]

theorem card_excessVariables4 (m : ℕ) : (excessVariables4 m).card = 2*m := by
  have hc : ({2,3} : Finset (Fin 4)).card = 2 := by decide
  simpa [excessVariables4,hc,Nat.mul_comm] using
    Finset.card_product (Finset.univ : Finset (Fin m)) ({2,3} : Finset (Fin 4))

def reducedNormals4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) : Fin m → Fin 4 → ℤ :=
  specializeNormalsList4 (excessVariables4 m).toList M

def reducedPolynomial4 {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ) : MvPolynomial (Vars4 m) ℤ :=
  eliminateList4 (excessVariables4 m).toList P

theorem reducedNormals4_coeff {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) (j : Fin 4) :
    reducedNormals4 M h j = if 2 ≤ j.val then 0 else M h j := by
  simp only [reducedNormals4,specializeNormalsList4_coeff,Finset.mem_toList,mem_excessVariables4]

theorem reducedNormals4_first_two {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    reducedNormals4 M h 0 = M h 0 ∧ reducedNormals4 M h 1 = M h 1 := by
  simp [reducedNormals4_coeff]

theorem reducedNormals4_polynomial {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    normalPolynomial4 (reducedNormals4 M) h =
      MvPolynomial.C (M h 0 : ℝ)*MvPolynomial.X (h,0) +
        MvPolynomial.C (M h 1 : ℝ)*MvPolynomial.X (h,1) := by
  norm_num [normalPolynomial4,reducedNormals4_coeff,Fin.sum_univ_succ]

theorem reducedPolynomial4_support {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ) :
    ∀ d ∈ (reducedPolynomial4 P).support, ∀ u : Vars4 m, 2 ≤ u.2.val → d u = 0 := by
  intro d hd u hu
  exact eliminateList4_independent (excessVariables4 m).toList P u
    (Finset.mem_toList.mpr ((mem_excessVariables4 u).mpr hu)) d hd

theorem reducedPolynomial4_nonzero {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0) :
    reducedPolynomial4 P ≠ 0 := eliminateList4_nonzero _ P hn

theorem reducedPolynomial4_height {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ) :
    height4 (reducedPolynomial4 P) ≤ height4 P := eliminateList4_height _ P

theorem reducedPolynomial4_blockDegree {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ) (h : Fin m) :
    blockDegree4 (reducedPolynomial4 P) h ≤ blockDegree4 P h := eliminateList4_blockDegree _ P h

theorem excessVariables4_free {m : ℕ} : ∀ u ∈ (excessVariables4 m).toList, u.2 ≠ 0 := by
  intro u hu hz
  have he := (mem_excessVariables4 u).mp (Finset.mem_toList.mp hu)
  rw [hz] at he
  norm_num at he

theorem reducedPolynomial4_closed {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c) :
    (reducedPolynomial4 P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 (reducedNormals4 M) r c :=
  eliminateList4_closed _ excessVariables4_free M hM r c P hn hP

def eliminatedDegrees4 {m : ℕ} : List (Vars4 m) → MvPolynomial (Vars4 m) ℤ →
    (Fin m → ℕ) → Fin m → ℕ
  | [],_,r => r
  | u::us,P,r => eliminatedDegrees4 us (eliminate4 u P)
      (fun h => r h - if u.1 = h then minimumExponent4 u P else 0)

theorem eliminateList4_homogeneous {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) (r : Fin m → ℕ) (hP : homogeneous4 r P) :
    homogeneous4 (eliminatedDegrees4 us P r) (eliminateList4 us P) := by
  induction us generalizing P r with
  | nil => exact hP
  | cons u us ih => exact ih _ _ (eliminate4_homogeneous u P r hP)

theorem eliminatedDegrees4_le {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) (r : Fin m → ℕ) (h : Fin m) :
    eliminatedDegrees4 us P r h ≤ r h := by
  induction us generalizing P r with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _ _).trans (Nat.sub_le _ _)

theorem eliminatedDegrees4_actual {m : ℕ} (us : List (Vars4 m))
    (P : MvPolynomial (Vars4 m) ℤ) (r : Fin m → ℕ) (hP : homogeneous4 r P)
    (hn : P ≠ 0) (h : Fin m) :
    eliminatedDegrees4 us P r h = blockDegree4 (eliminateList4 us P) h :=
  (homogeneous4_blockDegree _ _ (eliminateList4_homogeneous us P r hP)
    (eliminateList4_nonzero us P hn) h).symm

theorem reducedPolynomial4_homogeneous {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ)
    (r : Fin m → ℕ) (hP : homogeneous4 r P) (hn : P ≠ 0) :
    homogeneous4 (blockDegree4 (reducedPolynomial4 P)) (reducedPolynomial4 P) ∧
      (∀ h, blockDegree4 (reducedPolynomial4 P) h ≤ r h) := by
  have he : eliminatedDegrees4 (excessVariables4 m).toList P r =
      blockDegree4 (reducedPolynomial4 P) := by
    funext h
    exact eliminatedDegrees4_actual _ P r hP hn h
  constructor
  · rw [← he]
    exact eliminateList4_homogeneous _ P r hP
  · intro h
    rw [← he]
    exact eliminatedDegrees4_le _ P r h

def scalar4 {A : Type*} [CommRing A] {m : ℕ} :
    MvPolynomial (Vars4 m) A →+* MvPolynomial (Fin m) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = 0 then MvPolynomial.X u.1 else if u.2 = 1 then 1 else 0)

theorem scalar4_generators {A : Type*} [CommRing A] {m : ℕ} :
    (∀ c : A, scalar4 (MvPolynomial.C c : MvPolynomial (Vars4 m) A) = MvPolynomial.C c) ∧
      (∀ u : Vars4 m, scalar4 (MvPolynomial.X u : MvPolynomial (Vars4 m) A) =
        if u.2 = 0 then MvPolynomial.X u.1 else if u.2 = 1 then 1 else 0) := by
  constructor <;> intro x <;> simp [scalar4]

theorem scalar4_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {m : ℕ} (P : MvPolynomial (Vars4 m) A) :
    (scalar4 P).map f = scalar4 (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [scalar4]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F u hF =>
    simp only [map_mul,hF,MvPolynomial.map_X]
    by_cases h0 : u.2 = 0 <;> by_cases h1 : u.2 = 1 <;> simp [scalar4,h0,h1]

def scalarExponent4 {m : ℕ} (d : Vars4 m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun h => d (h,0))

def binarySupport4 {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (Vars4 m) A) : Prop :=
  ∀ d ∈ P.support, ∀ u : Vars4 m, 2 ≤ u.2.val → d u = 0

theorem binary_block_sum4 {m : ℕ} (d : Vars4 m →₀ ℕ)
    (hd : ∀ u : Vars4 m, 2 ≤ u.2.val → d u = 0) (h : Fin m) :
    (∑ j : Fin 4, d (h,j)) = d (h,0)+d (h,1) := by
  have hs : (∑ j ∈ ({0,1} : Finset (Fin 4)), d (h,j)) = ∑ j : Fin 4, d (h,j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply hd (h,j)
    fin_cases j <;> simp_all
  exact hs.symm.trans (by simp)

theorem scalar4_monomial {A : Type*} [CommRing A] {m : ℕ}
    (d : Vars4 m →₀ ℕ) (hd : ∀ u : Vars4 m, 2 ≤ u.2.val → d u = 0) (c : A) :
    scalar4 (MvPolynomial.monomial d c) = MvPolynomial.monomial (scalarExponent4 d) c := by
  rw [scalar4,MvPolynomial.eval₂Hom_monomial,MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [Finset.prod_eq_single (0 : Fin 4)]
  · simp [scalarExponent4]
  · intro j _ hj0
    by_cases hj1 : j = 1
    · simp [hj1]
    · have hz := hd (h,j) (by fin_cases j <;> simp_all)
      simp [hz]
  · simp

theorem scalarExponent4_inj {m : ℕ} (r : Fin m → ℕ) (d e : Vars4 m →₀ ℕ)
    (hd : ∀ u : Vars4 m, 2 ≤ u.2.val → d u = 0)
    (he : ∀ u : Vars4 m, 2 ≤ u.2.val → e u = 0)
    (hdr : ∀ h, (∑ j : Fin 4, d (h,j)) = r h)
    (her : ∀ h, (∑ j : Fin 4, e (h,j)) = r h)
    (hp : scalarExponent4 d = scalarExponent4 e) : d = e := by
  apply Finsupp.ext
  rintro ⟨h,j⟩
  have h0 : d (h,0) = e (h,0) := congrArg (fun b => b h) hp
  have hd' := hdr h
  have he' := her h
  rw [binary_block_sum4 d hd h] at hd'
  rw [binary_block_sum4 e he h] at he'
  by_cases hj0 : j = 0
  · subst j; exact h0
  by_cases hj1 : j = 1
  · subst j; omega
  have hj : 2 ≤ j.val := by fin_cases j <;> simp_all
  rw [hd (h,j) hj,he (h,j) hj]

theorem scalarExponent4_injOn {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A)
    (hh : homogeneous4 r P) (hb : binarySupport4 P) :
    Set.InjOn scalarExponent4 (↑P.support : Set (Vars4 m →₀ ℕ)) := by
  intro d hd e he hp
  exact scalarExponent4_inj r d e (hb d hd) (hb e he) (hh d hd) (hh e he) hp

theorem scalar4_as_sum {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (Vars4 m) A) (hb : binarySupport4 P) :
    scalar4 P = ∑ d ∈ P.support, MvPolynomial.monomial (scalarExponent4 d) (P.coeff d) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact scalar4_monomial d (hb d hd) (P.coeff d)

theorem scalar4_coeff {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A)
    (hh : homogeneous4 r P) (hb : binarySupport4 P)
    (d : Vars4 m →₀ ℕ) (hd : d ∈ P.support) :
    (scalar4 P).coeff (scalarExponent4 d) = P.coeff d := by
  rw [scalar4_as_sum P hb,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hed
    rw [MvPolynomial.coeff_monomial,if_neg]
    intro hp
    exact hed (scalarExponent4_injOn r P hh hb he hd hp)
  · intro hn
    exact False.elim (hn hd)

theorem scalar4_support {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A)
    (hh : homogeneous4 r P) (hb : binarySupport4 P) :
    (scalar4 P).support = P.support.image scalarExponent4 := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [scalar4_as_sum P hb] at he
    obtain ⟨d,hd,hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
    have heq : e = scalarExponent4 d := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (R := A) hm)
    exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
  · intro e he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
    rw [MvPolynomial.mem_support_iff,scalar4_coeff r P hh hb d hd]
    exact MvPolynomial.mem_support_iff.mp hd

def scalarSupportEquiv4 {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A)
    (hh : homogeneous4 r P) (hb : binarySupport4 P) :
    {d // d ∈ P.support} ≃ {e // e ∈ (scalar4 P).support} :=
  Equiv.ofBijective (fun d => ⟨scalarExponent4 d.val,
    by rw [scalar4_support r P hh hb]; exact Finset.mem_image.mpr ⟨d.val,d.property,rfl⟩⟩) (by
    constructor
    · intro d e he
      apply Subtype.ext
      exact scalarExponent4_injOn r P hh hb d.property e.property (congrArg Subtype.val he)
    · intro e
      have he : e.val ∈ P.support.image scalarExponent4 :=
        Eq.mp (congrArg (fun s : Finset (Fin m →₀ ℕ) => e.val ∈ s)
          (scalar4_support r P hh hb)) e.property
      obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp he
      exact ⟨⟨d,hd⟩,Subtype.ext hde⟩)

theorem scalar4_nonzero {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A)
    (hh : homogeneous4 r P) (hb : binarySupport4 P) (hn : P ≠ 0) : scalar4 P ≠ 0 := by
  obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hn
  apply MvPolynomial.ne_zero_iff.mpr
  refine ⟨scalarExponent4 d,?_⟩
  rw [scalar4_coeff r P hh hb d hd]
  exact MvPolynomial.mem_support_iff.mp hd

theorem scalar4_height {m : ℕ} (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) ℤ)
    (hh : homogeneous4 r P) (hb : binarySupport4 P) :
    JSP000334.rothIntegerHeight (scalar4 P) = height4 P := by
  unfold JSP000334.rothIntegerHeight height4
  rw [scalar4_support r P hh hb,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d hd
  change ((scalar4 P).coeff (scalarExponent4 d)).natAbs = (P.coeff d).natAbs
  rw [scalar4_coeff r P hh hb d hd]

theorem scalar4_support_degree {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A)
    (hh : homogeneous4 r P) (hb : binarySupport4 P) :
    ∀ e ∈ (scalar4 P).support, ∀ h, e h ≤ r h := by
  intro e he h
  rw [scalar4_support r P hh hb] at he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
  change d (h,0) ≤ r h
  rw [← hh d hd h,binary_block_sum4 d (hb d hd) h]
  exact Nat.le_add_right _ _

theorem scalar4_degree {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) A)
    (hh : homogeneous4 r P) (hb : binarySupport4 P) (h : Fin m) :
    (scalar4 P).degreeOf h ≤ r h :=
  MvPolynomial.degreeOf_le_iff.mpr (fun e he => scalar4_support_degree r P hh hb e he h)

def scalarNormal4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    MvPolynomial (Fin m) ℝ :=
  MvPolynomial.C (M h 0 : ℝ)*MvPolynomial.X h + MvPolynomial.C (M h 1 : ℝ)

theorem scalar4_normal {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    scalar4 (normalPolynomial4 (reducedNormals4 M) h) = scalarNormal4 M h := by
  simp only [reducedNormals4_polynomial,map_add,map_mul,
    (scalar4_generators (A := ℝ)).1,(scalar4_generators (A := ℝ)).2]
  simp [scalarNormal4]

theorem scalar4_normal_products {m : ℕ} (M : Fin m → Fin 4 → ℤ) (i : Fin m → ℕ) :
    scalar4 (∏ h, normalPolynomial4 (reducedNormals4 M) h^(i h)) =
      ∏ h, scalarNormal4 M h^(i h) := by
  simp only [map_prod,map_pow,scalar4_normal]

def scalarIdeal4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, scalarNormal4 M h^(i h)}

theorem scalar4_ideal_map {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map scalar4 (sourceNormalIdeal4 (reducedNormals4 M) r c) = scalarIdeal4 M r c := by
  unfold sourceNormalIdeal4 scalarIdeal4
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,scalar4_normal_products M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,scalar4_normal_products M i⟩

theorem scalar4_closed {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars4 m) ℤ)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 (reducedNormals4 M) r c) :
    (scalar4 P).map (Int.castRingHom ℝ) ∈ scalarIdeal4 M r c := by
  rw [scalar4_map,← scalar4_ideal_map M r c]
  exact Ideal.mem_map_of_mem scalar4 hP

open SchmidtRationalNormalization6 (rootNumerator6 rootDenominator6 integer_normalization6 root_ratio6 monic_generator6)
def monicNormal4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) : MvPolynomial (Fin m) ℝ :=
  MvPolynomial.X h - MvPolynomial.C
    ((rootNumerator6 (M h 0) (M h 1) : ℝ)/(rootDenominator6 (M h 0) (M h 1) : ℝ))

theorem scalarNormal4_monic {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (h : Fin m) :
    scalarNormal4 M h = MvPolynomial.C (M h 0 : ℝ)*monicNormal4 M h :=
  monic_generator6 (M h 0) (M h 1) (hM h) h

theorem normal_constant_unit4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (h : Fin m) :
    IsUnit (MvPolynomial.C (M h 0 : ℝ) : MvPolynomial (Fin m) ℝ) := by
  have ha : (M h 0 : ℝ) ≠ 0 := by exact_mod_cast hM h
  exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C

theorem scalar_products_scaling4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (i : Fin m → ℕ) :
    (∏ h, scalarNormal4 M h^(i h)) =
      MvPolynomial.C (∏ h, (M h 0 : ℝ)^(i h))*(∏ h, monicNormal4 M h^(i h)) := by
  simp only [scalarNormal4_monic M hM,mul_pow,Finset.prod_mul_distrib,map_prod,map_pow]

theorem scalar_products_membership4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (i : Fin m → ℕ) (I : Ideal (MvPolynomial (Fin m) ℝ)) :
    (∏ h, scalarNormal4 M h^(i h)) ∈ I ↔ (∏ h, monicNormal4 M h^(i h)) ∈ I := by
  have hn : (∏ h, (M h 0 : ℝ)^(i h)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro h _
    exact pow_ne_zero _ (by exact_mod_cast hM h)
  have hi : MvPolynomial.C ((∏ h, (M h 0 : ℝ)^(i h))⁻¹)*
      (∏ h, scalarNormal4 M h^(i h)) = ∏ h, monicNormal4 M h^(i h) := by
    rw [scalar_products_scaling4 M hM i,← mul_assoc,← MvPolynomial.C_mul,
      inv_mul_cancel₀ hn,map_one,one_mul]
  constructor
  · intro hp
    rw [← hi]
    exact I.mul_mem_left _ hp
  · intro hp
    rw [scalar_products_scaling4 M hM i]
    exact I.mul_mem_left _ hp

def monicIdeal4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, monicNormal4 M h^(i h)}

theorem scalarIdeal4_eq_monic {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ) :
    scalarIdeal4 M r c = monicIdeal4 M r c := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨i,hi,rfl⟩
    apply (scalar_products_membership4 M hM i _).mpr
    exact Ideal.subset_span ⟨i,hi,rfl⟩
  · apply Ideal.span_le.mpr
    rintro P ⟨i,hi,rfl⟩
    apply (scalar_products_membership4 M hM i _).mp
    exact Ideal.subset_span ⟨i,hi,rfl⟩

open SchmidtTaylorCorrespondence6 (translate6 translate6_products source_weight6 weight_nonneg6 translate6_zero_reflection)
def rootPoint4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) : Fin m → ℝ :=
  fun h => (rootNumerator6 (M h 0) (M h 1) : ℝ)/(rootDenominator6 (M h 0) (M h 1) : ℝ)

theorem monicIdeal4_support {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ)
    (hH : H ∈ monicIdeal4 M r c) :
    ∀ b ∈ (SchmidtTaylorCorrespondence6.translate6 (rootPoint4 M) H).support, c ≤ JSP000334.rothTaylorWeight r b := by
  induction hH using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i,hi,rfl⟩ := hF
    change ∀ b ∈ (SchmidtTaylorCorrespondence6.translate6 (rootPoint4 M)
      (∏ h, (MvPolynomial.X h - MvPolynomial.C (rootPoint4 M h))^(i h))).support, _
    rw [SchmidtTaylorCorrespondence6.translate6_products]
    intro b hb
    have he : b = Finsupp.equivFunOnFinite.symm i := by symm; simpa using hb
    subst b
    simpa only [SchmidtTaylorCorrespondence6.source_weight6] using hi
  | zero => simp
  | add F G hF hG ihF ihG =>
    rw [map_add]
    intro b hb
    rcases Finset.mem_union.mp (MvPolynomial.support_add hb) with hb | hb
    · exact ihF b hb
    · exact ihG b hb
  | smul a F hF ih =>
    change ∀ b ∈ (SchmidtTaylorCorrespondence6.translate6 (rootPoint4 M) (a*F)).support, _
    rw [map_mul]
    intro b hb
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hb)
    rw [← he,JSP000334.rothTaylorWeight_add]
    exact (ih v hv).trans (le_add_of_nonneg_left (SchmidtTaylorCorrespondence6.weight_nonneg6 r u))

theorem monicIdeal4_iff_support {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ) :
    H ∈ monicIdeal4 M r c ↔
      ∀ b ∈ (SchmidtTaylorCorrespondence6.translate6 (rootPoint4 M) H).support, c ≤ JSP000334.rothTaylorWeight r b := by
  refine ⟨monicIdeal4_support M r c H,?_⟩
  intro h
  have hs := congrArg (SchmidtTaylorCorrespondence6.translate6 (fun h => -rootPoint4 M h)) (SchmidtTaylorCorrespondence6.translate6 (rootPoint4 M) H).as_sum
  rw [SchmidtTaylorCorrespondence6.translate6_inverse,map_sum] at hs
  rw [hs]
  apply Ideal.sum_mem
  intro b hb
  rw [SchmidtTaylorCorrespondence6.translate6_monomial_inverse]
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  refine ⟨fun h => b h,?_,rfl⟩
  exact h b hb

theorem monicIdeal4_iff_coeff {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ) :
    H ∈ monicIdeal4 M r c ↔
      ∀ b, JSP000334.rothTaylorWeight r b < c → (SchmidtTaylorCorrespondence6.translate6 (rootPoint4 M) H).coeff b = 0 := by
  rw [monicIdeal4_iff_support]
  constructor
  · intro h b hb
    by_contra hn
    exact (not_le.mpr hb) (h b (MvPolynomial.mem_support_iff.mpr hn))
  · intro h b hb
    by_contra! hn
    exact (MvPolynomial.mem_support_iff.mp hb) (h b hn)

theorem monicIdeal4_iff_divided {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (z : Fin m → ℚ) (hz : ∀ h, rootPoint4 M h = (z h : ℝ))
    (c : ℝ) (G : MvPolynomial (Fin m) ℤ) :
    G.map (Int.castRingHom ℝ) ∈ monicIdeal4 M r c ↔
      ∀ J, JSP000334.rothTaylorWeight r J < c →
        MvPolynomial.eval₂ (Int.castRingHom ℚ) z (JSP000334.rothIntegerDividedDerivative J G) = 0 := by
  rw [monicIdeal4_iff_coeff]
  have he : rootPoint4 M = fun h => (z h : ℝ) := funext hz
  simp only [he,SchmidtTaylorCorrespondence6.translate6_zero_reflection]

theorem monicIdeal4_index_lower {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (r : Fin m → ℕ) (z : Fin m → ℚ) (hz : ∀ h, rootPoint4 M h = (z h : ℝ))
    (c : ℝ) (G : MvPolynomial (Fin m) ℤ)
    (hG : G.map (Int.castRingHom ℝ) ∈ monicIdeal4 M r c) :
    (c : WithTop ℝ) ≤ JSP000334.rothWeightedTaylorIndex r z (G.map (Int.castRingHom ℚ)) := by
  apply (JSP000334.rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
  intro b hb
  by_contra! hn
  have hv := (monicIdeal4_iff_divided M r z hz c G).mp hG b hn
  apply MvPolynomial.mem_support_iff.mp hb
  rw [JSP000334.rothTaylorPolynomial_coeff,JSP000334.rothIntegerDividedDerivative_eval]
  exact hv



theorem high_index_scalar_polynomial4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0) (hh : homogeneous4 r P) :
    ∃ G : MvPolynomial (Fin m) ℤ, G ≠ 0 ∧
      JSP000334.rothIntegerHeight G ≤ height4 P ∧
      (∀ h, G.degreeOf h ≤ r h) ∧
      ∀ c : ℝ, P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c →
        G.map (Int.castRingHom ℝ) ∈ monicIdeal4 M r c := by
  let F := reducedPolynomial4 P
  have hFn : F ≠ 0 := reducedPolynomial4_nonzero P hn
  have hFh := (reducedPolynomial4_homogeneous P r hh hn).1
  have hFb := reducedPolynomial4_support P
  refine ⟨scalar4 F,scalar4_nonzero _ F hFh hFb hFn,?_,?_,?_⟩
  · rw [scalar4_height _ F hFh hFb]
    exact reducedPolynomial4_height P
  · intro h
    exact (scalar4_degree _ F hFh hFb h).trans
      ((reducedPolynomial4_homogeneous P r hh hn).2 h)
  · intro c hc
    rw [← scalarIdeal4_eq_monic M hM r c]
    exact scalar4_closed M r c F (reducedPolynomial4_closed M hM r c P hn hc)

theorem high_index_scalar_contradiction4 (m : ℕ) (hm : 0 < m)
    (M : Fin m → Fin 4 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (theta C c : ℝ) (ht : 0 < theta) (ht1 : theta < 1/12)
    (hC : 0 < C) (hC1 : C ≤ 1) (hc : theta < c)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(r h : ℝ))
    (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0) (hh : homogeneous4 r P)
    (hindex : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c)
    (hgrowth : ∀ h : Fin m,
      |(rootDenominator6 (M ⟨0,hm⟩ 0) (M ⟨0,hm⟩ 1) : ℝ)|^((r ⟨0,hm⟩ : ℝ)*C) ≤
        |(rootDenominator6 (M h 0) (M h 1) : ℝ)|^(r h))
    (hden : ∀ h, (2 : ℝ)^(3*m) ≤
      |(rootDenominator6 (M h 0) (M h 1) : ℝ)|^(JSP000334.omega65 m theta*C))
    (hheight : (height4 P : ℝ) ≤
      |(rootDenominator6 (M ⟨0,hm⟩ 0) (M ⟨0,hm⟩ 1) : ℝ)|^
        (JSP000334.omega65 m theta*(r ⟨0,hm⟩ : ℝ)*C)) : False := by
  obtain ⟨G,hGn,hGH,hdeg,htransfer⟩ := high_index_scalar_polynomial4 M hM r P hn hh
  let p : Fin m → ℤ := fun h => rootNumerator6 (M h 0) (M h 1)
  let q : Fin m → ℤ := fun h => rootDenominator6 (M h 0) (M h 1)
  have hq (h) : q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1 := by
    obtain ⟨_,_,_,_,_,hq,hcop⟩ := integer_normalization6 (M h 0) (M h 1) (hM h)
    exact ⟨hq,hcop⟩
  have hheightG : (JSP000334.rothIntegerHeight G : ℝ) ≤
      |(q ⟨0,hm⟩ : ℝ)|^(JSP000334.omega65 m theta*(r ⟨0,hm⟩ : ℝ)*C) :=
    (by exact_mod_cast hGH : (JSP000334.rothIntegerHeight G : ℝ) ≤ (height4 P : ℝ)).trans hheight
  obtain ⟨J,hJ,hne⟩ := JSP000334.SchmidtHilfssatz12.hilfssatz12_nonvanishing
    m hm theta C ht ht1 hC hC1 r p q G hr hsep hq hgrowth hden hGn
      (fun b hb h => (MvPolynomial.monomial_le_degreeOf h hb).trans (hdeg h)) hheightG
  have hz : ∀ h, rootPoint4 M h = (((p h : ℚ)/(q h : ℚ) : ℚ) : ℝ) := by
    intro h
    simp only [rootPoint4,p,q,Rat.cast_div,Rat.cast_intCast]
  exact hne ((monicIdeal4_iff_divided M r (fun h => (p h : ℚ)/(q h : ℚ)) hz c G).mp
    (htransfer c hindex) J (hJ.trans_lt hc))

end CompoundFeasibility.SchmidtScalarReduction4Literal178

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtNormalCoordinates4Literal178
open SourceMultiblock4 SourceNormalIndex4 Auxiliary4 SchmidtScalarReduction4Literal178
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


end CompoundFeasibility.SchmidtNormalCoordinates4Literal178

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedDual4Literal178
open OriginalSelectedSystem4 OriginalLastDual4 OriginalAuxiliaryDual4 SourceNormalIndex4

def dualValue4 {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (M : Fin 4 → ℤ) (i : Fin 4) : K :=
  (B⁻¹.transpose *ᵥ (fun k => (M k : K))) i

def mixedProduct4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 4 → ℤ) (s : MixedIndex4) : ℝ :=
  ‖dualValue4 L M (s 0)‖ *
    ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) M (s 1)‖ *
    ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) M (s 2)‖

def mixedNonzero4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 4 → ℤ) (s : MixedIndex4) : Prop :=
  dualValue4 L M (s 0) ≠ 0 ∧
    dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) M (s 1) ≠ 0 ∧
    dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) M (s 2) ≠ 0

theorem mixedProduct4_nonzero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 4 → ℤ) (s : MixedIndex4) :
    mixedProduct4 A2 A3 L M s ≠ 0 ↔ mixedNonzero4 A2 A3 L M s := by
  simp [mixedProduct4,mixedNonzero4,mul_ne_zero_iff,and_assoc]

theorem dualValue4_scaling {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (z M : Fin 4 → ℤ) (g : ℤ)
    (h : ∀ i, z i = g*M i) (i : Fin 4) :
    dualValue4 B z i = (g : K)*dualValue4 B M i := by
  simp only [dualValue4,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [h k,Int.cast_mul]
  ring

theorem dualValue4_scaling_zero {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (z M : Fin 4 → ℤ) (g : ℤ)
    (hg : g ≠ 0) (h : ∀ i, z i = g*M i) (i : Fin 4) :
    dualValue4 B z i = 0 ↔ dualValue4 B M i = 0 := by
  rw [dualValue4_scaling B z M g h i]
  exact mul_eq_zero_iff_left (show (g : K) ≠ 0 by exact_mod_cast hg)

def lastDualValue4 {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (i : Fin 4) : K :=
  ∑ k, B⁻¹ k i * (lastDual4 (fun j i => (v j i : ℚ)) hv k : K)

def lastDualProduct4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (s : MixedIndex4) : ℝ :=
  ‖lastDualValue4 L v hv (s 0)‖ *
    ‖lastDualValue4 (A2.map (algebraMap ℚ ℚ_[2])) v hv (s 1)‖ *
    ‖lastDualValue4 (A3.map (algebraMap ℚ ℚ_[3])) v hv (s 2)‖

theorem primitive_lastDualValue4_zero {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (h : ∀ i, integerLastDual4 v i = g*M i) (i : Fin 4) :
    dualValue4 B M i = 0 ↔ lastDualValue4 B v hv i = 0 := by
  rw [← dualValue4_scaling_zero B (integerLastDual4 v) M g hg h i]
  change (B⁻¹.transpose *ᵥ (fun k => (integerLastDual4 v k : K))) i = 0 ↔ _
  rw [cofactor_dual_coordinates4 B v hv i]
  exact mul_eq_zero_iff_left (show ((Matrix.det v : ℤ) : K) ≠ 0 by exact_mod_cast integerFrame4_det_ne_zero v hv)

theorem primitive_lastDualProduct4_zero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (h : ∀ i, integerLastDual4 v i = g*M i) (s : MixedIndex4) :
    mixedProduct4 A2 A3 L M s = 0 ↔ lastDualProduct4 A2 A3 L v hv s = 0 := by
  simp only [mixedProduct4,lastDualProduct4,mul_eq_zero,norm_eq_zero,
    primitive_lastDualValue4_zero _ v hv M g hg h]

def nonzeroBranch4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (s : MixedIndex4) : Set ℝ :=
  {q | ∃ hq : q ∈ W, mixedNonzero4 A2 A3 L (M ⟨q,hq⟩) s}

theorem nonzeroBranch4_subset (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (s : MixedIndex4) : nonzeroBranch4 A2 A3 L W M s ⊆ W := fun _ h => h.choose

theorem mem_nonzeroBranch4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (s : MixedIndex4) (q : W) :
    q.val ∈ nonzeroBranch4 A2 A3 L W M s ↔ mixedNonzero4 A2 A3 L (M q) s := by
  constructor
  · rintro ⟨hq,h⟩
    exact h
  · intro h
    exact ⟨q.property,h⟩

theorem failure_eventual_zero_branch4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (S : Finset MixedIndex4)
    (hfail : ¬ ∃ T : ℝ, ∀ q : W, T < q.val → ∀ s ∈ S,
      mixedProduct4 A2 A3 L (M q) s = 0) :
    ∃ s ∈ S, ¬ BddAbove (nonzeroBranch4 A2 A3 L W M s) := by
  by_contra! hb
  have hu : BddAbove (⋃ s ∈ S, nonzeroBranch4 A2 A3 L W M s) :=
    S.finite_toSet.bddAbove_biUnion.mpr hb
  obtain ⟨T,hT⟩ := hu
  apply hfail
  refine ⟨T,?_⟩
  intro q hq s hs
  by_contra hn
  have hmem := (mem_nonzeroBranch4 A2 A3 L W M s q).mpr
    ((mixedProduct4_nonzero A2 A3 L (M q) s).mp hn)
  exact (not_le_of_gt hq) (hT (Set.mem_iUnion₂.mpr ⟨s,hs,hmem⟩))


theorem same_frame_primitive_normals4 {W : Set ℝ}
    (v : W → Fin 4 → Fin 4 → ℤ)
    (hv : ∀ q, LinearIndependent ℝ (fun j => integerReal (v q j))) :
    ∃ (g : W → ℤ) (M a : W → Fin 4 → ℤ), ∀ q,
      g q ≠ 0 ∧ M q ≠ 0 ∧
      (∀ i, integerLastDual4 (v q) i = g q*M q i) ∧
      (∑ i, a q i*M q i) = 1 ∧ Ideal.span (Set.range (M q)) = ⊤ ∧
      (∀ j : Fin 3, (∑ i, M q i*v q j.castSucc i) = 0) ∧
      LinearMap.ker (normalForm4 (M q)) =
        Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (v q j.castSucc i : ℚ))) ∧
      LinearMap.ker (realNormalForm4 (M q)) =
        Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (v q j.castSucc))) ∧
      0 < SchmidtNormalCoordinates4Literal178.normalHeight4 (M q) := by
  have hp (q : W) := primitive_cofactor_normal4 (v q) (hv q)
  choose g M a h using hp
  refine ⟨g,M,a,?_⟩
  intro q
  exact ⟨(h q).1,(h q).2.1,(h q).2.2.1,(h q).2.2.2.1,
    (h q).2.2.2.2.1,(h q).2.2.2.2.2.1,(h q).2.2.2.2.2.2.1,
    (h q).2.2.2.2.2.2.2,
    SchmidtNormalCoordinates4Literal178.normalHeight4_pos (M q) (h q).2.1⟩

theorem same_frame_high_index_transfer4 {m : ℕ}
    (M N : Fin m → Fin 4 → ℤ) (hN : ∀ h, N h ≠ 0)
    (hker : ∀ h, LinearMap.ker (realNormalForm4 (M h)) =
      LinearMap.ker (realNormalForm4 (N h)))
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock4.Vars4 m) ℤ)
    (hrestr : ∀ J : SourceMultiblock4.Vars4 m →₀ ℕ,
      Auxiliary4.rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2)
          (SourceMultiblock4.derivative4 J (P.map (Int.castRingHom ℝ))) = 0) :
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 N r c := by
  apply sourceNormalIdeal4_of_derivative_restrictions N hN r c
  intro J hJ y hy
  exact hrestr J hJ y (fun h => (hker h).symm ▸ hy h)

end CompoundFeasibility.SourceSelectedDual4Literal178

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalHeight4Literal178
open SourceSelectedDual4Literal178 SchmidtNormalCoordinates4Literal178 OriginalSelectedInputs4

theorem normal_pi_norm_le_height4 (M : Fin 4 → ℤ) :
    ‖(fun i => (M i : ℝ))‖ ≤ (normalHeight4 M : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using normalHeight4_coord M i

theorem real_dual_lower4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (M : Fin 4 → ℤ) i,
      dualValue4 L M i ≠ 0 →
      C ≤ ‖dualValue4 L M i‖*(max 1 (normalHeight4 M : ℝ))^D := by
  obtain ⟨C,hC,D,h⟩ := fixed_dual_liouville4 L hL hAlg
  refine ⟨C,hC,D,?_⟩
  intro M i hn
  have hl := h i M hn
  rw [← Real.norm_eq_abs] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (le_trans zero_le_one (le_max_left _ _))
    (max_le_max_left 1 (normal_pi_norm_le_height4 M)) D) (norm_nonneg _))

def finiteValue4 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 4) (Fin 4) ℚ) (M : Fin 4 → ℤ) (i : Fin 4) : ℚ_[p] :=
  ∑ k, (B i k : ℚ_[p])*(M k : ℚ_[p])

theorem fixed_rational_denominator4 (B : Matrix (Fin 4) (Fin 4) ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ N : Matrix (Fin 4) (Fin 4) ℤ,
      ∀ i j, (N i j : ℚ) = (d : ℚ)*B i j := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun ij : Fin 4 × Fin 4 => B ij.1 ij.2)
  choose N hN using hd
  refine ⟨d.val,mem_nonZeroDivisors_iff_ne_zero.mp d.property,fun i j => N (i,j),?_⟩
  intro i j
  simpa only [Algebra.smul_def,eq_intCast] using hN (i,j)

theorem finite_denominator_identity4 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 4) (Fin 4) ℚ) (d : ℤ) (hd : d ≠ 0)
    (N : Matrix (Fin 4) (Fin 4) ℤ)
    (hN : ∀ i j, (N i j : ℚ) = (d : ℚ)*B i j)
    (M : Fin 4 → ℤ) (s : Fin 4) :
    finiteValue4 p B M s = ((∑ i, M i*N s i : ℤ) : ℚ_[p])/(d : ℚ_[p]) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hr : (∑ i, B s i*(M i : ℚ)) = ((∑ i, M i*N s i : ℤ) : ℚ)/(d : ℚ) := by
    apply (eq_div_iff hdQ).mpr
    simp only [Int.cast_sum,Int.cast_mul,Finset.sum_mul,hN]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = algebraMap ℚ ℚ_[p] (∑ i, B s i*(M i : ℚ)) := by
      simp [finiteValue4]
    _ = _ := by rw [hr,map_div₀,map_intCast,map_intCast]

theorem integer_numerator_height4 (N : Matrix (Fin 4) (Fin 4) ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 4 → ℤ) s,
      |((∑ i, M i*N s i : ℤ) : ℝ)| ≤ C*max 1 (normalHeight4 M : ℝ) := by
  let C : ℝ := 1+∑ s, ∑ i, |(N s i : ℝ)|
  have hsum : 0 ≤ ∑ s, ∑ i, |(N s i : ℝ)| :=
    Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro M s
  have hrow : (∑ i, |(N s i : ℝ)|) ≤ C := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun s : Fin 4 => ∑ i, |(N s i : ℝ)|)
      (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  calc
    _ = ‖∑ i, (M i : ℝ)*(N s i : ℝ)‖ := by simp only [Int.cast_sum,Int.cast_mul,Real.norm_eq_abs]
    _ ≤ ∑ i, |(M i : ℝ)| *|(N s i : ℝ)| := by
      simpa only [norm_mul,Real.norm_eq_abs] using
        norm_sum_le (s := Finset.univ) (f := fun i => (M i : ℝ)*(N s i : ℝ))
    _ ≤ ∑ i, max 1 (normalHeight4 M : ℝ)*|(N s i : ℝ)| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        ((normalHeight4_coord M i).trans (le_max_right _ _)) (abs_nonneg _)
    _ = (∑ i, |(N s i : ℝ)|)*max 1 (normalHeight4 M : ℝ) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow (zero_le_one.trans (le_max_left _ _))

theorem finite_form_lower4 (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : Fin 4 → ℤ) s,
      finiteValue4 p A M s ≠ 0 →
      c ≤ ‖finiteValue4 p A M s‖*max 1 (normalHeight4 M : ℝ) ∧
      c/max 1 (normalHeight4 M : ℝ) ≤ ‖finiteValue4 p A M s‖ := by
  obtain ⟨d,hd,N,hN⟩ := fixed_rational_denominator4 A
  obtain ⟨C,hC,hheight⟩ := integer_numerator_height4 N
  have hdp : (d : ℚ_[p]) ≠ 0 := by exact_mod_cast hd
  have hdn : 0 < ‖(d : ℚ_[p])‖ := norm_pos_iff.mpr hdp
  have hden : 0 < C*‖(d : ℚ_[p])‖ := mul_pos hC hdn
  refine ⟨1/(C*‖(d : ℚ_[p])‖),one_div_pos.mpr hden,?_⟩
  intro M s hne
  let z : ℤ := ∑ i, M i*N s i
  have hz : z ≠ 0 := by
    intro hz
    apply hne
    rw [finite_denominator_identity4 p A d hd N hN M s]
    change (z : ℚ_[p])/(d : ℚ_[p]) = 0
    rw [hz,Int.cast_zero,zero_div]
  have ha : 0 < |(z : ℝ)| := abs_pos.mpr (by exact_mod_cast hz)
  have hzlower : 1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := by
    rcases hp with rfl | rfl
    · exact (div_le_iff₀ ha).mp (SourceFieldLower6.integer_padic2_lower6 z hz) |>.trans_eq (mul_comm _ _)
    · exact (div_le_iff₀ ha).mp (SourceFieldLower6.integer_padic3_lower6 z hz) |>.trans_eq (mul_comm _ _)
  have hnorm : ‖(z : ℚ_[p])‖ = ‖finiteValue4 p A M s‖*‖(d : ℚ_[p])‖ := by
    rw [finite_denominator_identity4 p A d hd N hN M s,norm_div,div_mul_cancel₀ _ hdn.ne']
  have htotal : 1 ≤ (C*‖(d : ℚ_[p])‖)*
      (‖finiteValue4 p A M s‖*max 1 (normalHeight4 M : ℝ)) := by
    calc
      1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := hzlower
      _ ≤ (C*max 1 (normalHeight4 M : ℝ))*‖(z : ℚ_[p])‖ :=
        mul_le_mul_of_nonneg_right (hheight M s) (norm_nonneg _)
      _ = _ := by rw [hnorm]; ring
  have hl : 1/(C*‖(d : ℚ_[p])‖) ≤
      ‖finiteValue4 p A M s‖*max 1 (normalHeight4 M : ℝ) :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)
  exact ⟨hl,(div_le_iff₀ (zero_lt_one.trans_le (le_max_left _ _))).mpr hl⟩




theorem finite_dualValue4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (M : Fin 4 → ℤ) (s : Fin 4) :
    dualValue4 (A.map (algebraMap ℚ ℚ_[p])) M s = finiteValue4 p A⁻¹.transpose M s := by
  have hd : A.det ≠ 0 := by rw [hA]; exact one_ne_zero
  have hi := (Auxiliary6.SourceBalance.mapped_inverse (algebraMap ℚ ℚ_[p]) A hd).1
  have he : (A.map (algebraMap ℚ ℚ_[p]))⁻¹ = A⁻¹.map (algebraMap ℚ ℚ_[p]) :=
    Matrix.inv_eq_left_inv hi
  simp [dualValue4,finiteValue4,he,Matrix.mulVec,dotProduct]

theorem finite_dual_lower4 (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 4 → ℤ) s,
      dualValue4 (A.map (algebraMap ℚ ℚ_[p])) M s ≠ 0 →
      C ≤ ‖dualValue4 (A.map (algebraMap ℚ ℚ_[p])) M s‖*max 1 (normalHeight4 M : ℝ) := by
  obtain ⟨C,hC,h⟩ := finite_form_lower4 p hp A⁻¹.transpose
  refine ⟨C,hC,?_⟩
  intro M s hn
  rw [finite_dualValue4 p A hA M s] at hn ⊢
  exact (h M s hn).1

theorem mixed_dual_lower4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (M : Fin 4 → ℤ) (s : OriginalSelectedSystem4.MixedIndex4),
      mixedNonzero4 A2 A3 L M s →
      C ≤ mixedProduct4 A2 A3 L M s*(max 1 (normalHeight4 M : ℝ))^(D+2) := by
  obtain ⟨C0,hC0,D,h0⟩ := real_dual_lower4 L hL hAlg
  obtain ⟨C2,hC2,hp2⟩ := finite_dual_lower4 2 (Or.inl rfl) A2 h2
  obtain ⟨C3,hC3,hp3⟩ := finite_dual_lower4 3 (Or.inr rfl) A3 h3
  refine ⟨C0*C2*C3,mul_pos (mul_pos hC0 hC2) hC3,D,?_⟩
  intro M s hn
  let H : ℝ := max 1 (normalHeight4 M : ℝ)
  have hH : 0 ≤ H := zero_le_one.trans (le_max_left _ _)
  have hr := h0 M (s 0) hn.1
  have h2' := hp2 M (s 1) hn.2.1
  have h3' := hp3 M (s 2) hn.2.2
  calc
    _ ≤ (‖dualValue4 L M (s 0)‖*H^D)*
        (‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) M (s 1)‖*H)*
        (‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) M (s 2)‖*H) :=
      mul_le_mul (mul_le_mul hr h2' hC2.le
        (mul_nonneg (norm_nonneg _) (pow_nonneg hH _))) h3' hC3.le
        (mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hH _))
          (mul_nonneg (norm_nonneg _) hH))
    _ = _ := by rw [pow_add,pow_two]; unfold mixedProduct4; ring


open SourceSelectedDual4Literal178 SchmidtNormalCoordinates4Literal178 OriginalSelectedSystem4
open OriginalAuxiliaryDual4 OriginalLastDual4 OriginalDeformedSource4 OriginalDeformation4

theorem primitive_mixed_le_cofactor4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Fin 4 → Fin 4 → ℤ) (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hs : ∀ i, integerLastDual4 v i = g*M i) (s : MixedIndex4) :
    mixedProduct4 A2 A3 L M s ≤ mixedProduct4 A2 A3 L (integerLastDual4 v) s := by
  have hP : 0 ≤ mixedProduct4 A2 A3 L M s := by
    unfold mixedProduct4
    positivity
  calc
    _ = 1*mixedProduct4 A2 A3 L M s := by ring
    _ ≤ (‖(g : ℝ)‖*‖(g : ℚ_[2])‖*‖(g : ℚ_[3])‖)*mixedProduct4 A2 A3 L M s :=
      mul_le_mul_of_nonneg_right (SourceLocalUpper6.integer_g_three_place6 g hg) hP
    _ = _ := by
      simp only [mixedProduct4,dualValue4_scaling _ _ _ g hs,norm_mul]
      ring

theorem padic_cofactor_bound4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (v : Fin 4 → Fin 4 → ℤ) (b : Fin 4 → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hv : ∀ (j : Fin 3) i,
      ‖(A.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun k => (v j.castSucc k : ℚ_[p]))) i‖ ≤ b i)
    (i : Fin 4) :
    ‖dualValue4 (A.map (algebraMap ℚ ℚ_[p])) (integerLastDual4 v) i‖ ≤
      ∏ k : Fin 3, b (i.succAbove k) := by
  rw [dualValue4,cofactor_minor_norm4 _ (mapped_det_one4 A hA)]
  apply padic_det3_bound4 p _ _ (fun k => hb _) (fun j k => ?_)
  simpa [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using
    hv j (i.succAbove k)

theorem mixed_cofactor_decay4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (v : Fin 4 → Fin 4 → ℤ) (Q d : ℝ) (hQ : 0 < Q)
    (A b2 b3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hb2 : ∀ i, 0 < b2 i) (hb3 : ∀ i, 0 < b3 i)
    (hbal : (∏ i, A i)*(∏ i, b2 i)*(∏ i, b3 i) = 1)
    (hr : ∀ (j : Fin 3) i, |(L *ᵥ (fun k => (v j.castSucc k : ℝ))) i| ≤ Q^(-d)*A i)
    (hp2 : ∀ (j : Fin 3) i,
      ‖(A2.map (algebraMap ℚ ℚ_[2]) *ᵥ (fun k => (v j.castSucc k : ℚ_[2]))) i‖ ≤ b2 i)
    (hp3 : ∀ (j : Fin 3) i,
      ‖(A3.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun k => (v j.castSucc k : ℚ_[3]))) i‖ ≤ b3 i)
    (s : MixedIndex4) (hs : 1 ≤ A (s 0)*b2 (s 1)*b3 (s 2)*Q^(d/2)) :
    mixedProduct4 A2 A3 L (integerLastDual4 v) s ≤ 6*Q^(-5*d/2) := by
  let R := ∏ k : Fin 3, A ((s 0).succAbove k)
  let B2 := ∏ k : Fin 3, b2 ((s 1).succAbove k)
  let B3 := ∏ k : Fin 3, b3 ((s 2).succAbove k)
  let D := A (s 0)*b2 (s 1)*b3 (s 2)
  let P := mixedProduct4 A2 A3 L (integerLastDual4 v) s
  have hn : 0 ≤ P := by dsimp [P,mixedProduct4]; positivity
  have hcancel : R*B2*B3*D = 1 := by
    have ha := Fin.prod_univ_succAbove A (s 0)
    have h2' := Fin.prod_univ_succAbove b2 (s 1)
    have h3' := Fin.prod_univ_succAbove b3 (s 2)
    rw [ha,h2',h3'] at hbal
    dsimp [R,B2,B3,D]
    nlinarith only [hbal]
  have hr' := real_cofactor_bound4 L hL v (fun _ : Fin 3 => Q^(-d)) A hr (s 0)
  have h2' := padic_cofactor_bound4 2 A2 h2 v b2 (fun i => (hb2 i).le) hp2 (s 1)
  have h3' := padic_cofactor_bound4 3 A3 h3 v b3 (fun i => (hb3 i).le) hp3 (s 2)
  have hR : 0 ≤ R := Finset.prod_nonneg (fun k _ => (hA _).le)
  have hB2 : 0 ≤ B2 := Finset.prod_nonneg (fun k _ => (hb2 _).le)
  have hB3 : 0 ≤ B3 := Finset.prod_nonneg (fun k _ => (hb3 _).le)
  have hbound : P ≤ (6*(Q^(-d))^3*R)*B2*B3 := by
    dsimp only [P,mixedProduct4,R,B2,B3]
    apply mul_le_mul (mul_le_mul (by simpa using hr') h2' (norm_nonneg _) (by dsimp only [R] at hR; positivity))
      h3' (norm_nonneg _) (by dsimp only [R,B2] at hR hB2; positivity)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (hA _).le (hb2 _).le) (hb3 _).le
  have hPD : P*D ≤ 6*Q^(-3*d) := by
    calc
      _ ≤ ((6*(Q^(-d))^3*R)*B2*B3)*D := mul_le_mul_of_nonneg_right hbound hD
      _ = 6*(Q^(-d))^3*(R*B2*B3*D) := by ring
      _ = 6*Q^(-3*d) := by
        rw [hcancel,mul_one,← Real.rpow_natCast,← Real.rpow_mul hQ.le]
        congr 2
        ring
  calc
    P ≤ P*(D*Q^(d/2)) := by simpa using mul_le_mul_of_nonneg_left hs hn
    _ = (P*D)*Q^(d/2) := by ring
    _ ≤ (6*Q^(-3*d))*Q^(d/2) := mul_le_mul_of_nonneg_right hPD (by positivity)
    _ = 6*Q^(-5*d/2) := by rw [mul_assoc,← Real.rpow_add hQ]; congr 2; ring


theorem rescaled_balance4 (Q : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 4 → ℝ)
    (hbal : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (∏ i, A i)*(∏ i, (Q^(5 : ℕ))^(c2 i/5))*(∏ i, (Q^(5 : ℕ))^(c3 i/5)) = 1 := by
  rw [mul_assoc,← Finset.prod_mul_distrib]
  convert hbal using 2
  apply Finset.prod_congr rfl
  intro i _
  rw [rescaled_power4 Q _ (zero_lt_one.trans hQ),rescaled_power4 Q _ (zero_lt_one.trans hQ),
    ← Real.rpow_add (zero_lt_one.trans hQ)]

theorem source_selected_mixed_decay4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hscale : ∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i)
    (s : MixedIndex4)
    (hs : s ∈ publishedIndexSet4 (Q^(5 : ℕ)) (delta/24)
      (deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma)
      (fun i => c2 i/5) (fun i => c3 i/5)) :
    mixedProduct4 A2 A3 L M s ≤ 6*(Q^(5 : ℕ))^(-5*(delta/24)/2) := by
  let A := deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma
  let b2 : Fin 4 → ℝ := fun i => (Q^(5 : ℕ))^(c2 i/5)
  let b3 : Fin 4 → ℝ := fun i => (Q^(5 : ℕ))^(c3 i/5)
  have hbal := rescaled_balance4 Q hQ A c2 c3 F.balance
  let v : Fin 4 → Fin 4 → ℤ := fun j => (F.w j : Fin 4 → ℤ)
  have hp2 : ∀ (j : Fin 3) i,
      ‖(A2.map (algebraMap ℚ ℚ_[2]) *ᵥ (fun k => (v j.castSucc k : ℚ_[2]))) i‖ ≤ b2 i := by
    intro j i
    exact (SourceWeights4.finite_form_bounds A2 A3 Q hQ c2 c3 hc2 hc3 (F.w j.castSucc)).1 i
  have hp3 : ∀ (j : Fin 3) i,
      ‖(A3.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun k => (v j.castSucc k : ℚ_[3]))) i‖ ≤ b3 i := by
    intro j i
    exact (SourceWeights4.finite_form_bounds A2 A3 Q hQ c2 c3 hc2 hc3 (F.w j.castSucc)).2 i
  have hr : ∀ (j : Fin 3) i, |(L *ᵥ (fun k => (v j.castSucc k : ℝ))) i| ≤
      (Q^(5 : ℕ))^(-(delta/24))*A i := fun j i => attaining_first_three4 F j i
  have hs' : 1 ≤ A (s 0)*b2 (s 1)*b3 (s 2)*(Q^(5 : ℕ))^((delta/24)/2) :=
    (Finset.mem_filter.mp hs).2
  have hcof := mixed_cofactor_decay4 A2 A3 L h2 h3 hLdet v (Q^(5 : ℕ)) (delta/24)
    (pow_pos (zero_lt_one.trans hQ) _) A b2 b3 F.widths_pos
    (fun i => Real.rpow_pos_of_pos (pow_pos (zero_lt_one.trans hQ) _) _)
    (fun i => Real.rpow_pos_of_pos (pow_pos (zero_lt_one.trans hQ) _) _) hbal hr hp2 hp3 s hs'
  exact (primitive_mixed_le_cofactor4 A2 A3 L v M g hg hscale s).trans hcof


def inverseConstant4 (B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  1+∑ i, ∑ k, |B⁻¹ i k|

theorem inverseConstant4_pos (B : Matrix (Fin 4) (Fin 4) ℝ) : 0 < inverseConstant4 B := by
  have h : 0 ≤ ∑ i, ∑ k, |B⁻¹ i k| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
  unfold inverseConstant4
  linarith

theorem inverse_coordinate4 (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : IsUnit B)
    (x : Fin 4 → ℝ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hx : ∀ k, ‖(B *ᵥ x) k‖ ≤ Q) (i : Fin 4) :
    |x i| ≤ inverseConstant4 B*Q := by
  have hid : B⁻¹ *ᵥ (B *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB),Matrix.one_mulVec]
  have hrow : (∑ k, |B⁻¹ i k|) ≤ inverseConstant4 B := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 4 => ∑ k, |B⁻¹ i k|)
      (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ i)
    unfold inverseConstant4
    linarith
  calc
    |x i| = ‖∑ k, B⁻¹ i k*(B *ᵥ x) k‖ := by
      change |x i| = ‖(B⁻¹ *ᵥ (B *ᵥ x)) i‖
      rw [hid,Real.norm_eq_abs]
    _ ≤ ∑ k, ‖B⁻¹ i k*(B *ᵥ x) k‖ := norm_sum_le _ _
    _ ≤ ∑ k, |B⁻¹ i k| *Q := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
    _ = (∑ k, |B⁻¹ i k|)*Q := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hQ

theorem normalHeight4_real_le (M : Fin 4 → ℤ) (B : ℝ)
    (h : ∀ i, |(M i : ℝ)| ≤ B) : (normalHeight4 M : ℝ) ≤ B := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4))
    Finset.univ_nonempty (fun i => (M i).natAbs)
  change ((Finset.univ.sup (fun i => (M i).natAbs) : ℕ) : ℝ) ≤ B
  rw [hi]
  have he : ((M i).natAbs : ℝ) = |(M i : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [he]
  exact h i


theorem cofactor_coordinate_upper4 (v : Fin 4 → Fin 4 → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ (j : Fin 3) i, |(v j.castSucc i : ℝ)| ≤ B) (i : Fin 4) :
    |(integerLastDual4 v i : ℝ)| ≤ 6*B^3 := by
  have h := real_cofactor_bound4 (1 : Matrix (Fin 4) (Fin 4) ℝ) (by simp) v
    (fun _ : Fin 3 => B) (fun _ : Fin 4 => 1) (fun j k => by simpa using hv j k) i
  simpa using h

theorem source_normal_height_upper4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (hd : 0 < delta)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hscale : ∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i) :
    (normalHeight4 M : ℝ) ≤ (6*(inverseConstant4 L)^3)*(Q^(5 : ℕ))^3 := by
  let V := Q^(5 : ℕ)
  have hV : 1 < V := one_lt_pow₀ hQ (by decide)
  have hsmall : V^(-(delta/24)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hV.le (by linarith)
  have hform (j : Fin 3) (i : Fin 4) :
      ‖(L *ᵥ integerReal (F.w j.castSucc : Fin 4 → ℤ)) i‖ ≤ V := by
    rw [Real.norm_eq_abs]
    exact (attaining_first_three4 F j i).trans
      ((mul_le_mul_of_nonneg_right hsmall (F.widths_pos i).le).trans
        (by simpa using (F.sizes i).1.le))
  have hcoord (j : Fin 3) (i : Fin 4) :
      |((F.w j.castSucc : Fin 4 → ℤ) i : ℝ)| ≤ inverseConstant4 L*V :=
    inverse_coordinate4 L hL _ V (zero_lt_one.trans hV).le (hform j) i
  have hMbound := normalHeight4_normalization_bound _ M g hg hscale
  have hcof : (normalHeight4 (integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ))) : ℝ) ≤
      6*(inverseConstant4 L*V)^3 :=
    normalHeight4_real_le _ _ (cofactor_coordinate_upper4 _ _
      (mul_nonneg (inverseConstant4_pos L).le (zero_lt_one.trans hV).le) hcoord)
  calc
    _ ≤ (normalHeight4 (integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ))) : ℝ) := by exact_mod_cast hMbound
    _ ≤ 6*(inverseConstant4 L*V)^3 := hcof
    _ = _ := by dsimp [V]; ring

theorem source_normal_height_upper_envelope4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (hd : 0 < delta)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hscale : ∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i)
    (hcut : 6*(inverseConstant4 L)^3 ≤ Q^(5 : ℕ)) :
    max 1 (normalHeight4 M : ℝ) ≤ (Q^(5 : ℕ))^(4 : ℝ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl,Real.rpow_natCast]
  apply max_le
  · exact one_le_pow₀ (one_lt_pow₀ hQ (by decide)).le
  · exact (source_normal_height_upper4 hd F M g hg hscale).trans
      ((mul_le_mul_of_nonneg_right hcut (by positivity)).trans_eq (by ring))
theorem combined_product4 (C Q eps H P : ℝ) (n : ℕ)
    (hQ : 0 < Q) (hH : 0 ≤ H)
    (hl : C ≤ P*H^n) (hu : P ≤ 6*Q^(-eps)) :
    (C/6)*Q^eps ≤ H^n := by
  have h := hl.trans (mul_le_mul_of_nonneg_right hu (pow_nonneg hH n))
  have hp : 0 < Q^eps := Real.rpow_pos_of_pos hQ _
  have he : Q^(-eps)*Q^eps = 1 := by
    rw [← Real.rpow_add hQ]
    convert Real.rpow_zero Q using 1 <;> ring
  have ht := mul_le_mul_of_nonneg_right h hp.le
  have hr : (6*Q^(-eps)*H^n)*Q^eps = 6*H^n := by
    calc
      _ = 6*H^n*(Q^(-eps)*Q^eps) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hr] at ht
  linarith

def lowerThreshold4 (C eps : ℝ) : ℝ := max 2 ((6/C)^((eps/2)⁻¹))

def heightAlpha4 (eps : ℝ) (n : ℕ) : ℝ := eps/(2*(n : ℝ))

theorem lower_absorption4 (C eps Q H : ℝ) (n : ℕ) (hn0 : 0 < n) (hC : 0 < C)
    (hd : 0 < eps) (hQ : lowerThreshold4 C eps ≤ Q) (hH : 1 ≤ H)
    (hl : (C/6)*Q^(eps) ≤ H^n) :
    Q^(heightAlpha4 eps n) ≤ H := by
  have hQ2 : 2 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := by linarith
  have he : 0 < eps/2 := by positivity
  have hc : 0 < 6/C := by positivity
  have ht : (6/C)^((eps/2)⁻¹) ≤ Q := (le_max_right _ _).trans hQ
  have hb := Real.rpow_le_rpow (Real.rpow_nonneg hc.le _) ht he.le
  rw [Real.rpow_inv_rpow hc.le he.ne'] at hb
  have hconst : 1 ≤ (C/6)*Q^(eps/2) := by
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ C/6 by positivity)
    have hh0 : (C/6)*(6/C) = 1 := by field_simp
    rwa [hh0] at hh
  have hn : 0 < (n : ℝ) := by positivity
  have hpow : (Q^(heightAlpha4 eps n))^n = Q^(eps/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ0.le]
    congr 1
    simp only [heightAlpha4,Nat.cast_add,Nat.cast_one]
    field_simp
    <;> ring
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hQ0.le _) (zero_le_one.trans hH) hn).mp
  simp only [Real.rpow_natCast]
  rw [hpow]
  calc
    Q^(eps/2) ≤ ((C/6)*Q^(eps/2))*Q^(eps/2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hQ0.le _)
    _ = (C/6)*Q^(eps) := by
      rw [mul_assoc,← Real.rpow_add hQ0]
      congr 2
      ring
    _ ≤ _ := hl



theorem selected_lower_height4 (C eps Q H P : ℝ) (n : ℕ)
    (hn : 0 < n) (hC : 0 < C) (he : 0 < eps) (hQ : lowerThreshold4 C eps ≤ Q)
    (hH : 1 ≤ H) (hl : C ≤ P*H^n) (hu : P ≤ 6*Q^(-eps)) :
    Q^(heightAlpha4 eps n) ≤ H := by
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((le_max_left _ _).trans hQ)
  exact lower_absorption4 C eps Q H n hn hC he hQ hH
    (combined_product4 C Q eps H P n hQ0 (zero_le_one.trans hH) hl hu)


theorem source_uniform_height_envelopes4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∃ T : ℝ, 1 < T ∧
      ∀ (Q : ℝ), T < Q → ∀ (hQ : 1 < Q) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
      ∀ (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3),
      ∀ F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u,
      ∀ (M : Fin 4 → ℤ) (g : ℤ), g ≠ 0 →
      (∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i) →
      ∀ s ∈ publishedIndexSet4 (Q^(5 : ℕ)) (delta/24)
        (deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma)
        (fun i => c2 i/5) (fun i => c3 i/5),
      mixedNonzero4 A2 A3 L M s →
      (Q^(5 : ℕ))^alpha ≤ max 1 (normalHeight4 M : ℝ) ∧
        max 1 (normalHeight4 M : ℝ) ≤ (Q^(5 : ℕ))^(4 : ℝ) := by
  obtain ⟨C,hC,D,hlower⟩ := mixed_dual_lower4 A2 A3 L h2 h3 hLdet hAlg
  let eps := 5*(delta/24)/2
  let alpha := heightAlpha4 eps (D+2)
  let T := max (lowerThreshold4 C eps) (6*(inverseConstant4 L)^3)
  have he : 0 < eps := by dsimp [eps]; positivity
  have ha : 0 < alpha := by dsimp [alpha,heightAlpha4]; positivity
  have hT : 1 < T := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨alpha,ha,T,hT,?_⟩
  intro Q hTQ hQ hL c0 c2 c3 hc2 hc3 u F M g hg hscale s hs hn
  have hQQ : Q ≤ Q^(5 : ℕ) := le_self_pow₀ hQ.le (by decide)
  have hcut : lowerThreshold4 C eps ≤ Q^(5 : ℕ) :=
    ((le_max_left _ _).trans hTQ.le).trans hQQ
  constructor
  · exact selected_lower_height4 C eps (Q^(5 : ℕ)) (max 1 (normalHeight4 M : ℝ))
      (mixedProduct4 A2 A3 L M s) (D+2) (by omega) hC he hcut (le_max_left _ _)
      (hlower M s hn) (by
        convert source_selected_mixed_decay4 h2 h3 hLdet hc2 hc3 F M g hg hscale s hs using 1 <;>
          dsimp [eps] <;> ring)
  · exact source_normal_height_upper_envelope4 hd F M g hg hscale
      (((le_max_right _ _).trans hTQ.le).trans hQQ)

end CompoundFeasibility.SourceNormalHeight4Literal178

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtSourceParameters4Literal178
open SourceMultiblock4 SourceNormalIndex4 Auxiliary4 SchmidtNormalCoordinates4Literal178 SchmidtScalarReduction4Literal178
theorem eta_m_theta4 (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (K : IntermediateField ℚ ℝ) :
    ∃ eta theta : ℝ, ∃ m : ℕ, eta = delta/3456 ∧ theta = eta/2 ∧
      0 < eta ∧ eta < 1 ∧ 1728*eta < delta ∧ 0 < m ∧
      4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
      0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧ 0 < JSP000334.omega65 m theta := by
  let eta := delta/3456
  let theta := eta/2
  have he : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ))))
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmn : 0 < m := by exact_mod_cast (lt_trans zero_lt_one hm1)
  have ht : 0 < theta := by dsimp [theta]; positivity
  refine ⟨eta,theta,m,rfl,rfl,he,?_,?_,hmn,
    (lt_of_le_of_lt (le_max_right _ _) hm).le,ht,?_,?_,JSP000334.omega65_pos m theta ht⟩
  · dsimp [eta]; linarith
  · dsimp [eta]; linarith
  · dsimp [theta,eta]; linarith
  · dsimp [theta]; nlinarith

theorem positive_gamma4 (alpha eta : ℝ) (ha : 0 < alpha) (he : 0 < eta) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 3 ∧ 4*gamma*(1+eta) ≤ alpha ∧ 4*gamma ≤ alpha := by
  let gamma := min 1 (alpha/(4*(1+eta)))
  have hg : 0 < gamma := lt_min zero_lt_one (div_pos ha (by positivity))
  have hc : gamma ≤ alpha/(4*(1+eta)) := min_le_right _ _
  have hb : gamma*(4*(1+eta)) ≤ alpha := (le_div_iff₀ (by positivity)).mp hc
  refine ⟨gamma,hg,(min_le_left _ _).trans (by norm_num),?_,?_⟩
  · nlinarith
  · nlinarith [mul_pos hg he]

theorem height_comparison4 (m : ℕ) (hm : 0 < m) (alpha gamma : ℝ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hcompat : 4*gamma ≤ alpha)
    (Q H : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (henv : ∀ h, Q h^alpha ≤ H h ∧ H h ≤ Q h^(4 : ℝ)) (r : Fin m → ℕ)
    (hbal : ∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h)) :
    ∀ h, H ⟨0,hm⟩^(gamma*(r ⟨0,hm⟩ : ℝ)) ≤ H h^(r h) := by
  simpa only [mul_comm] using JSP000334.parameter_roth_growth m hm alpha 4 gamma ha.le hg
    hcompat Q H hQ henv r hbal

theorem normal_budget4 (m : ℕ) (alpha omega gamma Q H : ℝ)
    (ho : 0 < omega) (hg : 0 < gamma) (hQ : 1 < Q) (henv : Q^alpha ≤ H)
    (hcut : (27*m : ℕ)*Real.log 2 ≤ alpha*omega*gamma*Real.log Q) :
    (2 : ℝ)^(27*m) ≤ H^(omega*gamma) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have hh : 0 < H := (Real.rpow_pos_of_pos hq _).trans_le henv
  apply (Real.log_le_log_iff (by positivity : (0 : ℝ) < 2^(27*m)) (Real.rpow_pos_of_pos hh _)).mp
  rw [Real.log_pow,Real.log_rpow hh]
  have hl : alpha*Real.log Q ≤ Real.log H := by
    simpa only [Real.log_rpow hq] using Real.log_le_log (Real.rpow_pos_of_pos hq _) henv
  have hb := mul_le_mul_of_nonneg_left hl (mul_pos ho hg).le
  nlinarith

theorem polynomial_budget4 (m r0 N : ℕ) (eta alpha omega gamma D Q H X : ℝ)
    (ho : 0 < omega) (hg : 0 < gamma) (hD : 1 ≤ D) (hQ : 1 < Q)
    (henv : Q^alpha ≤ H) (hX : 0 ≤ X) (hheight : X ≤ D^N)
    (hsum : (N : ℝ) ≤ (m : ℝ)*(1+eta)*(r0 : ℝ))
    (hcut : 9*(m : ℝ)*(1+eta)*Real.log D ≤ alpha*omega*gamma*Real.log Q) :
    X^(9 : ℕ) ≤ H^(omega*gamma*(r0 : ℝ)) := by
  have hd : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlogD := Real.log_nonneg hD
  have hh : 0 < H := (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).trans_le henv
  have hbudget : (D^N)^(9 : ℕ) ≤ H^(omega*gamma*(r0 : ℝ)) := by
    apply (Real.log_le_log_iff (by positivity : 0 < (D^N)^(9 : ℕ))
      (Real.rpow_pos_of_pos hh _)).mp
    rw [Real.log_pow,Real.log_pow,Real.log_rpow hh]
    have hl : alpha*Real.log Q ≤ Real.log H := by
      simpa only [Real.log_rpow (lt_trans zero_lt_one hQ)] using
        Real.log_le_log (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) henv
    have h1 := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 9*Real.log D)
    have h2 := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg r0)
    have h3 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ omega*gamma*(r0 : ℝ))
    norm_num only [Nat.cast_ofNat] at *
    nlinarith
  exact (pow_le_pow_left₀ hX hheight 9).trans hbudget

theorem denominator_growth4 (H0 H Q0 Q gamma : ℝ) (r0 r : ℕ)
    (hH0 : 0 ≤ H0) (hH : 0 ≤ H) (hQ0 : 0 ≤ Q0) (hg : 0 ≤ gamma)
    (hupper : Q0 ≤ H0) (hlower : H^(1/3 : ℝ) ≤ Q)
    (hcompare : H0^(gamma*(r0 : ℝ)) ≤ H^(r : ℝ)) :
    Q0^((r0 : ℝ)*(gamma/3)) ≤ Q^(r : ℝ) := by
  calc
    Q0^((r0 : ℝ)*(gamma/3)) ≤ H0^((r0 : ℝ)*(gamma/3)) :=
      Real.rpow_le_rpow hQ0 hupper (by positivity)
    _ = (H0^(gamma*(r0 : ℝ)))^(1/3 : ℝ) := by
      rw [← Real.rpow_mul hH0]
      congr 1
      ring
    _ ≤ (H^(r : ℝ))^(1/3 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hH0 _) hcompare (by norm_num)
    _ = (H^(1/3 : ℝ))^(r : ℝ) := by
      rw [← Real.rpow_mul hH,← Real.rpow_mul hH]
      congr 1
      ring
    _ ≤ Q^(r : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hH _) hlower (Nat.cast_nonneg r)

theorem third_budget4 (H Q a : ℝ) (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hroot : H^(1/3 : ℝ) ≤ Q) : H^a ≤ (Q^(a/3))^9 := by
  calc
    H^a = (H^(1/3 : ℝ))^(3*a) := by
      rw [← Real.rpow_mul hH]
      congr 1
      ring
    _ ≤ Q^(3*a) := Real.rpow_le_rpow (Real.rpow_nonneg hH _) hroot (by positivity)
    _ = (Q^(a/3))^9 := by
      rw [← Real.rpow_mul_natCast hQ]
      congr 1
      norm_num
      ring

theorem denominator_absolute4 (m : ℕ) (H Q omega gamma : ℝ)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ho : 0 ≤ omega) (hg : 0 ≤ gamma)
    (hroot : H^(1/3 : ℝ) ≤ Q) (hbudget : (2 : ℝ)^(27*m) ≤ H^(omega*gamma)) :
    (2 : ℝ)^(3*m) ≤ Q^(omega*(gamma/3)) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (9 : ℕ) ≠ 0) (Real.rpow_nonneg hQ _)
  calc
    ((2 : ℝ)^(3*m))^9 = (2 : ℝ)^(27*m) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ H^(omega*gamma) := hbudget
    _ ≤ (Q^((omega*gamma)/3))^9 := third_budget4 H Q _ hH hQ (mul_nonneg ho hg) hroot
    _ = (Q^(omega*(gamma/3)))^9 := by congr 2; ring

theorem polynomial_height4 (A B H Q omega gamma : ℝ) (r0 : ℕ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ho : 0 ≤ omega) (hg : 0 ≤ gamma)
    (hAB : A ≤ B) (hroot : H^(1/3 : ℝ) ≤ Q)
    (hbudget : B^9 ≤ H^(omega*gamma*(r0 : ℝ))) :
    A ≤ Q^(omega*(r0 : ℝ)*(gamma/3)) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (9 : ℕ) ≠ 0) (Real.rpow_nonneg hQ _)
  calc
    A^9 ≤ B^9 := pow_le_pow_left₀ hA hAB 9
    _ ≤ H^(omega*gamma*(r0 : ℝ)) := hbudget
    _ ≤ (Q^((omega*gamma*(r0 : ℝ))/3))^9 :=
      third_budget4 H Q _ hH hQ (by positivity) hroot
    _ = (Q^(omega*(r0 : ℝ)*(gamma/3)))^9 := by congr 2; ring



theorem primitive_high_index_contradiction4 (m : ℕ) (hm : 0 < m)
    (M : Fin m → Fin 4 → ℤ) (hM : ∀ h, Ideal.span (Set.range (M h)) = ⊤)
    (theta gamma c : ℝ) (ht : 0 < theta) (ht1 : theta < 1/12)
    (hg : 0 < gamma) (hg3 : gamma ≤ 3) (hc : theta < c)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(r h : ℝ))
    (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0) (hh : homogeneous4 r P)
    (hindex : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c)
    (hcompare : ∀ h, (normalHeight4 (M ⟨0,hm⟩) : ℝ)^(gamma*(r ⟨0,hm⟩ : ℝ)) ≤
      (normalHeight4 (M h) : ℝ)^(r h))
    (hbudget : ∀ h, (2 : ℝ)^(27*m) ≤
      (normalHeight4 (M h) : ℝ)^(JSP000334.omega65 m theta*gamma))
    (hpoly : (height4 P : ℝ)^9 ≤ (normalHeight4 (M ⟨0,hm⟩) : ℝ)^
      (JSP000334.omega65 m theta*gamma*(r ⟨0,hm⟩ : ℝ))) : False := by
  let C : (h : Fin m) → NormalCoordinateChoice4 (M h) :=
    fun h => (normal_coordinate_choice4 (M h) (hM h)).some
  let e := fun h => (C h).e
  let N := permutedNormals4 M e
  let P' := transport4 ℤ e P
  have hN (h) : N h 0 ≠ 0 := by
    change M h ((C h).e 0) ≠ 0
    rw [(C h).e_zero]
    exact (C h).first_nonzero
  have hNH (h) : normalHeight4 (M h) = (N h 0).natAbs := by
    change normalHeight4 (M h) = (M h ((C h).e 0)).natAbs
    rw [(C h).e_zero]
    exact (C h).height_attains
  have hroot (h) : (normalHeight4 (M h) : ℝ)^(1/3 : ℝ) ≤
      |(SchmidtRationalNormalization6.rootDenominator6 (N h 0) (N h 1) : ℝ)| ∧
      |(SchmidtRationalNormalization6.rootDenominator6 (N h 0) (N h 1) : ℝ)| ≤
        (normalHeight4 (M h) : ℝ) := by
    have hb : Int.gcd (N h 0) (N h 1)^3 ≤ (N h 0).natAbs^2 := by
      change Int.gcd (M h ((C h).e 0)) (M h ((C h).e 1))^3 ≤
        (M h ((C h).e 0)).natAbs^2
      rw [(C h).e_zero,(C h).e_one]
      exact (C h).gcd_bound
    have hx := denominator_real_bounds4 (N h 0) (N h 1) (hN h) hb
    have ha : |(N h 0 : ℝ)| = (normalHeight4 (M h) : ℝ) := by
      rw [hNH h]
      rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
    rwa [ha] at hx
  have hPindex : P'.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 N r c := by
    dsimp only [P']
    rw [transport4_map]
    exact (transport4_normalIdeal_iff e M r c _).mp hindex
  have ho := JSP000334.omega65_pos m theta ht
  apply high_index_scalar_contradiction4 m hm N hN theta (gamma/3) c ht ht1
    (by positivity) (by linarith) hc r hr hsep P' ((transport4_nonzero e P).mpr hn)
    ((transport4_homogeneous e r P).mpr hh) hPindex
  · intro h
    simpa only [Real.rpow_natCast] using denominator_growth4
      (normalHeight4 (M ⟨0,hm⟩) : ℝ) (normalHeight4 (M h) : ℝ) _ _ gamma
      (r ⟨0,hm⟩) (r h) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (abs_nonneg _) hg.le
      (hroot _).2 (hroot h).1 (by simpa only [Real.rpow_natCast] using hcompare h)
  · intro h
    exact denominator_absolute4 m _ _ _ gamma (Nat.cast_nonneg _) (abs_nonneg _)
      ho.le hg.le (hroot h).1 (hbudget h)
  · dsimp only [P']
    rw [transport4_height]
    exact polynomial_height4 (height4 P : ℝ) (height4 P : ℝ) _ _ _ gamma (r ⟨0,hm⟩)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (abs_nonneg _) ho.le hg.le le_rfl (hroot _).1 hpoly

theorem original_blocks_cutoff4 (U : Set ℝ) (hU : ¬ BddAbove U)
    (cut eta E rho : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho) (m : ℕ) :
    ∃ t : Fin m → U, StrictMono (fun h => (t h).val) ∧ Set.Finite (Set.range t) ∧
      (∀ h, cut < (t h).val ∧ 1 < (t h).val^(5 : ℕ) ∧
        16*E < ((t h).val^(5 : ℕ))^eta ∧
        4*(eta⁻¹+1) < ((t h).val^(5 : ℕ))^eta) ∧
      ∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log ((t h).val^(5 : ℕ)) ≤
          rho*Real.log ((t ⟨h.val+1,hh⟩).val^(5 : ℕ)) := by
  let B := max (Real.log (16*E)/eta) (Real.log (4*(eta⁻¹+1))/eta)
  obtain ⟨q,hq,hmono,hsep⟩ := JSP000334.parameter_sparse_Q U hU (max cut (Real.exp B))
    ((1+eta)/rho) m
  let t : Fin m → U := fun h => ⟨q h,(hq h).1⟩
  have hlog (h) : B < Real.log (q h) := by
    have ht : Real.exp B < q h := lt_of_le_of_lt (le_max_right _ _) (hq h).2.1
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) ht
  have hQ (h) : 1 < (q h)^(5 : ℕ) := one_lt_pow₀ (hq h).2.2 (by decide)
  have hlogpow (h) : B < Real.log ((q h)^(5 : ℕ)) := by
    rw [Real.log_pow]
    have hl := Real.log_pos (hq h).2.2
    norm_num only [Nat.cast_ofNat]
    linarith [hlog h]
  refine ⟨t,hmono,Set.finite_range t,?_,?_⟩
  · intro h
    refine ⟨lt_of_le_of_lt (le_max_left _ _) (hq h).2.1,hQ h,?_,?_⟩
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by linarith)
        (lt_of_le_of_lt (le_max_left _ _) (hlogpow h))
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by positivity)
        (lt_of_le_of_lt (le_max_right _ _) (hlogpow h))
  · intro h hh
    have hs0 := hsep h hh
    rw [div_mul_eq_mul_div] at hs0
    have hs := (div_lt_iff₀ hp).mp hs0
    dsimp [t]
    rw [Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith

def budgetLog4 (m : ℕ) (eta alpha omega gamma D E : ℝ) : ℝ :=
  max (max (Real.log (16*E)/eta) (Real.log (4*(eta⁻¹+1))/eta))
    (max (((27*m : ℕ) : ℝ)*Real.log 2/(alpha*omega*gamma))
      (9*(m : ℝ)*(1+eta)*Real.log D/(alpha*omega*gamma)))

def originalCutoff4 (T : ℝ) (m : ℕ) (eta alpha omega gamma D E : ℝ) : ℝ :=
  max (max T 1) (Real.exp (budgetLog4 m eta alpha omega gamma D E))

theorem cutoff_budgets4 (T : ℝ) (m : ℕ) (eta alpha omega gamma D E q : ℝ)
    (ha : 0 < alpha) (ho : 0 < omega) (hg : 0 < gamma)
    (hq : originalCutoff4 T m eta alpha omega gamma D E < q) :
    T < q ∧ 1 < q^(5 : ℕ) ∧
      (27*m : ℕ)*Real.log 2 ≤ alpha*omega*gamma*Real.log (q^(5 : ℕ)) ∧
      9*(m : ℝ)*(1+eta)*Real.log D ≤ alpha*omega*gamma*Real.log (q^(5 : ℕ)) := by
  have hT : T < q := lt_of_le_of_lt ((le_max_left T 1).trans (le_max_left _ _)) hq
  have hq1 : 1 < q := lt_of_le_of_lt ((le_max_right T 1).trans (le_max_left _ _)) hq
  have hex : Real.exp (budgetLog4 m eta alpha omega gamma D E) < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hl : budgetLog4 m eta alpha omega gamma D E < Real.log q := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hex
  have hlQ : budgetLog4 m eta alpha omega gamma D E < Real.log (q^(5 : ℕ)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_pos hq1]
  have hn : ((27*m : ℕ) : ℝ)*Real.log 2/(alpha*omega*gamma) < Real.log (q^(5 : ℕ)) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlQ
  have hp : 9*(m : ℝ)*(1+eta)*Real.log D/(alpha*omega*gamma) < Real.log (q^(5 : ℕ)) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlQ
  have hden : 0 < alpha*omega*gamma := mul_pos (mul_pos ha ho) hg
  exact ⟨hT,one_lt_pow₀ hq1 (by decide),
    (by nlinarith [(div_lt_iff₀ hden).mp hn]),(by nlinarith [(div_lt_iff₀ hden).mp hp])⟩


end CompoundFeasibility.SchmidtSourceParameters4Literal178

end

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedVanishing4Literal178
open SourceSelectedDual4Literal178 SourceNormalHeight4Literal178 SchmidtNormalCoordinates4Literal178 SchmidtSourceParameters4Literal178
open OriginalSelectedSystem4 OriginalDeformedSource4 OriginalLastDual4 OriginalAuxiliaryDual4
open SourceMultiblock4 SourceNormalIndex4 Auxiliary4 Auxiliary4.SourceVanishing4
open Auxiliary4.SourceExpansion4 Auxiliary4.SourceGrid4 Auxiliary4.SourceEvaluation4

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

theorem source_nonzero_branch_contradiction4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (g : U → ℤ) (M : U → Fin 4 → ℤ)
    (hnormal : ∀ q, g q ≠ 0 ∧ M q ≠ 0 ∧
      (∀ i, integerLastDual4 (fun j => ((F q).w j : Fin 4 → ℤ)) i = g q*M q i) ∧
      Ideal.span (Set.range (M q)) = ⊤ ∧
      LinearMap.ker (normalForm4 (M q)) =
        Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (((F q).w j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
      LinearMap.ker (realNormalForm4 (M q)) =
        Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal ((F q).w j.castSucc : Fin 4 → ℤ))))
    (s : MixedIndex4)
    (hselected : ∀ q : U, s ∈ publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
      (SourceWeights4.frameWidths F q) (fun i => c2 i/5) (fun i => c3 i/5))
    (hnonzero : ∀ q, mixedNonzero4 A2 A3 L (M q) s) : False := by
  obtain ⟨alpha,halpha,T,hT,henvelopes⟩ :=
    source_uniform_height_envelopes4 A2 A3 L h2 h3 hLdet ha delta hd
  obtain ⟨V,hVU,hV,d,hdp,hd1,c,hc,hbal,hfin,hframe⟩ :=
    SourceWeights4.fixed_weights_same_frame4 F hU hd hc2 hc3
  obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ := source_auxiliary4_grid_vanishing A2 A3 L h2 h3 hLdet ha
  obtain ⟨eta,theta,m,hee,hte,he,he1,hed,hm,hmb,ht,ht1,htm,ho⟩ := eta_m_theta4 d hdp hd1 K
  obtain ⟨gamma,hg,hg3,hcompat,hcompat'⟩ := positive_gamma4 alpha eta halpha he
  let omega := JSP000334.omega65 m theta
  let cut := originalCutoff4 T m eta alpha omega gamma D E
  obtain ⟨t0,ht0,hfinite,hgrowth,hsep⟩ := original_blocks_cutoff4 V hV cut eta E omega he hE ho m
  let lift : V → U := fun q => ⟨q.val,hVU q.property⟩
  let t : Fin m → U := fun h => lift (t0 h)
  let Q : Fin m → ℝ := fun h => (t h).val^(5 : ℕ)
  let H : Fin m → ℝ := fun h => (normalHeight4 (M (t h)) : ℝ)
  have hQ (h) : 1 < Q h := (hgrowth h).2.1
  have hcut (h) := cutoff_budgets4 T m eta alpha omega gamma D E (t h).val
    halpha ho hg (hgrowth h).1
  have hH (h) : max 1 (normalHeight4 (M (t h)) : ℝ) = H h := by
    apply max_eq_right
    exact_mod_cast normalHeight4_pos (M (t h)) (hnormal (t h)).2.1
  have henv (h) : (Q h)^alpha ≤ H h ∧ H h ≤ (Q h)^(4 : ℝ) := by
    have hh := henvelopes (t h).val (hcut h).1 (hQU _ (t h).property) hL c0 c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) (u (t h)) (F (t h))
      (M (t h)) (g (t h)) (hnormal (t h)).1 (hnormal (t h)).2.2.1
      s (hselected (t h)) (hnonzero (t h))
    rwa [hH h] at hh
  have hmono : Monotone Q := by
    intro i j hij
    exact pow_le_pow_left₀ (zero_lt_one.trans (hQU _ (t i).property)).le (ht0.monotone hij) 5
  obtain ⟨r,hr,hrsep,hrbal,hrsum⟩ := SchmidtParameters6.anchored_degrees6 m hm eta omega he ho Q hQ hmono hsep
  obtain ⟨P,hP,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,hvan⟩ := haux eta he m hmb r hr
  have hgrid := hvan Q hQ ⟨0,hm⟩ d hed hd1
    (fun h => (hgrowth h).2.2.1) (fun h => (hgrowth h).2.2.2) hrbal c hc hbal
    (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ))
    (fun h j i => (hframe (t h) (t0 h).property).1 j i)
    (fun h j i => (hframe (t h) (t0 h).property).2.1 j i)
    (fun h j i => (hframe (t h) (t0 h).property).2.2 j i)
  have hindex := (integer_grid_high_normal_index4 r hr P hhom
    (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) (fun h => M (t h))
    (fun h => (hnormal (t h)).2.1) (fun h => (hnormal (t h)).2.2.2.2.1)
    (fun h => (hnormal (t h)).2.2.2.2.2) eta he hgrid).2
  have hcompare := height_comparison4 m hm alpha gamma halpha hg hcompat' Q H hQ henv r
    (fun h => (hrbal h).1)
  have hbudget (h) := normal_budget4 m alpha omega gamma (Q h) (H h) ho hg (hQ h)
    (henv h).1 (hcut h).2.2.1
  have hpoly := polynomial_budget4 m (r ⟨0,hm⟩) (∑ h, r h) eta alpha omega gamma D
    (Q ⟨0,hm⟩) (H ⟨0,hm⟩) (height4 P : ℝ) ho hg hD (hQ _) (henv _).1
    (Nat.cast_nonneg _) hheight hrsum (hcut ⟨0,hm⟩).2.2.2
  exact primitive_high_index_contradiction4 m hm (fun h => M (t h))
    (fun h => (hnormal (t h)).2.2.2.1) theta gamma ((m : ℝ)*eta) ht ht1 hg hg3 htm
    r hr hrsep P hP hhom hindex hcompare hbudget hpoly


theorem same_frame_selected_vanishing4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (S : Finset MixedIndex4)
    (hselected : ∀ q : U, ∀ s ∈ S, s ∈ publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
      (SourceWeights4.frameWidths F q) (fun i => c2 i/5) (fun i => c3 i/5)) :
    ∃ T : ℝ, ∀ q : U, T < q.val → ∀ s ∈ S,
      lastDualProduct4 A2 A3 L (fun j => ((F q).w j : Fin 4 → ℤ)) (F q).rational_independent s = 0 := by
  obtain ⟨g,M,a,hn⟩ := same_frame_primitive_normals4
    (fun q : U => fun j => ((F q).w j : Fin 4 → ℤ)) (fun q => (F q).real_independent)
  have hz : ∃ T : ℝ, ∀ q : U, T < q.val → ∀ s ∈ S, mixedProduct4 A2 A3 L (M q) s = 0 := by
    by_contra hf
    obtain ⟨s,hs,hB⟩ := failure_eventual_zero_branch4 A2 A3 L U M S hf
    let B := nonzeroBranch4 A2 A3 L U M s
    let lift : B → U := fun q => ⟨q.val,(nonzeroBranch4_subset A2 A3 L U M s) q.property⟩
    refine source_nonzero_branch_contradiction4
      (A2 := A2) (A3 := A3) (L := L) (hL := hL) (c0 := c0) (c2 := c2) (c3 := c3)
      (delta := delta) (U := B)
      (hQU := fun q hq => hQU q ((nonzeroBranch4_subset A2 A3 L U M s) hq))
      (u := fun q : B => u (lift q)) h2 h3 hLdet ha (fun q : B => F (lift q)) hB hd hc2 hc3
      (fun q => g (lift q)) (fun q => M (lift q)) ?_ s ?_ ?_
    · intro q
      exact ⟨(hn (lift q)).1,(hn (lift q)).2.1,(hn (lift q)).2.2.1,
        (hn (lift q)).2.2.2.2.1,(hn (lift q)).2.2.2.2.2.2.1,
        (hn (lift q)).2.2.2.2.2.2.2.1⟩
    · intro q
      exact hselected (lift q) s hs
    · intro q
      exact (mem_nonzeroBranch4 A2 A3 L U M s (lift q)).mp q.property
  obtain ⟨T,hT⟩ := hz
  refine ⟨T,?_⟩
  intro q hq s hs
  exact (primitive_lastDualProduct4_zero A2 A3 L _ (F q).rational_independent
    (M q) (g q) (hn q).1 (hn q).2.2.1 s).mp (hT q hq s hs)

theorem source_selected_vanishing4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ U : Set ℝ, ∃ hUV : U ⊆ V, ¬ BddAbove U ∧
      ∃ u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ∃ F : (q : U) → DeformedAttaining4 A2 A3 L (sourceUnit42 L hLdet) q.val
        (hQV q.val (hUV q.property)) c0 c2 c3 delta (u q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ W : Set ℝ, ∃ hWU : W ⊆ U, ¬ BddAbove W ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
        (∀ q : U, q.val ∈ W →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
            (OriginalDeformation4.deformedWidths4 q.val c0
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q.val
                  (hQV q.val (hUV q.property)) c0 c2 c3)) (F q).sigma) (fun i => c2 i/5) (fun i => c3 i/5) = S) ∧
        ∃ T : ℝ, ∀ q : U, q.val ∈ W → T < q.val → ∀ s ∈ S,
          lastDualProduct4 A2 A3 L (fun j => ((F q).w j : Fin 4 → ℤ)) (F q).rational_independent s = 0 := by
  obtain ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,hhigh⟩ :=
    source_normalized_selected_high_index4 A2 A3 L h2 h3 hLdet hAlg delta hd
      c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap
  let lift : W → U := fun q => ⟨q.val,hWU q.property⟩
  obtain ⟨T,hT⟩ := same_frame_selected_vanishing4
    (A2 := A2) (A3 := A3) (L := L) (hL := sourceUnit42 L hLdet)
    (c0 := c0) (c2 := c2) (c3 := c3) (delta := delta) (U := W)
    (hQU := fun q hq => hQV q (hUV (hWU hq))) (u := fun q : W => u (lift q)) h2 h3 hLdet hAlg
    (fun q : W => F (lift q)) hW hd hc2 hc3 S (fun q s hs => by
      have heq := hselected (lift q) q.property
      exact Eq.mpr (congrArg (fun K : Finset MixedIndex4 => s ∈ K) heq) hs)
  refine ⟨U,hUV,hU,u,F,S,hS,W,hWU,hW,hWp,hselected,T,?_⟩
  intro q hq hTq s hs
  exact hT ⟨q.val,hq⟩ hTq s hs

end CompoundFeasibility.SourceSelectedVanishing4Literal178
end

#check CompoundFeasibility.SchmidtScalarReduction4Literal178.blockDegree4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.blockDegree4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.blockDegree4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.homogeneous4_blockDegree
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.homogeneous4_blockDegree
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.homogeneous4_blockDegree
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4_weight
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4_weight
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4_weight
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4_forward
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4_forward
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.pivotExponent4_forward
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.normalCoordinateWeight4_nonneg
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.normalCoordinateWeight4_nonneg
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.normalCoordinateWeight4_nonneg
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_support
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_support
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_support
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_iff_support
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_iff_support
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_iff_support
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.support_X_pow_mul4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.support_X_pow_mul4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.support_X_pow_mul4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.free_weight_shift4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.free_weight_shift4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.free_weight_shift4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_saturation
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_saturation
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.sourceNormalIdeal4_saturation
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_monomial
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_monomial
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_monomial
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_coeff
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_coeff
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_coeff
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.minimumExponent4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.minimumExponent4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.minimumExponent4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.minimumExponent4_spec
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.minimumExponent4_spec
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.minimumExponent4_spec
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_coeff
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_coeff
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_coeff
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_factor
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_factor
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_factor
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_coeff
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_coeff
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_coeff
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_nonzero
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_nonzero
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_nonzero
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_nonzero
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_nonzero
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.extracted4_nonzero
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_support_source
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_support_source
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_support_source
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_height
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_height
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_height
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_blockDegree
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_blockDegree
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_blockDegree
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_preserves_independence
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_preserves_independence
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_preserves_independence
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_homogeneous
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_homogeneous
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_homogeneous
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroNormalCoefficient4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroNormalCoefficient4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroNormalCoefficient4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_map
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_map
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_map
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroNormalCoefficient4_pivot
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroNormalCoefficient4_pivot
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroNormalCoefficient4_pivot
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_normal
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_normal
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_normal
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_normal_products
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_normal_products
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_normal_products
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_ideal_map
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_ideal_map
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.zeroSpecialize4_ideal_map
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_closed
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_closed
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminate4_closed
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4_coeff
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4_coeff
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4_coeff
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4_pivot
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4_pivot
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.specializeNormalsList4_pivot
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_nonzero
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_nonzero
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_nonzero
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_height
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_height
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_height
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_blockDegree
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_blockDegree
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_blockDegree
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_preserves_independence
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_preserves_independence
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_preserves_independence
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_independent
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_independent
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_independent
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_closed
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_closed
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_closed
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.excessVariables4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.excessVariables4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.excessVariables4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.mem_excessVariables4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.mem_excessVariables4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.mem_excessVariables4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.card_excessVariables4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.card_excessVariables4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.card_excessVariables4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_coeff
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_coeff
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_coeff
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_first_two
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_first_two
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_first_two
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_polynomial
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_polynomial
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedNormals4_polynomial
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_support
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_support
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_support
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_nonzero
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_nonzero
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_nonzero
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_height
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_height
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_height
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_blockDegree
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_blockDegree
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_blockDegree
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.excessVariables4_free
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.excessVariables4_free
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.excessVariables4_free
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_closed
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_closed
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_closed
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_homogeneous
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_homogeneous
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminateList4_homogeneous
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4_le
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4_le
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4_le
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4_actual
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4_actual
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.eliminatedDegrees4_actual
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_homogeneous
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_homogeneous
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.reducedPolynomial4_homogeneous
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_generators
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_generators
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_generators
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_map
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_map
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_map
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.binarySupport4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.binarySupport4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.binarySupport4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.binary_block_sum4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.binary_block_sum4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.binary_block_sum4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_monomial
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_monomial
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_monomial
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4_inj
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4_inj
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4_inj
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4_injOn
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4_injOn
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarExponent4_injOn
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_as_sum
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_as_sum
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_as_sum
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_coeff
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_coeff
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_coeff
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_support
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_support
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_support
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarSupportEquiv4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarSupportEquiv4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarSupportEquiv4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_nonzero
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_nonzero
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_nonzero
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_height
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_height
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_height
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_support_degree
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_support_degree
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_support_degree
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_degree
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_degree
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_degree
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarNormal4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarNormal4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarNormal4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_normal
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_normal
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_normal
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_normal_products
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_normal_products
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_normal_products
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarIdeal4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarIdeal4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarIdeal4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_ideal_map
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_ideal_map
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_ideal_map
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_closed
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_closed
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar4_closed
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.monicNormal4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.monicNormal4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.monicNormal4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarNormal4_monic
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarNormal4_monic
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarNormal4_monic
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.normal_constant_unit4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.normal_constant_unit4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.normal_constant_unit4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar_products_scaling4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar_products_scaling4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar_products_scaling4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar_products_membership4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar_products_membership4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalar_products_membership4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarIdeal4_eq_monic
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarIdeal4_eq_monic
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.scalarIdeal4_eq_monic
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.rootPoint4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.rootPoint4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.rootPoint4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_support
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_support
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_support
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_support
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_support
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_support
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_coeff
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_coeff
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_coeff
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_divided
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_divided
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_iff_divided
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_index_lower
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_index_lower
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.monicIdeal4_index_lower
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.high_index_scalar_polynomial4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.high_index_scalar_polynomial4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.high_index_scalar_polynomial4
#check CompoundFeasibility.SchmidtScalarReduction4Literal178.high_index_scalar_contradiction4
#print CompoundFeasibility.SchmidtScalarReduction4Literal178.high_index_scalar_contradiction4
#print axioms CompoundFeasibility.SchmidtScalarReduction4Literal178.high_index_scalar_contradiction4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_coord
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_coord
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_coord
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_pos
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_pos
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_pos
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_neg
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_neg
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_neg
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_le_iff
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_le_iff
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_le_iff
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_normalization_bound
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_normalization_bound
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normalHeight4_normalization_bound
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.primitive_common_divisor4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.primitive_common_divisor4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.primitive_common_divisor4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.height_attaining4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.height_attaining4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.height_attaining4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.three_gcd_product_dvd4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.three_gcd_product_dvd4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.three_gcd_product_dvd4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.minimum_secondary_gcd4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.minimum_secondary_gcd4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.minimum_secondary_gcd4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.primitive_nonzero4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.primitive_nonzero4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.primitive_nonzero4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.select_minimum_pair4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.select_minimum_pair4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.select_minimum_pair4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.select_pair4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.select_pair4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.select_pair4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.pairPermutation4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.pairPermutation4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.pairPermutation4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.pairPermutation4_coordinates
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.pairPermutation4_coordinates
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.pairPermutation4_coordinates
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.coefficientMultiset4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.coefficientMultiset4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.coefficientMultiset4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_coefficients4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_coefficients4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_coefficients4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_range4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_range4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_range4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_primitive4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_primitive4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_primitive4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_height4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_height4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_height4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_bezout4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_bezout4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permuted_bezout4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.NormalCoordinateChoice4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.NormalCoordinateChoice4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.NormalCoordinateChoice4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normal_coordinate_choice4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normal_coordinate_choice4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.normal_coordinate_choice4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.NormalCoordinateChoice4.permuted_data
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.NormalCoordinateChoice4.permuted_data
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.NormalCoordinateChoice4.permuted_data
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_apply
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_apply
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_apply
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_symm_apply
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_symm_apply
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_symm_apply
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_inverses
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_inverses
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.variablePermutation4_inverses
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_inverse
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_inverse
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_inverse
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_nonzero
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_nonzero
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_nonzero
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4_apply
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4_apply
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4_apply
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_coeff
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_coeff
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_coeff
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_coeff_all
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_coeff_all
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_coeff_all
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_support
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_support
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_support
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_height
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_height
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_height
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4_block_sum
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4_block_sum
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.exponentPermutation4_block_sum
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_blockDegree
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_blockDegree
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_blockDegree
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_homogeneous
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_homogeneous
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_homogeneous
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_X
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_X
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_X
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_C
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_C
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_C
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_map
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_map
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_map
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permutedNormals4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permutedNormals4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.permutedNormals4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalPolynomial
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalPolynomial
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalPolynomial
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normal_products
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normal_products
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normal_products
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalIdeal_map
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalIdeal_map
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalIdeal_map
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalIdeal_iff
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalIdeal_iff
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.transport4_normalIdeal_iff
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.denominator_nat_bounds4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.denominator_nat_bounds4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.denominator_nat_bounds4
#check CompoundFeasibility.SchmidtNormalCoordinates4Literal178.denominator_real_bounds4
#print CompoundFeasibility.SchmidtNormalCoordinates4Literal178.denominator_real_bounds4
#print axioms CompoundFeasibility.SchmidtNormalCoordinates4Literal178.denominator_real_bounds4
#check CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4
#print CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4
#check CompoundFeasibility.SourceSelectedDual4Literal178.mixedProduct4
#print CompoundFeasibility.SourceSelectedDual4Literal178.mixedProduct4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.mixedProduct4
#check CompoundFeasibility.SourceSelectedDual4Literal178.mixedNonzero4
#print CompoundFeasibility.SourceSelectedDual4Literal178.mixedNonzero4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.mixedNonzero4
#check CompoundFeasibility.SourceSelectedDual4Literal178.mixedProduct4_nonzero
#print CompoundFeasibility.SourceSelectedDual4Literal178.mixedProduct4_nonzero
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.mixedProduct4_nonzero
#check CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4_scaling
#print CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4_scaling
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4_scaling
#check CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4_scaling_zero
#print CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4_scaling_zero
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.dualValue4_scaling_zero
#check CompoundFeasibility.SourceSelectedDual4Literal178.lastDualValue4
#print CompoundFeasibility.SourceSelectedDual4Literal178.lastDualValue4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.lastDualValue4
#check CompoundFeasibility.SourceSelectedDual4Literal178.lastDualProduct4
#print CompoundFeasibility.SourceSelectedDual4Literal178.lastDualProduct4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.lastDualProduct4
#check CompoundFeasibility.SourceSelectedDual4Literal178.primitive_lastDualValue4_zero
#print CompoundFeasibility.SourceSelectedDual4Literal178.primitive_lastDualValue4_zero
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.primitive_lastDualValue4_zero
#check CompoundFeasibility.SourceSelectedDual4Literal178.primitive_lastDualProduct4_zero
#print CompoundFeasibility.SourceSelectedDual4Literal178.primitive_lastDualProduct4_zero
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.primitive_lastDualProduct4_zero
#check CompoundFeasibility.SourceSelectedDual4Literal178.nonzeroBranch4
#print CompoundFeasibility.SourceSelectedDual4Literal178.nonzeroBranch4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.nonzeroBranch4
#check CompoundFeasibility.SourceSelectedDual4Literal178.nonzeroBranch4_subset
#print CompoundFeasibility.SourceSelectedDual4Literal178.nonzeroBranch4_subset
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.nonzeroBranch4_subset
#check CompoundFeasibility.SourceSelectedDual4Literal178.mem_nonzeroBranch4
#print CompoundFeasibility.SourceSelectedDual4Literal178.mem_nonzeroBranch4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.mem_nonzeroBranch4
#check CompoundFeasibility.SourceSelectedDual4Literal178.failure_eventual_zero_branch4
#print CompoundFeasibility.SourceSelectedDual4Literal178.failure_eventual_zero_branch4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.failure_eventual_zero_branch4
#check CompoundFeasibility.SourceSelectedDual4Literal178.same_frame_primitive_normals4
#print CompoundFeasibility.SourceSelectedDual4Literal178.same_frame_primitive_normals4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.same_frame_primitive_normals4
#check CompoundFeasibility.SourceSelectedDual4Literal178.same_frame_high_index_transfer4
#print CompoundFeasibility.SourceSelectedDual4Literal178.same_frame_high_index_transfer4
#print axioms CompoundFeasibility.SourceSelectedDual4Literal178.same_frame_high_index_transfer4
#check CompoundFeasibility.SourceNormalHeight4Literal178.normal_pi_norm_le_height4
#print CompoundFeasibility.SourceNormalHeight4Literal178.normal_pi_norm_le_height4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.normal_pi_norm_le_height4
#check CompoundFeasibility.SourceNormalHeight4Literal178.real_dual_lower4
#print CompoundFeasibility.SourceNormalHeight4Literal178.real_dual_lower4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.real_dual_lower4
#check CompoundFeasibility.SourceNormalHeight4Literal178.finiteValue4
#print CompoundFeasibility.SourceNormalHeight4Literal178.finiteValue4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.finiteValue4
#check CompoundFeasibility.SourceNormalHeight4Literal178.fixed_rational_denominator4
#print CompoundFeasibility.SourceNormalHeight4Literal178.fixed_rational_denominator4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.fixed_rational_denominator4
#check CompoundFeasibility.SourceNormalHeight4Literal178.finite_denominator_identity4
#print CompoundFeasibility.SourceNormalHeight4Literal178.finite_denominator_identity4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.finite_denominator_identity4
#check CompoundFeasibility.SourceNormalHeight4Literal178.integer_numerator_height4
#print CompoundFeasibility.SourceNormalHeight4Literal178.integer_numerator_height4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.integer_numerator_height4
#check CompoundFeasibility.SourceNormalHeight4Literal178.finite_form_lower4
#print CompoundFeasibility.SourceNormalHeight4Literal178.finite_form_lower4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.finite_form_lower4
#check CompoundFeasibility.SourceNormalHeight4Literal178.finite_dualValue4
#print CompoundFeasibility.SourceNormalHeight4Literal178.finite_dualValue4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.finite_dualValue4
#check CompoundFeasibility.SourceNormalHeight4Literal178.finite_dual_lower4
#print CompoundFeasibility.SourceNormalHeight4Literal178.finite_dual_lower4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.finite_dual_lower4
#check CompoundFeasibility.SourceNormalHeight4Literal178.mixed_dual_lower4
#print CompoundFeasibility.SourceNormalHeight4Literal178.mixed_dual_lower4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.mixed_dual_lower4
#check CompoundFeasibility.SourceNormalHeight4Literal178.primitive_mixed_le_cofactor4
#print CompoundFeasibility.SourceNormalHeight4Literal178.primitive_mixed_le_cofactor4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.primitive_mixed_le_cofactor4
#check CompoundFeasibility.SourceNormalHeight4Literal178.padic_cofactor_bound4
#print CompoundFeasibility.SourceNormalHeight4Literal178.padic_cofactor_bound4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.padic_cofactor_bound4
#check CompoundFeasibility.SourceNormalHeight4Literal178.mixed_cofactor_decay4
#print CompoundFeasibility.SourceNormalHeight4Literal178.mixed_cofactor_decay4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.mixed_cofactor_decay4
#check CompoundFeasibility.SourceNormalHeight4Literal178.rescaled_balance4
#print CompoundFeasibility.SourceNormalHeight4Literal178.rescaled_balance4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.rescaled_balance4
#check CompoundFeasibility.SourceNormalHeight4Literal178.source_selected_mixed_decay4
#print CompoundFeasibility.SourceNormalHeight4Literal178.source_selected_mixed_decay4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.source_selected_mixed_decay4
#check CompoundFeasibility.SourceNormalHeight4Literal178.inverseConstant4
#print CompoundFeasibility.SourceNormalHeight4Literal178.inverseConstant4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.inverseConstant4
#check CompoundFeasibility.SourceNormalHeight4Literal178.inverseConstant4_pos
#print CompoundFeasibility.SourceNormalHeight4Literal178.inverseConstant4_pos
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.inverseConstant4_pos
#check CompoundFeasibility.SourceNormalHeight4Literal178.inverse_coordinate4
#print CompoundFeasibility.SourceNormalHeight4Literal178.inverse_coordinate4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.inverse_coordinate4
#check CompoundFeasibility.SourceNormalHeight4Literal178.normalHeight4_real_le
#print CompoundFeasibility.SourceNormalHeight4Literal178.normalHeight4_real_le
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.normalHeight4_real_le
#check CompoundFeasibility.SourceNormalHeight4Literal178.cofactor_coordinate_upper4
#print CompoundFeasibility.SourceNormalHeight4Literal178.cofactor_coordinate_upper4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.cofactor_coordinate_upper4
#check CompoundFeasibility.SourceNormalHeight4Literal178.source_normal_height_upper4
#print CompoundFeasibility.SourceNormalHeight4Literal178.source_normal_height_upper4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.source_normal_height_upper4
#check CompoundFeasibility.SourceNormalHeight4Literal178.source_normal_height_upper_envelope4
#print CompoundFeasibility.SourceNormalHeight4Literal178.source_normal_height_upper_envelope4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.source_normal_height_upper_envelope4
#check CompoundFeasibility.SourceNormalHeight4Literal178.combined_product4
#print CompoundFeasibility.SourceNormalHeight4Literal178.combined_product4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.combined_product4
#check CompoundFeasibility.SourceNormalHeight4Literal178.lowerThreshold4
#print CompoundFeasibility.SourceNormalHeight4Literal178.lowerThreshold4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.lowerThreshold4
#check CompoundFeasibility.SourceNormalHeight4Literal178.heightAlpha4
#print CompoundFeasibility.SourceNormalHeight4Literal178.heightAlpha4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.heightAlpha4
#check CompoundFeasibility.SourceNormalHeight4Literal178.lower_absorption4
#print CompoundFeasibility.SourceNormalHeight4Literal178.lower_absorption4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.lower_absorption4
#check CompoundFeasibility.SourceNormalHeight4Literal178.selected_lower_height4
#print CompoundFeasibility.SourceNormalHeight4Literal178.selected_lower_height4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.selected_lower_height4
#check CompoundFeasibility.SourceNormalHeight4Literal178.source_uniform_height_envelopes4
#print CompoundFeasibility.SourceNormalHeight4Literal178.source_uniform_height_envelopes4
#print axioms CompoundFeasibility.SourceNormalHeight4Literal178.source_uniform_height_envelopes4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.eta_m_theta4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.eta_m_theta4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.eta_m_theta4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.positive_gamma4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.positive_gamma4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.positive_gamma4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.height_comparison4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.height_comparison4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.height_comparison4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.normal_budget4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.normal_budget4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.normal_budget4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.polynomial_budget4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.polynomial_budget4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.polynomial_budget4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.denominator_growth4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.denominator_growth4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.denominator_growth4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.third_budget4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.third_budget4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.third_budget4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.denominator_absolute4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.denominator_absolute4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.denominator_absolute4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.polynomial_height4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.polynomial_height4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.polynomial_height4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.primitive_high_index_contradiction4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.primitive_high_index_contradiction4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.primitive_high_index_contradiction4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.original_blocks_cutoff4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.original_blocks_cutoff4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.original_blocks_cutoff4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.budgetLog4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.budgetLog4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.budgetLog4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.originalCutoff4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.originalCutoff4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.originalCutoff4
#check CompoundFeasibility.SchmidtSourceParameters4Literal178.cutoff_budgets4
#print CompoundFeasibility.SchmidtSourceParameters4Literal178.cutoff_budgets4
#print axioms CompoundFeasibility.SchmidtSourceParameters4Literal178.cutoff_budgets4
#check CompoundFeasibility.SourceSelectedVanishing4Literal178.source_nonzero_branch_contradiction4
#print CompoundFeasibility.SourceSelectedVanishing4Literal178.source_nonzero_branch_contradiction4
#print axioms CompoundFeasibility.SourceSelectedVanishing4Literal178.source_nonzero_branch_contradiction4
#check CompoundFeasibility.SourceSelectedVanishing4Literal178.same_frame_selected_vanishing4
#print CompoundFeasibility.SourceSelectedVanishing4Literal178.same_frame_selected_vanishing4
#print axioms CompoundFeasibility.SourceSelectedVanishing4Literal178.same_frame_selected_vanishing4
#check CompoundFeasibility.SourceSelectedVanishing4Literal178.source_selected_vanishing4
#print CompoundFeasibility.SourceSelectedVanishing4Literal178.source_selected_vanishing4
#print axioms CompoundFeasibility.SourceSelectedVanishing4Literal178.source_selected_vanishing4
