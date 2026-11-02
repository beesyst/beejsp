import SubspaceBridge.SourceNormalizedHighIndex4
import SubspaceBridge.SchmidtTaylorCorrespondence6
import SubspaceBridge.SchmidtHilfssatz12
import Mathlib.Algebra.MvPolynomial.Division
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtScalarReduction4
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

end CompoundFeasibility.SchmidtScalarReduction4
