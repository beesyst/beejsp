import SubspaceBridge.SourceNormalHighIndex10
import Mathlib.Algebra.MvPolynomial.Division
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SchmidtPolynomial10
open SourceNormalHighIndex10 SchmidtNormal10
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def height10 {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) : ℕ :=
  P.support.sup (fun d => (P.coeff d).natAbs)

def blockDegree10 {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) (h : Fin m) : ℕ :=
  P.support.sup (fun d => ∑ j : Fin 10, d (h,j))

theorem rothAux_weight_block {m : ℕ} (d : SourceMultiblock10.Vars10 m →₀ ℕ) (h : Fin m) :
    Finsupp.weight (fun u : SourceMultiblock10.Vars10 m => if u.1 = h then 1 else 0) d =
      ∑ j : Fin 10, d (h,j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type, nsmul_eq_mul]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero]
  calc
    (∑ x : Fin m, ∑ j : Fin 10,
        if x = h then d (x,j) else 0) =
      ∑ x : Fin m,
        if x = h then (∑ j : Fin 10, d (x,j)) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = h
          · simp [hx]
          · simp [hx]
    _ = ∑ j : Fin 10, d (h,j) := by simp

theorem rothAux_weighted_neg {m : ℕ} (w : SourceMultiblock10.Vars10 m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) K) (n : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous w P n) :
    MvPolynomial.IsWeightedHomogeneous w (-P) n := by
  intro d hd
  apply hP
  simpa using hd

theorem homogeneous10_scale {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) K) (hP : homogeneous10 r P)
    (b : Fin m → K) (f : SourceMultiblock10.Vars10 m → MvPolynomial (SourceMultiblock10.Vars10 m) K) :
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
  have he : (∏ u : SourceMultiblock10.Vars10 m, (MvPolynomial.C (b u.1) : MvPolynomial (SourceMultiblock10.Vars10 m) K)^d u) =
      MvPolynomial.C (∏ h, b h^(r h)) := by
    rw [Fintype.prod_prod_type]
    simp only [Finset.prod_pow_eq_pow_sum,hP d hd,map_prod,map_pow]
  rw [he]
  ring

def numerator10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) :
    MvPolynomial (SourceMultiblock10.Vars10 m) ℤ →+* MvPolynomial (SourceMultiblock10.Vars10 m) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = 0 then
    MvPolynomial.X u - ∑ j ∈ Finset.univ.erase 0,
      MvPolynomial.C (M u.1 j)*MvPolynomial.X (u.1,j)
    else MvPolynomial.C (M u.1 0)*MvPolynomial.X u)

theorem numerator10_map {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) :
    (numerator10 M P).map (Int.castRingHom ℚ) =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun u => MvPolynomial.C (M u.1 0 : ℚ)*
          inverse10 M (fun _ => 0) (MvPolynomial.X u)) (P.map (Int.castRingHom ℚ)) := by
  have hgen (u : SourceMultiblock10.Vars10 m) :
      (numerator10 M (MvPolynomial.X u)).map (Int.castRingHom ℚ) =
        MvPolynomial.C (M u.1 0 : ℚ)*inverse10 M (fun _ => 0) (MvPolynomial.X u) := by
    simp only [numerator10,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd]
    by_cases hu : u.2 = 0
    · rw [if_pos hu]
      have hn : (M u.1 0 : ℚ) ≠ 0 := by exact_mod_cast hM u.1
      have hc : (MvPolynomial.C (M u.1 0 : ℚ) : MvPolynomial (SourceMultiblock10.Vars10 m) ℚ)*
          MvPolynomial.C ((M u.1 0 : ℚ)⁻¹) = 1 := by
        rw [← MvPolynomial.C_mul,mul_inv_cancel₀ hn,map_one]
      simp only [map_sub,map_sum,map_mul,MvPolynomial.map_X,MvPolynomial.map_C,
        inverse10,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,if_pos hu]
      rw [← mul_assoc,hc,one_mul]
      rfl
    · simp only [if_neg hu,map_mul,MvPolynomial.map_C,MvPolynomial.map_X,
        inverse10,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,if_neg hu]
      rfl
  induction P using MvPolynomial.induction_on with
  | C c => simp [numerator10]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X,hgen,MvPolynomial.eval₂Hom_X']

def denominator10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) (r : Fin m → ℕ) : ℕ :=
  ∏ h, (M h 0).natAbs^(r h)

theorem denominator10_ne_zero {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) : denominator10 M r ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun h _ => pow_ne_zero _ (Int.natAbs_ne_zero.mpr (hM h)))

theorem numerator10_homogeneous {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) :
    (numerator10 M P).map (Int.castRingHom ℚ) =
      MvPolynomial.C ((∏ h, M h 0^(r h) : ℤ) : ℚ)*normalPolynomialQ10 M P := by
  rw [numerator10_map M hM]
  have hhom := homogeneous10_map (Int.castRingHom ℚ) r P hP
  rw [homogeneous10_scale r _ hhom (fun h => (M h 0 : ℚ))
    (fun u => inverse10 M (fun _ => 0) (MvPolynomial.X u))]
  congr 1
  · simp
  · rw [normalPolynomialQ10]
    have he : MvPolynomial.eval₂Hom MvPolynomial.C
        (fun u => inverse10 (K := ℚ) M (fun _ => 0) (MvPolynomial.X u)) =
        inverse10 M (fun _ => 0) := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [inverse10]
      · intro u; simp
    exact congrArg (fun f => f (P.map (Int.castRingHom ℚ))) he

theorem normalPolynomialQ10_integral_multiple {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) :
    ∃ Q : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ,
      Q.map (Int.castRingHom ℚ) = MvPolynomial.C (denominator10 M r : ℚ)*normalPolynomialQ10 M P := by
  let A : ℤ := ∏ h, M h 0^(r h)
  refine ⟨MvPolynomial.C (Int.sign A)*numerator10 M P,?_⟩
  rw [map_mul,MvPolynomial.map_C,numerator10_homogeneous M hM r P hP,← mul_assoc,
    ← MvPolynomial.C_mul]
  have he : (Int.sign A : ℚ)*(A : ℚ) = (denominator10 M r : ℚ) := by
    have hsign := Int.sign_mul_self_eq_natAbs A
    have habs : A.natAbs = denominator10 M r := by
      change Int.natAbsHom (∏ h, M h 0^r h) = _
      rw [map_prod]
      simp only [map_pow]
      rfl
    rw [habs] at hsign
    exact_mod_cast hsign
  change MvPolynomial.C ((Int.sign A : ℚ)*(A : ℚ))*normalPolynomialQ10 M P = _
  rw [he]

theorem inverse10_X_weight {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (h : Fin m) (u : SourceMultiblock10.Vars10 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : SourceMultiblock10.Vars10 m => if v.1 = h then 1 else 0)
      (inverse10 (K := K) M k (MvPolynomial.X u)) (if u.1 = h then 1 else 0) := by
  let w := fun v : SourceMultiblock10.Vars10 m => if v.1 = h then 1 else 0
  have hs : MvPolynomial.IsWeightedHomogeneous w
      (∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (M u.1 j : K)*MvPolynomial.X (u.1,j)) (w u) := by
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j _
    simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w (M u.1 j : K)).mul
      (MvPolynomial.isWeightedHomogeneous_X K w (u.1,j))
  by_cases hu : u.2 = k u.1
  · simp only [inverse10,MvPolynomial.eval₂Hom_X',if_pos hu]
    simpa only [zero_add,sub_eq_add_neg] using
      (MvPolynomial.isWeightedHomogeneous_C w ((M u.1 (k u.1) : K)⁻¹)).mul
        ((MvPolynomial.isWeightedHomogeneous_X K w u).add (rothAux_weighted_neg w _ _ hs))
  · simpa only [inverse10,MvPolynomial.eval₂Hom_X',if_neg hu] using
      MvPolynomial.isWeightedHomogeneous_X K w u

theorem homogeneous10_substitution {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) K) (hP : homogeneous10 r P)
    (f : MvPolynomial (SourceMultiblock10.Vars10 m) K →+* MvPolynomial (SourceMultiblock10.Vars10 m) K)
    (hC : ∀ c, f (MvPolynomial.C c) = MvPolynomial.C c)
    (hX : ∀ h u, MvPolynomial.IsWeightedHomogeneous
      (fun v : SourceMultiblock10.Vars10 m => if v.1 = h then 1 else 0) (f (MvPolynomial.X u))
      (if u.1 = h then 1 else 0)) : homogeneous10 r (f P) := by
  have hall (h : Fin m) : MvPolynomial.IsWeightedHomogeneous
      (fun v : SourceMultiblock10.Vars10 m => if v.1 = h then 1 else 0) (f P) (r h) := by
    let w := fun v : SourceMultiblock10.Vars10 m => if v.1 = h then 1 else 0
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
    have he : (∑ u : SourceMultiblock10.Vars10 m, d u*w u) = r h := by
      rw [← hP d hd h,← rothAux_weight_block]
      rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)]
      rfl
    rw [he] at hw
    simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w (P.coeff d)).mul hw
  intro d hd h
  rw [← rothAux_weight_block]
  exact hall h (MvPolynomial.mem_support_iff.mp hd)

theorem inverse10_homogeneous {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) K) (hP : homogeneous10 r P) :
    homogeneous10 r (inverse10 M k P) :=
  homogeneous10_substitution r P hP (inverse10 M k) (by intro c; simp [inverse10])
    (inverse10_X_weight M k)

theorem homogeneous10_blockDegree {A : Type*} [CommRing A] {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) (hP : homogeneous10 r P) (hn : P ≠ 0) (h : Fin m) :
    blockDegree10 P h = r h := by
  unfold blockDegree10
  apply le_antisymm
  · exact Finset.sup_le (fun d hd => (hP d hd h).le)
  · obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hn
    rw [← hP d hd h]
    exact Finset.le_sup (f := fun d => ∑ j : Fin 10, d (h,j)) hd

theorem normalPolynomialQ10_degrees {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) (hn : P ≠ 0) :
    homogeneous10 r (normalPolynomialQ10 M P) ∧
      (∀ h, blockDegree10 (normalPolynomialQ10 M P) h = r h) := by
  have hh := inverse10_homogeneous M (fun _ => 0) r (P.map (Int.castRingHom ℚ))
    (homogeneous10_map (Int.castRingHom ℚ) r P hP)
  exact ⟨hh,homogeneous10_blockDegree r _ hh (normalPolynomialQ10_nonzero M hM P hn)⟩

theorem normalPolynomialQ10_blockDegree {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) (hn : P ≠ 0) (h : Fin m) :
    blockDegree10 (normalPolynomialQ10 M P) h = blockDegree10 P h := by
  rw [(normalPolynomialQ10_degrees M hM r P hP hn).2 h,homogeneous10_blockDegree r P hP hn h]

theorem sourceNormalIdeal10_antitone {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    sourceNormalIdeal10 M r c₂ ≤ sourceNormalIdeal10 M r c₁ := by
  apply Ideal.span_mono
  rintro F ⟨i,hi,rfl⟩
  exact ⟨i,hc.trans hi,rfl⟩

theorem sourceStrictNormalIdeal10_iff {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (theta : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    P ∈ sourceStrictNormalIdeal10 M r theta ↔
      ∃ c : ℝ, theta < c ∧ P ∈ sourceNormalIdeal10 M r c := by
  constructor
  · intro hP
    induction hP using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨i,hi,rfl⟩ := hF
      exact ⟨_,hi,Ideal.subset_span ⟨i,le_rfl,rfl⟩⟩
    | zero => exact ⟨theta+1,by linarith,Ideal.zero_mem _⟩
    | add F G hF hG ihF ihG =>
      obtain ⟨c,hc,hFc⟩ := ihF
      obtain ⟨d,hd,hGd⟩ := ihG
      exact ⟨min c d,lt_min hc hd,Ideal.add_mem _
        (sourceNormalIdeal10_antitone M r (min_le_left c d) hFc)
        (sourceNormalIdeal10_antitone M r (min_le_right c d) hGd)⟩
    | smul a F hF ih =>
      obtain ⟨c,hc,hFc⟩ := ih
      exact ⟨c,hc,Ideal.mul_mem_left _ a hFc⟩
  · rintro ⟨c,hc,hP⟩
    apply (show sourceNormalIdeal10 M r c ≤ sourceStrictNormalIdeal10 M r theta from ?_) hP
    apply Ideal.span_le.mpr
    rintro F ⟨i,hi,rfl⟩
    exact Ideal.subset_span ⟨i,hc.trans_le hi,rfl⟩

def pivotExponent10 {m : ℕ} (k : Fin m → Fin 10) (i : Fin m → ℕ) : SourceMultiblock10.Vars10 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k u.1 then i u.1 else 0)

theorem pivotExponent10_weight {m : ℕ} (k : Fin m → Fin 10) (i r : Fin m → ℕ) :
    normalCoordinateWeight10 r k (pivotExponent10 k i) = ∑ h, (i h : ℝ)/(r h : ℝ) := by
  simp [normalCoordinateWeight10,pivotExponent10]

theorem pivotExponent10_forward {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (i : Fin m → ℕ) :
    forward10 M k (MvPolynomial.monomial (pivotExponent10 k i) 1) =
      ∏ h, (linearNormal10 (K := ℝ) M h)^(i h) := by
  rw [forward10_monomial]
  have hfree : (∏ h : Fin m, ∏ j ∈ Finset.univ.erase (k h),
      (MvPolynomial.X (h,j) : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) ^ pivotExponent10 k i (h,j)) = 1 := by
    apply Finset.prod_eq_one
    intro h _
    apply Finset.prod_eq_one
    intro j hj
    simp [pivotExponent10,(Finset.mem_erase.mp hj).1]
  simp [hfree,pivotExponent10]

theorem normalCoordinateWeight10_nonneg {m : ℕ} (r : Fin m → ℕ)
    (k : Fin m → Fin 10) (b : SourceMultiblock10.Vars10 m →₀ ℕ) : 0 ≤ normalCoordinateWeight10 r k b := by
  unfold normalCoordinateWeight10
  positivity

theorem sourceNormalIdeal10_support {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) (hP : P ∈ sourceNormalIdeal10 M r c) :
    ∀ b ∈ (inverse10 M k P).support, c ≤ normalCoordinateWeight10 r k b := by
  induction hP using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i,hi,rfl⟩ := hF
    rw [← pivotExponent10_forward M k i,inverse6_forward10 M k hk]
    intro b hb
    have he : b = pivotExponent10 k i := by symm; simpa using hb
    subst b
    simpa only [pivotExponent10_weight] using hi
  | zero => simp
  | add F G hF hG ihF ihG =>
    rw [map_add]
    intro b hb
    rcases Finset.mem_union.mp (MvPolynomial.support_add hb) with hb | hb
    · exact ihF b hb
    · exact ihG b hb
  | smul a F hF ih =>
    change ∀ b ∈ (inverse10 M k (a*F)).support, _
    rw [map_mul]
    intro b hb
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hb)
    rw [← he,normalCoordinateWeight10_add]
    exact (ih v hv).trans (le_add_of_nonneg_left (normalCoordinateWeight10_nonneg r k u))

theorem sourceNormalIdeal10_iff_support {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    P ∈ sourceNormalIdeal10 M r c ↔
      ∀ b ∈ (inverse10 M k P).support, c ≤ normalCoordinateWeight10 r k b := by
  refine ⟨sourceNormalIdeal10_support M k hk r c P,?_⟩
  intro hP
  have hsum := congrArg (forward10 M k) (inverse10 M k P).as_sum
  rw [forward6_inverse10 M k hk P,map_sum] at hsum
  rw [hsum]
  apply Ideal.sum_mem
  intro b hb
  exact forward10_monomial_mem M k r c b _ (hP b hb)

theorem sourceNormalIdeal10_iff_coeff {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    P ∈ sourceNormalIdeal10 M r c ↔
      ∀ b, normalCoordinateWeight10 r k b < c → (inverse10 M k P).coeff b = 0 := by
  rw [sourceNormalIdeal10_iff_support M k hk]
  constructor
  · intro h b hb
    by_contra hn
    exact (not_le.mpr hb) (h b (MvPolynomial.mem_support_iff.mpr hn))
  · intro h b hb
    by_contra! hn
    exact (MvPolynomial.mem_support_iff.mp hb) (h b hn)

theorem sourceStrictNormalIdeal10_iff_support {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (theta : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    P ∈ sourceStrictNormalIdeal10 M r theta ↔
      ∀ b ∈ (inverse10 M k P).support, theta < normalCoordinateWeight10 r k b := by
  rw [sourceStrictNormalIdeal10_iff]
  constructor
  · rintro ⟨c,hc,hP⟩ b hb
    exact hc.trans_le (sourceNormalIdeal10_support M k hk r c P hP b hb)
  · intro h
    by_cases hzero : inverse10 M k P = 0
    · have hz : P = 0 := by
        rw [← forward6_inverse10 M k hk P,hzero,map_zero]
      exact ⟨theta+1,by linarith,hz ▸ Ideal.zero_mem _⟩
    · have hn : (inverse10 M k P).support.Nonempty :=
        MvPolynomial.support_nonempty.mpr hzero
      obtain ⟨b,hb,hmin⟩ := Finset.exists_min_image
        (inverse10 M k P).support (normalCoordinateWeight10 r k) hn
      exact ⟨_,h b hb,(sourceNormalIdeal10_iff_support M k hk r _ P).mpr hmin⟩

theorem sourceStrictNormalIdeal10_iff_coeff {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (theta : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    P ∈ sourceStrictNormalIdeal10 M r theta ↔
      ∀ b, normalCoordinateWeight10 r k b ≤ theta → (inverse10 M k P).coeff b = 0 := by
  rw [sourceStrictNormalIdeal10_iff_support M k hk]
  constructor
  · intro h b hb
    by_contra hn
    exact (not_lt.mpr hb) (h b (MvPolynomial.mem_support_iff.mpr hn))
  · intro h b hb
    by_contra! hn
    exact (MvPolynomial.mem_support_iff.mp hb) (h b hn)

theorem sourceNormalIdeal10_upper_iff {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (theta : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    (∀ c : ℝ, theta < c → P ∉ sourceNormalIdeal10 M r c) ↔
      P ∉ sourceStrictNormalIdeal10 M r theta := by
  rw [sourceStrictNormalIdeal10_iff]
  simp only [not_exists,not_and]

theorem sourceNormalIdeal10_upper_iff_coefficient_witness {m : ℕ}
    (M : Fin m → Fin 10 → ℤ) (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0)
    (r : Fin m → ℕ) (theta : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    (∀ c : ℝ, theta < c → P ∉ sourceNormalIdeal10 M r c) ↔
      ∃ b, normalCoordinateWeight10 r k b ≤ theta ∧ (inverse10 M k P).coeff b ≠ 0 := by
  rw [sourceNormalIdeal10_upper_iff,sourceStrictNormalIdeal10_iff_coeff M k hk]
  push_neg
  rfl

theorem sourceNormalIdeal10_support_coordinate_independent {m : ℕ}
    (M : Fin m → Fin 10 → ℤ) (k j : Fin m → Fin 10)
    (hk : ∀ h, M h (k h) ≠ 0) (hj : ∀ h, M h (j h) ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    (∀ b ∈ (inverse10 M k P).support, c ≤ normalCoordinateWeight10 r k b) ↔
      ∀ b ∈ (inverse10 M j P).support, c ≤ normalCoordinateWeight10 r j b := by
  rw [← sourceNormalIdeal10_iff_support M k hk,← sourceNormalIdeal10_iff_support M j hj]

def pivotNormals10 {m : ℕ} : Fin m → Fin 10 → ℤ := fun _ j => if j = 0 then 1 else 0

theorem pivotNormals10_polynomial {m : ℕ} (h : Fin m) :
    linearNormal10 (K := ℝ) pivotNormals10 h = MvPolynomial.X (h,0) := by
  simp [linearNormal10,pivotNormals10]

theorem pivotNormals10_inverse {m : ℕ} (F : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    inverse10 pivotNormals10 (fun _ => 0) F = F := by
  have he : inverse10 (K := ℝ) (m := m) pivotNormals10 (fun _ => 0) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [inverse10]
    · intro u
      by_cases hu : u.2 = 0 <;> simp [inverse10,pivotNormals10,hu]
  exact congrArg (fun f => f F) he

theorem coordinateIdeal10_support {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (F : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    F ∈ coordinateIdeal10 r c ↔
      ∀ d ∈ F.support, c ≤ normalCoordinateWeight10 r (fun _ => 0) d := by
  have he : coordinateIdeal10 r c = sourceNormalIdeal10 pivotNormals10 r c := by
    simp only [coordinateIdeal10,sourceNormalIdeal10,pivotNormals10_polynomial]
  rw [he,sourceNormalIdeal10_iff_support pivotNormals10 (fun _ => 0)
    (by intro h; simp [pivotNormals10]),pivotNormals10_inverse]

theorem coordinateStrictIdeal10_support {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (F : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    F ∈ coordinateStrictIdeal10 r c ↔
      ∀ d ∈ F.support, c < normalCoordinateWeight10 r (fun _ => 0) d := by
  have he : coordinateStrictIdeal10 r c = sourceStrictNormalIdeal10 pivotNormals10 r c := by
    simp only [coordinateStrictIdeal10,sourceStrictNormalIdeal10,pivotNormals10_polynomial]
  rw [he,sourceStrictNormalIdeal10_iff_support pivotNormals10 (fun _ => 0)
    (by intro h; simp [pivotNormals10]),pivotNormals10_inverse]

theorem support_X_pow_mul10 {A : Type*} [CommRing A] {m : ℕ}
    (u : SourceMultiblock10.Vars10 m) (a : ℕ) (F : MvPolynomial (SourceMultiblock10.Vars10 m) A) (d : SourceMultiblock10.Vars10 m →₀ ℕ) :
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

theorem free_weight_shift10 {m : ℕ} (r : Fin m → ℕ) (u : SourceMultiblock10.Vars10 m)
    (hu : u.2 ≠ 0) (a : ℕ) (d : SourceMultiblock10.Vars10 m →₀ ℕ) :
    normalCoordinateWeight10 r (fun _ => 0) (Finsupp.single u a+d) =
      normalCoordinateWeight10 r (fun _ => 0) d := by
  rw [normalCoordinateWeight10_add]
  have hz : normalCoordinateWeight10 r (fun _ => 0) (Finsupp.single u a) = 0 := by
    rcases u with ⟨g,k⟩
    simp [normalCoordinateWeight10,Finsupp.single_apply,Prod.mk.injEq,hu]
  rw [hz,zero_add]

theorem coordinateIdeal10_saturation {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    MvPolynomial.X u^a*F ∈ coordinateIdeal10 r c ↔ F ∈ coordinateIdeal10 r c := by
  rw [coordinateIdeal10_support,coordinateIdeal10_support]
  constructor
  · intro h d hd
    have hm := h _ ((support_X_pow_mul10 u a F _).mpr ⟨d,hd,rfl⟩)
    simpa only [free_weight_shift10 r u hu] using hm
  · intro h d hd
    obtain ⟨b,hb,rfl⟩ := (support_X_pow_mul10 u a F d).mp hd
    simpa only [free_weight_shift10 r u hu] using h b hb

theorem coordinateStrictIdeal10_saturation {m : ℕ} (r : Fin m → ℕ) (c : ℝ)
    (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    MvPolynomial.X u^a*F ∈ coordinateStrictIdeal10 r c ↔ F ∈ coordinateStrictIdeal10 r c := by
  rw [coordinateStrictIdeal10_support,coordinateStrictIdeal10_support]
  constructor
  · intro h d hd
    have hm := h _ ((support_X_pow_mul10 u a F _).mpr ⟨d,hd,rfl⟩)
    simpa only [free_weight_shift10 r u hu] using hm
  · intro h d hd
    obtain ⟨b,hb,rfl⟩ := (support_X_pow_mul10 u a F d).mp hd
    simpa only [free_weight_shift10 r u hu] using h b hb

theorem normalEquiv10_free {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Fin m → Fin 10 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0) :
    normalEquiv10 (K := K) M (fun _ => 0) hM (MvPolynomial.X u) = MvPolynomial.X u ∧
      (normalEquiv10 (K := K) M (fun _ => 0) hM).symm (MvPolynomial.X u) = MvPolynomial.X u := by
  constructor
  · change forward10 M (fun _ => 0) (MvPolynomial.X u) = _
    simp [forward10,hu]
  · change inverse10 M (fun _ => 0) (MvPolynomial.X u) = _
    simp [inverse10,hu]

theorem sourceNormalIdeal10_saturation {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    MvPolynomial.X u^a*F ∈ sourceNormalIdeal10 M r c ↔ F ∈ sourceNormalIdeal10 M r c := by
  rw [inverse10_ideal_iff M hM,inverse10_ideal_iff M hM,map_mul,map_pow]
  have hx : inverse10 (K := ℝ) M (fun _ => 0) (MvPolynomial.X u) = MvPolynomial.X u :=
    (normalEquiv10_free M hM u hu).2
  rw [hx,coordinateIdeal10_saturation r c u hu]

theorem sourceStrictNormalIdeal10_saturation {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0) (a : ℕ) (F : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    MvPolynomial.X u^a*F ∈ sourceStrictNormalIdeal10 M r c ↔ F ∈ sourceStrictNormalIdeal10 M r c := by
  rw [inverse10_strictIdeal_iff M hM,inverse10_strictIdeal_iff M hM,map_mul,map_pow]
  have hx : inverse10 (K := ℝ) M (fun _ => 0) (MvPolynomial.X u) = MvPolynomial.X u :=
    (normalEquiv10_free M hM u hu).2
  rw [hx,coordinateStrictIdeal10_saturation r c u hu]

def zeroSpecialize10 {A : Type*} [CommRing A] {m : ℕ} (u : SourceMultiblock10.Vars10 m) :
    MvPolynomial (SourceMultiblock10.Vars10 m) A →+* MvPolynomial (SourceMultiblock10.Vars10 m) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v => if v = u then 0 else MvPolynomial.X v)

theorem zeroSpecialize10_monomial {A : Type*} [CommRing A] {m : ℕ}
    (u : SourceMultiblock10.Vars10 m) (d : SourceMultiblock10.Vars10 m →₀ ℕ) (c : A) :
    zeroSpecialize10 u (MvPolynomial.monomial d c) =
      if d u = 0 then MvPolynomial.monomial d c else 0 := by
  rw [zeroSpecialize10,MvPolynomial.eval₂Hom_monomial]
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
    have hz : (∏ v : SourceMultiblock10.Vars10 m,
        (if v = u then 0 else MvPolynomial.X v)^d v) = (0 : MvPolynomial (SourceMultiblock10.Vars10 m) A) := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [hd]
    rw [hz,mul_zero]

theorem zeroSpecialize10_coeff {A : Type*} [CommRing A] {m : ℕ}
    (u : SourceMultiblock10.Vars10 m) (F : MvPolynomial (SourceMultiblock10.Vars10 m) A) (d : SourceMultiblock10.Vars10 m →₀ ℕ) :
    (zeroSpecialize10 u F).coeff d = if d u = 0 then F.coeff d else 0 := by
  induction F using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [zeroSpecialize10_monomial]
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

def minimumExponent10 {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) : ℕ :=
  if hn : P = 0 then 0 else
    (Classical.choose (Finset.exists_min_image P.support (fun d => d u)
      (MvPolynomial.support_nonempty.mpr hn))) u

theorem minimumExponent10_spec {m : ℕ} (u : SourceMultiblock10.Vars10 m)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0) :
    ∃ d ∈ P.support, d u = minimumExponent10 u P ∧
      ∀ b ∈ P.support, minimumExponent10 u P ≤ b u := by
  simp only [minimumExponent10,dif_neg hn]
  have hex := Finset.exists_min_image P.support (fun d => d u) (MvPolynomial.support_nonempty.mpr hn)
  exact ⟨Classical.choose hex,(Classical.choose_spec hex).1,rfl,(Classical.choose_spec hex).2⟩

def extracted10 {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) :
    MvPolynomial (SourceMultiblock10.Vars10 m) ℤ := P.divMonomial (Finsupp.single u (minimumExponent10 u P))

def eliminate10 {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) :
    MvPolynomial (SourceMultiblock10.Vars10 m) ℤ := zeroSpecialize10 u (extracted10 u P)

theorem extracted10_coeff {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) :
    (extracted10 u P).coeff d = P.coeff (Finsupp.single u (minimumExponent10 u P)+d) := rfl

theorem extracted10_factor {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (hn : P ≠ 0) : P = MvPolynomial.X u^(minimumExponent10 u P)*extracted10 u P := by
  obtain ⟨b,hb,hbe,hmin⟩ := minimumExponent10_spec u P hn
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.coeff_monomial_mul']
  by_cases hs : Finsupp.single u (minimumExponent10 u P) ≤ d
  · rw [if_pos hs,one_mul,extracted10_coeff,add_tsub_cancel_of_le hs]
  · rw [if_neg hs]
    apply MvPolynomial.not_mem_support_iff.mp
    intro hd
    exact hs (Finsupp.single_le_iff.mpr (hmin d hd))

theorem eliminate10_coeff {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) :
    (eliminate10 u P).coeff d = if d u = 0 then
      P.coeff (Finsupp.single u (minimumExponent10 u P)+d) else 0 := by
  rw [eliminate10,zeroSpecialize10_coeff,extracted10_coeff]

theorem eliminate10_nonzero {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (hn : P ≠ 0) : eliminate10 u P ≠ 0 := by
  obtain ⟨b,hb,hbe,hmin⟩ := minimumExponent10_spec u P hn
  let s := Finsupp.single u (minimumExponent10 u P)
  have hs : s ≤ b := Finsupp.single_le_iff.mpr (hmin b hb)
  have hz : (b-s) u = 0 := by simp [s,Finsupp.tsub_apply,hbe]
  have hcoeff : (eliminate10 u P).coeff (b-s) ≠ 0 := by
    rw [eliminate10_coeff,if_pos hz,show Finsupp.single u (minimumExponent10 u P) = s from rfl,
      add_tsub_cancel_of_le hs]
    exact MvPolynomial.mem_support_iff.mp hb
  exact MvPolynomial.ne_zero_iff.mpr ⟨b-s,hcoeff⟩

theorem extracted10_nonzero {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (hn : P ≠ 0) : extracted10 u P ≠ 0 := by
  intro hz
  apply eliminate10_nonzero u P hn
  rw [eliminate10,hz,map_zero]

theorem eliminate10_support_source {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) (hd : d ∈ (eliminate10 u P).support) :
    d u = 0 ∧ Finsupp.single u (minimumExponent10 u P)+d ∈ P.support := by
  have hn := MvPolynomial.mem_support_iff.mp hd
  rw [eliminate10_coeff] at hn
  by_cases hz : d u = 0
  · exact ⟨hz,MvPolynomial.mem_support_iff.mpr (by simpa [hz] using hn)⟩
  · simp [hz] at hn

theorem eliminate10_height {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) :
    height10 (eliminate10 u P) ≤ height10 P := by
  apply Finset.sup_le
  intro d hd
  obtain ⟨hz,hp⟩ := eliminate10_support_source u P d hd
  change ((eliminate10 u P).coeff d).natAbs ≤ height10 P
  rw [eliminate10_coeff,if_pos hz]
  exact Finset.le_sup (f := fun b => (P.coeff b).natAbs) hp

theorem eliminate10_blockDegree {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (h : Fin m) : blockDegree10 (eliminate10 u P) h ≤ blockDegree10 P h := by
  apply Finset.sup_le
  intro d hd
  have hp := (eliminate10_support_source u P d hd).2
  calc
    (∑ j : Fin 10, d (h,j)) ≤ ∑ j : Fin 10, (Finsupp.single u (minimumExponent10 u P)+d) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.le_add_left _ _
    _ ≤ blockDegree10 P h := Finset.le_sup (f := fun b => ∑ j : Fin 10, b (h,j)) hp

theorem eliminate10_preserves_independence {m : ℕ} (u v : SourceMultiblock10.Vars10 m)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hv : ∀ d ∈ P.support, d v = 0) :
    ∀ d ∈ (eliminate10 u P).support, d v = 0 := by
  intro d hd
  have he := hv _ (eliminate10_support_source u P d hd).2
  simp only [Finsupp.add_apply] at he
  omega

theorem eliminate10_homogeneous {m : ℕ} (u : SourceMultiblock10.Vars10 m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (r : Fin m → ℕ) (hP : homogeneous10 r P) :
    homogeneous10 (fun h => r h - if u.1 = h then minimumExponent10 u P else 0) (eliminate10 u P) := by
  intro d hd h
  have he := hP _ (eliminate10_support_source u P d hd).2 h
  have hs : (∑ j : Fin 10, (Finsupp.single u (minimumExponent10 u P)) (h,j)) =
      if u.1 = h then minimumExponent10 u P else 0 := by
    rcases u with ⟨g,k⟩
    by_cases hg : g = h
    · subst g; simp [Finsupp.single_apply,Prod.mk.injEq,eq_comm]
    · simp [Finsupp.single_apply,Prod.mk.injEq,hg]
  simp only [Finsupp.add_apply,Finset.sum_add_distrib,hs] at he
  change (∑ j : Fin 10, d (h,j)) = r h - if u.1 = h then minimumExponent10 u P else 0
  omega

def zeroNormalCoefficient10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) (u : SourceMultiblock10.Vars10 m)
    (h : Fin m) (j : Fin 10) : ℤ := if (h,j) = u then 0 else M h j

theorem zeroSpecialize10_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {m : ℕ} (u : SourceMultiblock10.Vars10 m) (F : MvPolynomial (SourceMultiblock10.Vars10 m) A) :
    (zeroSpecialize10 u F).map f = zeroSpecialize10 u (F.map f) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [zeroSpecialize10]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F v hF =>
    simp only [map_mul,hF,MvPolynomial.map_X]
    by_cases hv : v = u <;> simp [zeroSpecialize10,hv]

theorem zeroNormalCoefficient10_pivot {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0) (h : Fin m) :
    zeroNormalCoefficient10 M u h 0 = M h 0 := by
  have he : (h,0) ≠ u := by intro he; exact hu (congrArg Prod.snd he).symm
  simp [zeroNormalCoefficient10,he]

theorem zeroSpecialize10_normal {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (u : SourceMultiblock10.Vars10 m) (h : Fin m) :
    zeroSpecialize10 u (linearNormal10 (K := ℝ) M h) = linearNormal10 (K := ℝ) (zeroNormalCoefficient10 M u) h := by
  simp only [linearNormal10,map_sum,map_mul,zeroSpecialize10,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X']
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : (h,j) = u <;> simp [zeroNormalCoefficient10,he]

theorem zeroSpecialize10_normal_products {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (u : SourceMultiblock10.Vars10 m) (i : Fin m → ℕ) :
    zeroSpecialize10 u (∏ h, linearNormal10 (K := ℝ) M h^(i h)) =
      ∏ h, linearNormal10 (K := ℝ) (zeroNormalCoefficient10 M u) h^(i h) := by
  simp only [map_prod,map_pow,zeroSpecialize10_normal]

theorem zeroSpecialize10_ideal_map {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (u : SourceMultiblock10.Vars10 m) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (zeroSpecialize10 u) (sourceNormalIdeal10 M r c) =
      sourceNormalIdeal10 (zeroNormalCoefficient10 M u) r c := by
  unfold sourceNormalIdeal10
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,zeroSpecialize10_normal_products M u i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,zeroSpecialize10_normal_products M u i⟩

theorem zeroSpecialize10_strictIdeal_map {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (u : SourceMultiblock10.Vars10 m) (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map (zeroSpecialize10 u) (sourceStrictNormalIdeal10 M r c) =
      sourceStrictNormalIdeal10 (zeroNormalCoefficient10 M u) r c := by
  unfold sourceStrictNormalIdeal10
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨G,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,zeroSpecialize10_normal_products M u i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,zeroSpecialize10_normal_products M u i⟩

theorem eliminate10_closed {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c) :
    (eliminate10 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 (zeroNormalCoefficient10 M u) r c := by
  have hQ : (extracted10 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c := by
    apply (sourceNormalIdeal10_saturation M hM r c u hu (minimumExponent10 u P) _).mp
    rw [extracted10_factor u P hn,map_mul,map_pow,MvPolynomial.map_X] at hP
    exact hP
  rw [eliminate10,zeroSpecialize10_map,← zeroSpecialize10_ideal_map M u r c]
  exact Ideal.mem_map_of_mem (zeroSpecialize10 u) hQ

theorem eliminate10_strict {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c) :
    (eliminate10 u P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 (zeroNormalCoefficient10 M u) r c := by
  have hQ : (extracted10 u P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c := by
    apply (sourceStrictNormalIdeal10_saturation M hM r c u hu (minimumExponent10 u P) _).mp
    rw [extracted10_factor u P hn,map_mul,map_pow,MvPolynomial.map_X] at hP
    exact hP
  rw [eliminate10,zeroSpecialize10_map,← zeroSpecialize10_strictIdeal_map M u r c]
  exact Ideal.mem_map_of_mem (zeroSpecialize10 u) hQ

theorem eliminate10_step {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (u : SourceMultiblock10.Vars10 m) (hu : u.2 ≠ 0)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0) :
    P = MvPolynomial.X u^(minimumExponent10 u P)*extracted10 u P ∧
      extracted10 u P ≠ 0 ∧ eliminate10 u P ≠ 0 ∧
      height10 (eliminate10 u P) ≤ height10 P ∧
      (∀ h, blockDegree10 (eliminate10 u P) h ≤ blockDegree10 P h) ∧
      (∀ d ∈ (eliminate10 u P).support, d u = 0) ∧
      (∀ h, zeroNormalCoefficient10 M u h 0 = M h 0 ∧ zeroNormalCoefficient10 M u h 0 ≠ 0) ∧
      (∀ r c, P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c →
        (eliminate10 u P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 (zeroNormalCoefficient10 M u) r c) ∧
      (∀ r c, P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c →
        (eliminate10 u P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 (zeroNormalCoefficient10 M u) r c) := by
  refine ⟨extracted10_factor u P hn,extracted10_nonzero u P hn,eliminate10_nonzero u P hn,
    eliminate10_height u P,eliminate10_blockDegree u P,fun d hd => (eliminate10_support_source u P d hd).1,
    ?_,fun r c => eliminate10_closed M hM u hu r c P hn,fun r c => eliminate10_strict M hM u hu r c P hn⟩
  intro h
  rw [zeroNormalCoefficient10_pivot M u hu h]
  exact ⟨rfl,hM h⟩

def eliminateList10 {m : ℕ} : List (SourceMultiblock10.Vars10 m) → MvPolynomial (SourceMultiblock10.Vars10 m) ℤ → MvPolynomial (SourceMultiblock10.Vars10 m) ℤ
  | [],P => P
  | u::us,P => eliminateList10 us (eliminate10 u P)

def specializeNormalsList10 {m : ℕ} : List (SourceMultiblock10.Vars10 m) → (Fin m → Fin 10 → ℤ) → Fin m → Fin 10 → ℤ
  | [],M => M
  | u::us,M => specializeNormalsList10 us (zeroNormalCoefficient10 M u)

theorem specializeNormalsList10_coeff {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (M : Fin m → Fin 10 → ℤ) (h : Fin m) (j : Fin 10) :
    specializeNormalsList10 us M h j = if (h,j) ∈ us then 0 else M h j := by
  induction us generalizing M with
  | nil => simp [specializeNormalsList10]
  | cons u us ih =>
    rw [specializeNormalsList10,ih]
    by_cases ht : (h,j) ∈ us <;> by_cases he : (h,j) = u <;>
      simp [zeroNormalCoefficient10,ht,he]

theorem specializeNormalsList10_pivot {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    specializeNormalsList10 us M h 0 = M h 0 := by
  rw [specializeNormalsList10_coeff,if_neg]
  intro he
  exact hus (h,0) he rfl

theorem eliminateList10_nonzero {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0) : eliminateList10 us P ≠ 0 := by
  induction us generalizing P with
  | nil => exact hn
  | cons u us ih => exact ih _ (eliminate10_nonzero u P hn)

theorem eliminateList10_height {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) : height10 (eliminateList10 us P) ≤ height10 P := by
  induction us generalizing P with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _).trans (eliminate10_height u P)

theorem eliminateList10_blockDegree {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (h : Fin m) :
    blockDegree10 (eliminateList10 us P) h ≤ blockDegree10 P h := by
  induction us generalizing P with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _).trans (eliminate10_blockDegree u P h)

theorem eliminateList10_preserves_independence {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (v : SourceMultiblock10.Vars10 m) (hv : ∀ d ∈ P.support, d v = 0) :
    ∀ d ∈ (eliminateList10 us P).support, d v = 0 := by
  induction us generalizing P with
  | nil => exact hv
  | cons u us ih => exact ih _ (eliminate10_preserves_independence u v P hv)

theorem eliminateList10_independent {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) :
    ∀ v ∈ us, ∀ d ∈ (eliminateList10 us P).support, d v = 0 := by
  induction us generalizing P with
  | nil => simp
  | cons u us ih =>
    intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      exact eliminateList10_preserves_independence us (eliminate10 u P) u
        (fun d hd => (eliminate10_support_source u P d hd).1)
    · exact ih _ v hv

theorem eliminateList10_closed {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 10 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c) :
    (eliminateList10 us P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 (specializeNormalsList10 us M) r c := by
  induction us generalizing M P with
  | nil => exact hP
  | cons u us ih =>
    have hu := hus u (by simp)
    have htail : ∀ v ∈ us, v.2 ≠ 0 := fun v hv => hus v (by simp [hv])
    exact ih htail (zeroNormalCoefficient10 M u)
      (fun h => by rw [zeroNormalCoefficient10_pivot M u hu h]; exact hM h)
      (eliminate10 u P) (eliminate10_nonzero u P hn) (eliminate10_closed M hM u hu r c P hn hP)

theorem eliminateList10_strict {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (hus : ∀ u ∈ us, u.2 ≠ 0) (M : Fin m → Fin 10 → ℤ) (hM : ∀ h, M h 0 ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c) :
    (eliminateList10 us P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 (specializeNormalsList10 us M) r c := by
  induction us generalizing M P with
  | nil => exact hP
  | cons u us ih =>
    have hu := hus u (by simp)
    have htail : ∀ v ∈ us, v.2 ≠ 0 := fun v hv => hus v (by simp [hv])
    exact ih htail (zeroNormalCoefficient10 M u)
      (fun h => by rw [zeroNormalCoefficient10_pivot M u hu h]; exact hM h)
      (eliminate10 u P) (eliminate10_nonzero u P hn) (eliminate10_strict M hM u hu r c P hn hP)

def excessVariables10 (m : ℕ) : Finset (SourceMultiblock10.Vars10 m) :=
  Finset.univ.product ({2,3,4,5,6,7,8,9} : Finset (Fin 10))

theorem mem_excessVariables10 {m : ℕ} (u : SourceMultiblock10.Vars10 m) :
    u ∈ excessVariables10 m ↔ 2 ≤ u.2.val := by
  rcases u with ⟨h,k⟩
  fin_cases k <;> simp [excessVariables10]

theorem card_excessVariables10 (m : ℕ) : (excessVariables10 m).card = 8*m := by
  have hc : ({2,3,4,5,6,7,8,9} : Finset (Fin 10)).card = 8 := by decide
  simpa [excessVariables10,hc,Nat.mul_comm] using
    Finset.card_product (Finset.univ : Finset (Fin m)) ({2,3,4,5,6,7,8,9} : Finset (Fin 10))

def reducedNormals10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) : Fin m → Fin 10 → ℤ :=
  specializeNormalsList10 (excessVariables10 m).toList M

def reducedPolynomial10 {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ :=
  eliminateList10 (excessVariables10 m).toList P

theorem reducedNormals10_coeff {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) (j : Fin 10) :
    reducedNormals10 M h j = if 2 ≤ j.val then 0 else M h j := by
  simp only [reducedNormals10,specializeNormalsList10_coeff,Finset.mem_toList,mem_excessVariables10]

theorem reducedNormals10_first_two {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    reducedNormals10 M h 0 = M h 0 ∧ reducedNormals10 M h 1 = M h 1 := by
  simp [reducedNormals10_coeff]

theorem reducedNormals10_polynomial {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    linearNormal10 (K := ℝ) (reducedNormals10 M) h =
      MvPolynomial.C (M h 0 : ℝ)*MvPolynomial.X (h,0) +
        MvPolynomial.C (M h 1 : ℝ)*MvPolynomial.X (h,1) := by
  norm_num [linearNormal10,reducedNormals10_coeff,Fin.sum_univ_succ]

theorem reducedPolynomial10_support {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) :
    ∀ d ∈ (reducedPolynomial10 P).support, ∀ u : SourceMultiblock10.Vars10 m, 2 ≤ u.2.val → d u = 0 := by
  intro d hd u hu
  exact eliminateList10_independent (excessVariables10 m).toList P u
    (Finset.mem_toList.mpr ((mem_excessVariables10 u).mpr hu)) d hd

theorem reducedPolynomial10_nonzero {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0) :
    reducedPolynomial10 P ≠ 0 := eliminateList10_nonzero _ P hn

theorem reducedPolynomial10_height {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) :
    height10 (reducedPolynomial10 P) ≤ height10 P := eliminateList10_height _ P

theorem reducedPolynomial10_blockDegree {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (h : Fin m) :
    blockDegree10 (reducedPolynomial10 P) h ≤ blockDegree10 P h := eliminateList10_blockDegree _ P h

theorem excessVariables10_free {m : ℕ} : ∀ u ∈ (excessVariables10 m).toList, u.2 ≠ 0 := by
  intro u hu hz
  have he := (mem_excessVariables10 u).mp (Finset.mem_toList.mp hu)
  rw [hz] at he
  norm_num at he

theorem reducedPolynomial10_closed {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c) :
    (reducedPolynomial10 P).map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 (reducedNormals10 M) r c :=
  eliminateList10_closed _ excessVariables10_free M hM r c P hn hP

theorem reducedPolynomial10_strict {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ) (c : ℝ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hn : P ≠ 0)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c) :
    (reducedPolynomial10 P).map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 (reducedNormals10 M) r c :=
  eliminateList10_strict _ excessVariables10_free M hM r c P hn hP

def eliminatedDegrees10 {m : ℕ} : List (SourceMultiblock10.Vars10 m) → MvPolynomial (SourceMultiblock10.Vars10 m) ℤ →
    (Fin m → ℕ) → Fin m → ℕ
  | [],_,r => r
  | u::us,P,r => eliminatedDegrees10 us (eliminate10 u P)
      (fun h => r h - if u.1 = h then minimumExponent10 u P else 0)

theorem eliminateList10_homogeneous {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (r : Fin m → ℕ) (hP : homogeneous10 r P) :
    homogeneous10 (eliminatedDegrees10 us P r) (eliminateList10 us P) := by
  induction us generalizing P r with
  | nil => exact hP
  | cons u us ih => exact ih _ _ (eliminate10_homogeneous u P r hP)

theorem eliminatedDegrees10_le {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (r : Fin m → ℕ) (h : Fin m) :
    eliminatedDegrees10 us P r h ≤ r h := by
  induction us generalizing P r with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _ _).trans (Nat.sub_le _ _)

theorem eliminatedDegrees10_actual {m : ℕ} (us : List (SourceMultiblock10.Vars10 m))
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (r : Fin m → ℕ) (hP : homogeneous10 r P)
    (hn : P ≠ 0) (h : Fin m) :
    eliminatedDegrees10 us P r h = blockDegree10 (eliminateList10 us P) h :=
  (homogeneous10_blockDegree _ _ (eliminateList10_homogeneous us P r hP)
    (eliminateList10_nonzero us P hn) h).symm

theorem reducedPolynomial10_homogeneous {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (r : Fin m → ℕ) (hP : homogeneous10 r P) (hn : P ≠ 0) :
    homogeneous10 (blockDegree10 (reducedPolynomial10 P)) (reducedPolynomial10 P) ∧
      (∀ h, blockDegree10 (reducedPolynomial10 P) h ≤ r h) := by
  have he : eliminatedDegrees10 (excessVariables10 m).toList P r =
      blockDegree10 (reducedPolynomial10 P) := by
    funext h
    exact eliminatedDegrees10_actual _ P r hP hn h
  constructor
  · rw [← he]
    exact eliminateList10_homogeneous _ P r hP
  · intro h
    rw [← he]
    exact eliminatedDegrees10_le _ P r h

def scalar10 {A : Type*} [CommRing A] {m : ℕ} :
    MvPolynomial (SourceMultiblock10.Vars10 m) A →+* MvPolynomial (Fin m) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = 0 then MvPolynomial.X u.1 else if u.2 = 1 then 1 else 0)

theorem scalar10_generators {A : Type*} [CommRing A] {m : ℕ} :
    (∀ c : A, scalar10 (MvPolynomial.C c : MvPolynomial (SourceMultiblock10.Vars10 m) A) = MvPolynomial.C c) ∧
      (∀ u : SourceMultiblock10.Vars10 m, scalar10 (MvPolynomial.X u : MvPolynomial (SourceMultiblock10.Vars10 m) A) =
        if u.2 = 0 then MvPolynomial.X u.1 else if u.2 = 1 then 1 else 0) := by
  constructor <;> intro x <;> simp [scalar10]

theorem scalar10_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) :
    (scalar10 P).map f = scalar10 (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [scalar10]
  | add F G hF hG => simp only [map_add,hF,hG]
  | mul_X F u hF =>
    simp only [map_mul,hF,MvPolynomial.map_X]
    by_cases h0 : u.2 = 0 <;> by_cases h1 : u.2 = 1 <;> simp [scalar10,h0,h1]

def scalarExponent10 {m : ℕ} (d : SourceMultiblock10.Vars10 m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun h => d (h,0))

def binarySupport10 {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) : Prop :=
  ∀ d ∈ P.support, ∀ u : SourceMultiblock10.Vars10 m, 2 ≤ u.2.val → d u = 0

theorem binary_block_sum10 {m : ℕ} (d : SourceMultiblock10.Vars10 m →₀ ℕ)
    (hd : ∀ u : SourceMultiblock10.Vars10 m, 2 ≤ u.2.val → d u = 0) (h : Fin m) :
    (∑ j : Fin 10, d (h,j)) = d (h,0)+d (h,1) := by
  have hs : (∑ j ∈ ({0,1} : Finset (Fin 10)), d (h,j)) = ∑ j : Fin 10, d (h,j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply hd (h,j)
    fin_cases j <;> simp_all
  exact hs.symm.trans (by simp)

theorem scalar10_monomial {A : Type*} [CommRing A] {m : ℕ}
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) (hd : ∀ u : SourceMultiblock10.Vars10 m, 2 ≤ u.2.val → d u = 0) (c : A) :
    scalar10 (MvPolynomial.monomial d c) = MvPolynomial.monomial (scalarExponent10 d) c := by
  rw [scalar10,MvPolynomial.eval₂Hom_monomial,MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [Finset.prod_eq_single (0 : Fin 10)]
  · simp [scalarExponent10]
  · intro j _ hj0
    by_cases hj1 : j = 1
    · simp [hj1]
    · have hz := hd (h,j) (by fin_cases j <;> simp_all)
      simp [hz]
  · simp

theorem scalarExponent10_inj {m : ℕ} (r : Fin m → ℕ) (d e : SourceMultiblock10.Vars10 m →₀ ℕ)
    (hd : ∀ u : SourceMultiblock10.Vars10 m, 2 ≤ u.2.val → d u = 0)
    (he : ∀ u : SourceMultiblock10.Vars10 m, 2 ≤ u.2.val → e u = 0)
    (hdr : ∀ h, (∑ j : Fin 10, d (h,j)) = r h)
    (her : ∀ h, (∑ j : Fin 10, e (h,j)) = r h)
    (hp : scalarExponent10 d = scalarExponent10 e) : d = e := by
  apply Finsupp.ext
  rintro ⟨h,j⟩
  have h0 : d (h,0) = e (h,0) := congrArg (fun b => b h) hp
  have hd' := hdr h
  have he' := her h
  rw [binary_block_sum10 d hd h] at hd'
  rw [binary_block_sum10 e he h] at he'
  by_cases hj0 : j = 0
  · subst j; exact h0
  by_cases hj1 : j = 1
  · subst j; omega
  have hj : 2 ≤ j.val := by fin_cases j <;> simp_all
  rw [hd (h,j) hj,he (h,j) hj]

theorem scalarExponent10_injOn {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (hh : homogeneous10 r P) (hb : binarySupport10 P) :
    Set.InjOn scalarExponent10 (↑P.support : Set (SourceMultiblock10.Vars10 m →₀ ℕ)) := by
  intro d hd e he hp
  exact scalarExponent10_inj r d e (hb d hd) (hb e he) (hh d hd) (hh e he) hp

theorem scalar10_as_sum {A : Type*} [CommRing A] {m : ℕ}
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) A) (hb : binarySupport10 P) :
    scalar10 P = ∑ d ∈ P.support, MvPolynomial.monomial (scalarExponent10 d) (P.coeff d) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact scalar10_monomial d (hb d hd) (P.coeff d)

theorem scalar10_coeff {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (hh : homogeneous10 r P) (hb : binarySupport10 P)
    (d : SourceMultiblock10.Vars10 m →₀ ℕ) (hd : d ∈ P.support) :
    (scalar10 P).coeff (scalarExponent10 d) = P.coeff d := by
  rw [scalar10_as_sum P hb,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hed
    rw [MvPolynomial.coeff_monomial,if_neg]
    intro hp
    exact hed (scalarExponent10_injOn r P hh hb he hd hp)
  · intro hn
    exact False.elim (hn hd)

theorem scalar10_support {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (hh : homogeneous10 r P) (hb : binarySupport10 P) :
    (scalar10 P).support = P.support.image scalarExponent10 := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [scalar10_as_sum P hb] at he
    obtain ⟨d,hd,hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
    have heq : e = scalarExponent10 d := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (R := A) hm)
    exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
  · intro e he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
    rw [MvPolynomial.mem_support_iff,scalar10_coeff r P hh hb d hd]
    exact MvPolynomial.mem_support_iff.mp hd

def scalarSupportEquiv10 {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (hh : homogeneous10 r P) (hb : binarySupport10 P) :
    {d // d ∈ P.support} ≃ {e // e ∈ (scalar10 P).support} :=
  Equiv.ofBijective (fun d => ⟨scalarExponent10 d.val,
    by rw [scalar10_support r P hh hb]; exact Finset.mem_image.mpr ⟨d.val,d.property,rfl⟩⟩) (by
    constructor
    · intro d e he
      apply Subtype.ext
      exact scalarExponent10_injOn r P hh hb d.property e.property (congrArg Subtype.val he)
    · intro e
      have he : e.val ∈ P.support.image scalarExponent10 :=
        Eq.mp (congrArg (fun s : Finset (Fin m →₀ ℕ) => e.val ∈ s)
          (scalar10_support r P hh hb)) e.property
      obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp he
      exact ⟨⟨d,hd⟩,Subtype.ext hde⟩)

theorem scalar10_nonzero {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (hh : homogeneous10 r P) (hb : binarySupport10 P) (hn : P ≠ 0) : scalar10 P ≠ 0 := by
  obtain ⟨d,hd⟩ := MvPolynomial.support_nonempty.mpr hn
  apply MvPolynomial.ne_zero_iff.mpr
  refine ⟨scalarExponent10 d,?_⟩
  rw [scalar10_coeff r P hh hb d hd]
  exact MvPolynomial.mem_support_iff.mp hd

theorem scalar10_height {m : ℕ} (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (hh : homogeneous10 r P) (hb : binarySupport10 P) :
    JSP000334.rothIntegerHeight (scalar10 P) = height10 P := by
  unfold JSP000334.rothIntegerHeight height10
  rw [scalar10_support r P hh hb,Finset.sup_image]
  apply Finset.sup_congr rfl
  intro d hd
  change ((scalar10 P).coeff (scalarExponent10 d)).natAbs = (P.coeff d).natAbs
  rw [scalar10_coeff r P hh hb d hd]

theorem scalar10_support_degree {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (hh : homogeneous10 r P) (hb : binarySupport10 P) :
    ∀ e ∈ (scalar10 P).support, ∀ h, e h ≤ r h := by
  intro e he h
  rw [scalar10_support r P hh hb] at he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
  change d (h,0) ≤ r h
  rw [← hh d hd h,binary_block_sum10 d (hb d hd) h]
  exact Nat.le_add_right _ _

theorem scalar10_degree {A : Type*} [CommRing A] {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) A)
    (hh : homogeneous10 r P) (hb : binarySupport10 P) (h : Fin m) :
    (scalar10 P).degreeOf h ≤ r h :=
  MvPolynomial.degreeOf_le_iff.mpr (fun e he => scalar10_support_degree r P hh hb e he h)

def scalarNormal10 {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    MvPolynomial (Fin m) ℝ :=
  MvPolynomial.C (M h 0 : ℝ)*MvPolynomial.X h + MvPolynomial.C (M h 1 : ℝ)

theorem scalar10_normal {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    scalar10 (linearNormal10 (K := ℝ) (reducedNormals10 M) h) = scalarNormal10 M h := by
  simp only [reducedNormals10_polynomial,map_add,map_mul,
    (scalar10_generators (A := ℝ)).1,(scalar10_generators (A := ℝ)).2]
  simp [scalarNormal10]

theorem scalar10_normal_products {m : ℕ} (M : Fin m → Fin 10 → ℤ) (i : Fin m → ℕ) :
    scalar10 (∏ h, linearNormal10 (K := ℝ) (reducedNormals10 M) h^(i h)) =
      ∏ h, scalarNormal10 M h^(i h) := by
  simp only [map_prod,map_pow,scalar10_normal]

def scalarIdeal10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, scalarNormal10 M h^(i h)}

def scalarStrictIdeal10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) : Ideal (MvPolynomial (Fin m) ℝ) :=
  Ideal.span {P | ∃ i : Fin m → ℕ, c < ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    P = ∏ h, scalarNormal10 M h^(i h)}

theorem scalar10_ideal_map {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map scalar10 (sourceNormalIdeal10 (reducedNormals10 M) r c) = scalarIdeal10 M r c := by
  unfold sourceNormalIdeal10 scalarIdeal10
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,scalar10_normal_products M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,scalar10_normal_products M i⟩

theorem scalar10_strictIdeal_map {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) :
    Ideal.map scalar10 (sourceStrictNormalIdeal10 (reducedNormals10 M) r c) = scalarStrictIdeal10 M r c := by
  unfold sourceStrictNormalIdeal10 scalarStrictIdeal10
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨i,hi,scalar10_normal_products M i⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i,hi,rfl⟩,scalar10_normal_products M i⟩

theorem scalar10_closed {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 (reducedNormals10 M) r c) :
    (scalar10 P).map (Int.castRingHom ℝ) ∈ scalarIdeal10 M r c := by
  rw [scalar10_map,← scalar10_ideal_map M r c]
  exact Ideal.mem_map_of_mem scalar10 hP

theorem scalar10_strict {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (hP : P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 (reducedNormals10 M) r c) :
    (scalar10 P).map (Int.castRingHom ℝ) ∈ scalarStrictIdeal10 M r c := by
  rw [scalar10_map,← scalar10_strictIdeal_map M r c]
  exact Ideal.mem_map_of_mem scalar10 hP


end
end CompoundFeasibility.SchmidtPolynomial10
