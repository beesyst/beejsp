import SubspaceBridge.SourceSchmidtParameters6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtIndexSemantics6
open Auxiliary6 SourceNormalIndex SourceMultiblock

theorem sourceNormalIdeal6_antitone {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    sourceNormalIdeal6 M r c₂ ≤ sourceNormalIdeal6 M r c₁ := by
  apply Ideal.span_mono
  rintro F ⟨i,hi,rfl⟩
  exact ⟨i,hc.trans hi,rfl⟩

def sourceStrictNormalIdeal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (theta : ℝ) : Ideal (MvPolynomial (Vars6 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, theta < ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, (normalPolynomial6 M h)^(i h)}

theorem sourceStrictNormalIdeal6_iff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (theta : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceStrictNormalIdeal6 M r theta ↔
      ∃ c : ℝ, theta < c ∧ P ∈ sourceNormalIdeal6 M r c := by
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
        (sourceNormalIdeal6_antitone M r (min_le_left c d) hFc)
        (sourceNormalIdeal6_antitone M r (min_le_right c d) hGd)⟩
    | smul a F hF ih =>
      obtain ⟨c,hc,hFc⟩ := ih
      exact ⟨c,hc,Ideal.mul_mem_left _ a hFc⟩
  · rintro ⟨c,hc,hP⟩
    apply (show sourceNormalIdeal6 M r c ≤ sourceStrictNormalIdeal6 M r theta from ?_) hP
    apply Ideal.span_le.mpr
    rintro F ⟨i,hi,rfl⟩
    exact Ideal.subset_span ⟨i,hc.trans_le hi,rfl⟩

def pivotExponent6 {m : ℕ} (k : Fin m → Fin 6) (i : Fin m → ℕ) : Vars6 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k u.1 then i u.1 else 0)

theorem pivotExponent6_weight {m : ℕ} (k : Fin m → Fin 6) (i r : Fin m → ℕ) :
    normalCoordinateWeight6 r k (pivotExponent6 k i) = ∑ h, (i h : ℝ)/(r h : ℝ) := by
  simp [normalCoordinateWeight6,pivotExponent6]

theorem pivotExponent6_forward {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (i : Fin m → ℕ) :
    normalForward6 M k (MvPolynomial.monomial (pivotExponent6 k i) 1) =
      ∏ h, (normalPolynomial6 M h)^(i h) := by
  rw [normalForward6_monomial]
  have hfree : (∏ h : Fin m, ∏ j ∈ Finset.univ.erase (k h),
      (MvPolynomial.X (h,j) : MvPolynomial (Vars6 m) ℝ) ^ pivotExponent6 k i (h,j)) = 1 := by
    apply Finset.prod_eq_one
    intro h _
    apply Finset.prod_eq_one
    intro j hj
    simp [pivotExponent6,(Finset.mem_erase.mp hj).1]
  simp [hfree,pivotExponent6]

theorem normalCoordinateWeight6_nonneg {m : ℕ} (r : Fin m → ℕ)
    (k : Fin m → Fin 6) (b : Vars6 m →₀ ℕ) : 0 ≤ normalCoordinateWeight6 r k b := by
  unfold normalCoordinateWeight6
  positivity

theorem sourceNormalIdeal6_support {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (Vars6 m) ℝ) (hP : P ∈ sourceNormalIdeal6 M r c) :
    ∀ b ∈ (normalInverse6 M k P).support, c ≤ normalCoordinateWeight6 r k b := by
  induction hP using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i,hi,rfl⟩ := hF
    rw [← pivotExponent6_forward M k i,normalInverse6_forward6 M k hk]
    intro b hb
    have he : b = pivotExponent6 k i := by symm; simpa using hb
    subst b
    simpa only [pivotExponent6_weight] using hi
  | zero => simp
  | add F G hF hG ihF ihG =>
    rw [map_add]
    intro b hb
    rcases Finset.mem_union.mp (MvPolynomial.support_add hb) with hb | hb
    · exact ihF b hb
    · exact ihG b hb
  | smul a F hF ih =>
    change ∀ b ∈ (normalInverse6 M k (a*F)).support, _
    rw [map_mul]
    intro b hb
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hb)
    rw [← he,normalCoordinateWeight6_add]
    exact (ih v hv).trans (le_add_of_nonneg_left (normalCoordinateWeight6_nonneg r k u))

theorem sourceNormalIdeal6_iff_support {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceNormalIdeal6 M r c ↔
      ∀ b ∈ (normalInverse6 M k P).support, c ≤ normalCoordinateWeight6 r k b := by
  refine ⟨sourceNormalIdeal6_support M k hk r c P,?_⟩
  intro hP
  have hsum := congrArg (normalForward6 M k) (normalInverse6 M k P).as_sum
  rw [normalForward6_inverse6 M k hk P,map_sum] at hsum
  rw [hsum]
  apply Ideal.sum_mem
  intro b hb
  exact normalForward6_monomial_mem M k r c b _ (hP b hb)

theorem sourceNormalIdeal6_iff_coeff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (c : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceNormalIdeal6 M r c ↔
      ∀ b, normalCoordinateWeight6 r k b < c → (normalInverse6 M k P).coeff b = 0 := by
  rw [sourceNormalIdeal6_iff_support M k hk]
  constructor
  · intro h b hb
    by_contra hn
    exact (not_le.mpr hb) (h b (MvPolynomial.mem_support_iff.mpr hn))
  · intro h b hb
    by_contra! hn
    exact (MvPolynomial.mem_support_iff.mp hb) (h b hn)

theorem sourceStrictNormalIdeal6_iff_support {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (theta : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceStrictNormalIdeal6 M r theta ↔
      ∀ b ∈ (normalInverse6 M k P).support, theta < normalCoordinateWeight6 r k b := by
  rw [sourceStrictNormalIdeal6_iff]
  constructor
  · rintro ⟨c,hc,hP⟩ b hb
    exact hc.trans_le (sourceNormalIdeal6_support M k hk r c P hP b hb)
  · intro h
    by_cases hzero : normalInverse6 M k P = 0
    · have hz : P = 0 := by
        rw [← normalForward6_inverse6 M k hk P,hzero,map_zero]
      exact ⟨theta+1,by linarith,hz ▸ Ideal.zero_mem _⟩
    · have hn : (normalInverse6 M k P).support.Nonempty :=
        MvPolynomial.support_nonempty.mpr hzero
      obtain ⟨b,hb,hmin⟩ := Finset.exists_min_image
        (normalInverse6 M k P).support (normalCoordinateWeight6 r k) hn
      exact ⟨_,h b hb,(sourceNormalIdeal6_iff_support M k hk r _ P).mpr hmin⟩

theorem sourceStrictNormalIdeal6_iff_coeff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0) (r : Fin m → ℕ)
    (theta : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    P ∈ sourceStrictNormalIdeal6 M r theta ↔
      ∀ b, normalCoordinateWeight6 r k b ≤ theta → (normalInverse6 M k P).coeff b = 0 := by
  rw [sourceStrictNormalIdeal6_iff_support M k hk]
  constructor
  · intro h b hb
    by_contra hn
    exact (not_lt.mpr hb) (h b (MvPolynomial.mem_support_iff.mpr hn))
  · intro h b hb
    by_contra! hn
    exact (MvPolynomial.mem_support_iff.mp hb) (h b hn)

theorem sourceNormalIdeal6_upper_iff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (theta : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    (∀ c : ℝ, theta < c → P ∉ sourceNormalIdeal6 M r c) ↔
      P ∉ sourceStrictNormalIdeal6 M r theta := by
  rw [sourceStrictNormalIdeal6_iff]
  simp only [not_exists,not_and]

theorem sourceNormalIdeal6_upper_iff_coefficient_witness {m : ℕ}
    (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0)
    (r : Fin m → ℕ) (theta : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    (∀ c : ℝ, theta < c → P ∉ sourceNormalIdeal6 M r c) ↔
      ∃ b, normalCoordinateWeight6 r k b ≤ theta ∧ (normalInverse6 M k P).coeff b ≠ 0 := by
  rw [sourceNormalIdeal6_upper_iff,sourceStrictNormalIdeal6_iff_coeff M k hk]
  push_neg
  rfl

theorem sourceNormalIdeal6_support_coordinate_independent {m : ℕ}
    (M : Fin m → Fin 6 → ℤ) (k j : Fin m → Fin 6)
    (hk : ∀ h, M h (k h) ≠ 0) (hj : ∀ h, M h (j h) ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℝ) :
    (∀ b ∈ (normalInverse6 M k P).support, c ≤ normalCoordinateWeight6 r k b) ↔
      ∀ b ∈ (normalInverse6 M j P).support, c ≤ normalCoordinateWeight6 r j b := by
  rw [← sourceNormalIdeal6_iff_support M k hk,← sourceNormalIdeal6_iff_support M j hj]

open SourceReadiness6 SourceSchmidtParameters6

theorem schmidtPackage6_upper_iff_coefficient_witness
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) (k : Fin S.m → Fin 6)
    (hk : ∀ h, R.M (S.t h) (k h) ≠ 0) :
    (∀ c : ℝ, S.theta < c → S.P.map (Int.castRingHom ℝ) ∉
      sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c) ↔
      ∃ b, normalCoordinateWeight6 S.r k b ≤ S.theta ∧
        (normalInverse6 (fun h => R.M (S.t h)) k (S.P.map (Int.castRingHom ℝ))).coeff b ≠ 0 := by
  exact sourceNormalIdeal6_upper_iff_coefficient_witness _ k hk S.r S.theta _

end CompoundFeasibility.SchmidtIndexSemantics6
