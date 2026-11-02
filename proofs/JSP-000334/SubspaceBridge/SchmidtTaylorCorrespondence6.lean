import SubspaceBridge.SchmidtRationalNormalization6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtTaylorCorrespondence6
open SchmidtRationalNormalization6

def translate6 {K : Type*} [CommRing K] {m : ℕ} (z : Fin m → K) :
    MvPolynomial (Fin m) K →+* MvPolynomial (Fin m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun h => MvPolynomial.C (z h) + MvPolynomial.X h)

theorem translate6_C {K : Type*} [CommRing K] {m : ℕ} (z : Fin m → K) (a : K) :
    translate6 z (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [translate6]

theorem translate6_X {K : Type*} [CommRing K] {m : ℕ} (z : Fin m → K) (h : Fin m) :
    translate6 z (MvPolynomial.X h) = MvPolynomial.C (z h) + MvPolynomial.X h := by
  simp [translate6]

theorem translate6_inverse {K : Type*} [CommRing K] {m : ℕ}
    (z : Fin m → K) (P : MvPolynomial (Fin m) K) :
    translate6 (fun h => -z h) (translate6 z P) = P := by
  have he : (translate6 (fun h => -z h)).comp (translate6 z) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [translate6_C]
    · intro h
      simp [translate6_X,translate6_C]
  exact RingHom.congr_fun he P

theorem translate6_monic {K : Type*} [CommRing K] {m : ℕ} (z : Fin m → K) (h : Fin m) :
    translate6 z (MvPolynomial.X h - MvPolynomial.C (z h)) = MvPolynomial.X h := by
  simp [translate6_X,translate6_C]

theorem translate6_map {K L : Type*} [CommRing K] [CommRing L] {m : ℕ}
    (f : K →+* L) (z : Fin m → K) (P : MvPolynomial (Fin m) K) :
    translate6 (fun h => f (z h)) (P.map f) = (translate6 z P).map f := by
  have he : (translate6 (fun h => f (z h))).comp (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (translate6 z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [translate6_C]
    · intro h
      simp [translate6_X,translate6_C]
  exact RingHom.congr_fun he P

theorem translate6_rat {m : ℕ} (z : Fin m → ℚ) (P : MvPolynomial (Fin m) ℚ) :
    translate6 z P = JSP000334.rothTaylorPolynomial z P := rfl

def rootPoint6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) : Fin m → ℝ :=
  fun h => (rootNumerator6 (M h 0) (M h 1) : ℝ)/(rootDenominator6 (M h 0) (M h 1) : ℝ)

theorem source_weight6 {m : ℕ} (r i : Fin m → ℕ) :
    JSP000334.rothTaylorWeight r (Finsupp.equivFunOnFinite.symm i) =
      ∑ h, (i h : ℝ)/(r h : ℝ) := by
  simp [JSP000334.rothTaylorWeight]

theorem translate6_products {K : Type*} [CommRing K] {m : ℕ}
    (z : Fin m → K) (i : Fin m → ℕ) :
    translate6 z (∏ h, (MvPolynomial.X h - MvPolynomial.C (z h))^(i h)) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm i) 1 := by
  simp only [map_prod,map_pow,translate6_monic]
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp

theorem translate6_monomial_inverse {K : Type*} [CommRing K] {m : ℕ}
    (z : Fin m → K) (b : Fin m →₀ ℕ) (a : K) :
    translate6 (fun h => -z h) (MvPolynomial.monomial b a) =
      MvPolynomial.C a * ∏ h, (MvPolynomial.X h - MvPolynomial.C (z h))^(b h) := by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [map_mul,map_prod,map_pow,translate6_C,translate6_X,map_neg]
  congr 1
  apply Finset.prod_congr rfl
  intro h _
  congr 1
  ring

theorem weight_nonneg6 {m : ℕ} (r : Fin m → ℕ) (b : Fin m →₀ ℕ) :
    0 ≤ JSP000334.rothTaylorWeight r b := by
  unfold JSP000334.rothTaylorWeight
  positivity

theorem monicIdeal6_support {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ)
    (hH : H ∈ monicIdeal6 M r c) :
    ∀ b ∈ (translate6 (rootPoint6 M) H).support, c ≤ JSP000334.rothTaylorWeight r b := by
  induction hH using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i,hi,rfl⟩ := hF
    change ∀ b ∈ (translate6 (rootPoint6 M)
      (∏ h, (MvPolynomial.X h - MvPolynomial.C (rootPoint6 M h))^(i h))).support, _
    rw [translate6_products]
    intro b hb
    have he : b = Finsupp.equivFunOnFinite.symm i := by symm; simpa using hb
    subst b
    simpa only [source_weight6] using hi
  | zero => simp
  | add F G hF hG ihF ihG =>
    rw [map_add]
    intro b hb
    rcases Finset.mem_union.mp (MvPolynomial.support_add hb) with hb | hb
    · exact ihF b hb
    · exact ihG b hb
  | smul a F hF ih =>
    change ∀ b ∈ (translate6 (rootPoint6 M) (a*F)).support, _
    rw [map_mul]
    intro b hb
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hb)
    rw [← he,JSP000334.rothTaylorWeight_add]
    exact (ih v hv).trans (le_add_of_nonneg_left (weight_nonneg6 r u))

theorem monicIdeal6_iff_support {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ) :
    H ∈ monicIdeal6 M r c ↔
      ∀ b ∈ (translate6 (rootPoint6 M) H).support, c ≤ JSP000334.rothTaylorWeight r b := by
  refine ⟨monicIdeal6_support M r c H,?_⟩
  intro h
  have hs := congrArg (translate6 (fun h => -rootPoint6 M h)) (translate6 (rootPoint6 M) H).as_sum
  rw [translate6_inverse,map_sum] at hs
  rw [hs]
  apply Ideal.sum_mem
  intro b hb
  rw [translate6_monomial_inverse]
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  refine ⟨fun h => b h,?_,rfl⟩
  exact h b hb

theorem monicIdeal6_iff_coeff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ) :
    H ∈ monicIdeal6 M r c ↔
      ∀ b, JSP000334.rothTaylorWeight r b < c → (translate6 (rootPoint6 M) H).coeff b = 0 := by
  rw [monicIdeal6_iff_support]
  constructor
  · intro h b hb
    by_contra hn
    exact (not_le.mpr hb) (h b (MvPolynomial.mem_support_iff.mpr hn))
  · intro h b hb
    by_contra! hn
    exact (MvPolynomial.mem_support_iff.mp hb) (h b hn)

theorem monicStrictIdeal6_support {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ)
    (hH : H ∈ monicStrictIdeal6 M r c) :
    ∀ b ∈ (translate6 (rootPoint6 M) H).support, c < JSP000334.rothTaylorWeight r b := by
  induction hH using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i,hi,rfl⟩ := hF
    change ∀ b ∈ (translate6 (rootPoint6 M)
      (∏ h, (MvPolynomial.X h - MvPolynomial.C (rootPoint6 M h))^(i h))).support, _
    rw [translate6_products]
    intro b hb
    have he : b = Finsupp.equivFunOnFinite.symm i := by symm; simpa using hb
    subst b
    simpa only [source_weight6] using hi
  | zero => simp
  | add F G hF hG ihF ihG =>
    rw [map_add]
    intro b hb
    rcases Finset.mem_union.mp (MvPolynomial.support_add hb) with hb | hb
    · exact ihF b hb
    · exact ihG b hb
  | smul a F hF ih =>
    change ∀ b ∈ (translate6 (rootPoint6 M) (a*F)).support, _
    rw [map_mul]
    intro b hb
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hb)
    rw [← he,JSP000334.rothTaylorWeight_add]
    exact (ih v hv).trans_le (le_add_of_nonneg_left (weight_nonneg6 r u))

theorem monicStrictIdeal6_iff_support {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ) :
    H ∈ monicStrictIdeal6 M r c ↔
      ∀ b ∈ (translate6 (rootPoint6 M) H).support, c < JSP000334.rothTaylorWeight r b := by
  refine ⟨monicStrictIdeal6_support M r c H,?_⟩
  intro h
  have hs := congrArg (translate6 (fun h => -rootPoint6 M h)) (translate6 (rootPoint6 M) H).as_sum
  rw [translate6_inverse,map_sum] at hs
  rw [hs]
  apply Ideal.sum_mem
  intro b hb
  rw [translate6_monomial_inverse]
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  refine ⟨fun h => b h,?_,rfl⟩
  exact h b hb

theorem monicStrictIdeal6_iff_coeff {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (c : ℝ) (H : MvPolynomial (Fin m) ℝ) :
    H ∈ monicStrictIdeal6 M r c ↔
      ∀ b, JSP000334.rothTaylorWeight r b ≤ c → (translate6 (rootPoint6 M) H).coeff b = 0 := by
  rw [monicStrictIdeal6_iff_support]
  constructor
  · intro h b hb
    by_contra hn
    exact (not_lt.mpr hb) (h b (MvPolynomial.mem_support_iff.mpr hn))
  · intro h b hb
    by_contra! hn
    exact (MvPolynomial.mem_support_iff.mp hb) (h b hn)

theorem rational_coeff_zero6 {m : ℕ} (P : MvPolynomial (Fin m) ℚ) (J : Fin m →₀ ℕ) :
    (P.map (Rat.castHom ℝ)).coeff J = 0 ↔ P.coeff J = 0 := by
  rw [MvPolynomial.coeff_map]
  exact Rat.cast_eq_zero

theorem rational_eval_zero6 {m : ℕ} (z : Fin m → ℚ) (D : MvPolynomial (Fin m) ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun h => (z h : ℝ)) D = 0 ↔
      MvPolynomial.eval₂ (Int.castRingHom ℚ) z D = 0 := by
  have he : ((MvPolynomial.eval₂ (Int.castRingHom ℚ) z D : ℚ) : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun h => (z h : ℝ)) D := by
    exact MvPolynomial.eval₂_comp_left (Rat.castHom ℝ) (Int.castRingHom ℚ) z D
  rw [← he]
  exact Rat.cast_eq_zero

theorem translate6_integer_coeff {m : ℕ} (z : Fin m → ℚ)
    (G : MvPolynomial (Fin m) ℤ) (J : Fin m →₀ ℕ) :
    (translate6 z (G.map (Int.castRingHom ℚ))).coeff J =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) z (JSP000334.rothIntegerDividedDerivative J G) := by
  rw [translate6_rat,JSP000334.rothTaylorPolynomial_coeff,JSP000334.rothIntegerDividedDerivative_eval]

theorem translate6_integer_real {m : ℕ} (z : Fin m → ℚ)
    (G : MvPolynomial (Fin m) ℤ) :
    translate6 (fun h => (z h : ℝ)) (G.map (Int.castRingHom ℝ)) =
      (translate6 z (G.map (Int.castRingHom ℚ))).map (Rat.castHom ℝ) := by
  rw [← translate6_map,MvPolynomial.map_map]
  rfl

theorem translate6_integer_real_coeff {m : ℕ} (z : Fin m → ℚ)
    (G : MvPolynomial (Fin m) ℤ) (J : Fin m →₀ ℕ) :
    (translate6 (fun h => (z h : ℝ)) (G.map (Int.castRingHom ℝ))).coeff J =
      ((MvPolynomial.eval₂ (Int.castRingHom ℚ) z (JSP000334.rothIntegerDividedDerivative J G) : ℚ) : ℝ) := by
  rw [translate6_integer_real,MvPolynomial.coeff_map,translate6_integer_coeff]
  rfl

theorem translate6_zero_reflection {m : ℕ} (z : Fin m → ℚ)
    (G : MvPolynomial (Fin m) ℤ) (J : Fin m →₀ ℕ) :
    (translate6 (fun h => (z h : ℝ)) (G.map (Int.castRingHom ℝ))).coeff J = 0 ↔
      MvPolynomial.eval₂ (Int.castRingHom ℚ) z (JSP000334.rothIntegerDividedDerivative J G) = 0 := by
  rw [translate6_integer_real_coeff]
  exact Rat.cast_eq_zero

theorem monicIdeal6_iff_divided {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (z : Fin m → ℚ) (hz : ∀ h, rootPoint6 M h = (z h : ℝ))
    (c : ℝ) (G : MvPolynomial (Fin m) ℤ) :
    G.map (Int.castRingHom ℝ) ∈ monicIdeal6 M r c ↔
      ∀ J, JSP000334.rothTaylorWeight r J < c →
        MvPolynomial.eval₂ (Int.castRingHom ℚ) z (JSP000334.rothIntegerDividedDerivative J G) = 0 := by
  rw [monicIdeal6_iff_coeff]
  have he : rootPoint6 M = fun h => (z h : ℝ) := funext hz
  simp only [he,translate6_zero_reflection]

theorem monicStrictIdeal6_iff_divided {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (z : Fin m → ℚ) (hz : ∀ h, rootPoint6 M h = (z h : ℝ))
    (c : ℝ) (G : MvPolynomial (Fin m) ℤ) :
    G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 M r c ↔
      ∀ J, JSP000334.rothTaylorWeight r J ≤ c →
        MvPolynomial.eval₂ (Int.castRingHom ℚ) z (JSP000334.rothIntegerDividedDerivative J G) = 0 := by
  rw [monicStrictIdeal6_iff_coeff]
  have he : rootPoint6 M = fun h => (z h : ℝ) := funext hz
  simp only [he,translate6_zero_reflection]

theorem monicIdeal6_index_lower {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (z : Fin m → ℚ) (hz : ∀ h, rootPoint6 M h = (z h : ℝ))
    (c : ℝ) (G : MvPolynomial (Fin m) ℤ)
    (hG : G.map (Int.castRingHom ℝ) ∈ monicIdeal6 M r c) :
    (c : WithTop ℝ) ≤ JSP000334.rothWeightedTaylorIndex r z (G.map (Int.castRingHom ℚ)) := by
  apply (JSP000334.rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
  intro b hb
  by_contra! hn
  have hv := (monicIdeal6_iff_divided M r z hz c G).mp hG b hn
  apply MvPolynomial.mem_support_iff.mp hb
  rw [JSP000334.rothTaylorPolynomial_coeff,JSP000334.rothIntegerDividedDerivative_eval]
  exact hv

theorem monicStrictIdeal6_index_lower {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (r : Fin m → ℕ) (z : Fin m → ℚ) (hz : ∀ h, rootPoint6 M h = (z h : ℝ))
    (c : ℝ) (G : MvPolynomial (Fin m) ℤ)
    (hG : G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 M r c) :
    (c : WithTop ℝ) < JSP000334.rothWeightedTaylorIndex r z (G.map (Int.castRingHom ℚ)) := by
  apply lt_of_not_ge
  intro hn
  obtain ⟨J,hJ,hne⟩ := (JSP000334.rothWeightedTaylorIndex_le_iff _ _ _ _).mp hn
  apply hne
  rw [JSP000334.rothIntegerDividedDerivative_eval]
  exact (monicStrictIdeal6_iff_divided M r z hz c G).mp hG J hJ

open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SchmidtNormalSubstitution6 SchmidtExcessElimination6
open SchmidtScalarDehomogenization6 SourceSchmidtParameters6 SourceReadiness6

theorem schmidtPackage6_taylor_correspondence
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}
    (S : SchmidtPackage6 R s) :
    ∃ (C : (h : Fin S.m) → SchmidtHilfssatz13.NormalCoordinateChoice6 (R.M (S.t h)))
      (P' : MvPolynomial (Vars6 S.m) ℤ) (PN : MvPolynomial (Vars6 S.m) ℚ)
      (F : MvPolynomial (Vars6 S.m) ℤ) (G : MvPolynomial (Fin S.m) ℤ)
      (p q : Fin S.m → ℤ),
      let e := fun h => (C h).e
      let M' := permutedNormals6 (fun h => R.M (S.t h)) e
      (P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
      PN = normalPolynomialQ6 M' P' ∧ PN ≠ 0 ∧
      (∀ h k, M' h ((C h).e.symm k) = R.M (S.t h) k) ∧
      F = reducedPolynomial6 P' ∧ F ≠ 0 ∧ homogeneous6 (blockDegree6 F) F ∧
      G = scalar6 F ∧ G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height6 S.P ∧
      (∀ h, G.degreeOf h ≤ S.r h) ∧
      (∀ h, p h = rootNumerator6 (M' h 0) (M' h 1) ∧
        q h = rootDenominator6 (M' h 0) (M' h 1)) ∧
      (∀ h, let a := M' h 0
        let b := M' h 1
        let g := Int.gcd a b
        a ≠ 0 ∧ 0 < g ∧ (g : ℤ) ∣ a ∧ (g : ℤ) ∣ b ∧
        a = (g : ℤ)*q h ∧ b = -((g : ℤ)*p h) ∧ q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1 ∧
        (p h : ℚ)/(q h : ℚ) = -(b : ℚ)/(a : ℚ) ∧
        (p h : ℝ)/(q h : ℝ) = -(b : ℝ)/(a : ℝ) ∧
        g^5 ≤ a.natAbs^4 ∧ a.natAbs ≤ (q h).natAbs^5 ∧ (q h).natAbs ≤ a.natAbs ∧
        |(a : ℝ)|^(1/5 : ℝ) ≤ |(q h : ℝ)| ∧ |(q h : ℝ)| ≤ |(a : ℝ)|) ∧
      (∀ h, SourceNormalHeight.normalHeight6 (R.M (S.t h)) = (M' h 0).natAbs ∧
        SourceNormalHeight.normalHeight6 (M' h) = SourceNormalHeight.normalHeight6 (R.M (S.t h)) ∧
        (SourceNormalHeight.normalHeight6 (R.M (S.t h)) : ℝ)^(1/5 : ℝ) ≤ |(q h : ℝ)| ∧
        |(q h : ℝ)| ≤ (SourceNormalHeight.normalHeight6 (R.M (S.t h)) : ℝ)) ∧
      (∀ h, monicNormal6 M' h = MvPolynomial.X h - MvPolynomial.C ((p h : ℝ)/(q h : ℝ)) ∧
        scalarNormal6 M' h = MvPolynomial.C (M' h 0 : ℝ)*monicNormal6 M' h ∧
        IsUnit (MvPolynomial.C (M' h 0 : ℝ) : MvPolynomial (Fin S.m) ℝ)) ∧
      (∀ c, scalarIdeal6 M' S.r c = monicIdeal6 M' S.r c) ∧
      (∀ c, scalarStrictIdeal6 M' S.r c = monicStrictIdeal6 M' S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        G.map (Int.castRingHom ℝ) ∈ monicIdeal6 M' S.r c) ∧
      (∀ c : ℝ, S.P.map (Int.castRingHom ℝ) ∈
        sourceStrictNormalIdeal6 (fun h => R.M (S.t h)) S.r c →
        G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 M' S.r c) ∧
      G.map (Int.castRingHom ℝ) ∈ monicIdeal6 M' S.r ((S.m : ℝ)*S.eta) ∧
      G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 M' S.r S.theta) ∧
      (∀ c, G.map (Int.castRingHom ℝ) ∈ monicIdeal6 M' S.r c →
        ∀ J, JSP000334.rothTaylorWeight S.r J < c →
          MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(q h : ℚ))
            (JSP000334.rothIntegerDividedDerivative J G) = 0) ∧
      (∀ J, JSP000334.rothTaylorWeight S.r J < (S.m : ℝ)*S.eta →
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(q h : ℚ))
          (JSP000334.rothIntegerDividedDerivative J G) = 0) ∧
      (∀ J, JSP000334.rothTaylorWeight S.r J ≤ S.theta →
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(q h : ℚ))
          (JSP000334.rothIntegerDividedDerivative J G) = 0) ∧
      (((S.m : ℝ)*S.eta : ℝ) : WithTop ℝ) ≤
        JSP000334.rothWeightedTaylorIndex S.r (fun h => (p h : ℚ)/(q h : ℚ)) (G.map (Int.castRingHom ℚ)) ∧
      (S.theta : WithTop ℝ) <
        JSP000334.rothWeightedTaylorIndex S.r (fun h => (p h : ℚ)/(q h : ℚ)) (G.map (Int.castRingHom ℚ)) ∧
      ∃ I : ℝ, JSP000334.rothWeightedTaylorIndex S.r (fun h => (p h : ℚ)/(q h : ℚ))
        (G.map (Int.castRingHom ℚ)) = (I : WithTop ℝ) := by
  obtain ⟨C,P',PN,F,G,p,q,hnorm⟩ := schmidtPackage6_rational_normalization S
  have hcopy := hnorm
  rcases hnorm with ⟨heq,hinv,hPN,hPNn,hrecover,hF,hFn,hhom,hG,hGn,hheight,hdegree,
    hpq,hpair,hheightNormal,hmonic,hclosed,hstrict,htransfer,hstrictTransfer,hhigh,hstrictTheta⟩
  let e := fun h => (C h).e
  let M' := permutedNormals6 (fun h => R.M (S.t h)) e
  let z := fun h => (p h : ℚ)/(q h : ℚ)
  have hz (h) : rootPoint6 M' h = (z h : ℝ) := by
    simp only [rootPoint6,z,M',e,← (hpq h).1,← (hpq h).2,Rat.cast_div,Rat.cast_intCast]
  have hnonzero : G.map (Int.castRingHom ℚ) ≠ 0 := by
    exact fun h => hGn ((MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective) h)
  refine ⟨C,P',PN,F,G,p,q,hcopy,?_,?_,?_,?_,?_,?_⟩
  · intro c hc
    exact (monicIdeal6_iff_divided M' S.r z hz c G).mp hc
  · exact (monicIdeal6_iff_divided M' S.r z hz _ G).mp hhigh
  · exact (monicStrictIdeal6_iff_divided M' S.r z hz _ G).mp hstrictTheta
  · exact monicIdeal6_index_lower M' S.r z hz _ G hhigh
  · exact monicStrictIdeal6_index_lower M' S.r z hz _ G hstrictTheta
  · exact JSP000334.rothWeightedTaylorIndex_finite S.r z _ hnonzero

end CompoundFeasibility.SchmidtTaylorCorrespondence6
