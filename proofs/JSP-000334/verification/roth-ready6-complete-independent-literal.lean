import SubspaceBridge.SchmidtTaylorCorrespondence6
import SubspaceBridge.SchmidtHilfssatz12
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SchmidtNormalSubstitution6 SchmidtExcessElimination6
open SchmidtScalarDehomogenization6 SchmidtRationalNormalization6 SchmidtTaylorCorrespondence6
open SourceSchmidtParameters6 SourceReadiness6

theorem denominator_growth6 (H0 H Q0 Q gamma : ℝ) (r0 r : ℕ)
    (hH0 : 0 ≤ H0) (hH : 0 ≤ H) (hQ0 : 0 ≤ Q0) (hg : 0 ≤ gamma)
    (hupper : Q0 ≤ H0) (hlower : H^(1/5 : ℝ) ≤ Q)
    (hcompare : H0^(gamma*(r0 : ℝ)) ≤ H^(r : ℝ)) :
    Q0^((r0 : ℝ)*(gamma/5)) ≤ Q^(r : ℝ) := by
  calc
    Q0^((r0 : ℝ)*(gamma/5)) ≤ H0^((r0 : ℝ)*(gamma/5)) :=
      Real.rpow_le_rpow hQ0 hupper (by positivity)
    _ = (H0^(gamma*(r0 : ℝ)))^(1/5 : ℝ) := by
      rw [← Real.rpow_mul hH0]
      congr 1
      ring
    _ ≤ (H^(r : ℝ))^(1/5 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hH0 _) hcompare (by norm_num)
    _ = (H^(1/5 : ℝ))^(r : ℝ) := by
      rw [← Real.rpow_mul hH,← Real.rpow_mul hH]
      congr 1
      ring
    _ ≤ Q^(r : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hH _) hlower (Nat.cast_nonneg r)

theorem fifth_budget6 (H Q a : ℝ) (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hroot : H^(1/5 : ℝ) ≤ Q) : H^a ≤ (Q^(a/5))^25 := by
  calc
    H^a = (H^(1/5 : ℝ))^(5*a) := by
      rw [← Real.rpow_mul hH]
      congr 1
      ring
    _ ≤ Q^(5*a) := Real.rpow_le_rpow (Real.rpow_nonneg hH _) hroot (by positivity)
    _ = (Q^(a/5))^25 := by
      rw [← Real.rpow_mul_natCast hQ]
      congr 1
      norm_num
      ring

theorem denominator_absolute6 (m : ℕ) (H Q omega gamma : ℝ)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ho : 0 ≤ omega) (hg : 0 ≤ gamma)
    (hroot : H^(1/5 : ℝ) ≤ Q) (hbudget : (2 : ℝ)^(75*m) ≤ H^(omega*gamma)) :
    (2 : ℝ)^(3*m) ≤ Q^(omega*(gamma/5)) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (25 : ℕ) ≠ 0) (Real.rpow_nonneg hQ _)
  calc
    ((2 : ℝ)^(3*m))^25 = (2 : ℝ)^(75*m) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ H^(omega*gamma) := hbudget
    _ ≤ (Q^((omega*gamma)/5))^25 := fifth_budget6 H Q _ hH hQ (mul_nonneg ho hg) hroot
    _ = (Q^(omega*(gamma/5)))^25 := by congr 2; ring

theorem polynomial_height6 (A B H Q omega gamma : ℝ) (r0 : ℕ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ho : 0 ≤ omega) (hg : 0 ≤ gamma)
    (hAB : A ≤ B) (hroot : H^(1/5 : ℝ) ≤ Q)
    (hbudget : B^25 ≤ H^(omega*gamma*(r0 : ℝ))) :
    A ≤ Q^(omega*(r0 : ℝ)*(gamma/5)) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (25 : ℕ) ≠ 0) (Real.rpow_nonneg hQ _)
  calc
    A^25 ≤ B^25 := pow_le_pow_left₀ hA hAB 25
    _ ≤ H^(omega*gamma*(r0 : ℝ)) := hbudget
    _ ≤ (Q^((omega*gamma*(r0 : ℝ))/5))^25 :=
      fifth_budget6 H Q _ hH hQ (by positivity) hroot
    _ = (Q^(omega*(r0 : ℝ)*(gamma/5)))^25 := by congr 2; ring

variable
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}

theorem source_ranges6 (S : SchmidtPackage6 R s) :
    0 < S.m ∧ 0 < S.theta ∧ S.theta < 1/12 ∧ 0 < S.gamma ∧ S.gamma ≤ 5 ∧
      0 < S.gamma/5 ∧ S.gamma/5 ≤ 1 ∧ 0 < JSP000334.omega65 S.m S.theta := by
  have hC := JSP000334.SchmidtHilfssatz12.gamma_fifth_range S.gamma S.gamma_pos S.gamma_le_five
  exact ⟨S.m_pos,S.theta_pos,S.theta_lt,S.gamma_pos,S.gamma_le_five,hC.1,hC.2,S.omega_pos⟩

theorem source_degrees6 (S : SchmidtPackage6 R s) :
    (∀ h, 0 < S.r h) ∧
      ∀ (h : Fin S.m) (hh : h.val+1 < S.m),
        (S.r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 S.m S.theta*(S.r h : ℝ) := by
  exact ⟨S.degrees_pos,S.degrees_separation⟩

theorem schmidtPackage6_hilfssatz12_readiness
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
      ((P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
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
        (G.map (Int.castRingHom ℚ)) = (I : WithTop ℝ)) ∧
      (0 < S.m ∧ 0 < S.theta ∧ S.theta < 1/12 ∧ 0 < S.gamma ∧ S.gamma ≤ 5 ∧
        0 < S.gamma/5 ∧ S.gamma/5 ≤ 1 ∧ 0 < JSP000334.omega65 S.m S.theta) ∧
      (∀ h, 0 < S.r h) ∧
      (∀ (h : Fin S.m) (hh : h.val+1 < S.m),
        (S.r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 S.m S.theta*(S.r h : ℝ)) ∧
      (∀ h, q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1) ∧
      (∀ h, 0 < sourceH6 R S.t h ∧ 0 < |(q h : ℝ)| ∧
        (sourceH6 R S.t h)^(1/5 : ℝ) ≤ |(q h : ℝ)| ∧ |(q h : ℝ)| ≤ sourceH6 R S.t h) ∧
      (∀ h : Fin S.m,
        |(q ⟨0,S.m_pos⟩ : ℝ)|^((S.r ⟨0,S.m_pos⟩ : ℝ)*(S.gamma/5)) ≤ |(q h : ℝ)|^(S.r h)) ∧
      (∀ h, (2 : ℝ)^(3*S.m) ≤ |(q h : ℝ)|^(JSP000334.omega65 S.m S.theta*(S.gamma/5))) ∧
      G ≠ 0 ∧ (∀ b ∈ G.support, ∀ h, b h ≤ S.r h) ∧
      (JSP000334.rothIntegerHeight G : ℝ) ≤
        |(q ⟨0,S.m_pos⟩ : ℝ)|^(JSP000334.omega65 S.m S.theta*(S.r ⟨0,S.m_pos⟩ : ℝ)*(S.gamma/5)) := by
  obtain ⟨C,P',PN,F,G,p,q,hsource⟩ := schmidtPackage6_taylor_correspondence S
  have hcopy := hsource
  rcases hsource with ⟨hnorm,hclosedDerivative,hhighDerivative,hstrictDerivative,hhighIndex,hstrictIndex,hfinite⟩
  rcases hnorm with ⟨heq,hinv,hPN,hPNn,hrecover,hF,hFn,hhom,hG,hGn,hheight,hdegree,
    hpq,hpair,hheightNormal,hmonic,hclosed,hstrict,htransfer,hstrictTransfer,hhigh,hstrictTheta⟩
  have hq (h) : q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1 := by
    exact ⟨(hpair h).2.2.2.2.2.2.1,(hpair h).2.2.2.2.2.2.2.1⟩
  have hH (h) : 0 < sourceH6 R S.t h := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hQ (h) : 0 < |(q h : ℝ)| := abs_pos.mpr (by exact_mod_cast (hq h).1)
  have hb (h) : (sourceH6 R S.t h)^(1/5 : ℝ) ≤ |(q h : ℝ)| ∧
      |(q h : ℝ)| ≤ sourceH6 R S.t h := by
    rw [S.normal_height_convention h]
    exact (hheightNormal h).2.2
  refine ⟨C,P',PN,F,G,p,q,hcopy,source_ranges6 S,S.degrees_pos,S.degrees_separation,hq,
    fun h => ⟨hH h,hQ h,(hb h).1,(hb h).2⟩,?_,?_,hGn,?_,?_⟩
  · intro h
    simpa only [Real.rpow_natCast] using denominator_growth6
      (sourceH6 R S.t ⟨0,S.m_pos⟩) (sourceH6 R S.t h)
      |(q ⟨0,S.m_pos⟩ : ℝ)| |(q h : ℝ)| S.gamma (S.r ⟨0,S.m_pos⟩) (S.r h)
      (hH _).le (hH h).le (hQ _).le S.gamma_pos.le (hb _).2 (hb h).1 (by simpa only [Real.rpow_natCast] using S.height_comparison h)
  · intro h
    exact denominator_absolute6 S.m (sourceH6 R S.t h) |(q h : ℝ)| _ S.gamma
      (hH h).le (hQ h).le S.omega_pos.le S.gamma_pos.le (hb h).1 (S.normal_budget h)
  · intro b hb h
    exact (MvPolynomial.monomial_le_degreeOf h hb).trans (hdegree h)
  · exact polynomial_height6 (JSP000334.rothIntegerHeight G : ℝ) (height6 S.P : ℝ)
      (sourceH6 R S.t ⟨0,S.m_pos⟩) |(q ⟨0,S.m_pos⟩ : ℝ)| _ S.gamma (S.r ⟨0,S.m_pos⟩)
      (Nat.cast_nonneg _) (hH _).le (hQ _).le S.omega_pos.le S.gamma_pos.le
      (by exact_mod_cast hheight) (hb _).1 S.polynomial_budget

end CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal

#print axioms CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal.denominator_growth6
#print axioms CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal.fifth_budget6
#print axioms CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal.denominator_absolute6
#print axioms CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal.polynomial_height6
#print axioms CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal.source_ranges6
#print axioms CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal.source_degrees6
#print axioms CompoundFeasibility.SchmidtHilfssatz12Readiness6Literal.schmidtPackage6_hilfssatz12_readiness
