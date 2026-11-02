import SubspaceBridge.SchmidtHilfssatz12Readiness6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtSatz11Conclusion6Literal
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SchmidtNormalSubstitution6 SchmidtExcessElimination6
open SchmidtScalarDehomogenization6 SchmidtRationalNormalization6 SchmidtTaylorCorrespondence6
open SourceSchmidtParameters6 SourceReadiness6

open SchmidtHilfssatz12Readiness6

theorem hilfssatz12_weight6 {m : ℕ} (r : Fin m → ℕ) (J : Fin m →₀ ℕ) :
    (∑ h, (J h : ℝ)/(r h : ℝ)) = JSP000334.rothTaylorWeight r J := rfl

theorem schmidtPackage6_nonvanishing
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
      (((P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
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
        |(q ⟨0,S.m_pos⟩ : ℝ)|^(JSP000334.omega65 S.m S.theta*(S.r ⟨0,S.m_pos⟩ : ℝ)*(S.gamma/5))) ∧
      ∃ J : Fin S.m →₀ ℕ, JSP000334.rothTaylorWeight S.r J ≤ S.theta ∧
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(q h : ℚ))
          (JSP000334.rothIntegerDividedDerivative J G) ≠ 0 := by
  obtain ⟨C,P',PN,F,G,p,q,hready⟩ := schmidtPackage6_hilfssatz12_readiness S
  have hcopy := hready
  rcases hready with ⟨hsource,hparams,hr,hsep,hq,hbases,hgrowth,hden,hG,hb,hheight⟩
  obtain ⟨J,hweight,hne⟩ := JSP000334.SchmidtHilfssatz12.hilfssatz12_gamma_fifth
    S.m S.m_pos S.theta S.gamma hparams.2.1 hparams.2.2.1 hparams.2.2.2.1 hparams.2.2.2.2.1
    S.r p q G hr hsep hq hgrowth hden hG hb hheight
  refine ⟨C,P',PN,F,G,p,q,hcopy,J,?_,hne⟩
  rw [← hilfssatz12_weight6]
  exact hweight

theorem schmidtPackage6_scalar_upper
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
      (((P' = transport6 ℤ e S.P ∧ (transport6 ℤ e).symm P' = S.P ∧
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
        |(q ⟨0,S.m_pos⟩ : ℝ)|^(JSP000334.omega65 S.m S.theta*(S.r ⟨0,S.m_pos⟩ : ℝ)*(S.gamma/5))) ∧
      ∃ J : Fin S.m →₀ ℕ, JSP000334.rothTaylorWeight S.r J ≤ S.theta ∧
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ)/(q h : ℚ))
          (JSP000334.rothIntegerDividedDerivative J G) ≠ 0 ∧
        ∀ c : ℝ, S.theta < c → G.map (Int.castRingHom ℝ) ∉ monicIdeal6 M' S.r c := by
  obtain ⟨C,P',PN,F,G,p,q,hready,J,hweight,hne⟩ := schmidtPackage6_nonvanishing S
  have hcopy := hready
  rcases hready with ⟨hsource,hparams,hr,hsep,hq,hbases,hgrowth,hden,hG,hb,hheight⟩
  rcases hsource with ⟨hnorm,hclosedDerivative,hhighDerivative,hstrictDerivative,hhighIndex,hstrictIndex,hfinite⟩
  refine ⟨C,P',PN,F,G,p,q,hcopy,J,hweight,hne,?_⟩
  intro c hc hmem
  exact hne (hclosedDerivative c hmem J (hweight.trans_lt hc))

variable
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}

theorem schmidtPackage6_source_upper (S : SchmidtPackage6 R s) :
    ∀ c : ℝ, S.theta < c → S.P.map (Int.castRingHom ℝ) ∉
      sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c := by
  obtain ⟨C,P',PN,F,G,p,q,hready,J,hweight,hne,hupper⟩ := schmidtPackage6_scalar_upper S
  rcases hready with ⟨hsource,hparams,hr,hsep,hq,hbases,hgrowth,hden,hG,hb,hheight⟩
  rcases hsource with ⟨hnorm,hclosedDerivative,hhighDerivative,hstrictDerivative,hhighIndex,hstrictIndex,hfinite⟩
  rcases hnorm with ⟨heq,hinv,hPN,hPNn,hrecover,hF,hFn,hhom,hGdef,hGn,hheightOriginal,hdegree,
    hpq,hpair,hheightNormal,hmonic,hclosed,hstrict,htransfer,hstrictTransfer,hhigh,hstrictTheta⟩
  intro c hc hmem
  exact hupper c hc (htransfer c hmem)

theorem schmidtPackage6_impossible (S : SchmidtPackage6 R s) : False := by
  exact schmidtPackage6_source_upper S ((S.m : ℝ)*S.eta) S.theta_index S.high_index

theorem nonzeroReady_excluded6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (s : SourceMixed6.MixedIndex6) :
    ¬ R.nonzeroReady s := by
  intro hready
  obtain ⟨S⟩ := construct_schmidt_package6 R s hready
  exact schmidtPackage6_impossible S

theorem source_eventual_zero6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    ∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ SourceMixed6.admissibleMixed6 R.c (R.delta/2),
      SourceMixed6.actualNormProduct6 A2 A3 L (R.M q) s = 0 := by
  apply R.branches.resolve_left
  rintro ⟨s,hs⟩
  exact nonzeroReady_excluded6 R s hs

end CompoundFeasibility.SchmidtSatz11Conclusion6Literal

#print axioms CompoundFeasibility.SchmidtSatz11Conclusion6Literal.hilfssatz12_weight6
#print axioms CompoundFeasibility.SchmidtSatz11Conclusion6Literal.schmidtPackage6_nonvanishing
#print axioms CompoundFeasibility.SchmidtSatz11Conclusion6Literal.schmidtPackage6_scalar_upper
#print axioms CompoundFeasibility.SchmidtSatz11Conclusion6Literal.schmidtPackage6_source_upper
#print axioms CompoundFeasibility.SchmidtSatz11Conclusion6Literal.schmidtPackage6_impossible
#print axioms CompoundFeasibility.SchmidtSatz11Conclusion6Literal.nonzeroReady_excluded6
#print axioms CompoundFeasibility.SchmidtSatz11Conclusion6Literal.source_eventual_zero6
