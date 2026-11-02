import SubspaceBridge.SourceRationalSamples10
import SubspaceBridge.SourceFixedSampleBudget10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedBudget10
open SourceOriginalDual10 SourceOriginalVariable10 SourceSampling10 SourceSelectedSet10 SourceSelectedUpper10
open OriginalDual10 SchmidtNormal10 SchmidtCoordinate10 SchmidtPolynomial10 SchmidtRationalNormalization6 SchmidtScalar10

theorem original_rational_fixed_budgets10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ D0 E0 alpha C_upper T : ℝ, 1 ≤ D0 ∧ 1 ≤ E0 ∧ 0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      ∀ (_hfail : ∀ B : ℝ, ∃ Q : ℝ, ∃ hQ : 1 < Q, B < Q ∧
        ∃ D : OriginalData10 A2 A3 L hL Q hQ delta S0,
          ∃ s ∈ S0, dataRationalDualProduct10 D s ≠ 0),
      ∀ B1 : ℝ, ∃ U : Set ℝ, ¬ BddAbove U ∧ ∃ hQU : ∀ q ∈ U, 1 < q,
        ∃ D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0,
          (∀ q : U, ∃ s ∈ S0, dataRationalDualProduct10 (D q) s ≠ 0) ∧
      ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
        (∀ q : V, max T B1 < q.val) ∧
      ∃ e : ℝ, 0 < e ∧ e < 1 ∧ ∃ c : Fin 3 → Fin 10 → ℝ,
        (∀ tau i, |c tau i| ≤ 1) ∧ (∑ tau, ∑ i, c tau i) = 0 ∧
        (∀ i, c 1 i ≤ 0 ∧ c 2 i ≤ 0) ∧
      ∃ eta : ℝ, 0 < eta ∧ 4000*eta < e ∧ ∃ m : ℕ, ∃ hm : 0 < m,
        4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
        (∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
          Nonempty (OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm)) ∧
        (∀ (rho B : ℝ)
          (S : OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm) (h : Fin m),
          ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9 ∧
          ∃ s ∈ S0, mixedProduct10 A2 A3 L (S.data.M h) s ≠ 0 ∧
            mixedProduct10 A2 A3 L (S.data.M h) s ≤ 362880*((S.data.t h).val^5)^(-17*delta/10)) ∧
    let C_sch := min (1/2 : ℝ) (alpha/180)
    let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
    let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
    let w := JSP000334.omega65 m theta
    ∃ B0 : ℝ,
      B0 = max T (max C_upper (max 2 (max ((2 : ℝ)^(27*(m : ℝ)/(alpha*w*C_sch)))
        (D0^(9*((m : ℝ)*(1+eta))/(alpha*w*C_sch)))))) ∧
      1 < B0 ∧ 0 < C_sch ∧ C_sch ≤ 1 ∧
      0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧
      0 < rho ∧ rho ≤ 1/2 ∧ rho ≤ w ∧ 0 < w ∧
      0 < (2 : ℝ)^(27*(m : ℝ)/(alpha*w*C_sch)) ∧
      0 < D0^(9*((m : ℝ)*(1+eta))/(alpha*w*C_sch)) ∧
      ∀ (B : ℝ), B0 ≤ B →
      ∀ (S : OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm),
            ∃ (C : (h : Fin m) → NormalCoordinateChoice10 (S.data.M h))
              (G : MvPolynomial (Fin m) ℤ),
              G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height10 S.data.P ∧
              (∀ h, G.degreeOf h ≤ S.data.r h) ∧
              G.map (Int.castRingHom ℝ) ∈ monicIdeal6
                (binaryLift6 (permutedNormals10 S.data.M (fun h => (C h).e))) S.data.r ((m : ℝ)*eta) ∧
              (∀ h, 0 < S.data.r h) ∧
              (∀ (h : Fin m) (hh : h.val+1 < m),
                (S.data.r ⟨h.val+1,hh⟩ : ℝ) ≤ w*(S.data.r h : ℝ)) ∧
              let N := permutedNormals10 S.data.M (fun g => (C g).e)
              let b := fun h => rootDenominator6 (N h 0) (N h 1)
              let p := fun h => rootNumerator6 (N h 0) (N h 1)
              (JSP000334.rothIntegerHeight G : ℝ) ≤ D0^((m : ℝ)*(1+eta)*(S.data.r ⟨0,hm⟩ : ℝ)) ∧
              (JSP000334.rothIntegerHeight G : ℝ) ≤
                |(b ⟨0,hm⟩ : ℝ)|^(w*(S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ∧
              ∀ h, B0 < (S.data.t h).val^5 ∧
                ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                N h 0 ≠ 0 ∧ Int.gcd (N h 0) (N h 1)^9 ≤ (N h 0).natAbs^8 ∧
                b h ≠ 0 ∧ Int.gcd (p h) (b h) = 1 ∧
                (normalHeight10 (S.data.M h) : ℝ)^(1/9 : ℝ) ≤ |(b h : ℝ)| ∧
                |(b h : ℝ)| ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                ((S.data.t h).val^5)^(alpha/9) ≤ |(b h : ℝ)| ∧
                |(b ⟨0,hm⟩ : ℝ)|^((S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ≤
                  |(b h : ℝ)|^(S.data.r h : ℝ) ∧
                (2 : ℝ)^(3*m) ≤ |(b h : ℝ)|^(w*C_sch) := by
  obtain ⟨K,hK,D0,E0,alpha,C_upper,T,hD,hE,ha,hC,hT,hinputs⟩ :=
    original_rational_counterexample_samples10 A2 A3 L h2 h3 hLd hL hAlg delta hd S0
  refine ⟨K,hK,D0,E0,alpha,C_upper,T,hD,hE,ha,hC,hT,?_⟩
  intro hfail B1
  obtain ⟨U,hU,hQU,D,hbad,V,hVU,hV,hlarge,e,he,he1,c,hc,hbal,hfin,
    eta,heta,hmargin,m,hm,hcount,hfamily,hheight⟩ := hinputs hfail B1
  refine ⟨U,hU,hQU,D,hbad,V,hVU,hV,hlarge,e,he,he1,c,hc,hbal,hfin,
    eta,heta,hmargin,m,hm,hcount,hfamily,hheight,?_⟩
  obtain ⟨B0,hB0,hB01,hCs,hCs1,ht,htu,htmargin,hr,hrhalf,hrw,hw,hden,hpoly,hbudget⟩ :=
    fixed_sample_schmidt_budgets10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
      V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 alpha C_upper T
      heta hD ha hC hT m hm
  refine ⟨B0,hB0,hB01,hCs,hCs1,ht,htu,htmargin,hr,hrhalf,hrw,hw,hden,hpoly,?_⟩
  intro B hB S
  exact hbudget B hB S (fun h => ⟨(hheight _ B S h).1,(hheight _ B S h).2.1⟩)

end CompoundFeasibility.SourceFixedBudget10
