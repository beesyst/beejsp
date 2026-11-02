import SubspaceBridge.SourceSampleSchmidtBudgets10
import SubspaceBridge.SourceSchmidtVanishing10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtContradiction10
open SchmidtNormal10 OriginalDual10 SourceSampling10 SourceSelectedSet10 SourceHeightEnvelope10
open SchmidtCoordinate10 SchmidtPolynomial10 SchmidtRationalNormalization6 SchmidtScalar10 SourceSchmidtBudget10

theorem original_sample_schmidt_contradiction10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hc0 : ∀ i, |c 0 i| ≤ 1) (hb : (∑ tau, ∑ i, c tau i) = 0)
    (hc : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ alpha_growth C_upper T C_sch beta : ℝ,
      0 < alpha_growth ∧ 0 < C_upper ∧ 1 < T ∧
      C_sch = min (1/2 : ℝ) (alpha_growth/180) ∧ 0 < C_sch ∧ C_sch ≤ 1 ∧ 0 < beta ∧
      ∀ (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
        (eta D E : ℝ), 0 < eta → 1 ≤ D → ∀ (m : ℕ) (hm : 0 < m),
        (∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
          Nonempty (OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)) →
        let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
        let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
        let w := JSP000334.omega65 m theta
        ∃ B0 : ℝ,
          B0 = max T (max 2 (max ((2 : ℝ)^(27*(m : ℝ)/(beta*w*C_sch)))
            (D^(9*((m : ℝ)*(1+eta))/(beta*w*C_sch))))) ∧
          1 < B0 ∧ 0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧
          0 < rho ∧ rho ≤ 1/2 ∧ rho ≤ w ∧ 0 < w ∧
          0 < (2 : ℝ)^(27*(m : ℝ)/(beta*w*C_sch)) ∧
          0 < D^(9*((m : ℝ)*(1+eta))/(beta*w*C_sch)) ∧
          (∀ B : ℝ, Nonempty
            (OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)) ∧
          ∀ (B : ℝ), B0 ≤ B →
          ∀ (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
            (s : Fin m → MixedIndex10),
            (∀ h, s h ∈ roundedSelector10 ((S.data.t h).val^5) (epsilon/2)
              (fun i => ((S.data.t h).val^5)^(c 0 i)) (c 1) (c 2)) →
            (∀ h, (L⁻¹.transpose *ᵥ integerReal (S.data.M h)) (s h 0) ≠ 0) →
            (∀ h, ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
              (fun k => (S.data.M h k : ℚ_[2]))) (s h 1) ≠ 0) →
            (∀ h, ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
              (fun k => (S.data.M h k : ℚ_[3]))) (s h 2) ≠ 0) →
            False := by
  obtain ⟨a,Cu,T,Cs,beta,ha,hCu,hT,hCs,hCspos,hCsone,hbeta,hbudgets⟩ :=
    original_sample_schmidt_budgets10 A2 A3 L h2 h3 hL hAlg c2 c3 hc2 hc3
      c hc0 hb hc epsilon he
  refine ⟨a,Cu,T,Cs,beta,ha,hCu,hT,hCs,hCspos,hCsone,hbeta,?_⟩
  intro V v eta D E heta hD m hm hfamily
  obtain ⟨B0,hB0,hBpos,ht,htu,hte,hr,hrhalf,hrw,hw,hdpos,hppos,hfamily',happly⟩ :=
    hbudgets V v eta D E heta hD m hm hfamily
  refine ⟨B0,hB0,hBpos,ht,htu,hte,hr,hrhalf,hrw,hw,hdpos,hppos,hfamily',?_⟩
  intro B hB S s hs hn0 hn2 hn3
  obtain ⟨C,G,hGn,_hGH,hdegree,hideal,hdegreepos,hsep,hheight,hdata⟩ :=
    happly B hB S s hs hn0 hn2 hn3
  let N := permutedNormals10 S.data.M (fun h => (C h).e)
  have hcop (h) : rootDenominator6 (N h 0) (N h 1) ≠ 0 ∧
      Int.gcd (rootNumerator6 (N h 0) (N h 1)) (rootDenominator6 (N h 0) (N h 1)) = 1 :=
    ⟨(hdata h).2.2.2.2.1,(hdata h).2.2.2.2.2.1⟩
  exact same_derivative_contradiction10 m hm N _ Cs ((m : ℝ)*eta)
    ht htu hCspos hCsone hte S.data.r G hdegreepos hsep hcop
    (fun h => (hdata h).2.2.2.2.2.2.2.2.2.1)
    (fun h => (hdata h).2.2.2.2.2.2.2.2.2.2)
    hGn hdegree hheight hideal

end CompoundFeasibility.SourceSchmidtContradiction10
