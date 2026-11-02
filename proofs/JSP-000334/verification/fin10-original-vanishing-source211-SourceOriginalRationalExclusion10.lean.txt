import SubspaceBridge.SourceOriginalSampleExclusion10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalVanishing10
open SourceFixedBudget10 SourceOriginalDual10 SourceOriginalVariable10 SourceSelectedSet10

theorem original_rational_failure_contradiction10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10)
    (hfail : ∀ B : ℝ, ∃ Q : ℝ, ∃ hQ : 1 < Q, B < Q ∧
      ∃ D : OriginalData10 A2 A3 L hL Q hQ delta S0,
        ∃ s ∈ S0, dataRationalDualProduct10 D s ≠ 0) : False := by
  obtain ⟨K,_hK,D0,E0,alpha,C_upper,T,_hD,_hE,_ha,_hC,_hT,hinputs⟩ :=
    original_rational_fixed_budgets10 A2 A3 L h2 h3 hLd hL hAlg delta hd S0
  obtain ⟨U,_hU,hQU,D,_hbad,V,hVU,_hV,_hlarge,e,_he,_he1,c,_hc,_hbal,_hfin,
    eta,_heta,_hmargin,m,hm,_hcount,hfamily,_hheight,hpackage⟩ := hinputs hfail 0
  let theta := min (1/24 : ℝ) ((m : ℝ)*eta/2)
  let rho := min (1/2 : ℝ) (JSP000334.omega65 m theta)
  obtain ⟨B0,_hB0,_hB01,hCs,hCs1,ht,htu,hmargin,hr,_hrhalf,_hrw,_hw,_hden,_hpoly,hbudget⟩ := hpackage
  obtain ⟨S⟩ := hfamily rho hr B0
  exact actual_sample_budget_contradiction10 S alpha B0 theta
    (min (1/2 : ℝ) (alpha/180)) ht htu hCs hCs1 hmargin (hbudget B0 le_rfl S)

end CompoundFeasibility.SourceOriginalVanishing10
