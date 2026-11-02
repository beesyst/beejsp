import SubspaceBridge.SourceOriginalFixedBudgets10
import SubspaceBridge.SourceSchmidtVanishing10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalVanishing10
open SourceFixedBudget10 SourceSchmidtContradiction10 SourceOriginalDual10 SourceOriginalVariable10
open SchmidtNormal10 OriginalDual10 SourceSampling10 SourceSelectedSet10
open SchmidtCoordinate10 SchmidtPolynomial10 SchmidtRationalNormalization6 SchmidtScalar10

theorem actual_sample_budget_contradiction10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
    {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (alpha B0 theta C_sch : ℝ)
    (ht : 0 < theta) (htu : theta < 1/12) (hCs : 0 < C_sch) (hCs1 : C_sch ≤ 1)
    (hmargin : theta < (m : ℝ)*eta)
    (hbudget :
            ∃ (C : (h : Fin m) → NormalCoordinateChoice10 (S.data.M h))
              (G : MvPolynomial (Fin m) ℤ),
              G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height10 S.data.P ∧
              (∀ h, G.degreeOf h ≤ S.data.r h) ∧
              G.map (Int.castRingHom ℝ) ∈ monicIdeal6
                (binaryLift6 (permutedNormals10 S.data.M (fun h => (C h).e))) S.data.r ((m : ℝ)*eta) ∧
              (∀ h, 0 < S.data.r h) ∧
              (∀ (h : Fin m) (hh : h.val+1 < m),
                (S.data.r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(S.data.r h : ℝ)) ∧
              let N := permutedNormals10 S.data.M (fun g => (C g).e)
              let b := fun h => rootDenominator6 (N h 0) (N h 1)
              let p := fun h => rootNumerator6 (N h 0) (N h 1)
              (JSP000334.rothIntegerHeight G : ℝ) ≤ D^((m : ℝ)*(1+eta)*(S.data.r ⟨0,hm⟩ : ℝ)) ∧
              (JSP000334.rothIntegerHeight G : ℝ) ≤
                |(b ⟨0,hm⟩ : ℝ)|^(JSP000334.omega65 m theta*(S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ∧
              ∀ h, B0 < (S.data.t h).val^5 ∧
                ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                N h 0 ≠ 0 ∧ Int.gcd (N h 0) (N h 1)^9 ≤ (N h 0).natAbs^8 ∧
                b h ≠ 0 ∧ Int.gcd (p h) (b h) = 1 ∧
                (normalHeight10 (S.data.M h) : ℝ)^(1/9 : ℝ) ≤ |(b h : ℝ)| ∧
                |(b h : ℝ)| ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
                ((S.data.t h).val^5)^(alpha/9) ≤ |(b h : ℝ)| ∧
                |(b ⟨0,hm⟩ : ℝ)|^((S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ≤
                  |(b h : ℝ)|^(S.data.r h : ℝ) ∧
                (2 : ℝ)^(3*m) ≤ |(b h : ℝ)|^(JSP000334.omega65 m theta*C_sch) ) : False := by
  obtain ⟨C,G,hGn,_hGH,hdeg,hideal,hpos,hsep,_hGHpower,hpoly,hdata⟩ := hbudget
  let N := permutedNormals10 S.data.M (fun h => (C h).e)
  have hb (h : Fin m) : rootDenominator6 (N h 0) (N h 1) ≠ 0 ∧
      Int.gcd (rootNumerator6 (N h 0) (N h 1)) (rootDenominator6 (N h 0) (N h 1)) = 1 := by
    obtain ⟨_hcut,_hheight,_hN,_hgcd,hbn,hcop,_hroot,_hupper,_hlower,_hgrow,_hden⟩ := hdata h
    exact ⟨hbn,hcop⟩
  have hgrowth (h : Fin m) :
      |(rootDenominator6 (N ⟨0,hm⟩ 0) (N ⟨0,hm⟩ 1) : ℝ)|^((S.data.r ⟨0,hm⟩ : ℝ)*C_sch) ≤
      |(rootDenominator6 (N h 0) (N h 1) : ℝ)|^(S.data.r h : ℝ) := by
    obtain ⟨_hcut,_hheight,_hN,_hgcd,_hbn,_hcop,_hroot,_hupper,_hlower,hgrow,_hden⟩ := hdata h
    exact hgrow
  have hden (h : Fin m) : (2 : ℝ)^(3*m) ≤
      |(rootDenominator6 (N h 0) (N h 1) : ℝ)|^(JSP000334.omega65 m theta*C_sch) := by
    obtain ⟨_hcut,_hheight,_hN,_hgcd,_hbn,_hcop,_hroot,_hupper,_hlower,_hgrow,hden⟩ := hdata h
    exact hden
  exact same_derivative_contradiction10 m hm N theta C_sch ((m : ℝ)*eta)
    ht htu hCs hCs1 hmargin S.data.r G hpos hsep hb hgrowth hden hGn hdeg hpoly hideal

end CompoundFeasibility.SourceOriginalVanishing10
