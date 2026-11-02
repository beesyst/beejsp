import SubspaceBridge.SchmidtSatz11Conclusion6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Satz11Fin6Replay
open Auxiliary6 SourceNormalIndex SourceMultiblock SchmidtIndexSemantics6
open SchmidtCoordinateTransport6 SchmidtNormalSubstitution6 SchmidtExcessElimination6
open SchmidtScalarDehomogenization6 SchmidtRationalNormalization6 SchmidtTaylorCorrespondence6
open SourceSchmidtParameters6 SourceReadiness6

open SchmidtHilfssatz12Readiness6

open SchmidtSatz11Conclusion6
variable
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV} {s : SourceMixed6.MixedIndex6}

theorem exact_source_upper (S : SchmidtPackage6 R s) :
    ∀ c : ℝ, S.theta < c → S.P.map (Int.castRingHom ℝ) ∉
      sourceNormalIdeal6 (fun h => R.M (S.t h)) S.r c := schmidtPackage6_source_upper S

theorem exact_package_contradiction (S : SchmidtPackage6 R s) : False := schmidtPackage6_impossible S

theorem exact_nonzero_ready_exclusion
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (s : SourceMixed6.MixedIndex6) :
    ¬ R.nonzeroReady s := nonzeroReady_excluded6 R s

theorem exact_eventual_zero
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    ∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ SourceMixed6.admissibleMixed6 R.c (R.delta/2),
      SourceMixed6.actualNormProduct6 A2 A3 L (R.M q) s = 0 := source_eventual_zero6 R

end CompoundFeasibility.Satz11Fin6Replay

#print axioms CompoundFeasibility.Satz11Fin6Replay.exact_source_upper
#print axioms CompoundFeasibility.Satz11Fin6Replay.exact_package_contradiction
#print axioms CompoundFeasibility.Satz11Fin6Replay.exact_nonzero_ready_exclusion
#print axioms CompoundFeasibility.Satz11Fin6Replay.exact_eventual_zero
