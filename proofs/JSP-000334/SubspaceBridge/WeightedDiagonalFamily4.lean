import SubspaceBridge.WeightedDiagonalPoint4
import SubspaceBridge.AllPointSourceFamily4
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_integer_source_family4 (Omega : Set ℝ) (hOmega : ¬BddAbove Omega)
    (z : Omega → Fin 4 → ℤ)
    (hp : ∀ q : Omega,∃ choice : Fin 3 → Fin 4,∃ d∈finiteWeightCandidates4 560,
      sourceWeightConditions4 d ∧
      CompoundFeasibility.OriginalVariableGap4.originalSourceSolution4
        (retainedRationalMatrix4 (choice 1)) (retainedRationalMatrix4 (choice 2))
        (retainedRealMatrix4 (choice 0)) (d 0) (d 1) (d 2) q.val ((1 : ℝ)/80) (z q)) :
    ∃ P : Submodule ℚ (Fin 4 → ℚ),P≠⊤ ∧ ∃ W : Set ℝ,W⊆Omega ∧ ¬BddAbove W ∧
      ∀ q : Omega,q.val∈W → (fun i => (z q i : ℚ))∈P := by
  classical
  choose choice d hd hc hsol using hp
  let F : Set ((Fin 3 → Fin 4) × (Fin 3 → Fin 4 → ℝ)) := Set.univ ×ˢ finiteWeightCandidates4 560
  have hF : F.Finite := Set.finite_univ.prod (finiteWeightCandidates4_finite 560)
  let a (Q : ℝ) := if h : Q∈Omega then (choice ⟨Q,h⟩,d ⟨Q,h⟩) else (fun _ => 0,fun _ _ => 0)
  have ha : ∀ Q∈Omega,a Q∈F := by
    intro Q h
    simp only [a,dif_pos h,F,Set.mem_prod,Set.mem_univ,true_and]
    exact hd ⟨Q,h⟩
  obtain ⟨⟨k,c⟩,hkc,hT⟩ := allpoint_finite_parameter_fiber3 F hF Omega hOmega a ha
  let T : Set ℝ := {Q | Q∈Omega ∧ a Q=(k,c)}
  let embed (t : T) : Omega := ⟨t.val,t.property.1⟩
  have he (t : T) : choice (embed t)=k ∧ d (embed t)=c := by
    have hh := t.property.2
    simp only [a,dif_pos t.property.1] at hh
    exact Prod.mk.inj hh
  have hcfix : sourceWeightConditions4 c := hkc.2.2
  have hs (t : T) : CompoundFeasibility.OriginalVariableGap4.originalSourceSolution4
      (retainedRationalMatrix4 (k 1)) (retainedRationalMatrix4 (k 2))
      (retainedRealMatrix4 (k 0)) (c 0) (c 1) (c 2) t.val ((1 : ℝ)/80) (z (embed t)) := by
    have hh := hsol (embed t)
    simpa only [(he t).1,(he t).2] using hh
  have htQ : ∀ Q∈T,1<Q := fun Q h => (hs ⟨Q,h⟩).2.1
  have hbal : ∑ i : Fin 4,(c 0 i+c 1 i+c 2 i)=0 := by
    have hh := hcfix.2.2
    simpa [Fin.sum_univ_three,Finset.sum_add_distrib] using hh
  have hAlg : ∀ i j,IsAlgebraic ℚ (retainedRealMatrix4 (k 0) i j) := by
    intro i j
    exact isAlgebraic_int _
  obtain ⟨P,hP,W,hWT,hW,hm⟩ := allpoint_fixed_source_family4
    (retainedRationalMatrix4 (k 1)) (retainedRationalMatrix4 (k 2))
    (retainedRealMatrix4 (k 0)) (retained_rational_det4 _) (retained_rational_det4 _)
    (retained_real_det4 _) hAlg (c 0) (c 1) (c 2) hcfix.1
    (hcfix.2.1 1 (by decide)) (hcfix.2.1 2 (by decide)) hbal ((1 : ℝ)/80) (by norm_num)
    T hT htQ (fun t => z (embed t)) hs
  refine ⟨P,hP,W,fun Q h => (hWT h).1,hW,?_⟩
  intro q hqW
  exact hm ⟨q.val,hWT hqW⟩ hqW

end JSP000334
