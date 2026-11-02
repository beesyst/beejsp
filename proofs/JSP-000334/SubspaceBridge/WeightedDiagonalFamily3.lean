import SubspaceBridge.WeightedDiagonalPoint3
namespace JSP000334
open scoped BigOperators Matrix

theorem weighted_integer_source_family3 (Omega : Set ℝ) (hOmega : ¬BddAbove Omega)
    (z : Omega → IntegerTriple) (hy : ∀ q,PrimitiveTriple (z q))
    (hp : ∀ q,∃ choice : Fin 3 → Fin 3,∃ d∈finiteWeightCandidates3 336,
      ∃ hQ : 1<q.val,sourceWeightConditions3 d ∧
      z q∈qSourceLattice3 (choice 1) (choice 2) q.val (d 1) (d 2) ∧
      coordinateGauge3 (qSourceCoordinates3 (choice 0) q.val (d 0) hQ) (integerTripleReal3 (z q))≤q.val^(-(1 : ℝ)/24)) :
    ∃ P : Submodule ℚ (Fin 3 → ℚ),P≠⊤ ∧ ∃ W : Set ℝ,W⊆Omega ∧ ¬BddAbove W ∧
      ∀ q : Omega,q.val∈W → (fun i => (z q i : ℚ))∈P := by
  classical
  choose choice d hd hQ hc hzL hg using hp
  let F : Set ((Fin 3 → Fin 3) × (Fin 3 → Fin 3 → ℝ)) := Set.univ ×ˢ finiteWeightCandidates3 336
  have hF : F.Finite := Set.finite_univ.prod (finiteWeightCandidates3_finite 336)
  let a (Q : ℝ) := if h : Q ∈ Omega then (choice ⟨Q,h⟩,d ⟨Q,h⟩) else (fun _ => 0,fun _ _ => 0)
  have ha : ∀ Q ∈ Omega, a Q ∈ F := by
    intro Q h
    simp only [a,dif_pos h,F,Set.mem_prod,Set.mem_univ,true_and]
    exact hd ⟨Q,h⟩
  obtain ⟨⟨k,c⟩,hkc,hT⟩ := allpoint_finite_parameter_fiber3 F hF Omega hOmega a ha
  let T : Set ℝ := {Q | Q ∈ Omega ∧ a Q = (k,c)}
  let embed (t : T) : Omega := ⟨t.val,t.property.1⟩
  have hcfix : sourceWeightConditions3 c := hkc.2.2
  have he (t : T) : choice (embed t) = k ∧ d (embed t) = c := by
    have hh := t.property.2
    simp only [a,dif_pos t.property.1] at hh
    exact Prod.mk.inj hh
  have htq : ∀ Q ∈ T, 1 < Q := fun Q h => hQ ⟨Q,h.1⟩
  have hmem (t : T) : z (embed t) ∈ qSourceLattice3 (k 1) (k 2) t.val (c 1) (c 2) := by
    have hh := hzL (embed t)
    simpa only [(he t).1,(he t).2] using hh
  have hshort (t : T) : coordinateGauge3 (qSourceCoordinates3 (k 0) t.val (c 0) (htq _ t.property))
      (integerTripleReal3 (z (embed t))) ≤ t.val^(-(1 : ℝ)/24) := by
    have hh := hg (embed t)
    simpa only [(he t).1,(he t).2] using hh
  have hbal : ∑ i, (c 0 i+c 1 i+c 2 i) = 0 := by
    have hh := hcfix.2.2
    simp only [Fin.sum_univ_three] at hh ⊢
    linarith
  have hframe (t : T) : ∃ (B : Basis (Fin 3) ℝ RealTriple)
      (u : Fin 3 → qSourceLattice3 (k 1) (k 2) t.val (c 1) (c 2)),
      lattice3 B = (qSourceLattice3 (k 1) (k 2) t.val (c 1) (c 2)).toIntSubmodule.map integerTripleReal3 ∧
      LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
      ∀ j, coordinateGauge3 (qSourceCoordinates3 (k 0) t.val (c 0) (htq _ t.property))
        (integerTripleReal3 (u j : IntegerTriple)) =
        successiveRadius3 B (qSourceCoordinates3 (k 0) t.val (c 0) (htq _ t.property)) j := by
    obtain ⟨B,u,hB,hu,ha,_⟩ := exists_qSource_integer_attaining_frame (k 0) (k 1) (k 2) t.val
      (c 0) (c 1) (c 2) (htq _ t.property) (fun i => (hcfix.2.1 1 (by decide) i).2)
      (fun i => (hcfix.2.1 2 (by decide) i).2) hbal
    exact ⟨B,u,hB,hu,ha⟩
  choose B u hB hu hatt using hframe
  have hn (t : T) : z (embed t) ≠ 0 := by
    intro heq
    obtain ⟨b,hb⟩ := hy (embed t)
    simp [heq] at hb
  obtain ⟨P,hP,W,hWT,hW,hm⟩ := allpoint_fixed_short_family3 (k 0) (k 1) (k 2) (c 0) (c 1) (c 2)
    (fun i => abs_le.mp (hcfix.1 i)) (hcfix.2.1 1 (by decide)) (hcfix.2.1 2 (by decide)) hbal
    T hT htq B u hB hu hatt (fun t => z (embed t)) hn hmem hshort
  refine ⟨P,hP,W,fun Q hQW => (hWT hQW).1,hW,?_⟩
  intro q hqW
  exact hm ⟨q.val,hWT hqW⟩ hqW

end JSP000334
