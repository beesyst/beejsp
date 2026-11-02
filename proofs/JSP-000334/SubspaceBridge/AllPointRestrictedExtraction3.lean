import SubspaceBridge.AllPointShortExtraction3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_rank1_extract3 (k0 k2 k3 : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 3 → ℝ)
    (hc0 : ∀ i, -1 ≤ c0 i ∧ c0 i ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k2 k3 Q.val c2 c3)
    (hB : ∀ Q : Omega, lattice3 (B Q) = (qSourceLattice3 k2 k3 Q.val c2 c3).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j,
      coordinateGauge3 (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property))
        (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega,
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) 0 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) 1*Q.val^(-delta))
    (z : Omega → IntegerTriple)
    (hz : ∀ Q : Omega, z Q ∈ qSourceLattice3 k2 k3 Q.val c2 c3)
    (hshort : ∀ Q : Omega, coordinateGauge3 (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property))
      (integerTripleReal3 (z Q)) < successiveRadius3 (B Q)
      (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) 1) :
    ∃ P : Submodule ℚ (Fin 3 → ℚ), P ≠ ⊤ ∧ ∃ W : Set ℝ,
      W ⊆ Omega ∧ ¬ BddAbove W ∧ ∀ Q : Omega, Q.val ∈ W → (fun i => (z Q i : ℚ)) ∈ P := by
  obtain ⟨b,hb0,W,hWO,hW,hfixed⟩ := source_original_fixed_rank1_restricted3 k0 k2 k3 delta hd
    c0 c2 c3 hc0 hc2 hc3 hb Omega hOmega hQ B u hB hu hatt hgap Omega (fun _ h => h) hOmega
  refine ⟨Submodule.span ℚ {fun i => (b i : ℚ)},allpoint_line_proper3 b hb0,W,hWO,hW,?_⟩
  intro Q hQW
  have hfac : Q.val^(-delta) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (hQ _ Q.property) (by linarith)
  obtain ⟨_,_,_,hl,_,_⟩ := exists_successive_minima3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ _ Q.property))
  have hg : successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ _ Q.property)) 0 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ _ Q.property)) 1 :=
    (hgap Q).trans (by nlinarith [hl 1])
  have hm := allpoint_source_short_rational3 k0 k2 k3 Q.val (hQ _ Q.property) c0 c2 c3
    (B Q) (u Q) (hB Q) (hu Q) (hatt Q) 1
    (fun i hi => by
      have he : i = 0 := by omega
      simpa only [he] using hg)
    (z Q) (hz Q) (hshort Q)
  rw [allpoint_first_rational_span3 (fun j => (u Q j : IntegerTriple))] at hm
  rwa [hfixed Q hQW] at hm

theorem allpoint_rank2_extract3 (k0 k2 k3 : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 3 → ℝ)
    (hc0 : ∀ i, -1 ≤ c0 i ∧ c0 i ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k2 k3 Q.val c2 c3)
    (hB : ∀ Q : Omega, lattice3 (B Q) = (qSourceLattice3 k2 k3 Q.val c2 c3).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j,
      coordinateGauge3 (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property))
        (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega,
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) 2*Q.val^(-delta))
    (z : Omega → IntegerTriple)
    (hz : ∀ Q : Omega, z Q ∈ qSourceLattice3 k2 k3 Q.val c2 c3)
    (hshort : ∀ Q : Omega, coordinateGauge3 (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property))
      (integerTripleReal3 (z Q)) < successiveRadius3 (B Q)
      (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) 2) :
    ∃ P : Submodule ℚ (Fin 3 → ℚ), P ≠ ⊤ ∧ ∃ W : Set ℝ,
      W ⊆ Omega ∧ ¬ BddAbove W ∧ ∀ Q : Omega, Q.val ∈ W → (fun i => (z Q i : ℚ)) ∈ P := by
  obtain ⟨b,hb0,W,hWO,hW,hfixed⟩ := source_fixed_last_dual_under_gap3 k0 k2 k3 delta hd
    c0 c2 c3 hc0 hc2 hc3 hb Omega hOmega hQ B u hB hu hatt hgap
  refine ⟨LinearMap.ker (originalPlanePairing3 (fun i => (b i : ℚ))),
    allpoint_kernel_proper3 b hb0,W,hWO,hW,?_⟩
  intro Q hQW
  have hfac : Q.val^(-delta) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (hQ _ Q.property) (by linarith)
  obtain ⟨_,_,_,hl,_,_⟩ := exists_successive_minima3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ _ Q.property))
  have hg : successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ _ Q.property)) 1 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ _ Q.property)) 2 :=
    (hgap Q).trans (by nlinarith [hl 2])
  have hm := allpoint_source_short_rational3 k0 k2 k3 Q.val (hQ _ Q.property) c0 c2 c3
    (B Q) (u Q) (hB Q) (hu Q) (hatt Q) 2
    (fun i hi => (successiveRadius3_monotone (B Q) _ (show i ≤ 1 by omega)).trans_lt hg)
    (z Q) (hz Q) (hshort Q)
  have hann := allpoint_plane_annihilation3 (fun j => (u Q j : IntegerTriple)) (hu Q) _ hm
  have hbmem : (fun i => (b i : ℚ)) ∈
      Submodule.span ℚ {dualFrameVector3 (fun j => (u Q j : IntegerTriple)) 2} := by
    rw [hfixed Q hQW]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hbmem
  change originalPlanePairing3 (fun i => (b i : ℚ)) (fun i => (z Q i : ℚ)) = 0
  rw [← hr]
  change (∑ i, (z Q i : ℚ)*(r*dualFrameVector3 (fun j => (u Q j : IntegerTriple)) 2 i)) = 0
  calc
    _ = r*(∑ i, (z Q i : ℚ)*dualFrameVector3 (fun j => (u Q j : IntegerTriple)) 2 i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      change r*originalPlanePairing3 (dualFrameVector3 (fun j => (u Q j : IntegerTriple)) 2)
        (fun i => (z Q i : ℚ)) = 0
      rw [hann,mul_zero]

end JSP000334
