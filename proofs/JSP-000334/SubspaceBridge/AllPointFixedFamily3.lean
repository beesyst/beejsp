import SubspaceBridge.AllPointRestrictedExtraction3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_finite_parameter_fiber3 {A : Type*} (F : Set A) (hF : F.Finite)
    (U : Set ℝ) (hU : ¬ BddAbove U) (a : ℝ → A) (ha : ∀ Q ∈ U, a Q ∈ F) :
    ∃ d ∈ F, ¬ BddAbove {Q | Q ∈ U ∧ a Q = d} := by
  classical
  by_contra hnone
  have hb (d : F) : BddAbove {Q | Q ∈ U ∧ a Q = d.val} := by
    by_contra h
    exact hnone ⟨d.val,d.property,h⟩
  choose b hb using hb
  letI := hF.fintype
  obtain ⟨B,hB⟩ := (Set.finite_range b).bddAbove
  apply hU
  refine ⟨B,?_⟩
  intro Q hQ
  let d : F := ⟨a Q,ha Q hQ⟩
  exact (hb d ⟨hQ,rfl⟩).trans (hB (Set.mem_range_self d))

theorem allpoint_fixed_short_family3 (k0 k2 k3 : Fin 3)
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

    (z : Omega → IntegerTriple) (hz0 : ∀ Q : Omega, z Q ≠ 0)
    (hz : ∀ Q : Omega, z Q ∈ qSourceLattice3 k2 k3 Q.val c2 c3)
    (hshort : ∀ Q : Omega, coordinateGauge3 (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property))
      (integerTripleReal3 (z Q)) ≤ Q.val^(-(1 : ℝ)/24)) :
    ∃ P : Submodule ℚ (Fin 3 → ℚ), P ≠ ⊤ ∧ ∃ W : Set ℝ,
      W ⊆ Omega ∧ ¬ BddAbove W ∧ ∀ Q : Omega, Q.val ∈ W → (fun i => (z Q i : ℚ)) ∈ P := by
  classical
  obtain ⟨C,hC,hcut⟩ := allpoint_rank_cutoff3 ((1 : ℝ)/24) (by norm_num)
  let O : Set ℝ := {Q | Q ∈ Omega ∧ C < Q}
  have hO : ¬ BddAbove O := sourceDual_unbounded_tail3 Omega hOmega C
  let embed (q : O) : Omega := ⟨q.val,q.property.1⟩
  have hdata (q : O) : ∃ k : Fin 3, (k = 1 ∨ k = 2) ∧
      successiveRadius3 (B (embed q)) (qSourceCoordinates3 k0 q.val c0 (hQ _ q.property.1)) (k-1) <
        successiveRadius3 (B (embed q)) (qSourceCoordinates3 k0 q.val c0 (hQ _ q.property.1)) k*q.val^(-((1 : ℝ)/192)) ∧
      coordinateGauge3 (qSourceCoordinates3 k0 q.val c0 (hQ _ q.property.1)) (integerTripleReal3 (z (embed q))) <
        successiveRadius3 (B (embed q)) (qSourceCoordinates3 k0 q.val c0 (hQ _ q.property.1)) k := by
    have hmem (v : qSourceLattice3 k2 k3 q.val c2 c3) : integerTripleReal3 (v : IntegerTriple) ∈ lattice3 (B (embed q)) := by
      rw [hB (embed q)]
      exact Submodule.mem_map.mpr ⟨(v : IntegerTriple),v.property,rfl⟩
    have hzmem : integerTripleReal3 (z (embed q)) ∈ lattice3 (B (embed q)) :=
      hmem ⟨z (embed q),hz (embed q)⟩
    have hn : integerTripleReal3 (z (embed q)) ≠ 0 := by
      intro he
      apply hz0 (embed q)
      apply integerTripleReal3_injective
      simpa only [map_zero] using he
    have hp := (gap_source_product3 k0 k2 k3 q.val c0 c2 c3 (hQ _ q.property.1)
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb (B (embed q)) (u (embed q))
      (hB (embed q)) (hatt (embed q))).1
    obtain ⟨k,hk,hg,hs,_⟩ := allpoint_rank_threshold3 ((1 : ℝ)/24) q.val (by norm_num)
      (hQ _ q.property.1) (hcut _ q.property.2) (B (embed q))
      (qSourceCoordinates3 k0 q.val c0 (hQ _ q.property.1))
      (fun j => integerTripleReal3 (u (embed q) j : IntegerTriple)) (hu (embed q))
      (fun j => hmem (u (embed q) j)) (hatt (embed q)) (integerTripleReal3 (z (embed q)))
      hzmem hn (by simpa only [neg_div] using hshort (embed q)) hp
    exact ⟨k,hk,by norm_num at hg; exact hg,hs⟩
  choose k hk hg hs using hdata
  let f (Q : ℝ) : Fin 3 := if h : Q ∈ O then k ⟨Q,h⟩ else 0
  obtain ⟨r,_,hT⟩ := allpoint_finite_parameter_fiber3 (Set.univ : Set (Fin 3)) Set.finite_univ O hO f (by intros; trivial)
  let T : Set ℝ := {Q | Q ∈ O ∧ f Q = r}
  let original (t : T) : O := ⟨t.val,t.property.1⟩
  let e (t : T) : Omega := embed (original t)
  have hkr (t : T) : k (original t) = r := by
    simpa only [f,dif_pos t.property.1,original] using t.property.2
  obtain ⟨t,ht,_⟩ := not_bddAbove_iff.mp hT 0
  have hr : r = 1 ∨ r = 2 := by
    rw [← hkr ⟨t,ht⟩]
    exact hk (original ⟨t,ht⟩)
  have hQt : ∀ Q ∈ T, 1 < Q := fun Q hQT => hQ Q hQT.1.1
  have hBT (t : T) : lattice3 (B (e t)) = (qSourceLattice3 k2 k3 t.val c2 c3).toIntSubmodule.map integerTripleReal3 := hB (e t)
  rcases hr with hr | hr
  · have hgT (t : T) : successiveRadius3 (B (e t)) (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) 0 <
        successiveRadius3 (B (e t)) (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) 1*t.val^(-((1 : ℝ)/192)) := by
      have hh := hg (original t)
      rw [hkr t,hr] at hh
      simpa using hh
    have hsT (t : T) : coordinateGauge3 (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) (integerTripleReal3 (z (e t))) <
        successiveRadius3 (B (e t)) (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) 1 := by
      have hh := hs (original t)
      rw [hkr t,hr] at hh
      exact hh
    obtain ⟨P,hP,W,hWT,hW,hm⟩ := allpoint_rank1_extract3 k0 k2 k3 ((1 : ℝ)/192) (by norm_num)
      c0 c2 c3 hc0 hc2 hc3 hb T hT hQt (fun t => B (e t)) (fun t => u (e t)) hBT
      (fun t => hu (e t)) (fun t => hatt (e t)) hgT (fun t => z (e t)) (fun t => hz (e t)) hsT
    refine ⟨P,hP,W,fun Q hQW => (hWT hQW).1.1,hW,?_⟩
    intro Q hQW
    exact hm ⟨Q.val,hWT hQW⟩ hQW
  · have hgT (t : T) : successiveRadius3 (B (e t)) (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) 1 <
        successiveRadius3 (B (e t)) (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) 2*t.val^(-((1 : ℝ)/192)) := by
      have hh := hg (original t)
      rw [hkr t,hr] at hh
      simpa using hh
    have hsT (t : T) : coordinateGauge3 (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) (integerTripleReal3 (z (e t))) <
        successiveRadius3 (B (e t)) (qSourceCoordinates3 k0 t.val c0 (hQt _ t.property)) 2 := by
      have hh := hs (original t)
      rw [hkr t,hr] at hh
      exact hh
    obtain ⟨P,hP,W,hWT,hW,hm⟩ := allpoint_rank2_extract3 k0 k2 k3 ((1 : ℝ)/192) (by norm_num)
      c0 c2 c3 hc0 hc2 hc3 hb T hT hQt (fun t => B (e t)) (fun t => u (e t)) hBT
      (fun t => hu (e t)) (fun t => hatt (e t)) hgT (fun t => z (e t)) (fun t => hz (e t)) hsT
    refine ⟨P,hP,W,fun Q hQW => (hWT hQW).1.1,hW,?_⟩
    intro Q hQW
    exact hm ⟨Q.val,hWT hQW⟩ hQW

end JSP000334
