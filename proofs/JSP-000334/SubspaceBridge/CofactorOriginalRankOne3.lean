import SubspaceBridge.CofactorGapPersistence3
import SubspaceBridge.CofactorExteriorTransport3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

theorem source_original_fixed_rank1_3 (k0 k2 k3 : Fin 3) (delta : ℝ) (hd : 0 < delta)
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
      successiveRadius3 (B Q) (qSourceCoordinates3 k0 Q.val c0 (hQ Q.val Q.property)) 1*Q.val^(-delta)) :
    ∃ b : IntegerTriple, b ≠ 0 ∧ ∃ W : Set ℝ, W ⊆ Omega ∧ ¬ BddAbove W ∧
      ∀ Q : Omega, Q.val ∈ W →
        Submodule.span ℚ {fun i => ((u Q 0 : IntegerTriple) i : ℚ)} =
          Submodule.span ℚ {fun i => (b i : ℚ)} := by
  classical
  obtain ⟨C,hC,hcut⟩ := exterior_square_cutoff3 delta hd
  let O : Set ℝ := {Q | Q ∈ Omega ∧ C < Q}
  have hO : ¬ BddAbove O := sourceDual_unbounded_tail3 Omega hOmega C
  let embed (q : O) : Omega := ⟨q.val,q.property.1⟩
  have hq (q : O) : 1 < q.val := hQ _ q.property.1
  obtain ⟨h0,h2,h3,hbalance⟩ := pairWeights3_bounds c0 c2 c3 hc0 hc2 hc3 hb
  have hdata (q : O) :
      ∃ (D : Basis (Fin 3) ℝ RealTriple)
        (v : Fin 3 → cofactorSourceLattice3 k2 k3 (q.val^2) (pairWeights3 c2) (pairWeights3 c3)),
        lattice3 D = (cofactorSourceLattice3 k2 k3 (q.val^2) (pairWeights3 c2) (pairWeights3 c3)).toIntSubmodule.map integerTripleReal3 ∧
        LinearIndependent ℝ (fun j => integerTripleReal3 (v j : IntegerTriple)) ∧
        (∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k0 (q.val^2) (pairWeights3 c0) (pairWeights3_Q_squared _ (hq q)))
          (integerTripleReal3 (v j : IntegerTriple)) = successiveRadius3 D
          (cofactorSourceCoordinates3 k0 (q.val^2) (pairWeights3 c0) (pairWeights3_Q_squared _ (hq q))) j) ∧
        successiveRadius3 D (cofactorSourceCoordinates3 k0 (q.val^2) (pairWeights3 c0) (pairWeights3_Q_squared _ (hq q))) 1 <
          successiveRadius3 D (cofactorSourceCoordinates3 k0 (q.val^2) (pairWeights3 c0) (pairWeights3_Q_squared _ (hq q))) 2*(q.val^2)^(-delta/4) ∧
        Submodule.span ℚ {fun i => ((u (embed q) 0 : IntegerTriple) i : ℚ)} =
          Submodule.span ℚ {dualFrameVector3 (fun j => (v j : IntegerTriple)) 2} := by
    obtain ⟨D,v,hD,hv,ha,_⟩ := exists_cofactorSource_integer_attaining_frame k0 k2 k3 (q.val^2)
      (pairWeights3 c0) (pairWeights3 c2) (pairWeights3 c3) (pairWeights3_Q_squared _ (hq q))
      (fun i => (h2 i).2) (fun i => (h3 i).2) hbalance
    have hp := source_exterior_square_gap_plane3 k0 k2 k3 q.val delta (hq q) hd c0 c2 c3
      hc0 hc2 hc3 hb (B (embed q)) (u (embed q)) (hB (embed q)) (hu (embed q))
      (hatt (embed q)) (hgap (embed q)) D v hD hv ha (hcut _ q.property.2)
    exact ⟨D,v,hD,hv,ha,hp.1,hp.2⟩
  choose D v hD hv ha hg hs using hdata
  let T : Set ℝ := {t | ∃ q : O, q.val^2 = t}
  let original (t : T) : O := Classical.choose t.property
  have parameter (t : T) : (original t).val^2 = t.val := Classical.choose_spec t.property
  have hT : ¬ BddAbove T := by
    rintro ⟨M,hM⟩
    apply hO
    refine ⟨max 1 M,?_⟩
    intro Q hQO
    have hp := hM (show Q^2 ∈ T from ⟨⟨Q,hQO⟩,rfl⟩)
    have hQone := hQ Q hQO.1
    have hMM := le_max_right 1 M
    nlinarith [sq_nonneg (Q-1)]
  have htq (t : T) : 1 < t.val := by
    rw [← parameter t]
    exact pairWeights3_Q_squared _ (hq (original t))
  let vt (t : T) : Fin 3 → cofactorSourceLattice3 k2 k3 t.val (pairWeights3 c2) (pairWeights3 c3) :=
    fun j => ⟨(v (original t) j : IntegerTriple),by
      have hh := (v (original t) j).property
      exact Eq.mp (congrArg (fun q : ℝ =>
        (v (original t) j : IntegerTriple) ∈
          cofactorSourceLattice3 k2 k3 q (pairWeights3 c2) (pairWeights3 c3)) (parameter t)) hh⟩
  have he (t : T) : cofactorSourceCoordinates3 k0 t.val (pairWeights3 c0) (htq t) =
      cofactorSourceCoordinates3 k0 ((original t).val^2) (pairWeights3 c0) (pairWeights3_Q_squared _ (hq (original t))) := by
    congr 1
    exact (parameter t).symm
  have hDt (t : T) : lattice3 (D (original t)) =
      (cofactorSourceLattice3 k2 k3 t.val (pairWeights3 c2) (pairWeights3 c3)).toIntSubmodule.map integerTripleReal3 := by
    rw [← parameter t]
    exact hD (original t)
  have hvt (t : T) : LinearIndependent ℝ (fun j => integerTripleReal3 (vt t j : IntegerTriple)) := hv (original t)
  have hat (t : T) (j : Fin 3) : coordinateGauge3 (cofactorSourceCoordinates3 k0 t.val (pairWeights3 c0) (htq t))
      (integerTripleReal3 (vt t j : IntegerTriple)) =
      successiveRadius3 (D (original t)) (cofactorSourceCoordinates3 k0 t.val (pairWeights3 c0) (htq t)) j := by
    rw [he t]
    exact ha (original t) j
  have hgt (t : T) : successiveRadius3 (D (original t)) (cofactorSourceCoordinates3 k0 t.val (pairWeights3 c0) (htq t)) 1 <
      successiveRadius3 (D (original t)) (cofactorSourceCoordinates3 k0 t.val (pairWeights3 c0) (htq t)) 2*t.val^(-(delta/4)) := by
    rw [he t,← parameter t]
    simpa only [neg_div] using hg (original t)
  obtain ⟨b,hb0,V,hVT,hV,hfixed⟩ := cofactor_source_fixed_last_dual_under_gap3 k0 k2 k3 (delta/4)
    (by linarith) (pairWeights3 c0) (pairWeights3 c2) (pairWeights3 c3) h0 h2 h3 hbalance
    T hT (fun t ht => htq ⟨t,ht⟩) (fun t => D (original t)) vt hDt hvt hat hgt
  let W : Set ℝ := {Q | ∃ t : T, t.val ∈ V ∧ (original t).val = Q}
  have hWO : W ⊆ Omega := by
    rintro Q ⟨t,ht,heq⟩
    rw [← heq]
    exact (original t).property.1
  have hW : ¬ BddAbove W := by
    rintro ⟨M,hM⟩
    apply hV
    refine ⟨(max 1 M)^2,?_⟩
    intro t ht
    let s : T := ⟨t,hVT ht⟩
    have hqM : (original s).val ≤ M := hM ⟨s,ht,rfl⟩
    have hq0 : 0 ≤ (original s).val := (lt_trans zero_lt_one (hq (original s))).le
    have hp := pow_le_pow_left₀ hq0 (hqM.trans (le_max_right 1 M)) 2
    simpa only [parameter s] using hp
  refine ⟨b,hb0,W,hWO,hW,?_⟩
  rintro Q ⟨t,ht,heq⟩
  have hline := (hs (original t)).trans (hfixed t ht)
  have hqeq : embed (original t) = Q := Subtype.ext heq
  cases hqeq
  exact hline

theorem source_original_fixed_rank1_restricted3 (k0 k2 k3 : Fin 3) (delta : ℝ) (hd : 0 < delta)
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
    (U : Set ℝ) (hU : U ⊆ Omega) (hUb : ¬ BddAbove U) :
    ∃ b : IntegerTriple, b ≠ 0 ∧ ∃ W : Set ℝ, W ⊆ U ∧ ¬ BddAbove W ∧
      ∀ Q : Omega, Q.val ∈ W →
        Submodule.span ℚ {fun i => ((u Q 0 : IntegerTriple) i : ℚ)} =
          Submodule.span ℚ {fun i => (b i : ℚ)} := by
  let f (q : U) : Omega := ⟨q.val,hU q.property⟩
  obtain ⟨b,hb0,W,hWU,hW,hl⟩ := source_original_fixed_rank1_3 k0 k2 k3 delta hd c0 c2 c3
    hc0 hc2 hc3 hb U hUb (fun Q hQU => hQ Q (hU hQU))
    (fun q => B (f q)) (fun q => u (f q)) (fun q => hB (f q))
    (fun q => hu (f q)) (fun q => hatt (f q)) (fun q => hgap (f q))
  refine ⟨b,hb0,W,hWU,hW,?_⟩
  intro Q hQW
  exact hl ⟨Q.val,hWU hQW⟩ hQW

end
end JSP000334
