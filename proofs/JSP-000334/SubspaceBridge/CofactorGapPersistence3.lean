import SubspaceBridge.CofactorGap3
import SubspaceBridge.OriginalPlaneTransport3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

theorem cofactor_originalPlane_deformed_transport3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) = successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) j)
    (hgap : successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      successiveRadius3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta))
    (d : cofactor_GapDeformedData3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ B u)
    (hcut : 3072 < Q ^ (2 * delta)) :
    (∀ i : Fin 2, integerTripleReal3 (d.frame (Fin.castLE (by decide) i) : IntegerTriple) ∈
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2) ∧
    minimaFlag3 (fun j => integerTripleReal3 (d.frame j : IntegerTriple)) 2 =
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2 ∧
    Submodule.span ℚ {dualFrameVector3 (fun j => (d.frame j : IntegerTriple)) 2} =
      Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} := by
  have hQ0 := lt_trans zero_lt_one hQ
  obtain ⟨_,_,_,hl,_,_⟩ := exists_successive_minima3 B (cofactorSourceCoordinates3 k₀ Q c₀ hQ)
  have hp := (cofactor_gap_source_product3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb B u hB hatt).1
  have hsep := originalPlane_off_plane_margin3 _ hl Q delta hQ0 hp hgap hcut
  have hQ5 : 1 < Q ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hQ (by norm_num : (0 : ℝ) < 5)
  have hsmall : successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) d.widths d.positive) 1 < 1 :=
    d.small.trans (by simpa using Real.rpow_lt_rpow_of_exponent_lt hQ5 (show -(delta / 18) < 0 by linarith))
  have hmem (i : Fin 2) : integerTripleReal3 (d.frame (Fin.castLE (by decide) i) : IntegerTriple) ∈
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2 := by
    let k : Fin 3 := Fin.castLE (by decide) i
    let z : cofactorSourceLattice3 k₂ k₃ Q c₂ c₃ := ⟨(d.frame k : IntegerTriple), by
      have hz := (d.frame k).property
      exact Eq.mp (congrArg (fun G : AddSubgroup IntegerTriple => (d.frame k : IntegerTriple) ∈ G)
        (cofactor_gap_rescaled_lattice3 k₂ k₃ Q c₂ c₃ hQ0)) hz⟩
    have hk : k ≤ 1 := by change i.val ≤ 1; omega
    have hm := successiveRadius3_monotone B (archCoordinates3 (cofactorRealCoordinates3 k₀) d.widths d.positive) hk
    have hg : coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) d.widths d.positive)
        (integerTripleReal3 (z : IntegerTriple)) < 1 := by
      rw [d.attaining]
      exact hm.trans_lt hsmall
    apply Classical.byContradiction
    intro hout
    have hh := d.separation 2 z hout
    linarith
  have hle : minimaFlag3 (fun j => integerTripleReal3 (d.frame j : IntegerTriple)) 2 ≤
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hmem i
  have heq : minimaFlag3 (fun j => integerTripleReal3 (d.frame j : IntegerTriple)) 2 =
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2 :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [minimaFlag3_finrank _ d.independent, minimaFlag3_finrank _ hu])
  exact ⟨hmem,heq,originalPlane_real_to_rational_dual3 _ _ hu d.independent heq⟩

theorem cofactor_originalPlane_pullback_unbounded3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (Omega : Set ℝ) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (F : cofactor_GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u)
    (U : Set ℝ) (hU : U ⊆ F.domain) (hUb : ¬ BddAbove U) :
    ¬ BddAbove {Q : ℝ | ∃ t : F.domain, t.val ∈ U ∧ (F.original t).val = Q} := by
  rintro ⟨b,hb⟩
  apply hUb
  refine ⟨(max 1 b) ^ (5 : ℕ),?_⟩
  intro t ht
  let s : F.domain := ⟨t,hU ht⟩
  have hq : (F.original s).val ≤ b := hb ⟨s,ht,rfl⟩
  have hq0 : 0 ≤ (F.original s).val := (lt_trans zero_lt_one (hQ _ (F.original s).property)).le
  have hp := pow_le_pow_left₀ hq0 (hq.trans (le_max_right 1 b)) 5
  simpa only [F.parameter s] using hp

theorem cofactor_source_fixed_last_dual_under_gap3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega, successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (cofactorSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta)) :
    ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ V : Set ℝ, V ⊆ Omega ∧ ¬ BddAbove V ∧
      ∀ Q : Omega, Q.val ∈ V →
        Submodule.span ℚ {dualFrameVector3 (fun j => (u Q j : IntegerTriple)) 2} =
          Submodule.span ℚ {fun i => (v i : ℚ)} := by
  obtain ⟨C,hC⟩ := originalPlane_power_cutoff3 delta hd
  let cut := max 1 C
  obtain ⟨F,v,hv,U,hU,hUb,hline⟩ := cofactor_source_gap_satz51_applicable3 k₀ k₂ k₃ delta hd
    c₀ c₂ c₃ hc₀ hc₂ hc₃ hb Omega hOmega hQ B u hB hu hatt hgap
  let T : Set ℝ := {t | t ∈ U ∧ cut ^ (5 : ℕ) < t}
  have hT : T ⊆ F.domain := fun _ ht => hU ht.1
  have hTb : ¬ BddAbove T := sourceDual_unbounded_tail3 U hUb (cut ^ (5 : ℕ))
  let V : Set ℝ := {Q | ∃ t : F.domain, t.val ∈ T ∧ (F.original t).val = Q}
  refine ⟨v,hv,V,?_,cofactor_originalPlane_pullback_unbounded3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u F T hT hTb,?_⟩
  · rintro Q ⟨t,ht,heq⟩
    rw [← heq]
    exact (F.original t).property
  · rintro Q ⟨t,ht,heq⟩
    have hq0 : 0 ≤ (F.original t).val := (lt_trans zero_lt_one (hQ _ (F.original t).property)).le
    have hpower : cut ^ (5 : ℕ) < (F.original t).val ^ (5 : ℕ) := by
      rw [F.parameter t]
      exact ht.2
    have hlarge : cut < (F.original t).val := lt_of_pow_lt_pow_left₀ 5 hq0 hpower
    have hcut := hC (F.original t).val (lt_of_le_of_lt (le_max_right 1 C) hlarge)
    have htransport := cofactor_originalPlane_deformed_transport3 k₀ k₂ k₃ (F.original t).val delta
      c₀ c₂ c₃ (hQ _ (F.original t).property) hd (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb
      (B (F.original t)) (u (F.original t)) (hB (F.original t)) (hu (F.original t))
      (hatt (F.original t)) (hgap (F.original t)) (F.data t) hcut
    have hsub : F.original t = Q := Subtype.ext heq
    have hh := htransport.2.2.symm.trans (hline t ht.1)
    cases hsub
    exact hh

end
end JSP000334
