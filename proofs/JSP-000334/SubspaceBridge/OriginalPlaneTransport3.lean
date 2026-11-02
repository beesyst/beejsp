import SubspaceBridge.GapTransport3
open scoped BigOperators
namespace JSP000334

def originalPlanePairing3 (z : Fin 3 → ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ i, x i * z i
  map_add' x y := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum,mul_assoc]

theorem originalPlane_annihilator_line3 (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => (w j i : ℚ)))
    (z : Fin 3 → ℚ) (hz : z ≠ 0)
    (h0 : originalPlanePairing3 z (fun i => (w 0 i : ℚ)) = 0)
    (h1 : originalPlanePairing3 z (fun i => (w 1 i : ℚ)) = 0) :
    Submodule.span ℚ {z} = Submodule.span ℚ {dualFrameVector3 w 2} := by
  classical
  let b := basisOfLinearIndependentOfCardEqFinrank hw (by simp)
  have hb (i : Fin 3) : b i = fun k => (w i k : ℚ) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hw _) i
  let c := originalPlanePairing3 z (fun i => (w 2 i : ℚ))
  have hf : originalPlanePairing3 z = c • originalPlanePairing3 (dualFrameVector3 w 2) := by
    apply b.ext
    intro i
    rw [hb]
    change originalPlanePairing3 z (fun k => (w i k : ℚ)) =
      c * (∑ k, (w i k : ℚ) * dualFrameVector3 w 2 k)
    rw [dualFrameVector3_pairing w hw i 2]
    fin_cases i <;> simp [h0,h1,c]
  have he : z = c • dualFrameVector3 w 2 := by
    ext i
    have hh := congrArg (fun f : (Fin 3 → ℚ) →ₗ[ℚ] ℚ => f (Pi.single i 1)) hf
    simpa [originalPlanePairing3,Pi.single_apply] using hh
  have hc : c ≠ 0 := by intro h; apply hz; rw [he,h,zero_smul]
  rw [he]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _

theorem originalPlane_last_dual_nonzero3 (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => (w j i : ℚ))) :
    dualFrameVector3 w 2 ≠ 0 := by
  intro h
  have hp := dualFrameVector3_pairing w hw 2 2
  simp [h] at hp

theorem originalPlane_real_to_rational_dual3 (a b : Fin 3 → IntegerTriple)
    (ha : LinearIndependent ℝ (fun j => integerTripleReal3 (a j)))
    (hb : LinearIndependent ℝ (fun j => integerTripleReal3 (b j)))
    (hplane : minimaFlag3 (fun j => integerTripleReal3 (b j)) 2 =
      minimaFlag3 (fun j => integerTripleReal3 (a j)) 2) :
    Submodule.span ℚ {dualFrameVector3 b 2} = Submodule.span ℚ {dualFrameVector3 a 2} := by
  have haQ := dualFrameMatrix3_rational_independent a ha
  have hbQ := dualFrameMatrix3_rational_independent b hb
  let z := dualFrameVector3 b 2
  let f : RealTriple →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, x i * (z i : ℝ)
      map_add' := fun x y => by simp [add_mul,Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum,mul_assoc] }
  have hker : minimaFlag3 (fun j => integerTripleReal3 (b j)) 2 ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hi : (Fin.castLE (by decide) i : Fin 3) ≠ 2 := by
      intro he
      have hh := congrArg Fin.val he
      simp at hh
      omega
    have hp := dualFrameVector3_pairing b hbQ (Fin.castLE (by decide) i) 2
    have hp0 : (∑ k, (b (Fin.castLE (by decide) i) k : ℚ) * z k) = 0 := by simpa [hi] using hp
    change (∑ k, ((b (Fin.castLE (by decide) i) k : ℤ) : ℝ) * (z k : ℝ)) = 0
    exact_mod_cast hp0
  have hann (j : Fin 2) : originalPlanePairing3 z (fun i => (a (Fin.castLE (by decide) j) i : ℚ)) = 0 := by
    have hx : integerTripleReal3 (a (Fin.castLE (by decide) j)) ∈
        minimaFlag3 (fun k => integerTripleReal3 (a k)) 2 := Submodule.subset_span ⟨j,rfl⟩
    rw [← hplane] at hx
    have hh := hker hx
    change (∑ k, ((a (Fin.castLE (by decide) j) k : ℤ) : ℝ) * (z k : ℝ)) = 0 at hh
    change (∑ k, (a (Fin.castLE (by decide) j) k : ℚ) * z k) = 0
    exact_mod_cast hh
  exact originalPlane_annihilator_line3 a haQ z (originalPlane_last_dual_nonzero3 b hbQ) (hann 0) (hann 1)

theorem originalPlane_scaled_cube3 (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i) :
    (gapFactors3 l 2 * l 2) ^ (3 : ℕ) = (l 0 * l 1 * l 2) * (l 2 / l 1) ^ (2 : ℕ) := by
  change (gapRadius3 l / l 1 * l 2) ^ (3 : ℕ) = _
  rw [mul_pow,div_pow,gapRadius3_cube l hl]
  field_simp [(hl 1).ne']
  <;> ring

theorem originalPlane_scaled_cube_gt3 (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i)
    (Q delta : ℝ) (hQ : 0 < Q) (hprod : (1 : ℝ) / 6 ≤ ∏ i, l i)
    (hgap : l 1 < l 2 * Q ^ (-delta)) :
    Q ^ (2 * delta) / 6 < (gapFactors3 l 2 * l 2) ^ (3 : ℕ) := by
  have hp := Real.rpow_pos_of_pos hQ delta
  have he : Q ^ (-delta) * Q ^ delta = 1 := by rw [← Real.rpow_add hQ]; simp
  have hm := mul_lt_mul_of_pos_right hgap hp
  simp only [mul_assoc,he,mul_one] at hm
  have hr : Q ^ delta < l 2 / l 1 := (lt_div_iff₀ (hl 1)).mpr (by nlinarith)
  have hs := pow_lt_pow_left₀ hr hp.le (by decide : (2 : ℕ) ≠ 0)
  have hpow : Q ^ (2 * delta) = (Q ^ delta) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast hQ.le]
    congr 1
    ring
  rw [← hpow] at hs
  rw [originalPlane_scaled_cube3 l hl]
  rw [Fin.prod_univ_three] at hprod
  have hb := mul_le_mul_of_nonneg_right hprod (sq_nonneg (l 2 / l 1))
  nlinarith

theorem originalPlane_power_cutoff3 (delta : ℝ) (hd : 0 < delta) :
    ∃ C : ℝ, ∀ Q : ℝ, C < Q → 3072 < Q ^ (2 * delta) := by
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < 2 * delta by linarith)).eventually
      (Filter.eventually_gt_atTop 3072))
  exact ⟨C,fun Q h => hC Q h.le⟩

theorem originalPlane_off_plane_margin3 (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i)
    (Q delta : ℝ) (hQ : 0 < Q) (hprod : (1 : ℝ) / 6 ≤ ∏ i, l i)
    (hgap : l 1 < l 2 * Q ^ (-delta)) (hcut : 3072 < Q ^ (2 * delta)) :
    1 < gapFactors3 l 2 * l 2 / 8 := by
  have hc := originalPlane_scaled_cube_gt3 l hl Q delta hQ hprod hgap
  have hs : 0 < gapFactors3 l 2 * l 2 :=
    mul_pos (div_pos (gapRadius3_pos l hl) (hl 1)) (hl 2)
  have hb : (8 : ℝ) ^ (3 : ℕ) < (gapFactors3 l 2 * l 2) ^ (3 : ℕ) := by norm_num; linarith
  have hh := lt_of_pow_lt_pow_left₀ 3 hs.le hb
  linarith

theorem originalPlane_deformed_transport3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) = successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j)
    (hgap : successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta))
    (d : GapDeformedData3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ B u)
    (hcut : 3072 < Q ^ (2 * delta)) :
    (∀ i : Fin 2, integerTripleReal3 (d.frame (Fin.castLE (by decide) i) : IntegerTriple) ∈
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2) ∧
    minimaFlag3 (fun j => integerTripleReal3 (d.frame j : IntegerTriple)) 2 =
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2 ∧
    Submodule.span ℚ {dualFrameVector3 (fun j => (d.frame j : IntegerTriple)) 2} =
      Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} := by
  have hQ0 := lt_trans zero_lt_one hQ
  obtain ⟨_,_,_,hl,_,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k₀ Q c₀ hQ)
  have hp := (gap_source_product3 k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb B u hB hatt).1
  have hsep := originalPlane_off_plane_margin3 _ hl Q delta hQ0 hp hgap hcut
  have hQ5 : 1 < Q ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hQ (by norm_num : (0 : ℝ) < 5)
  have hsmall : successiveRadius3 B (archCoordinates3 (retainedRealCoordinates3 k₀) d.widths d.positive) 1 < 1 :=
    d.small.trans (by simpa using Real.rpow_lt_rpow_of_exponent_lt hQ5 (show -(delta / 18) < 0 by linarith))
  have hmem (i : Fin 2) : integerTripleReal3 (d.frame (Fin.castLE (by decide) i) : IntegerTriple) ∈
      minimaFlag3 (fun j => integerTripleReal3 (u j : IntegerTriple)) 2 := by
    let k : Fin 3 := Fin.castLE (by decide) i
    let z : qSourceLattice3 k₂ k₃ Q c₂ c₃ := ⟨(d.frame k : IntegerTriple), by
      have hz := (d.frame k).property
      exact Eq.mp (congrArg (fun G : AddSubgroup IntegerTriple => (d.frame k : IntegerTriple) ∈ G)
        (gap_rescaled_lattice3 k₂ k₃ Q c₂ c₃ hQ0)) hz⟩
    have hk : k ≤ 1 := by change i.val ≤ 1; omega
    have hm := successiveRadius3_monotone B (archCoordinates3 (retainedRealCoordinates3 k₀) d.widths d.positive) hk
    have hg : coordinateGauge3 (archCoordinates3 (retainedRealCoordinates3 k₀) d.widths d.positive)
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

theorem originalPlane_pullback_unbounded3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (Omega : Set ℝ) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (F : GapSatz51Family3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u)
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

theorem source_fixed_last_dual_under_gap3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → qSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (qSourceLattice3 k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega, successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta)) :
    ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ V : Set ℝ, V ⊆ Omega ∧ ¬ BddAbove V ∧
      ∀ Q : Omega, Q.val ∈ V →
        Submodule.span ℚ {dualFrameVector3 (fun j => (u Q j : IntegerTriple)) 2} =
          Submodule.span ℚ {fun i => (v i : ℚ)} := by
  obtain ⟨C,hC⟩ := originalPlane_power_cutoff3 delta hd
  let cut := max 1 C
  obtain ⟨F,v,hv,U,hU,hUb,hline⟩ := source_gap_satz51_applicable3 k₀ k₂ k₃ delta hd
    c₀ c₂ c₃ hc₀ hc₂ hc₃ hb Omega hOmega hQ B u hB hu hatt hgap
  let T : Set ℝ := {t | t ∈ U ∧ cut ^ (5 : ℕ) < t}
  have hT : T ⊆ F.domain := fun _ ht => hU ht.1
  have hTb : ¬ BddAbove T := sourceDual_unbounded_tail3 U hUb (cut ^ (5 : ℕ))
  let V : Set ℝ := {Q | ∃ t : F.domain, t.val ∈ T ∧ (F.original t).val = Q}
  refine ⟨v,hv,V,?_,originalPlane_pullback_unbounded3 k₀ k₂ k₃ delta c₀ c₂ c₃ Omega hQ B u F T hT hTb,?_⟩
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
    have htransport := originalPlane_deformed_transport3 k₀ k₂ k₃ (F.original t).val delta
      c₀ c₂ c₃ (hQ _ (F.original t).property) hd (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb
      (B (F.original t)) (u (F.original t)) (hB (F.original t)) (hu (F.original t))
      (hatt (F.original t)) (hgap (F.original t)) (F.data t) hcut
    have hsub : F.original t = Q := Subtype.ext heq
    have hh := htransport.2.2.symm.trans (hline t ht.1)
    cases hsub
    exact hh

end JSP000334
