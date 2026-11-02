import SubspaceBridge.CofactorExteriorMinima3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

theorem exterior_square_cutoff3 (delta : ℝ) (hd : 0 < delta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℝ, C < Q → (1119744 : ℝ)^2 < Q^(delta/2) := by
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < delta/2 by linarith)).eventually
      (Filter.eventually_gt_atTop ((1119744 : ℝ)^2)))
  exact ⟨max 1 C,le_max_left _ _,fun Q h => hC Q (lt_of_le_of_lt (le_max_right _ _) h).le⟩

theorem exterior_square_gap_scalar3 (a b c m n Q delta : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : 0 < n)
    (hQ : 1 < Q) (hd : 0 < delta)
    (hlo : b*c/1119744 ≤ n) (hhi : m ≤ 1119744*(a*c))
    (hgap : a < b*Q^(-delta)) (hcut : (1119744 : ℝ)^2 < Q^(delta/2)) :
    m < n*(Q^2)^(-delta/4) ∧ 2*a*c < n := by
  have hp : 0 < Q := lt_trans zero_lt_one hQ
  have hneg := Real.rpow_pos_of_pos hp (-delta)
  have hbc : b*c ≤ 1119744*n := by
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1119744)).mp hlo
    nlinarith
  have hprod : a*c < (b*c)*Q^(-delta) := by
    have h := mul_lt_mul_of_pos_right hgap hc
    nlinarith
  have hpow : (Q^2)^(-delta/4) = Q^(-delta/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp.le]
    congr 1
    ring
  have hfactor : (1119744 : ℝ)^2*Q^(-delta) < Q^(-delta/2) := by
    calc
      _ < Q^(delta/2)*Q^(-delta) := mul_lt_mul_of_pos_right hcut hneg
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  have hsep : (2*1119744 : ℝ)*Q^(-delta) < 1 := by
    have hmono : Q^(delta/2) ≤ Q^delta := Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
    have hnum : (2*1119744 : ℝ) < Q^delta := by nlinarith
    have hh := mul_lt_mul_of_pos_right hnum hneg
    rw [← Real.rpow_add hp,add_neg_cancel,Real.rpow_zero] at hh
    exact hh
  constructor
  · rw [hpow]
    calc
      m ≤ 1119744*(a*c) := hhi
      _ < 1119744*((b*c)*Q^(-delta)) := mul_lt_mul_of_pos_left hprod (by norm_num)
      _ ≤ 1119744*((1119744*n)*Q^(-delta)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbc hneg.le) (by norm_num)
      _ = n*((1119744 : ℝ)^2*Q^(-delta)) := by ring
      _ < n*Q^(-delta/2) := mul_lt_mul_of_pos_left hfactor hn
  · calc
      2*a*c = 2*(a*c) := by ring
      _ < 2*((b*c)*Q^(-delta)) := mul_lt_mul_of_pos_left hprod (by norm_num)
      _ ≤ 2*((1119744*n)*Q^(-delta)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbc hneg.le) (by norm_num)
      _ = n*((2*1119744 : ℝ)*Q^(-delta)) := by ring
      _ < n*1 := mul_lt_mul_of_pos_left hsep hn
      _ = n := mul_one _

theorem hodgeFrame3_source_gauges (k : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 3 → ℝ) (u : Fin 3 → IntegerTriple) (l : Fin 3 → ℝ)
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k Q c hQ) (integerTripleReal3 (u j)) = l j) :
    ∀ j, coordinateGauge3 (cofactorSourceCoordinates3 k (Q^2) (pairWeights3 c) (pairWeights3_Q_squared Q hQ))
      (integerTripleReal3 (hodgeFrame3 u j)) ≤ 2*pairProducts3 l j := by
  intro j
  fin_cases j
  · simpa [hodgeFrame3,pairProducts3,hatt,mul_assoc] using hodgeWedge3_source_gauge k Q hQ c (u 0) (u 1)
  · simpa [hodgeFrame3,pairProducts3,hatt,mul_assoc] using hodgeWedge3_source_gauge k Q hQ c (u 0) (u 2)
  · simpa [hodgeFrame3,pairProducts3,hatt,mul_assoc] using hodgeWedge3_source_gauge k Q hQ c (u 1) (u 2)

theorem source_exterior_square_gap_plane3 (k0 k2 k3 : Fin 3) (Q delta : ℝ)
    (hQ : 1 < Q) (hd : 0 < delta)
    (c0 c2 c3 : Fin 3 → ℝ)
    (hc0 : ∀ i, -1 ≤ c0 i ∧ c0 i ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k2 k3 Q c2 c3)
    (hB : lattice3 B = (qSourceLattice3 k2 k3 Q c2 c3).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k0 Q c0 hQ) (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) j)
    (hgap : successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) 0 <
      successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) 1*Q^(-delta))
    (D : Basis (Fin 3) ℝ RealTriple)
    (v : Fin 3 → cofactorSourceLattice3 k2 k3 (Q^2) (pairWeights3 c2) (pairWeights3 c3))
    (hD : lattice3 D = (cofactorSourceLattice3 k2 k3 (Q^2) (pairWeights3 c2) (pairWeights3 c3)).toIntSubmodule.map integerTripleReal3)
    (hv : LinearIndependent ℝ (fun j => integerTripleReal3 (v j : IntegerTriple)))
    (hav : ∀ j, coordinateGauge3
      (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ))
      (integerTripleReal3 (v j : IntegerTriple)) = successiveRadius3 D
      (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)) j)
    (hcut : (1119744 : ℝ)^2 < Q^(delta/2)) :
    successiveRadius3 D (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)) 1 <
      successiveRadius3 D (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)) 2*(Q^2)^(-delta/4) ∧
    Submodule.span ℚ {fun i => ((u 0 : IntegerTriple) i : ℚ)} =
      Submodule.span ℚ {dualFrameVector3 (fun j => (v j : IntegerTriple)) 2} := by
  let l := successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ)
  let e := cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)
  let m := successiveRadius3 D e
  obtain ⟨_,_,_,hl,ho,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k0 Q c0 hQ)
  obtain ⟨_,_,_,hm,hmo,_⟩ := exists_successive_minima3 D e
  have hcmp := source_exterior_square_comparison3 k0 k2 k3 Q hQ c0 c2 c3 hc0 hc2 hc3 hb B u hB hu hatt D hD
  have hlo : l 1*l 2/1119744 ≤ m 2 := by simpa [l,m,e,pairProducts3,Matrix.cons_val_two] using (hcmp 2).1
  have hhi : m 1 ≤ 1119744*(l 0*l 2) := by simpa [l,m,e,pairProducts3] using (hcmp 1).2
  have hg := exterior_square_gap_scalar3 (l 0) (l 1) (l 2) (m 1) (m 2) Q delta
    (hl 0) (hl 1) (hl 2) (hm 2) hQ hd hlo hhi hgap hcut
  refine ⟨hg.1,?_⟩
  have hp : (Q^2)^(-delta/4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (pairWeights3_Q_squared Q hQ) (by linarith)
  have hm12 : m 1 < m 2 := hg.1.trans (by nlinarith [hm 2])
  let w := hodgeFrame3 (fun j => (u j : IntegerTriple))
  have hwcast : (fun j => integerTripleReal3 (w j)) =
      hodgeFrame3 (fun j => integerTripleReal3 (u j : IntegerTriple)) :=
    hodgeFrame3_map (Int.castRingHom ℝ) (fun j => (u j : IntegerTriple))
  have hwr : LinearIndependent ℝ (fun j => integerTripleReal3 (w j)) := by
    rw [hwcast]
    exact hodgeFrame3_independent _ hu
  have hvmem (j : Fin 3) : integerTripleReal3 (v j : IntegerTriple) ∈ lattice3 D := by
    rw [hD]
    exact Submodule.mem_map.mpr ⟨(v j : IntegerTriple),(v j).property,rfl⟩
  have hwmem (j : Fin 3) : integerTripleReal3 (w j) ∈ lattice3 D := by
    rw [hD]
    apply Submodule.mem_map.mpr
    refine ⟨w j,?_,rfl⟩
    fin_cases j
    · exact hodgeWedge3_source_mem k2 k3 Q hQ c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) (u 0) (u 1)
    · exact hodgeWedge3_source_mem k2 k3 Q hQ c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) (u 0) (u 2)
    · exact hodgeWedge3_source_mem k2 k3 Q hQ c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) (u 1) (u 2)
  have hle : minimaFlag3 (fun j => integerTripleReal3 (w j)) 2 ≤
      minimaFlag3 (fun j => integerTripleReal3 (v j : IntegerTriple)) 2 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    let idx : Fin 3 := Fin.castLE (by decide) j
    have hgauge := hodgeFrame3_source_gauges k0 Q hQ c0 (fun j => (u j : IntegerTriple)) l hatt idx
    have hidx : idx ≤ 1 := by change j.val ≤ 1; omega
    have hpmono := pairProducts3_monotone l hl ho.1 ho.2 hidx
    have hgb : coordinateGauge3 e (integerTripleReal3 (w idx)) ≤ 2*l 0*l 2 := by
      have hh := hgauge.trans (mul_le_mul_of_nonneg_left hpmono (by norm_num : (0 : ℝ) ≤ 2))
      simpa only [pairProducts3,Matrix.cons_val_one,mul_assoc] using hh
    apply lattice3_short_mem_minimaFlag D e (fun j => integerTripleReal3 (v j : IntegerTriple))
      hv hvmem hav 2
    · intro i hi
      exact (successiveRadius3_monotone D e (show i ≤ 1 by omega)).trans_lt hm12
    · exact hwmem idx
    · exact hgb.trans_lt hg.2
  have heq : minimaFlag3 (fun j => integerTripleReal3 (w j)) 2 =
      minimaFlag3 (fun j => integerTripleReal3 (v j : IntegerTriple)) 2 :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [minimaFlag3_finrank _ hwr,minimaFlag3_finrank _ hv])
  have hdual := originalPlane_real_to_rational_dual3 (fun j => (v j : IntegerTriple)) w hv hwr heq
  exact (hodgeFrame3_original_first_line (fun j => (u j : IntegerTriple)) hu).trans hdual

end
end JSP000334
