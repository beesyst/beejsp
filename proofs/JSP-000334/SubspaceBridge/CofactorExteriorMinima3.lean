import SubspaceBridge.CofactorExteriorReal3
open scoped BigOperators Matrix
open MeasureTheory
namespace JSP000334
noncomputable section

def pairProducts3 (l : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![l 0*l 1,l 0*l 2,l 1*l 2]

theorem pairProducts3_positive (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i) :
    ∀ i, 0 < pairProducts3 l i := by
  intro i
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  fin_cases i <;> simp [pairProducts3] <;> positivity

theorem pairProducts3_product (l : Fin 3 → ℝ) :
    (∏ i, pairProducts3 l i) = (∏ i, l i)^2 := by
  simp [pairProducts3,Fin.prod_univ_three]
  ring

theorem pairProducts3_monotone (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i)
    (h01 : l 0 ≤ l 1) (h12 : l 1 ≤ l 2) : Monotone (pairProducts3 l) := by
  intro i j hij
  have hijN : i.val ≤ j.val := hij
  fin_cases i <;> fin_cases j <;>
    norm_num [pairProducts3] at hijN ⊢ <;> nlinarith [hl 0,hl 1,hl 2]

theorem cofactor_product_bounds3 (k0 k2 k3 : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 3 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple)
    (hB : lattice3 B = (cofactorSourceLattice3 k2 k3 Q c2 c3).toIntSubmodule.map integerTripleReal3) :
    (1 : ℝ)/6 ≤ ∏ i, successiveRadius3 B (cofactorSourceCoordinates3 k0 Q c0 hQ) i ∧
      (∏ i, successiveRadius3 B (cofactorSourceCoordinates3 k0 Q c0 hQ) i) < 216 := by
  let P := ∏ i, Q ^ c0 i
  have hP : 0 < P := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  have hcov : ZLattice.covolume (lattice3 B) =
      ((cofactorSourceLattice3 k2 k3 Q c2 c3).index : ℝ) := by
    rw [hB]
    have h := cofactorSourceLattice3_spec k2 k3 Q c2 c3 hQ hc2 hc3
    rw [h.2.2.1]
    exact h.2.2.2
  have hvol : volume.real (parallelepipedBody3 (cofactorSourceCoordinates3 k0 Q c0 hQ)) = 8*P := by
    rw [← cofactorSourceBody3_eq_parallelepiped k0 Q c0 hQ,cofactorSourceBody3_volume k0 Q c0 hQ]
  have hi : ((cofactorSourceLattice3 k2 k3 Q c2 c3).index : ℝ) = P*qRoundingFactor3 Q c2 c3 := by
    rw [(cofactorSourceLattice3_spec k2 k3 Q c2 c3 hQ hc2 hc3).2.2.1,
      qCongruenceIndex3_balanced Q c0 c2 c3 hQ hb]
  have hlower := source_minima_product_lower3 B (cofactorSourceCoordinates3 k0 Q c0 hQ)
    ((cofactorSourceLattice3 k2 k3 Q c2 c3).index : ℝ) P hP hvol hcov
  have hupper := successive_minima3_parallelepiped_volume_upper B (cofactorSourceCoordinates3 k0 Q c0 hQ)
  rw [hvol,hcov,hi] at hupper
  rw [hi] at hlower
  have hR := qRoundingFactor3_bounds Q c2 c3 hQ hc2 hc3
  have hlow' : qRoundingFactor3 Q c2 c3 / 6 ≤
      ∏ i, successiveRadius3 B (cofactorSourceCoordinates3 k0 Q c0 hQ) i := by
    have he : P*qRoundingFactor3 Q c2 c3/(6*P) = qRoundingFactor3 Q c2 c3/6 := by field_simp <;> ring
    rwa [he] at hlower
  refine ⟨by linarith,?_⟩
  have hup : (∏ i, successiveRadius3 B (cofactorSourceCoordinates3 k0 Q c0 hQ) i) ≤ qRoundingFactor3 Q c2 c3 := by nlinarith
  exact hup.trans_lt hR.2

theorem hodgeFrame3_forward_bounds (k0 k2 k3 : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 3 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k2 k3 Q c2 c3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k0 Q c0 hQ) (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) j)
    (D : Basis (Fin 3) ℝ RealTriple)
    (hD : lattice3 D = (cofactorSourceLattice3 k2 k3 (Q^2) (pairWeights3 c2) (pairWeights3 c3)).toIntSubmodule.map integerTripleReal3) :
    ∀ i, successiveRadius3 D (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)) i ≤
      2*pairProducts3 (successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ)) i := by
  let l := successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ)
  let w := hodgeFrame3 (fun j => (u j : IntegerTriple))
  let e := cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)
  have hwcast : (fun j => integerTripleReal3 (w j)) =
      hodgeFrame3 (fun j => integerTripleReal3 (u j : IntegerTriple)) :=
    hodgeFrame3_map (Int.castRingHom ℝ) (fun j => (u j : IntegerTriple))
  have hw := hodgeFrame3_independent (fun j => integerTripleReal3 (u j : IntegerTriple)) hu
  rw [← hwcast] at hw
  have hwmem (j : Fin 3) : integerTripleReal3 (w j) ∈ lattice3 D := by
    rw [hD]
    apply Submodule.mem_map.mpr
    refine ⟨w j,?_,rfl⟩
    fin_cases j
    · exact hodgeWedge3_source_mem k2 k3 Q hQ c2 c3 hc2 hc3 (u 0) (u 1)
    · exact hodgeWedge3_source_mem k2 k3 Q hQ c2 c3 hc2 hc3 (u 0) (u 2)
    · exact hodgeWedge3_source_mem k2 k3 Q hQ c2 c3 hc2 hc3 (u 1) (u 2)
  have hwg (j : Fin 3) : coordinateGauge3 e (integerTripleReal3 (w j)) ≤ 2*pairProducts3 l j := by
    fin_cases j
    · simpa [w,hodgeFrame3,pairProducts3,l,e,hatt,mul_assoc] using hodgeWedge3_source_gauge k0 Q hQ c0 (u 0) (u 1)
    · simpa [w,hodgeFrame3,pairProducts3,l,e,hatt,mul_assoc] using hodgeWedge3_source_gauge k0 Q hQ c0 (u 0) (u 2)
    · simpa [w,hodgeFrame3,pairProducts3,l,e,hatt,mul_assoc] using hodgeWedge3_source_gauge k0 Q hQ c0 (u 1) (u 2)
  obtain ⟨_,_,_,hl,ho,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k0 Q c0 hQ)
  intro i
  let f : Fin (i.val+1) → Fin 3 := Fin.castLE (by omega)
  apply successiveRadius3_le_family D e i (fun j => integerTripleReal3 (w (f j)))
    (hw.comp f (Fin.castLE_injective _)) (fun j => hwmem (f j))
  intro j
  apply (hwg (f j)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply pairProducts3_monotone l hl ho.1 ho.2
  change j.val ≤ i.val
  omega

theorem source_exterior_square_comparison3 (k0 k2 k3 : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 3 → ℝ)
    (hc0 : ∀ i, -1 ≤ c0 i ∧ c0 i ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k2 k3 Q c2 c3)
    (hB : lattice3 B = (qSourceLattice3 k2 k3 Q c2 c3).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k0 Q c0 hQ) (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ) j)
    (D : Basis (Fin 3) ℝ RealTriple)
    (hD : lattice3 D = (cofactorSourceLattice3 k2 k3 (Q^2) (pairWeights3 c2) (pairWeights3 c3)).toIntSubmodule.map integerTripleReal3) :
    ∀ i, pairProducts3 (successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ)) i / 1119744 ≤
      successiveRadius3 D (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)) i ∧
      successiveRadius3 D (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ)) i ≤
        1119744*pairProducts3 (successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ)) i := by
  let l := successiveRadius3 B (qSourceCoordinates3 k0 Q c0 hQ)
  let m := successiveRadius3 D (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ))
  obtain ⟨_,_,_,hl,_,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k0 Q c0 hQ)
  obtain ⟨_,_,_,hm,_,_⟩ := exists_successive_minima3 D
    (cofactorSourceCoordinates3 k0 (Q^2) (pairWeights3 c0) (pairWeights3_Q_squared Q hQ))
  obtain ⟨h0,h2,h3,hbalance⟩ := pairWeights3_bounds c0 c2 c3 hc0 hc2 hc3 hb
  have hmp := (cofactor_product_bounds3 k0 k2 k3 (Q^2) (pairWeights3_Q_squared Q hQ)
    (pairWeights3 c0) (pairWeights3 c2) (pairWeights3 c3) (fun i => (h2 i).2)
    (fun i => (h3 i).2) hbalance D hD).1
  have hlp := (gap_source_product3 k0 k2 k3 Q c0 c2 c3 hQ (fun i => (hc2 i).2)
    (fun i => (hc3 i).2) hb B u hB hatt).2
  have hpp : (∏ i, pairProducts3 l i) ≤ (216 : ℝ)^2 := by
    rw [pairProducts3_product]
    have hn : 0 ≤ ∏ i, l i := Finset.prod_nonneg (fun i _ => (hl i).le)
    nlinarith
  have hf := hodgeFrame3_forward_bounds k0 k2 k3 Q hQ c0 c2 c3
    (fun i => (hc2 i).2) (fun i => (hc3 i).2) B u hu hatt D hD
  have hr := cofactor_compound_reverse_product3 (pairProducts3 l) m
    (pairProducts3_positive l hl) hm hpp hmp hf
  intro i
  refine ⟨hr i,?_⟩
  apply (hf i).trans
  have hp := (pairProducts3_positive l hl i).le
  nlinarith

end
end JSP000334
