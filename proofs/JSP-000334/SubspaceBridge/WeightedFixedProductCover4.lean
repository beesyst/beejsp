import SubspaceBridge.WeightedFixedProductPoint4
import SubspaceBridge.WeightedDiagonalFamily4
import SubspaceBridge.AllPointGeneralPosition4
namespace JSP000334
open scoped BigOperators Matrix

def weightedFixedProductQuadruples4 (k : Fin 4 → ℚ) (a : ℚ) (y : (Fin 4 → ℤ)) : Prop :=
  PrimitiveFour y ∧ (∀ i,threePlaceProduct (y i : ℚ)=threePlaceProduct (k i)) ∧
    threePlaceProduct (∑ i : Fin 4,(y i : ℚ))=threePlaceProduct a

theorem weighted_fixed_product_cover4 (k : Fin 4 → ℚ) (a : ℚ) (hk : ∀ i,k i≠0) (ha : a≠0) :
    ∃ F : Set (Submodule ℚ (Fin 4 → ℚ)),F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ y : (Fin 4 → ℤ),weightedFixedProductQuadruples4 k a y → ∃ P∈F,(fun i => (y i : ℚ))∈P := by
  classical
  by_contra hno
  change allpoint_no_finite_cover4 (weightedFixedProductQuadruples4 k a) at hno
  obtain ⟨z,hE,hheight,hmono,havoid⟩ := allpoint_general_position_sequence4 (weightedFixedProductQuadruples4 k a) hno
  obtain ⟨N,hN⟩ := exists_nat_gt (weightedProductCutoff4 k a)
  let q (n : ℕ) : ℝ := (archFourHeight (z (n+N)) : ℝ)^8
  let Omega : Set ℝ := Set.range q
  have hOmega : ¬BddAbove Omega := by
    rintro ⟨M,hM⟩
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hb := hM (show q n∈Omega from Set.mem_range_self n)
    have hH := (hheight (n+N)).1
    have hHn := (hheight (n+N)).2
    have hnN : (n : ℝ)≤(n+N : ℕ) := by exact_mod_cast Nat.le_add_right n N
    have hsq : (archFourHeight (z (n+N)) : ℝ)≤(archFourHeight (z (n+N)) : ℝ)^2 := by nlinarith
    have hfour : (archFourHeight (z (n+N)) : ℝ)^2≤(archFourHeight (z (n+N)) : ℝ)^4 := by
      nlinarith [sq_nonneg ((archFourHeight (z (n+N)) : ℝ)^2-1)]
    have height : (archFourHeight (z (n+N)) : ℝ)^4≤(archFourHeight (z (n+N)) : ℝ)^8 := by
      nlinarith [sq_nonneg ((archFourHeight (z (n+N)) : ℝ)^4-1)]
    change (archFourHeight (z (n+N)) : ℝ)^8≤M at hb
    linarith
  have hex (t : Omega) : ∃ n : ℕ,q n=t.val := t.property
  choose original hparam using hex
  let y (t : Omega) := z (original t+N)
  have hlarge (t : Omega) : weightedProductCutoff4 k a≤(archFourHeight (y t) : ℝ) := by
    have hh := (hheight (original t+N)).2
    have hnN : (N : ℝ)≤(original t+N : ℕ) := by exact_mod_cast Nat.le_add_left N (original t)
    dsimp [y]
    linarith
  have hp (t : Omega) : ∃ choice : Fin 3 → Fin 4,∃ d∈finiteWeightCandidates4 560,
      sourceWeightConditions4 d ∧
      CompoundFeasibility.OriginalVariableGap4.originalSourceSolution4
        (retainedRationalMatrix4 (choice 1)) (retainedRationalMatrix4 (choice 2))
        (retainedRealMatrix4 (choice 0)) (d 0) (d 1) (d 2) t.val ((1 : ℝ)/80) (y t) := by
    have he := hE (original t+N)
    have hp := weighted_fixed_product_point4 k a hk ha (y t) he.1 he.2.1 he.2.2 (hlarge t)
    simpa only [y,← hparam t] using hp
  obtain ⟨P,hP,W,hWO,hW,hm⟩ := weighted_integer_source_family4 Omega hOmega y
    hp
  have hS := allpoint_general_position_intersection4 z (fun n => (hheight n).1) havoid P hP
  have hsub : W⊆(fun n => (archFourHeight (z n) : ℝ)^8) '' {n | (fun i => (z n i : ℚ))∈P} := by
    intro Q hQW
    let t : Omega := ⟨Q,hWO hQW⟩
    exact ⟨original t+N,hm t hQW,hparam t⟩
  exact hW ((hS.image (fun n => (archFourHeight (z n) : ℝ)^8)).bddAbove.mono hsub)

end JSP000334
