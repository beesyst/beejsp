import SubspaceBridge.WeightedFixedProductPoint3
import SubspaceBridge.AllPointGeneralPosition3
namespace JSP000334
open scoped BigOperators Matrix

def weightedFixedProductTriples3 (k : Fin 3 → ℚ) (a : ℚ) (y : IntegerTriple) : Prop :=
  PrimitiveTriple y ∧ (∀ i,threePlaceProduct (y i : ℚ)=threePlaceProduct (k i)) ∧
    threePlaceProduct ((y 0 : ℚ)+y 1+y 2)=threePlaceProduct a

theorem weighted_fixed_product_cover3 (k : Fin 3 → ℚ) (a : ℚ) (hk : ∀ i,k i≠0) (ha : a≠0) :
    ∃ F : Set (Submodule ℚ (Fin 3 → ℚ)),F.Finite ∧ (∀ P∈F,P≠⊤) ∧
      ∀ y : IntegerTriple,weightedFixedProductTriples3 k a y → ∃ P∈F,(fun i => (y i : ℚ))∈P := by
  classical
  by_contra hno
  change allpoint_no_finite_cover3 (weightedFixedProductTriples3 k a) at hno
  obtain ⟨z,hE,hheight,hmono,havoid⟩ := allpoint_general_position_sequence3 (weightedFixedProductTriples3 k a) hno
  obtain ⟨N,hN⟩ := exists_nat_gt (weightedProductCutoff3 k a)
  let q (n : ℕ) : ℝ := (archTripleHeight (z (n+N)) : ℝ)^4
  let Omega : Set ℝ := Set.range q
  have hOmega : ¬BddAbove Omega := by
    rintro ⟨M,hM⟩
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hb := hM (show q n∈Omega from Set.mem_range_self n)
    have hH := (hheight (n+N)).1
    have hHn := (hheight (n+N)).2
    have hnN : (n : ℝ)≤(n+N : ℕ) := by exact_mod_cast Nat.le_add_right n N
    have hsq : (archTripleHeight (z (n+N)) : ℝ)≤(archTripleHeight (z (n+N)) : ℝ)^2 := by nlinarith
    have hfour : (archTripleHeight (z (n+N)) : ℝ)^2≤(archTripleHeight (z (n+N)) : ℝ)^4 := by
      nlinarith [sq_nonneg ((archTripleHeight (z (n+N)) : ℝ)^2-1)]
    change (archTripleHeight (z (n+N)) : ℝ)^4≤M at hb
    linarith
  have hex (t : Omega) : ∃ n : ℕ,q n=t.val := t.property
  choose original hparam using hex
  let y (t : Omega) := z (original t+N)
  have hlarge (t : Omega) : weightedProductCutoff3 k a≤(archTripleHeight (y t) : ℝ) := by
    have hh := (hheight (original t+N)).2
    have hnN : (N : ℝ)≤(original t+N : ℕ) := by exact_mod_cast Nat.le_add_left N (original t)
    dsimp [y]
    linarith
  have hp (t : Omega) : ∃ choice : Fin 3 → Fin 3,∃ d∈finiteWeightCandidates3 336,
      ∃ hQ : 1<t.val,sourceWeightConditions3 d ∧
      y t∈qSourceLattice3 (choice 1) (choice 2) t.val (d 1) (d 2) ∧
      coordinateGauge3 (qSourceCoordinates3 (choice 0) t.val (d 0) hQ) (integerTripleReal3 (y t))≤t.val^(-(1 : ℝ)/24) := by
    have he := hE (original t+N)
    have hp := weighted_fixed_product_point3 k a hk ha (y t) he.1 he.2.1 he.2.2 (hlarge t)
    simpa only [y,← hparam t] using hp
  obtain ⟨P,hP,W,hWO,hW,hm⟩ := weighted_integer_source_family3 Omega hOmega y
    (fun t => (hE (original t+N)).1) hp
  have hS := (allpoint_general_position_intersection3 z (fun n => (hheight n).1) havoid P hP).1
  have hsub : W⊆(fun n => (archTripleHeight (z n) : ℝ)^4) '' {n | (fun i => (z n i : ℚ))∈P} := by
    intro Q hQW
    let t : Omega := ⟨Q,hWO hQW⟩
    exact ⟨original t+N,hm t hQW,hparam t⟩
  exact hW ((hS.image (fun n => (archTripleHeight (z n) : ℝ)^4)).bddAbove.mono hsub)

end JSP000334
