import SubspaceBridge.MinimaProduct5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalVariableGap5

def originalSourceSolution5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ)
    (Q delta : ℝ) (x : Fin 5 → ℤ) : Prop :=
  x ≠ 0 ∧ 1 < Q ∧ 0 < delta ∧
    (∀ i, |(L *ᵥ integerReal x) i| ≤ Q^(c0 i-delta)) ∧
    (∀ i, (padicNorm 2 ((A2 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c2 i)) ∧
    (∀ i, (padicNorm 3 ((A3 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c3 i))

def originalRothProperty5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ B : ℝ, ∀ Q : ℝ, B < Q →
    ¬ ∃ x : Fin 5 → ℤ, originalSourceSolution5 A2 A3 L c0 c2 c3 Q delta x

theorem nonroth_iff_unbounded_solutions5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ) :
    ¬ originalRothProperty5 A2 A3 L c0 c2 c3 ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ¬ BddAbove {Q : ℝ | ∃ x : Fin 5 → ℤ,
          originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x} := by
  constructor
  · intro hn
    unfold originalRothProperty5 at hn
    push_neg at hn
    obtain ⟨epsilon,he,hsol⟩ := hn
    refine ⟨epsilon,he,not_bddAbove_iff.mpr ?_⟩
    intro B
    obtain ⟨Q,hBQ,x,hx⟩ := hsol B
    exact ⟨Q,⟨x,hx⟩,hBQ⟩
  · rintro ⟨epsilon,he,hU⟩ hR
    obtain ⟨B,hB⟩ := hR epsilon he
    obtain ⟨Q,⟨x,hx⟩,hBQ⟩ := not_bddAbove_iff.mp hU B
    exact hB Q hBQ ⟨x,hx⟩


theorem source_solution_lattice5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (Q epsilon : ℝ) (x : Fin 5 → ℤ)
    (hs : originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x) :
    x ∈ originalSourceGroup5 A2 A3 Q c2 c3 := by
  change (x ∈ lattice5 2 A2 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))) ∧
    (x ∈ lattice5 3 A3 (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))))
  constructor
  · apply (lattice5_spec 2 A2 _ x).mpr
    intro i
    simpa only [zpow_neg,zpow_natCast] using
      (padic_rpow_ceil42 2 Q (c2 i) hs.2.1 (hc2 i) _).mp (hs.2.2.2.2.1 i)
  · apply (lattice5_spec 3 A3 _ x).mpr
    intro i
    simpa only [zpow_neg,zpow_natCast] using
      (padic_rpow_ceil42 3 Q (c3 i) hs.2.1 (hc3 i) _).mp (hs.2.2.2.2.2 i)

theorem source_solution_gauge5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (Q epsilon : ℝ) (hQ : 1 < Q) (x : Fin 5 → ℤ)
    (hs : originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x) :
    coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x) ≤ Q^(-epsilon) := by
  apply (originalCoordinates5_bounds L hL Q hQ c0 (integerReal x) _).mpr
  intro i
  have he : Q^(c0 i-epsilon) = Q^(-epsilon)*Q^(c0 i) := by
    rw [← Real.rpow_add (lt_trans zero_lt_one hQ)]
    congr 1
    ring
  rw [← he]
  exact hs.2.2.2.1 i

theorem source_first_minimum_le_gauge5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (Q : ℝ) (hQ : 1 < Q) (x : Fin 5 → ℤ) (hx : x ≠ 0)
    (hm : x ∈ originalSourceGroup5 A2 A3 Q c2 c3) :
    sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 ≤
      coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x) := by
  have hn : integerReal x ≠ 0 := by
    intro hz
    exact hx (integerReal_injective (hz.trans integerReal.map_zero.symm))
  have hi : LinearIndependent ℝ (fun _ : Fin 1 => integerReal x) :=
    (linearIndependent_unique_iff _).mpr hn
  apply (sourceMinima5_radius_set_properties A2 A3 L hL Q hQ c0 c2 c3 0).2.2.2
  exact ⟨fun _ : Fin 1 => integerReal x,hi,fun _ => ⟨x,hm,rfl⟩,fun _ => le_rfl⟩

theorem source_solution_small_first5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (Q epsilon : ℝ) (hQ : 1 < Q) (x : Fin 5 → ℤ)
    (hs : originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x) :
    sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 < Q^(-(epsilon/2)) := by
  have hm := source_solution_lattice5 A2 A3 L c0 c2 c3 hc2 hc3 Q epsilon x hs
  have hfirst := source_first_minimum_le_gauge5 A2 A3 L hL c0 c2 c3 Q hQ x hs.1 hm
  have hg := source_solution_gauge5 A2 A3 L hL c0 c2 c3 Q epsilon hQ x hs
  exact (hfirst.trans hg).trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hQ (by linarith [hs.2.2.1]))


theorem finite5_adjacent_gap (lam : Fin 5 → ℝ)
    (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (c Q s : ℝ) (hprod : c ≤ ∏ i, lam i) (hQ : 1 < Q)
    (hfirst : lam 0 < Q^(-s)) (hcut : Q^(-s) < c) :
    ∃ j : Fin 4, lam j.castSucc < lam j.succ * Q^(-(s/5)) := by
  by_contra hn
  push_neg at hn
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  let r : ℝ := Q^(s/5)
  have hr : 0 < r := Real.rpow_pos_of_pos hQ0 _
  have hcancel : Q^(-(s/5))*r = 1 := by
    dsimp [r]
    rw [← Real.rpow_add hQ0]
    simp
  have hstep (j : Fin 4) : lam j.succ ≤ lam j.castSucc * r := by
    have hh := mul_le_mul_of_nonneg_right (hn j) hr.le
    simpa only [mul_assoc,hcancel,mul_one] using hh
  have h1 : lam 1 ≤ lam 0*r := hstep 0
  have h2 : lam 2 ≤ (lam 0*r)*r := (hstep 1).trans (mul_le_mul_of_nonneg_right h1 hr.le)
  have h3 : lam 3 ≤ ((lam 0*r)*r)*r := (hstep 2).trans (mul_le_mul_of_nonneg_right h2 hr.le)
  have h4 : lam 4 ≤ (((lam 0*r)*r)*r)*r := (hstep 3).trans (mul_le_mul_of_nonneg_right h3 hr.le)
  have he : (((Q^(-s)*r)*r)*r)*r = Q^(-(s/5)) := by
    dsimp [r]
    rw [← Real.rpow_add hQ0,← Real.rpow_add hQ0,← Real.rpow_add hQ0,← Real.rpow_add hQ0]
    congr 1
    ring
  have hlast : lam 4 < Q^(-(s/5)) := by
    rw [← he]
    exact h4.trans_lt (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hfirst hr) hr) hr) hr)
  have hprod' : (∏ i, lam i) ≤ (lam 4)^5 := by
    calc
      _ ≤ ∏ _i : Fin 5, lam 4 := Finset.prod_le_prod (fun i _ => (hp i).le) (fun i _ => hm (Fin.le_last i))
      _ = _ := by simp
  have hpow : (Q^(-(s/5)))^5 = Q^(-s) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ0.le]
    congr 1
    norm_num
  have hsmall : (lam 4)^5 < Q^(-s) := by
    rw [← hpow]
    exact pow_lt_pow_left₀ hlast (hp 4).le (by decide)
  exact (not_lt_of_ge hprod) (hprod'.trans_lt (hsmall.trans hcut))

theorem finite4_unbounded_cover (U : Set ℝ) (E : Fin 4 → Set ℝ)
    (hU : ¬ BddAbove U) (hcover : ∀ Q ∈ U, ∃ j, Q ∈ E j) : ∃ j, ¬ BddAbove (E j) := by
  by_contra hn
  push_neg at hn
  have hb : BddAbove (⋃ j ∈ (Set.univ : Set (Fin 4)), E j) :=
    Set.finite_univ.bddAbove_biUnion.mpr (fun j _ => hn j)
  apply hU
  apply hb.mono
  intro Q hQ
  obtain ⟨j,hj⟩ := hcover Q hQ
  exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Set.mem_univ j,hj⟩⟩

theorem first_minimum_cutoff5 (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    ∃ B : ℝ, 1 < B ∧ ∀ Q : ℝ, B < Q → Q^(-s) < c :=
  OriginalVariableGap4.first_minimum_cutoff4 c s hc hs

theorem matrixUnit5 {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)

def completeFin5GapPackage
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ) : Prop :=
    ∃ epsilon deltaGap c5 C5 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 4,
      0 < epsilon ∧ deltaGap = (epsilon/2)/5 ∧ 0 < deltaGap ∧
      0 < c5 ∧ 0 < C5 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 5 → ℤ,
        originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 5 → ℤ,
        originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x ∧
        x ∈ originalSourceGroup5 A2 A3 Q c2 c3 ∧
        coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c5 ≤ (∏ i : Fin 5, sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
        (∏ i : Fin 5, sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ≤ C5) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧ 1 ≤ j.val+1 ∧ j.val+1 ≤ 4 ∧
      ∀ Q ∈ V, B < Q ∧ ∃ hQ : 1 < Q,
        sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc <
          sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j.succ * Q^(-deltaGap)

theorem source_fin5_nonroth_gap_units5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (c0 c2 c3 : Fin 5 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (hn : ¬ originalRothProperty5 A2 A3 L c0 c2 c3) :
    completeFin5GapPackage A2 A3 L hL c0 c2 c3 := by
  obtain ⟨epsilon,he,hU⟩ := (nonroth_iff_unbounded_solutions5 A2 A3 L c0 c2 c3).mp hn
  let U : Set ℝ := {Q | ∃ x, originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x}
  obtain ⟨c5,C5,hc5,hC5,hbounds⟩ :=
    source_original_uniform_minima_two_sided5 A2 A3 L h2 h3 hL
  obtain ⟨B,hB,hcut⟩ := first_minimum_cutoff5 c5 (epsilon/2) hc5 (by positivity)
  let T : Set ℝ := {Q | Q ∈ U ∧ B < Q}
  have hT : ¬ BddAbove T := JSP000334.sourceDual_unbounded_tail3 U hU B
  let E : Fin 4 → Set ℝ := fun j => {Q | Q ∈ T ∧ ∃ hQ : 1 < Q,
    sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j.succ * Q^(-((epsilon/2)/5))}
  have hcover : ∀ Q ∈ T, ∃ j, Q ∈ E j := by
    intro Q hQT
    obtain ⟨x,hx⟩ := hQT.1
    have hQ := hx.2.1
    have hp := sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3
    have hfirst := source_solution_small_first5 A2 A3 L hL c0 c2 c3 hc2 hc3 Q epsilon hQ x hx
    obtain ⟨j,hj⟩ := finite5_adjacent_gap _ hp.1 hp.2 c5 Q (epsilon/2)
      (hbounds Q hQ c0 c2 c3 hc2 hc3 hb).1 hQ hfirst (hcut Q hQT.2)
    exact ⟨j,hQT,hQ,hj⟩
  obtain ⟨j,hj⟩ := finite4_unbounded_cover T E hT hcover
  refine ⟨epsilon,(epsilon/2)/5,c5,C5,B,U,E j,j,he,rfl,by positivity,
    hc5,hC5,hB,rfl,hU,?_,?_,?_,hj,by omega,by omega,?_⟩
  · intro Q hQU
    obtain ⟨x,hx⟩ := hQU
    have hQ := hx.2.1
    exact ⟨hQ,x,hx,source_solution_lattice5 A2 A3 L c0 c2 c3 hc2 hc3 Q epsilon x hx,
      source_solution_gauge5 A2 A3 L hL c0 c2 c3 Q epsilon hQ x hx,
      source_solution_small_first5 A2 A3 L hL c0 c2 c3 hc2 hc3 Q epsilon hQ x hx⟩
  · intro Q hQ
    exact hbounds Q hQ c0 c2 c3 hc2 hc3 hb
  · intro Q hQ
    exact hQ.1.1
  · intro Q hQ
    exact ⟨hQ.1.2,hQ.2⟩

theorem source_fin5_nonroth_gap5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2Det : A2.det ≠ 0) (h3Det : A3.det ≠ 0) (hLDet : L.det ≠ 0)
    (_hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c0 c2 c3 : Fin 5 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0)
    (hn : ¬ originalRothProperty5 A2 A3 L c0 c2 c3) :
    ∃ hL : IsUnit L, completeFin5GapPackage A2 A3 L hL c0 c2 c3 := by
  have h2 : IsUnit A2 := by
    apply (Matrix.isUnit_iff_isUnit_det A2).mpr
    exact isUnit_iff_ne_zero.mpr h2Det
  have h3 : IsUnit A3 := by
    apply (Matrix.isUnit_iff_isUnit_det A3).mpr
    exact isUnit_iff_ne_zero.mpr h3Det
  have hL : IsUnit L := by
    apply (Matrix.isUnit_iff_isUnit_det L).mpr
    exact isUnit_iff_ne_zero.mpr hLDet
  exact ⟨hL,source_fin5_nonroth_gap_units5 A2 A3 L h2 h3 hL c0 c2 c3 hc2 hc3 hb hn⟩


end CompoundFeasibility.OriginalVariableGap5
