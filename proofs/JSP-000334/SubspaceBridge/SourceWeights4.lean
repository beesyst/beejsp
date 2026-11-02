import SubspaceBridge.SourceVanishing4
import SubspaceBridge.OriginalSelectedInputs4
import Mathlib.Topology.MetricSpace.Pseudo.Pi
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceWeights4
open OriginalDeformation4 OriginalDeformedSource4 OriginalSelectedSystem4

theorem select_unbounded_weights (U : Set ℝ) (hU : ¬ BddAbove U)
    (alpha : ℝ → Fin 4 → ℝ) (hb : ∀ q ∈ U, ∀ i, |alpha q i| ≤ 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ V : Set ℝ, V ⊆ U ∧ ¬ BddAbove V ∧ ∃ q0 ∈ V,
      ∀ q ∈ V, ∀ i, |alpha q i-alpha q0 i| < epsilon := by
  let B : Set (Fin 4 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨S,hSB,hS,hcover⟩ := hB.finite_cover_balls (show 0 < epsilon/2 by positivity)
  let F : (Fin 4 → ℝ) → Set ℝ := fun x => {q | q ∈ U ∧ alpha q ∈ Metric.ball x (epsilon/2)}
  have hUF : U ⊆ ⋃ x ∈ S, F x := by
    intro q hq
    have ha : alpha q ∈ B := by
      intro i hi
      exact abs_le.mp (hb q hq i)
    obtain ⟨x,hx,hqx⟩ := Set.mem_iUnion₂.mp (hcover ha)
    exact Set.mem_iUnion₂.mpr ⟨x,hx,hq,hqx⟩
  have hex : ∃ x ∈ S, ¬ BddAbove (F x) := by
    by_contra hn
    push_neg at hn
    exact hU (((hS.bddAbove_biUnion).mpr hn).mono hUF)
  obtain ⟨x,hx,hF⟩ := hex
  obtain ⟨q0,h0,_⟩ := not_bddAbove_iff.mp hF 0
  refine ⟨F x,fun q hq => hq.1,hF,q0,h0,?_⟩
  intro q hq i
  have hqi := (dist_pi_lt_iff (show 0 < epsilon/2 by positivity)).mp hq.2 i
  have h0i := (dist_pi_lt_iff (show 0 < epsilon/2 by positivity)).mp h0.2 i
  rw [Real.dist_eq] at hqi h0i
  calc
    |alpha q i-alpha q0 i| ≤ |alpha q i-x i|+|x i-alpha q0 i| := abs_sub_le _ _ _
    _ < epsilon/2+epsilon/2 := add_lt_add hqi (by simpa only [abs_sub_comm] using h0i)
    _ = epsilon := by ring


def logWeight (Q a : ℝ) : ℝ := Real.log a / Real.log Q

theorem logWeight_bounds (Q a : ℝ) (hQ : 1 < Q) (ha : 0 < a)
    (hau : a < Q) (hai : a⁻¹ < Q) : -1 < logWeight Q a ∧ logWeight Q a < 1 := by
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have h1 := Real.log_lt_log ha hau
  have h2 := Real.log_lt_log (inv_pos.mpr ha) hai
  rw [Real.log_inv] at h2
  constructor
  · apply (lt_div_iff₀ hlog).mpr
    linarith
  · apply (div_lt_iff₀ hlog).mpr
    linarith

theorem logWeight_power (Q a : ℝ) (hQ : 1 < Q) (ha : 0 < a) : Q^(logWeight Q a)=a := by
  rw [logWeight,Real.rpow_def_of_pos (lt_trans zero_lt_one hQ)]
  have he : Real.log Q*(Real.log a/Real.log Q)=Real.log a := by
    field_simp [(Real.log_pos hQ).ne']
  rw [he,Real.exp_log ha]

theorem logWeight_balance (Q : ℝ) (hQ : 1 < Q) (a b2 b3 : Fin 4 → ℝ)
    (ha : ∀ i,0<a i) (hp : (∏ i,a i*Q^(b2 i)*Q^(b3 i))=1) :
    (∑ i,logWeight Q (a i))+(∑ i,b2 i)+(∑ i,b3 i)=0 := by
  have hq := lt_trans zero_lt_one hQ
  have hpow : Q^(∑ i : Fin 4,(logWeight Q (a i)+b2 i+b3 i))=1 := by
    rw [Real.rpow_sum_of_pos hq]
    calc
      _ = ∏ i : Fin 4,a i*Q^(b2 i)*Q^(b3 i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Real.rpow_add hq,Real.rpow_add hq,logWeight_power Q (a i) hQ (ha i)]
      _ = 1 := hp
  have hs := (Real.rpow_right_inj hq (ne_of_gt hQ)).mp (hpow.trans (Real.rpow_zero Q).symm)
  simpa only [Finset.sum_add_distrib] using hs

def fixedWeights (a b2 b3 : Fin 4 → ℝ) (tau : Fin 3) (i : Fin 4) : ℝ :=
  if tau=0 then a i else if tau=1 then b2 i else b3 i

theorem fixedWeights_bounds_balance (a b2 b3 : Fin 4 → ℝ)
    (ha : ∀ i,-1<a i ∧ a i<1) (h2 : ∀ i,-1≤b2 i ∧ b2 i≤0)
    (h3 : ∀ i,-1≤b3 i ∧ b3 i≤0)
    (hb : (∑ i,a i)+(∑ i,b2 i)+(∑ i,b3 i)=0) :
    (∀ tau i,|fixedWeights a b2 b3 tau i|≤1) ∧ (∑ tau,∑ i,fixedWeights a b2 b3 tau i)=0 := by
  constructor
  · intro tau i
    fin_cases tau <;> simp only [fixedWeights,Fin.reduceFinMk,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
    · exact abs_le.mpr ⟨(ha i).1.le,(ha i).2.le⟩
    · exact abs_le.mpr ⟨(h2 i).1,(h2 i).2.trans (by norm_num)⟩
    · exact abs_le.mpr ⟨(h3 i).1,(h3 i).2.trans (by norm_num)⟩
  · simpa [Fin.sum_univ_three,fixedWeights,add_assoc] using hb

theorem finite_form_bounds (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (q : ℝ) (hq : 1 < q) (c2 c3 : Fin 4 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (z : originalSourceGroup4 A2 A3 q c2 c3) :
    (∀ i, ‖(SourceForms4.finiteMatrix4 2 A2 *ᵥ (fun j => ((z : Fin 4 → ℤ) j : ℚ_[2]))) i‖ ≤
      (q^(5 : ℕ))^(c2 i/5)) ∧
    (∀ i, ‖(SourceForms4.finiteMatrix4 3 A3 *ᵥ (fun j => ((z : Fin 4 → ℤ) j : ℚ_[3]))) i‖ ≤
      (q^(5 : ℕ))^(c3 i/5)) := by
  have hm := z.property
  change _ ∈ sourceLattice4 A2 A3 _ _ at hm
  constructor
  · intro i
    rw [rescaled_power4 q _ (zero_lt_one.trans hq),SourceForms4.finiteMatrix4,OriginalAuxiliaryDual4.finite_form_norm4]
    apply (padic_rpow_ceil42 2 q (c2 i) hq (hc2 i) _).mpr
    simpa only [zpow_neg,zpow_natCast] using (lattice4_spec 2 A2 _ _).mp hm.1 i
  · intro i
    rw [rescaled_power4 q _ (zero_lt_one.trans hq),SourceForms4.finiteMatrix4,OriginalAuxiliaryDual4.finite_form_norm4]
    apply (padic_rpow_ceil42 3 q (c3 i) hq (hc3 i) _).mpr
    simpa only [zpow_neg,zpow_natCast] using (lattice4_spec 3 A3 _ _).mp hm.2 i


variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

def frameWidths (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
    (hQU q.val q.property) c0 c2 c3 delta (u q)) (q : U) : Fin 4 → ℝ :=
  deformedWidths4 q.val c0
    (gapDeformation4 (sourceMinima4 A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3)) (F q).sigma

theorem fixed_weights_same_frame4
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ V : Set ℝ, V ⊆ U ∧ ¬ BddAbove V ∧
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧
    ∃ c : Fin 3 → Fin 4 → ℝ, (∀ tau i, |c tau i| ≤ 1) ∧
      (∑ tau, ∑ i, c tau i) = 0 ∧
      (∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5) ∧
      ∀ (q : U), q.val ∈ V →
        (∀ (j : Fin 3) i, ‖(L *ᵥ integerReal ((F q).w j.castSucc : Fin 4 → ℤ)) i‖ ≤
          (q.val^(5 : ℕ))^(c 0 i-d)) ∧
        (∀ (j : Fin 3) i, ‖(SourceForms4.finiteMatrix4 2 A2 *ᵥ
          (fun k => (((F q).w j.castSucc : Fin 4 → ℤ) k : ℚ_[2]))) i‖ ≤ (q.val^(5 : ℕ))^(c 1 i)) ∧
        (∀ (j : Fin 3) i, ‖(SourceForms4.finiteMatrix4 3 A3 *ᵥ
          (fun k => (((F q).w j.castSucc : Fin 4 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^(5 : ℕ))^(c 2 i)) := by
  let eps : ℝ := min (delta/96) (1/4)
  have he : 0 < eps := lt_min (by positivity) (by norm_num)
  have he1 : eps < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hslack : eps+eps < delta/24 := by
    have hh : eps ≤ delta/96 := min_le_left _ _
    linarith
  have hqp (q : U) : 1 < q.val^(5 : ℕ) := one_lt_pow₀ (hQU q.val q.property) (by decide)
  have hab (q : U) (i : Fin 4) :
      -1 < logWeight (q.val^(5 : ℕ)) (frameWidths F q i) ∧
      logWeight (q.val^(5 : ℕ)) (frameWidths F q i) < 1 :=
    logWeight_bounds _ _ (hqp q) ((F q).widths_pos i) ((F q).sizes i).1 ((F q).sizes i).2.1
  let alpha : ℝ → Fin 4 → ℝ := fun q => if h : q ∈ U then
    fun i => logWeight (q^(5 : ℕ)) (frameWidths F ⟨q,h⟩ i) else 0
  have hb : ∀ q ∈ U, ∀ i, |alpha q i| ≤ 1 := by
    intro q hq i
    simp only [alpha,dif_pos hq]
    exact abs_le.mpr ⟨(hab ⟨q,hq⟩ i).1.le,(hab ⟨q,hq⟩ i).2.le⟩
  obtain ⟨V,hVU,hV,q0,hq0,hclose⟩ := select_unbounded_weights U hU alpha hb eps he
  let u0 : U := ⟨q0,hVU hq0⟩
  let a0 : Fin 4 → ℝ := fun i => logWeight (q0^(5 : ℕ)) (frameWidths F u0 i)
  let c := fixedWeights a0 (fun i => c2 i/5) (fun i => c3 i/5)
  have hp : (∏ i, frameWidths F u0 i*(q0^(5 : ℕ))^(c2 i/5)*(q0^(5 : ℕ))^(c3 i/5)) = 1 := by
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    have hpow (i : Fin 4) :
        (q0^(5 : ℕ))^(c2 i/5)*(q0^(5 : ℕ))^(c3 i/5) = q0^(c2 i+c3 i) := by
      rw [rescaled_power4 _ _ (zero_lt_one.trans (hQU q0 (hVU hq0))),
        rescaled_power4 _ _ (zero_lt_one.trans (hQU q0 (hVU hq0))),
        ← Real.rpow_add (zero_lt_one.trans (hQU q0 (hVU hq0)))]
    rw [mul_assoc,← Finset.prod_mul_distrib]
    simp_rw [hpow]
    exact (F u0).balance
  have hcb := fixedWeights_bounds_balance a0 (fun i => c2 i/5) (fun i => c3 i/5)
    (hab u0) (rescaled_finite_weights4 c2 hc2) (rescaled_finite_weights4 c3 hc3)
    (logWeight_balance _ (hqp u0) (frameWidths F u0) _ _ (F u0).widths_pos hp)
  refine ⟨V,hVU,hV,eps,he,he1,c,hcb.1,hcb.2,by intro i; exact ⟨rfl,rfl⟩,?_⟩
  intro q hq
  have happrox (i : Fin 4) :
      |logWeight (q.val^(5 : ℕ)) (frameWidths F q i)-a0 i| < eps := by
    have hh := hclose q.val hq i
    simpa only [alpha,dif_pos q.property,dif_pos (hVU hq0),a0,u0] using hh
  refine ⟨?_,?_,?_⟩
  · intro j i
    have heq : (q.val^(5 : ℕ))^(logWeight (q.val^(5 : ℕ)) (frameWidths F q i)) = frameWidths F q i :=
      logWeight_power _ _ (hqp q) ((F q).widths_pos i)
    have hexp : -delta/24+logWeight (q.val^(5 : ℕ)) (frameWidths F q i) ≤ a0 i-eps := by
      have hh := (abs_lt.mp (happrox i)).2
      linarith
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (q.val^(5 : ℕ))^(-(delta/24))*frameWidths F q i := attaining_first_three4 (F q) j i
      _ = (q.val^(5 : ℕ))^(-delta/24+logWeight (q.val^(5 : ℕ)) (frameWidths F q i)) := by
        rw [Real.rpow_add (zero_lt_one.trans (hqp q)),heq]
        congr 1 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hqp q).le hexp
  · intro j i
    exact (finite_form_bounds A2 A3 q.val (hQU q.val q.property) c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) ((F q).w j.castSucc)).1 i
  · intro j i
    exact (finite_form_bounds A2 A3 q.val (hQU q.val q.property) c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) ((F q).w j.castSucc)).2 i

end CompoundFeasibility.SourceWeights4
