import SubspaceBridge.AnalyticReadiness6
import SubspaceBridge.SourceGrid6
import Mathlib.Topology.MetricSpace.Pseudo.Pi
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceWeights

theorem select_unbounded_weights (U : Set ℝ) (hU : ¬ BddAbove U)
    (alpha : ℝ → Fin 6 → ℝ) (hb : ∀ q ∈ U, ∀ i, |alpha q i| ≤ 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ V : Set ℝ, V ⊆ U ∧ ¬ BddAbove V ∧ ∃ q0 ∈ V,
      ∀ q ∈ V, ∀ i, |alpha q i-alpha q0 i| < epsilon := by
  let B : Set (Fin 6 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨S,hSB,hS,hcover⟩ := hB.finite_cover_balls (show 0 < epsilon/2 by positivity)
  let F : (Fin 6 → ℝ) → Set ℝ := fun x => {q | q ∈ U ∧ alpha q ∈ Metric.ball x (epsilon/2)}
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

theorem logWeight_balance (Q : ℝ) (hQ : 1 < Q) (a b2 b3 : Fin 6 → ℝ)
    (ha : ∀ i,0<a i) (hp : (∏ i,a i*Q^(b2 i)*Q^(b3 i))=1) :
    (∑ i,logWeight Q (a i))+(∑ i,b2 i)+(∑ i,b3 i)=0 := by
  have hq := lt_trans zero_lt_one hQ
  have hpow : Q^(∑ i : Fin 6,(logWeight Q (a i)+b2 i+b3 i))=1 := by
    rw [Real.rpow_sum_of_pos hq]
    calc
      _ = ∏ i : Fin 6,a i*Q^(b2 i)*Q^(b3 i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Real.rpow_add hq,Real.rpow_add hq,logWeight_power Q (a i) hQ (ha i)]
      _ = 1 := hp
  have hs := (Real.rpow_right_inj hq (ne_of_gt hQ)).mp (hpow.trans (Real.rpow_zero Q).symm)
  simpa only [Finset.sum_add_distrib] using hs

def finiteWeight (c : Fin 4 → ℝ) (i : Fin 6) : ℝ := pairWeights42 c i/11

theorem finiteWeight_bounds (c : Fin 4 → ℝ) (hc : ∀ i,-1≤c i ∧ c i≤0) :
    ∀ i,-1≤finiteWeight c i ∧ finiteWeight c i≤0 := by
  intro i
  unfold finiteWeight pairWeights42
  constructor <;> linarith [(hc (lo i)).1,(hc (hi i)).1,(hc (lo i)).2,(hc (hi i)).2]

def fixedWeights (a b2 b3 : Fin 6 → ℝ) (tau : Fin 3) (i : Fin 6) : ℝ :=
  if tau=0 then a i else if tau=1 then b2 i else b3 i

theorem fixedWeights_bounds_balance (a b2 b3 : Fin 6 → ℝ)
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

def selectionSlack (delta4 : ℝ) : ℝ := min (delta4/1056) (1/4)

theorem selectionSlack_bounds (delta4 : ℝ) (hd : 0<delta4) :
    0<selectionSlack delta4 ∧ selectionSlack delta4<1 ∧
      selectionSlack delta4+selectionSlack delta4<delta4/264 := by
  have hlo : 0<selectionSlack delta4 := lt_min (by positivity) (by norm_num)
  have h1 := min_le_left (delta4/1056) (1/4 : ℝ)
  have h2 := min_le_right (delta4/1056) (1/4 : ℝ)
  exact ⟨hlo,by dsimp [selectionSlack]; linarith,by dsimp [selectionSlack]; linarith⟩


theorem weighted_form_bound (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (W : Fin 6 → ℝ) (hW : ∀ i,0<W i) (x : Fin 6 → ℝ) (g : ℝ)
    (hg : coordinateGauge6 (weightedCoordinates6 e W hW) x≤g) :
    ∀ i,‖e x i‖≤W i*g := by
  intro i
  have hi := (norm_le_pi_norm ((weightedCoordinates6 e W hW) x) i).trans hg
  change ‖e x i/W i‖≤g at hi
  rw [norm_div,Real.norm_of_nonneg (hW i).le,div_le_iff₀ (hW i)] at hi
  simpa only [mul_comm] using hi

theorem finite_form_norm (p : ℕ) [Fact p.Prime] (B : Matrix (Fin 4) (Fin 4) ℚ)
    (z : Fin 6 → ℤ) (i : Fin 6) :
    ‖(Auxiliary6.SourceExpansion.finiteMatrix p B *ᵥ (fun j => (z j : ℚ_[p]))) i‖ =
      (padicNorm p ((compound B *ᵥ (fun j => (z j : ℚ))) i) : ℝ) := by
  rw [← Auxiliary6.SourceExpansion.finite_norm p]
  congr 1

theorem finite_form_bounds (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (q : ℝ) (hq : 1<q) (c2 c3 : Fin 4 → ℝ)
    (hc2 : ∀ i,c2 i≤0) (hc3 : ∀ i,c3 i≤0)
    (z : directCompoundGroup42 A2 A3 q c2 c3) :
    (∀ i,‖(Auxiliary6.SourceExpansion.finiteMatrix 2 A2 *ᵥ (fun j => ((z : Fin 6 → ℤ) j : ℚ_[2]))) i‖≤
      (q^(11 : ℕ))^(finiteWeight c2 i)) ∧
    (∀ i,‖(Auxiliary6.SourceExpansion.finiteMatrix 3 A3 *ᵥ (fun j => ((z : Fin 6 → ℤ) j : ℚ_[3]))) i‖≤
      (q^(11 : ℕ))^(finiteWeight c3 i)) := by
  have hh := (compound42_source_lattice A2 A3 q hq c2 c3 hc2 hc3 z).mp z.property
  constructor
  · intro i
    rw [finite_form_norm,finiteWeight,davenport_rescaled_power42 q _ (lt_trans zero_lt_one hq)]
    exact hh.1 i
  · intro i
    rw [finite_form_norm,finiteWeight,davenport_rescaled_power42 q _ (lt_trans zero_lt_one hq)]
    exact hh.2 i

theorem real_form_slack (Q a c epsilon delta4 delta6 rho x : ℝ)
    (hQ : 1<Q) (ha : 0<a) (hpower : Q^(logWeight Q a)=a)
    (hclose : |logWeight Q a-c|<epsilon)
    (hslack : epsilon+delta6<delta4/264)
    (hrho : rho<Q^(-(delta4/264))) (hx : x≤a*rho) :
    x≤Q^(c-delta6) := by
  have he : logWeight Q a-delta4/264≤c-delta6 := by
    have hh := (abs_lt.mp hclose).2
    linarith
  apply le_of_lt
  calc
    x ≤ a*rho := hx
    _ < a*Q^(-(delta4/264)) := mul_lt_mul_of_pos_left hrho ha
    _ = Q^(logWeight Q a-delta4/264) := by
      conv_lhs => arg 1; rw [← hpower]
      rw [← Real.rpow_add (lt_trans zero_lt_one hQ)]
      congr 1
    _ ≤ Q^(c-delta6) := Real.rpow_le_rpow_of_exponent_le hQ.le he

theorem ready_frames (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (q : ℝ) (hq : 1<q)
    (c0 c2 c3 : Fin 4 → ℝ) (delta4 : ℝ)
    (v : Fin 6 → directCompoundGroup42 A2 A3 q c2 c3)
    (hr : sourceAnalyticReady42 A2 A3 L hL q hq c0 c2 c3 delta4 v) :
    ∃ sigma : Equiv.Perm (Fin 6),
      let W := davenportWidths42 q c0 (gapDeformation6 (directMinima42 A2 A3 L hL q hq c0 c2 c3)) sigma
      ∃ hW : ∀ i,0<W i,
        (∀ i,W i<q^(11 : ℕ) ∧ (W i)⁻¹<q^(11 : ℕ)) ∧
        (∏ i,W i*(q^(11 : ℕ))^(finiteWeight c2 i)*(q^(11 : ℕ))^(finiteWeight c3 i))=1 ∧
        ∃ w : Fin 6 → directCompoundGroup42 A2 A3 q c2 c3,
          LinearIndependent ℝ (fun j => integerReal (w j : Fin 6 → ℤ)) ∧
          let b := directRealBasis42 A2 A3 (q^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)
          let e := weightedCoordinates6 (compoundFormEquiv42 L hL) W hW
          (∀ j,coordinateGauge6 e (integerReal (w j : Fin 6 → ℤ))=successiveRadius6 b e j) ∧
          successiveRadius6 b e 4<(q^(11 : ℕ))^(-(delta4/264)) := by
  obtain ⟨hd,sigma,hW,hqp,h2,h3,hbounds,hprod,heq,hsep,w,hwi,hatt,hsmall⟩ := hr
  refine ⟨sigma,hW,hbounds,hprod,fun j => ⟨(w j : Fin 6 → ℤ),?_⟩,hwi,hatt,hsmall⟩
  rw [← davenport_rescaled_group42 A2 A3 q c2 c3]
  exact (w j).property


def actualWidths (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (q : ℝ) (hq : 1<q)
    (c0 c2 c3 : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 6)) : Fin 6 → ℝ :=
  davenportWidths42 q c0 (gapDeformation6 (directMinima42 A2 A3 L hL q hq c0 c2 c3)) sigma

theorem power11_unbounded (U : Set ℝ) (hU : ¬ BddAbove U) :
    ¬ BddAbove ((fun q : ℝ => q^(11 : ℕ)) '' U) := by
  intro hb
  apply davenportRescaledDomain42_unbounded U hU 0
  apply hb.mono
  rintro x ⟨q,hq,rfl⟩
  exact ⟨q,hq.1,rfl⟩

def fixedSourceWeights42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (delta4 : ℝ) (U : Set ℝ) (hQU : ∀ q ∈ U,1<q) : Prop :=
  ¬ BddAbove ((fun q : ℝ => q^(11 : ℕ)) '' U) ∧
  ∃ epsilon delta6 : ℝ,
    epsilon=selectionSlack delta4 ∧ delta6=selectionSlack delta4 ∧
    0<epsilon ∧ 0<delta6 ∧ delta6<1 ∧ epsilon+delta6<delta4/264 ∧
    ∃ c : Fin 3 → Fin 6 → ℝ,
      (∀ tau i,|c tau i|≤1) ∧ (∑ tau,∑ i,c tau i)=0 ∧
      (∀ i,c 1 i=finiteWeight c2 i ∧ c 2 i=finiteWeight c3 i) ∧
      ∃ sigma : U → Equiv.Perm (Fin 6),
      ∃ hW : ∀ (q : U) i,0<actualWidths A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 (sigma q) i,
      ∃ w : (q : U) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3,
      ∃ q0 : U,
        (∀ i,c 0 i=logWeight (q0.val^(11 : ℕ))
          (actualWidths A2 A3 L hL q0.val (hQU q0.val q0.property) c0 c2 c3 (sigma q0) i)) ∧
        ∀ q : U,
          let W := actualWidths A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 (sigma q)
          let b := directRealBasis42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)
          let e := weightedCoordinates6 (compoundFormEquiv42 L hL) W (hW q)
          (∀ i, -1<logWeight (q.val^(11 : ℕ)) (W i) ∧ logWeight (q.val^(11 : ℕ)) (W i)<1) ∧
          (∀ i,(q.val^(11 : ℕ))^(logWeight (q.val^(11 : ℕ)) (W i))=W i) ∧
          (∀ i,|logWeight (q.val^(11 : ℕ)) (W i)-c 0 i|<epsilon) ∧
          (∏ i,W i*(q.val^(11 : ℕ))^(finiteWeight c2 i)*(q.val^(11 : ℕ))^(finiteWeight c3 i))=1 ∧
          LinearIndependent ℝ (fun j => integerReal (w q j : Fin 6 → ℤ)) ∧
          LinearIndependent ℚ (fun j : Fin 5 => fun i => ((w q j.castSucc : Fin 6 → ℤ) i : ℚ)) ∧
          directCompoundGroup42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)=
            directCompoundGroup42 A2 A3 q.val c2 c3 ∧
          (∀ j,coordinateGauge6 e (integerReal (w q j : Fin 6 → ℤ))=successiveRadius6 b e j) ∧
          successiveRadius6 b e 4<(q.val^(11 : ℕ))^(-(delta4/264)) ∧
          (∀ j : Fin 5,∀ i,‖(compound L *ᵥ integerReal (w q j.castSucc : Fin 6 → ℤ)) i‖≤
            (q.val^(11 : ℕ))^(c 0 i-delta6)) ∧
          (∀ j : Fin 5,∀ i,‖(Auxiliary6.SourceExpansion.finiteMatrix 2 A2 *ᵥ
            (fun k => ((w q j.castSucc : Fin 6 → ℤ) k : ℚ_[2]))) i‖≤(q.val^(11 : ℕ))^(c 1 i)) ∧
          (∀ j : Fin 5,∀ i,‖(Auxiliary6.SourceExpansion.finiteMatrix 3 A3 *ᵥ
            (fun k => ((w q j.castSucc : Fin 6 → ℤ) k : ℚ_[3]))) i‖≤(q.val^(11 : ℕ))^(c 2 i))

theorem fixed_weights_of_ready (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (hc2 : ∀ i,-1≤c2 i ∧ c2 i≤0) (hc3 : ∀ i,-1≤c3 i ∧ c3 i≤0)
    (delta4 : ℝ) (hd : 0<delta4) (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U,1<q)
    (v : (q : U) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
    (hr : ∀ q : U,sourceAnalyticReady42 A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 delta4 (v q)) :
    ∃ V : Set ℝ,∃ hVU : V ⊆ U,¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L hL c0 c2 c3 delta4 V (fun q hq => hQU q (hVU hq)) := by
  classical
  choose sigma hW hbounds hprod w hwi hatt hsmall using
    (fun q : U => ready_frames A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 delta4 (v q) (hr q))
  let W (q : U) := actualWidths A2 A3 L hL q.val (hQU q.val q.property) c0 c2 c3 (sigma q)
  have hqp (q : U) : 1<q.val^(11 : ℕ) := one_lt_pow₀ (hQU q.val q.property) (by decide)
  have hab (q : U) (i : Fin 6) : -1<logWeight (q.val^(11 : ℕ)) (W q i) ∧
      logWeight (q.val^(11 : ℕ)) (W q i)<1 :=
    logWeight_bounds _ _ (hqp q) (hW q i) (hbounds q i).1 (hbounds q i).2
  let alpha : ℝ → Fin 6 → ℝ := fun q => if h : q ∈ U then
    fun i => logWeight (q^(11 : ℕ)) (W ⟨q,h⟩ i) else 0
  have hb : ∀ q ∈ U,∀ i,|alpha q i|≤1 := by
    intro q hq i
    simp only [alpha,dif_pos hq]
    exact abs_le.mpr ⟨(hab ⟨q,hq⟩ i).1.le,(hab ⟨q,hq⟩ i).2.le⟩
  let eps := selectionSlack delta4
  have hs := selectionSlack_bounds delta4 hd
  obtain ⟨V,hVU,hVb,q0,hq0,hclose⟩ := select_unbounded_weights U hU alpha hb eps hs.1
  let lift : V → U := fun q => ⟨q.val,hVU q.property⟩
  let u0 : U := ⟨q0,hVU hq0⟩
  let a0 : Fin 6 → ℝ := fun i => logWeight (q0^(11 : ℕ)) (W u0 i)
  let c := fixedWeights a0 (finiteWeight c2) (finiteWeight c3)
  have hc := fixedWeights_bounds_balance a0 (finiteWeight c2) (finiteWeight c3)
    (hab u0) (finiteWeight_bounds c2 hc2) (finiteWeight_bounds c3 hc3)
    (logWeight_balance _ (hqp u0) (W u0) (finiteWeight c2) (finiteWeight c3) (hW u0) (hprod u0))
  have happrox (q : V) (i : Fin 6) : |logWeight (q.val^(11 : ℕ)) (W (lift q) i)-a0 i|<eps := by
    have hh := hclose q.val q.property i
    simpa only [alpha,dif_pos (hVU q.property),dif_pos (hVU hq0),lift,u0,a0] using hh
  refine ⟨V,hVU,hVb,power11_unbounded V hVb,eps,eps,rfl,rfl,hs.1,hs.1,hs.2.1,hs.2.2,
    c,hc.1,hc.2,?_,fun q => sigma (lift q),fun q i => hW (lift q) i,
    fun q j => w (lift q) j,⟨q0,hq0⟩,?_,?_⟩
  · intro i
    constructor <;> rfl
  · intro i
    rfl
  · intro q
    let b := directRealBasis42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)
    let e := weightedCoordinates6 (compoundFormEquiv42 L hL) (W (lift q)) (hW (lift q))
    have hiQ : LinearIndependent ℚ (fun j i => ((w (lift q) j : Fin 6 → ℤ) i : ℚ)) :=
      (integer6_independent_iff42 _).mpr (hwi (lift q))
    have hm : Monotone (successiveRadius6 b e) := (exists_successive_minima6 b e).choose_spec.2.2.2.1
    refine ⟨hab (lift q),?_,happrox q,hprod (lift q),hwi (lift q),
      hiQ.comp Fin.castSucc (Fin.castSucc_injective 5),davenport_rescaled_group42 A2 A3 q.val c2 c3,
      hatt (lift q),hsmall (lift q),?_,?_,?_⟩
    · intro i
      exact logWeight_power _ _ (hqp (lift q)) (hW (lift q) i)
    · intro j i
      have hg : coordinateGauge6 e (integerReal (w (lift q) j.castSucc : Fin 6 → ℤ))≤successiveRadius6 b e 4 := by
        have heq : coordinateGauge6 e (integerReal (w (lift q) j.castSucc : Fin 6 → ℤ))=
            successiveRadius6 b e j.castSucc := hatt (lift q) j.castSucc
        exact heq.le.trans (hm (show j.castSucc ≤ (4 : Fin 6) from by
          change j.val ≤ 4
          have hj := j.isLt
          omega))
      have hg' := weighted_form_bound (compoundFormEquiv42 L hL) (W (lift q)) (hW (lift q))
        (integerReal (w (lift q) j.castSucc : Fin 6 → ℤ)) _ hg i
      exact real_form_slack (q.val^(11 : ℕ)) (W (lift q) i) (a0 i) eps delta4 eps
        (successiveRadius6 b e 4) _ (hqp (lift q)) (hW (lift q) i)
        (logWeight_power _ _ (hqp (lift q)) (hW (lift q) i)) (happrox q i) hs.2.2 (hsmall (lift q)) hg'
    · intro j i
      exact (finite_form_bounds A2 A3 q.val (hQU q.val (hVU q.property)) c2 c3
        (fun i => (hc2 i).2) (fun i => (hc3 i).2) (w (lift q) j.castSucc)).1 i
    · intro j i
      exact (finite_form_bounds A2 A3 q.val (hQU q.val (hVU q.property)) c2 c3
        (fun i => (hc2 i).2) (fun i => (hc3 i).2) (w (lift q) j.castSucc)).2 i


theorem source_compound_unbounded_fixed_weights42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    (∀ s t, IsAlgebraic ℚ (compound L s t)) ∧
    IsUnit (compound A₂) ∧ IsUnit (compound A₃) ∧ IsUnit (compound L) ∧
    ∃ κ C₄ C K T : ℝ, 0 < κ ∧ 0 < C₄ ∧ 0 < C ∧ 0 < K ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s, |pairWeights42 c₀ s| ≤ 2) ∧
        (∀ s, -2 ≤ pairWeights42 c₂ s ∧ pairWeights42 c₂ s ≤ 0) ∧
        (∀ s, -2 ≤ pairWeights42 c₃ s ∧ pairWeights42 c₃ s ≤ 0) ∧
        (∑ s, (pairWeights42 c₀ s + pairWeights42 c₂ s + pairWeights42 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hUb : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hmem : Q ∈ U),
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 1 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 2 * Q ^ (-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧ ¬ BddAbove (davenportRescaledDomain42 V T) ∧
            ∃ (u : (t : V) → Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃)
              (v : (t : V) → Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃),
              (∀ t : V, T < t.val ∧
                sourceHyperplane42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property))
                  c₀ c₂ c₃ κ (u t) (v t) ∧
                rationalDualLine42 (fun i => (u t i : Fin 4 → ℤ)) (fun j => (v t j : Fin 6 → ℤ))
                  (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃) ∧
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 4 <
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 5 *
                  t.val ^ (-delta / 2) ∧
                let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val
                  (hQU t.val (hVU t.property)) c₀ c₂ c₃
                (0 < ∏ i, rho i) ∧ (∏ i, rho i) ≤ 64*C₄^3 ∧
                  gapRadius6 rho^(6 : ℕ) < (64*C₄^3)*t.val ^ (-delta/2) ∧
                  sourceDavenportDecay42 A₂ A₃ L (sourceUnit42 L hL) t.val
                    (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) ∧
                  1/(C*t.val^(2 : ℕ)) ≤ rho 0 ∧ rho 5 ≤ K*t.val^(6 : ℕ) ∧
                  (∀ sigma : Equiv.Perm (Fin 6), ∀ i,
                    davenportWidths42 t.val c₀ (gapDeformation6 rho) sigma i ≤ C*K*t.val^(10 : ℕ) ∧
                    (davenportWidths42 t.val c₀ (gapDeformation6 rho) sigma i)⁻¹ ≤ C*K*t.val^(10 : ℕ)) ∧
                  sourceAnalyticReady42 A₂ A₃ L (sourceUnit42 L hL) t.val
                    (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) ) ∧ fixedSourceWeights42 A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ delta V
                (fun Q hQ => hQU Q (hVU hQ)) := by
  obtain ⟨halg,hu2,hu3,huL,kappa,C4,C,K,T,hk,hC4,hC,hK,hT,hcut,hfamily⟩ :=
    source_compound_unbounded_analytic_ready42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨halg,hu2,hu3,huL,kappa,C4,C,K,T,hk,hC4,hC,hK,hT,hcut,?_⟩
  intro c0 c2 c3 hc0 hc2 hc3 hb
  obtain ⟨hb0,hb2,hb3,hbb,hF⟩ := hfamily c0 c2 c3 hc0 hc2 hc3 hb
  refine ⟨hb0,hb2,hb3,hbb,?_⟩
  intro U hUb hQU hgap
  obtain ⟨U0,hU0U,hU0b,hres,u0,v0,hframes⟩ := hF U hUb hQU hgap
  let hQ0 : ∀ q ∈ U0,1<q := fun q hq => hQU q (hU0U hq)
  have hr : ∀ q : U0, sourceAnalyticReady42 A₂ A₃ L (sourceUnit42 L hL) q.val
      (hQ0 q.val q.property) c0 c2 c3 delta (v0 q) := by
    intro q
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hr⟩ := hframes q
    exact hr
  obtain ⟨V,hVU0,hVb,hfixed⟩ := fixed_weights_of_ready A₂ A₃ L (sourceUnit42 L hL)
    c0 c2 c3 hc2 hc3 delta hd U0 hU0b hQ0 v0 hr
  let hVU : V ⊆ U := fun q hq => hU0U (hVU0 hq)
  let lift : V → U0 := fun q => ⟨q.val,hVU0 q.property⟩
  refine ⟨V,hVU,hVb,davenportRescaledDomain42_unbounded V hVb T,
    (fun q => u0 (lift q)),(fun q => v0 (lift q)),?_,hfixed⟩
  intro q
  exact hframes (lift q)


theorem original_grid_eq (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (c2 c3 : Fin 4 → ℝ)
    (U : Set ℝ) (w : (q : U) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
    {m : ℕ} (t : Fin m → U) (a : Fin m → Fin 5 → ℕ) (h : Fin m) (i : Fin 6) :
    Auxiliary6.SourceGrid.gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a h i =
      ∑ j : Fin 5,(a h j : ℤ)*(w (t h) j.castSucc : Fin 6 → ℤ) i := rfl

end CompoundFeasibility.SourceWeights
