import SubspaceBridge.SourceCompoundGap53_242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundLine53_243

def cubeDomain243 (U : Set ℝ) : Set ℝ := (fun Q : ℝ => Q^3) '' U

theorem cubeDomain_unbounded243 (U : Set ℝ) (hU : ¬ BddAbove U)
    (hq : ∀ Q ∈ U, 1 < Q) : ¬ BddAbove (cubeDomain243 U) := by
  rintro ⟨b,hb⟩
  obtain ⟨Q,hQU,hbQ⟩ := not_bddAbove_iff.mp hU b
  have hpow : Q ≤ Q^3 := le_self_pow₀ (hq Q hQU).le (by decide)
  exact (not_le_of_gt (hbQ.trans_le hpow)) (hb ⟨Q,hQU,rfl⟩)

theorem cubeDomain_positive243 (U : Set ℝ) (hq : ∀ Q ∈ U, 1 < Q) :
    ∀ p ∈ cubeDomain243 U, 1 < p := by
  rintro p ⟨Q,hQU,rfl⟩
  exact Exterior53_242.powered_gt_one3242 Q (hq Q hQU)

theorem exists_cube_section243 (U : Set ℝ) :
    ∃ lift : cubeDomain243 U → U, ∀ p, (lift p).val^3 = p.val := by
  have hh (p : cubeDomain243 U) : ∃ q : U, q.val^3 = p.val := by
    obtain ⟨Q,hQU,he⟩ := p.property
    exact ⟨⟨Q,hQU⟩,he⟩
  choose lift hlift using hh
  exact ⟨lift,hlift⟩

theorem cube_pullback_unbounded243 (U : Set ℝ) (hq : ∀ Q ∈ U, 1 < Q)
    (lift : cubeDomain243 U → U) (hlift : ∀ p, (lift p).val^3 = p.val)
    (V : Set ℝ) (hVP : V ⊆ cubeDomain243 U) (hV : ¬ BddAbove V) :
    ¬ BddAbove {Q | ∃ p : cubeDomain243 U, p.val ∈ V ∧ (lift p).val = Q} := by
  rintro ⟨b,hb⟩
  apply hV
  refine ⟨(max b 1)^3,?_⟩
  intro P hPV
  let p : cubeDomain243 U := ⟨P,hVP hPV⟩
  have hbound : (lift p).val ≤ b := hb ⟨p,hPV,rfl⟩
  have hpos : 0 ≤ (lift p).val := (zero_lt_one.trans (hq _ (lift p).property)).le
  have hpow := pow_le_pow_left₀ hpos (hbound.trans (le_max_left b 1)) 3
  rw [hlift p] at hpow
  exact hpow

end CompoundFeasibility.CompoundLine53_243
