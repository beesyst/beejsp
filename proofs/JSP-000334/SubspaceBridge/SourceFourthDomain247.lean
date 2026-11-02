import SubspaceBridge.SourceAdjugateRecovery247
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag247

def fourthDomain247 (U : Set ℝ) : Set ℝ := (fun Q : ℝ => Q^4) '' U

theorem fourthDomain_unbounded247 (U : Set ℝ) (hU : ¬ BddAbove U)
    (hq : ∀ Q ∈ U, 1 < Q) : ¬ BddAbove (fourthDomain247 U) := by
  rintro ⟨b,hb⟩
  obtain ⟨Q,hQU,hbQ⟩ := not_bddAbove_iff.mp hU b
  have hpow : Q ≤ Q^4 := le_self_pow₀ (hq Q hQU).le (by decide)
  exact (not_le_of_gt (hbQ.trans_le hpow)) (hb ⟨Q,hQU,rfl⟩)

theorem fourthDomain_positive247 (U : Set ℝ) (hq : ∀ Q ∈ U, 1 < Q) :
    ∀ p ∈ fourthDomain247 U, 1 < p := by
  rintro p ⟨Q,hQU,rfl⟩
  exact Exterior54_246.powered_gt_one4246 Q (hq Q hQU)

theorem exists_fourth_section247 (U : Set ℝ) :
    ∃ lift : fourthDomain247 U → U, ∀ p, (lift p).val^4 = p.val := by
  have hh (p : fourthDomain247 U) : ∃ q : U, q.val^4 = p.val := by
    obtain ⟨Q,hQU,he⟩ := p.property
    exact ⟨⟨Q,hQU⟩,he⟩
  choose lift hlift using hh
  exact ⟨lift,hlift⟩

theorem fourth_pullback_unbounded247 (U : Set ℝ) (hq : ∀ Q ∈ U, 1 < Q)
    (lift : fourthDomain247 U → U) (hlift : ∀ p, (lift p).val^4 = p.val)
    (V : Set ℝ) (hVP : V ⊆ fourthDomain247 U) (hV : ¬ BddAbove V) :
    ¬ BddAbove {Q | ∃ p : fourthDomain247 U, p.val ∈ V ∧ (lift p).val = Q} := by
  rintro ⟨b,hb⟩
  apply hV
  refine ⟨(max b 1)^4,?_⟩
  intro P hPV
  let p : fourthDomain247 U := ⟨P,hVP hPV⟩
  have hbound : (lift p).val ≤ b := hb ⟨p,hPV,rfl⟩
  have hpos : 0 ≤ (lift p).val := (zero_lt_one.trans (hq _ (lift p).property)).le
  have hpow := pow_le_pow_left₀ hpos (hbound.trans (le_max_left b 1)) 4
  rw [hlift p] at hpow
  exact hpow

end CompoundFeasibility.SourceFlag247
