import SubspaceBridge.SourceCompoundGap52_239
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.CompoundLine52_240

def squareDomain240 (U : Set ℝ) : Set ℝ := (fun Q : ℝ => Q^2) '' U

theorem squareDomain_unbounded240 (U : Set ℝ) (hU : ¬ BddAbove U)
    (hq : ∀ Q ∈ U, 1 < Q) : ¬ BddAbove (squareDomain240 U) := by
  rintro ⟨b,hb⟩
  obtain ⟨Q,hQU,hbQ⟩ := not_bddAbove_iff.mp hU b
  have hpow : Q ≤ Q^2 := le_self_pow₀ (hq Q hQU).le (by decide)
  exact (not_le_of_gt (hbQ.trans_le hpow)) (hb ⟨Q,hQU,rfl⟩)

theorem squareDomain_positive240 (U : Set ℝ) (hq : ∀ Q ∈ U, 1 < Q) :
    ∀ p ∈ squareDomain240 U, 1 < p := by
  rintro p ⟨Q,hQU,rfl⟩
  exact Exterior52_238.powered_gt_one238 Q (hq Q hQU)

theorem exists_square_section240 (U : Set ℝ) :
    ∃ lift : squareDomain240 U → U, ∀ p, (lift p).val^2 = p.val := by
  have hh (p : squareDomain240 U) : ∃ q : U, q.val^2 = p.val := by
    obtain ⟨Q,hQU,he⟩ := p.property
    exact ⟨⟨Q,hQU⟩,he⟩
  choose lift hlift using hh
  exact ⟨lift,hlift⟩

theorem square_pullback_unbounded240 (U : Set ℝ) (hq : ∀ Q ∈ U, 1 < Q)
    (lift : squareDomain240 U → U) (hlift : ∀ p, (lift p).val^2 = p.val)
    (V : Set ℝ) (hVP : V ⊆ squareDomain240 U) (hV : ¬ BddAbove V) :
    ¬ BddAbove {Q | ∃ p : squareDomain240 U, p.val ∈ V ∧ (lift p).val = Q} := by
  rintro ⟨b,hb⟩
  apply hV
  refine ⟨(max b 1)^2,?_⟩
  intro P hPV
  let p : squareDomain240 U := ⟨P,hVP hPV⟩
  have hbound : (lift p).val ≤ b := hb ⟨p,hPV,rfl⟩
  have hpos : 0 ≤ (lift p).val := (zero_lt_one.trans (hq _ (lift p).property)).le
  have hpow := pow_le_pow_left₀ hpos (hbound.trans (le_max_left b 1)) 2
  rw [hlift p] at hpow
  exact hpow

end CompoundFeasibility.CompoundLine52_240
