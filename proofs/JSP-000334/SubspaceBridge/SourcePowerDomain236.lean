import SubspaceBridge.SourceDeformedData236
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceRatioLine236

def powerDomain236 (Omega : Set ℝ) (B : ℝ) : Set ℝ :=
  (fun Q : ℝ => Q^5) '' {Q | Q ∈ Omega ∧ B < Q}

theorem powerDomain_unbounded236 (Omega : Set ℝ) (hO : ¬ BddAbove Omega) (B : ℝ) :
    ¬ BddAbove (powerDomain236 Omega B) := by
  intro hb
  obtain ⟨b,hb⟩ := hb
  obtain ⟨Q,hQO,hQ⟩ := not_bddAbove_iff.mp hO (max B (max 1 b))
  have hBQ : B < Q := (le_max_left _ _).trans_lt hQ
  have h1Q : 1 < Q := ((le_max_left 1 b).trans (le_max_right B _)).trans_lt hQ
  have hbQ : b < Q := ((le_max_right 1 b).trans (le_max_right B _)).trans_lt hQ
  have hpow : Q ≤ Q^5 := le_self_pow₀ h1Q.le (by decide)
  exact (not_le_of_gt (hbQ.trans_le hpow)) (hb ⟨Q,⟨hQO,hBQ⟩,rfl⟩)

theorem exists_power_section236 (Omega : Set ℝ) (B : ℝ) :
    ∃ lift : powerDomain236 Omega B → {Q // Q ∈ Omega ∧ B < Q},
      ∀ p, (lift p).val^5 = p.val := by
  have hh (p : powerDomain236 Omega B) :
      ∃ q : {Q // Q ∈ Omega ∧ B < Q}, q.val^5 = p.val := by
    obtain ⟨Q,hQ,he⟩ := p.property
    exact ⟨⟨Q,hQ⟩,he⟩
  choose lift hlift using hh
  exact ⟨lift,hlift⟩

theorem power_pullback_unbounded236 (Omega : Set ℝ) (B : ℝ) (hB : 1 < B)
    (lift : powerDomain236 Omega B → {Q // Q ∈ Omega ∧ B < Q})
    (hlift : ∀ p, (lift p).val^5 = p.val)
    (V : Set ℝ) (hVO : V ⊆ powerDomain236 Omega B) (hV : ¬ BddAbove V) :
    ¬ BddAbove {Q | ∃ p : powerDomain236 Omega B, p.val ∈ V ∧ (lift p).val = Q} := by
  rintro ⟨b,hb⟩
  apply hV
  refine ⟨(max b 1)^5,?_⟩
  intro P hP
  let p : powerDomain236 Omega B := ⟨P,hVO hP⟩
  have hq : (lift p).val ≤ b := hb ⟨p,hP,rfl⟩
  have hq0 : 0 ≤ (lift p).val := (zero_lt_one.trans (hB.trans (lift p).property.2)).le
  have hpow := pow_le_pow_left₀ hq0 (hq.trans (le_max_left b 1)) 5
  rw [hlift p] at hpow
  exact hpow

end CompoundFeasibility.SourceRatioLine236
