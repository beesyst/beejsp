import SubspaceBridge.OriginalFlagAssembly4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.BoundedWeightsLiteral188
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4
noncomputable section

def scaledWeights4 (N : ℕ) (c : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => c i / (N : ℝ)

theorem exists_weight_bound4 (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ i, |c₀ i| ≤ (N : ℝ) ∧
      (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧ (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (∑ i, (|c₀ i|+|c₂ i|+|c₃ i|)) 1)
  have hN1 : (1 : ℝ) < N := (le_max_right _ _).trans_lt hN
  refine ⟨N,by exact_mod_cast hN1.le,?_⟩
  intro i
  have hs : |c₀ i|+|c₂ i|+|c₃ i| ≤ ∑ k, (|c₀ k|+|c₂ k|+|c₃ k|) :=
    Finset.single_le_sum (f := fun k : Fin 4 => |c₀ k|+|c₂ k|+|c₃ k|)
      (fun k _ => by positivity) (Finset.mem_univ i)
  have hsN := hs.trans_lt ((le_max_left _ _).trans_lt hN)
  refine ⟨by linarith [abs_nonneg (c₂ i),abs_nonneg (c₃ i)],⟨?_,hc₂ i⟩,⟨?_,hc₃ i⟩⟩
  · linarith [neg_abs_le (c₂ i),abs_nonneg (c₀ i),abs_nonneg (c₃ i)]
  · linarith [neg_abs_le (c₃ i),abs_nonneg (c₀ i),abs_nonneg (c₂ i)]

theorem scaledWeights4_conditions (N : ℕ) (hN : 1 ≤ N) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc : ∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧
      (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    (∀ i, |scaledWeights4 N c₀ i| ≤ 1) ∧
    (∀ i, -1 ≤ scaledWeights4 N c₂ i ∧ scaledWeights4 N c₂ i ≤ 0) ∧
    (∀ i, -1 ≤ scaledWeights4 N c₃ i ∧ scaledWeights4 N c₃ i ≤ 0) ∧
    (∑ i, (scaledWeights4 N c₀ i+scaledWeights4 N c₂ i+scaledWeights4 N c₃ i) = 0) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [scaledWeights4,abs_div,abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr (by simpa using (hc i).1)
  · intro i
    exact ⟨(le_div_iff₀ hn).mpr (by simpa using (hc i).2.1.1),div_nonpos_of_nonpos_of_nonneg (hc i).2.1.2 hn.le⟩
  · intro i
    exact ⟨(le_div_iff₀ hn).mpr (by simpa using (hc i).2.2.1),div_nonpos_of_nonpos_of_nonneg (hc i).2.2.2 hn.le⟩
  · calc
      _ = (∑ i, (c₀ i+c₂ i+c₃ i))/(N : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [scaledWeights4]
        ring
      _ = 0 := by rw [hb,zero_div]

theorem power_gt_one4 (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (hQ : 1 < Q) : 1 < Q^N :=
  one_lt_pow₀ hQ (by omega)

theorem scaled_power4 (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (hQ : 0 < Q) (c : ℝ) :
    (Q^N)^(c/(N : ℝ)) = Q^c := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  field_simp

theorem scaled_body4 (N : ℕ) (hN : 1 ≤ N) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ) :
    originalBody4 L (Q^N) (scaledWeights4 N c) = originalBody4 L Q c := by
  ext x
  simp only [originalBody4,Set.mem_setOf_eq,scaledWeights4,scaled_power4 N hN Q (lt_trans zero_lt_one hQ)]

theorem scaled_coordinates4 (N : ℕ) (hN : 1 ≤ N) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ) :
    originalCoordinates4 L hL (Q^N) (power_gt_one4 N hN Q hQ) (scaledWeights4 N c) =
      originalCoordinates4 L hL Q hQ c := by
  ext x i
  change (L *ᵥ x) i / (Q^N)^(c i/(N : ℝ)) = (L *ᵥ x) i / Q^(c i)
  rw [scaled_power4 N hN Q (lt_trans zero_lt_one hQ)]

theorem scaled_threshold4 (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (Q c : ℝ) :
    JSP000334.qThreshold p (Q^N) (c/(N : ℝ)) = JSP000334.qThreshold p Q c := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold JSP000334.qThreshold
  rw [Real.log_pow]
  congr 1
  field_simp
  ring

theorem scaled_ceiling4 (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (Q c : ℝ) :
    Nat.ceil (JSP000334.qThreshold p (Q^N) (c/(N : ℝ))) =
      Nat.ceil (JSP000334.qThreshold p Q c) := by
  rw [scaled_threshold4 N hN]

theorem scaled_group4 (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    originalSourceGroup4 A₂ A₃ (Q^N) (scaledWeights4 N c₂) (scaledWeights4 N c₃) =
      originalSourceGroup4 A₂ A₃ Q c₂ c₃ := by
  simp only [originalSourceGroup4,scaledWeights4,scaled_ceiling4 N hN]

theorem scaled_minima4 (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) :
    sourceMinima4 A₂ A₃ L hL (Q^N) (power_gt_one4 N hN Q hQ)
      (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  unfold sourceMinima4
  rw [scaled_group4 N hN,scaled_coordinates4 N hN]

theorem scaled_gap_power4 (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (hQ : 1 < Q) (delta : ℝ) :
    Q^(-delta) = (Q^N)^(-(delta/(N : ℝ))) := by
  rw [show -(delta/(N : ℝ)) = (-delta)/(N : ℝ) by ring,
    scaled_power4 N hN Q (lt_trans zero_lt_one hQ)]

def powerImage4 (N : ℕ) (U : Set ℝ) : Set ℝ := {R | ∃ Q ∈ U, R = Q^N}

theorem powerImage4_gt_one (N : ℕ) (hN : 1 ≤ N) (U : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) :
    ∀ R ∈ powerImage4 N U, 1 < R := by
  rintro R ⟨Q,hQ,rfl⟩
  exact power_gt_one4 N hN Q (hQU Q hQ)

theorem selected_gap_powerImage4 (N : ℕ) (hN : 1 ≤ N)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (delta : ℝ) (hd : 0 < delta)
    (U : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L hL Q (hQU Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L hL Q (hQU Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    0 < delta/(N : ℝ) ∧ ∀ (R : ℝ) (hR : R ∈ powerImage4 N U),
      sourceMinima4 A₂ A₃ L hL R (powerImage4_gt_one N hN U hQU R hR)
        (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.castSucc <
      sourceMinima4 A₂ A₃ L hL R (powerImage4_gt_one N hN U hQU R hR)
        (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ*R^(-(delta/(N : ℝ))) := by
  refine ⟨div_pos hd (by exact_mod_cast (show 0 < N by omega)),?_⟩
  rintro R ⟨Q,hQ,rfl⟩
  rw [scaled_minima4 N hN A₂ A₃ L hL Q (hQU Q hQ),
    scaled_minima4 N hN A₂ A₃ L hL Q (hQU Q hQ),← scaled_gap_power4 N hN Q (hQU Q hQ)]
  exact hgap Q hQ

theorem powerImage4_unbounded (N : ℕ) (hN : 1 ≤ N) (U : Set ℝ) (hU : ¬ BddAbove U) :
    ¬ BddAbove (powerImage4 N U) := by
  apply not_bddAbove_iff.mpr
  intro B
  obtain ⟨Q,hQU,hQB⟩ := not_bddAbove_iff.mp hU (max B 1)
  have hQ1 : 1 < Q := (le_max_right _ _).trans_lt hQB
  refine ⟨Q^N,⟨Q,hQU,rfl⟩,?_⟩
  exact ((le_max_left _ _).trans_lt hQB).trans_le (le_self_pow₀ hQ1.le (by omega))

theorem source_scaled_selected_flag4 (N : ℕ) (hN : 1 ≤ N)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc : ∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧
      (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (delta : ℝ) (hd : 0 < delta) (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q)
    (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    selectedFlagFamily4 A₂ A₃ (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ (powerImage4 N U) := by
  obtain ⟨ha₀,ha₂,ha₃,hab⟩ := scaledWeights4_conditions N hN c₀ c₂ c₃ hc hb
  obtain ⟨hdn,hgapn⟩ := selected_gap_powerImage4 N hN A₂ A₃ L (sourceUnit42 L hL)
    c₀ c₂ c₃ delta hd U hQU j hgap
  exact source_selected_gap_fixed_flag4 A₂ A₃ L h₂ h₃ hL hAlg (delta/(N : ℝ)) hdn
    (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) ha₀ ha₂ ha₃ hab
    (powerImage4 N U) (powerImage4_unbounded N hN U hU) (powerImage4_gt_one N hN U hQU) j hgapn

def originalPreimage4 (N : ℕ) (U Wfixed : Set ℝ) : Set ℝ := {Q | Q ∈ U ∧ Q^N ∈ Wfixed}

theorem originalPreimage4_unbounded (N : ℕ) (U Wfixed : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q)
    (hW : ¬ BddAbove Wfixed) (hWU : Wfixed ⊆ powerImage4 N U) :
    ¬ BddAbove (originalPreimage4 N U Wfixed) := by
  rintro ⟨B,hB⟩
  obtain ⟨R,hRW,hR⟩ := not_bddAbove_iff.mp hW ((max B 1)^N)
  obtain ⟨Q,hQU',rfl⟩ := hWU hRW
  have hQB : Q ≤ B := hB (show Q ∈ originalPreimage4 N U Wfixed from ⟨hQU',hRW⟩)
  have hp : Q^N ≤ (max B 1)^N :=
    pow_le_pow_left₀ (lt_trans zero_lt_one (hQU Q hQU')).le (hQB.trans (le_max_left _ _)) N
  exact (not_lt_of_ge hp) hR


end
end CompoundFeasibility.BoundedWeightsLiteral188

set_option pp.all true

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaledWeights4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.exists_weight_bound4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaledWeights4_conditions

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.power_gt_one4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_power4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_body4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_coordinates4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_threshold4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_ceiling4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_group4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_minima4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.scaled_gap_power4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.powerImage4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.powerImage4_gt_one

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.selected_gap_powerImage4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.powerImage4_unbounded

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.source_scaled_selected_flag4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.originalPreimage4

#print axioms CompoundFeasibility.BoundedWeightsLiteral188.originalPreimage4_unbounded
