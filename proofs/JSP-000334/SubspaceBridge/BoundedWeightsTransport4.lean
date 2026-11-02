import SubspaceBridge.BoundedWeights4
import SubspaceBridge.IntegerGroupTransport4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.BoundedWeights4
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4
noncomputable section

def transportedElement4 (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (c₂ c₃ : Fin 4 → ℝ) (Q : ℝ)
    (x : originalSourceGroup4 A₂ A₃ (Q^N) (scaledWeights4 N c₂) (scaledWeights4 N c₃)) :
    originalSourceGroup4 A₂ A₃ Q c₂ c₃ :=
  castGroupMember4 _ _ (scaled_group4 N hN A₂ A₃ Q c₂ c₃) x

def transportedFrame4 (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (c₂ c₃ : Fin 4 → ℝ) (U Wfixed : Set ℝ)
    (v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃)) :
    (q : originalPreimage4 N U Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃ :=
  fun q i => transportedElement4 N hN A₂ A₃ c₂ c₃ q.val (v ⟨q.val^N,q.property.2⟩ i)

theorem transportedElement4_values (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (c₂ c₃ : Fin 4 → ℝ) (Q : ℝ)
    (x : originalSourceGroup4 A₂ A₃ (Q^N) (scaledWeights4 N c₂) (scaledWeights4 N c₃)) :
    (transportedElement4 N hN A₂ A₃ c₂ c₃ Q x : Fin 4 → ℤ) = (x : Fin 4 → ℤ) := by
  unfold transportedElement4
  exact castGroupMember4_values _ _ _ x

theorem transportedFrame4_values (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (c₂ c₃ : Fin 4 → ℝ) (U Wfixed : Set ℝ)
    (v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃))
    (q : originalPreimage4 N U Wfixed) (i : Fin 4) :
    (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q i : Fin 4 → ℤ) =
      (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ) := by
  unfold transportedFrame4
  exact transportedElement4_values N hN A₂ A₃ c₂ c₃ q.val (v ⟨q.val^N,q.property.2⟩ i)

theorem transportedFrame4_flag (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (c₂ c₃ : Fin 4 → ℝ) (U Wfixed : Set ℝ) (d : Fin 4) (P : Submodule ℚ (Fin 4 → ℚ))
    (v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃))
    (hv : ∀ r : Wfixed, P = originalFirstFlag4 d (fun i => (v r i : Fin 4 → ℤ))) :
    ∀ q : originalPreimage4 N U Wfixed, P = originalFirstFlag4 d
      (fun i => (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q i : Fin 4 → ℤ)) := by
  intro q
  exact (hv ⟨q.val^N,q.property.2⟩).trans (congrArg (originalFirstFlag4 d)
    (funext fun i => (transportedFrame4_values N hN A₂ A₃ c₂ c₃ U Wfixed v q i).symm))

def exactNormalization4 (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c₀ c₂ c₃ : Fin 4 → ℝ) : Prop :=
  ∀ (Q : ℝ) (hQ : 1 < Q),
    originalBody4 L (Q^N) (scaledWeights4 N c₀) = originalBody4 L Q c₀ ∧
    originalCoordinates4 L hL (Q^N) (power_gt_one4 N hN Q hQ) (scaledWeights4 N c₀) =
      originalCoordinates4 L hL Q hQ c₀ ∧
    (∀ i, JSP000334.qThreshold 2 (Q^N) (scaledWeights4 N c₂ i) = JSP000334.qThreshold 2 Q (c₂ i) ∧
      Nat.ceil (JSP000334.qThreshold 2 (Q^N) (scaledWeights4 N c₂ i)) = Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) ∧
    (∀ i, JSP000334.qThreshold 3 (Q^N) (scaledWeights4 N c₃ i) = JSP000334.qThreshold 3 Q (c₃ i) ∧
      Nat.ceil (JSP000334.qThreshold 3 (Q^N) (scaledWeights4 N c₃ i)) = Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) ∧
    originalSourceGroup4 A₂ A₃ (Q^N) (scaledWeights4 N c₂) (scaledWeights4 N c₃) =
      originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
    ∀ k, sourceMinima4 A₂ A₃ L hL (Q^N) (power_gt_one4 N hN Q hQ)
      (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) k =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ k

theorem exactNormalization4_proved (N : ℕ) (hN : 1 ≤ N) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    exactNormalization4 N hN A₂ A₃ L hL c₀ c₂ c₃ := by
  intro Q hQ
  exact ⟨scaled_body4 N hN L Q hQ c₀,scaled_coordinates4 N hN L hL Q hQ c₀,
    fun i => ⟨scaled_threshold4 N hN 2 Q (c₂ i),scaled_ceiling4 N hN 2 Q (c₂ i)⟩,
    fun i => ⟨scaled_threshold4 N hN 3 Q (c₃ i),scaled_ceiling4 N hN 3 Q (c₃ i)⟩,
    scaled_group4 N hN A₂ A₃ Q c₂ c₃,scaled_minima4 N hN A₂ A₃ L hL Q hQ c₀ c₂ c₃⟩


theorem source_bounded_weights_fixed_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (delta : ℝ) (hd : 0 < delta) (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q)
    (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    ∃ (N : ℕ) (hN : 1 ≤ N),
      (∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧ (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) ∧
      (∀ i, |scaledWeights4 N c₀ i| ≤ 1) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₂ i ∧ scaledWeights4 N c₂ i ≤ 0) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₃ i ∧ scaledWeights4 N c₃ i ≤ 0) ∧
      (∑ i, (scaledWeights4 N c₀ i+scaledWeights4 N c₂ i+scaledWeights4 N c₃ i) = 0) ∧
      exactNormalization4 N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ ∧
      0 < delta/(N : ℝ) ∧
      (∀ Q ∈ U, Q^(-delta) = (Q^N)^(-(delta/(N : ℝ)))) ∧
      ¬ BddAbove (powerImage4 N U) ∧
      ∃ hWR : ∀ R ∈ powerImage4 N U, 1 < R,
        (∀ (R : ℝ) (hR : R ∈ powerImage4 N U),
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ*R^(-(delta/(N : ℝ)))) ∧
        ∃ (Wfixed : Set ℝ) (hWsub : Wfixed ⊆ powerImage4 N U), ¬ BddAbove Wfixed ∧
          ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = j.val+1 ∧
            (1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3) ∧ P ≠ ⊤ ∧
            ∃ v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃),
              (∀ r : Wfixed, P = originalFirstFlag4 j.succ (fun i => (v r i : Fin 4 → ℤ))) ∧
              originalPreimage4 N U Wfixed ⊆ U ∧ ¬ BddAbove (originalPreimage4 N U Wfixed) ∧
              ∃ u : (q : originalPreimage4 N U Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                ∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ)) := by
  obtain ⟨N,hN,hc⟩ := exists_weight_bound4 c₀ c₂ c₃ hc₂ hc₃
  obtain ⟨ha₀,ha₂,ha₃,hab⟩ := scaledWeights4_conditions N hN c₀ c₂ c₃ hc hb
  obtain ⟨hdn,hgapn⟩ := selected_gap_powerImage4 N hN A₂ A₃ L (sourceUnit42 L hL)
    c₀ c₂ c₃ delta hd U hQU j hgap
  obtain ⟨Wfixed,hWsub,hW,P,hPdim,v,hv⟩ := source_scaled_selected_flag4 N hN A₂ A₃ L
    h₂ h₃ hL hAlg c₀ c₂ c₃ hc hb delta hd U hU hQU j hgap
  have hproper : P ≠ ⊤ := by
    intro htop
    have hfour : Module.finrank ℚ P = 4 := by
      rw [htop,finrank_top]
      simp
    change Module.finrank ℚ P = j.val+1 at hPdim
    omega
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,exactNormalization4_proved N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃,
    hdn,(fun Q hQ => scaled_gap_power4 N hN Q (hQU Q hQ) delta),powerImage4_unbounded N hN U hU,
    powerImage4_gt_one N hN U hQU,hgapn,Wfixed,hWsub,hW,P,hPdim,?_,hproper,v,hv,
    (fun _ h => h.1),originalPreimage4_unbounded N U Wfixed hQU hW hWsub,
    transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v,
    transportedFrame4_values N hN A₂ A₃ c₂ c₃ U Wfixed v,
    transportedFrame4_flag N hN A₂ A₃ c₂ c₃ U Wfixed j.succ P v hv⟩
  change Module.finrank ℚ P = j.val+1 at hPdim
  constructor <;> omega

end
end CompoundFeasibility.BoundedWeights4
