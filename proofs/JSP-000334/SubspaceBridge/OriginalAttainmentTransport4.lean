import SubspaceBridge.OriginalAttainmentFlag4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalAttainmentTransport4
open OriginalAttainmentFlag4 BoundedWeights4 OriginalFlagAssembly4 Exterior3 OriginalLastDual4

theorem source_scaled_selected_attaining_flag4 (N : ℕ) (hN : 1 ≤ N)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc : ∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧
      (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (delta : ℝ) (hd : 0 < delta) (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q)
    (j : Fin 3)
    (hgap : ∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ j.succ*Q^(-delta)) :
    attainingFlagFamily4 A₂ A₃ L (sourceUnit42 L hL)
      (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃)
      j.succ (powerImage4 N U) (powerImage4_gt_one N hN U hQU) := by
  obtain ⟨ha₀,ha₂,ha₃,hab⟩ := scaledWeights4_conditions N hN c₀ c₂ c₃ hc hb
  obtain ⟨hdn,hgapn⟩ := selected_gap_powerImage4 N hN A₂ A₃ L (sourceUnit42 L hL)
    c₀ c₂ c₃ delta hd U hQU j hgap
  exact source_selected_gap_attaining_flag4 A₂ A₃ L h₂ h₃ hL hAlg (delta/(N : ℝ)) hdn
    (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) ha₀ ha₂ ha₃ hab
    (powerImage4 N U) (powerImage4_unbounded N hN U hU) (powerImage4_gt_one N hN U hQU) j hgapn

theorem transportedFrame4_attaining (N : ℕ) (hN : 1 ≤ N)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (U Wfixed : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q)
    (hWR : ∀ R ∈ Wfixed, 1 < R)
    (v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃))
    (hv : ∀ r : Wfixed, ambientFrame4 A₂ A₃ L hL r.val (hWR r.val r.property)
      (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) :
    ∀ q : originalPreimage4 N U Wfixed, ambientFrame4 A₂ A₃ L hL q.val (hQU q.val q.property.1)
      c₀ c₂ c₃ (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q) := by
  intro q
  let r : Wfixed := ⟨q.val^N,q.property.2⟩
  have hvalues : (fun i => integerReal
      (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q i : Fin 4 → ℤ)) =
      (fun i => integerReal (v r i : Fin 4 → ℤ)) := by
    funext i
    exact congrArg integerReal (transportedFrame4_values N hN A₂ A₃ c₂ c₃ U Wfixed v q i)
  have hnorm := exactNormalization4_proved N hN A₂ A₃ L hL c₀ c₂ c₃ q.val (hQU q.val q.property.1)
  constructor
  · rw [hvalues]
    exact (hv r).1
  · intro i
    change coordinateGauge4 (originalCoordinates4 L hL q.val (hQU q.val q.property.1) c₀)
      ((fun j => integerReal (transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v q j : Fin 4 → ℤ)) i) = _
    rw [hvalues]
    have hatt := (hv r).2 i
    change coordinateGauge4 (originalCoordinates4 L hL (q.val^N)
      (power_gt_one4 N hN q.val (hQU q.val q.property.1)) (scaledWeights4 N c₀))
      (integerReal (v r i : Fin 4 → ℤ)) =
      sourceMinima4 A₂ A₃ L hL (q.val^N) (power_gt_one4 N hN q.val (hQU q.val q.property.1))
        (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) i at hatt
    rw [hnorm.2.1,hnorm.2.2.2.2.2 i] at hatt
    exact hatt


theorem source_bounded_weights_attaining_flag4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
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
              (∀ r : Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) r.val
                (hWR r.val (hWsub r.property)) (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) ∧
              originalPreimage4 N U Wfixed ⊆ U ∧ ¬ BddAbove (originalPreimage4 N U Wfixed) ∧
              ∃ u : (q : originalPreimage4 N U Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                (∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ))) ∧
                ∀ q : originalPreimage4 N U Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val q.property.1)
                  c₀ c₂ c₃ (u q) := by
  obtain ⟨N,hN,hc⟩ := exists_weight_bound4 c₀ c₂ c₃ hc₂ hc₃
  obtain ⟨ha₀,ha₂,ha₃,hab⟩ := scaledWeights4_conditions N hN c₀ c₂ c₃ hc hb
  obtain ⟨hdn,hgapn⟩ := selected_gap_powerImage4 N hN A₂ A₃ L (sourceUnit42 L hL)
    c₀ c₂ c₃ delta hd U hQU j hgap
  obtain ⟨Wfixed,hWsub,hW,P,hPdim,v,hv⟩ := source_scaled_selected_attaining_flag4 N hN A₂ A₃ L
    h₂ h₃ hL hAlg c₀ c₂ c₃ hc hb delta hd U hU hQU j hgap
  have hproper : P ≠ ⊤ := by
    intro htop
    have hfour : Module.finrank ℚ P = 4 := by
      rw [htop,finrank_top]
      simp
    change Module.finrank ℚ P = j.val+1 at hPdim
    omega
  have hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3 := by
    change Module.finrank ℚ P = j.val+1 at hPdim
    constructor <;> omega
  have hvFlag := fun r => (hv r).1
  have hvAtt := fun r => (hv r).2
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,exactNormalization4_proved N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃,
    hdn,(fun Q hQ => scaled_gap_power4 N hN Q (hQU Q hQ) delta),powerImage4_unbounded N hN U hU,
    powerImage4_gt_one N hN U hQU,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hvFlag,hvAtt,
    (fun _ h => h.1),originalPreimage4_unbounded N U Wfixed hQU hW hWsub,?_⟩
  refine ⟨transportedFrame4 N hN A₂ A₃ c₂ c₃ U Wfixed v,
    transportedFrame4_values N hN A₂ A₃ c₂ c₃ U Wfixed v,
    transportedFrame4_flag N hN A₂ A₃ c₂ c₃ U Wfixed j.succ P v hvFlag,?_⟩
  exact transportedFrame4_attaining N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ U Wfixed hQU
      (fun R hR => powerImage4_gt_one N hN U hQU R (hWsub hR)) v hvAtt


end CompoundFeasibility.OriginalAttainmentTransport4
