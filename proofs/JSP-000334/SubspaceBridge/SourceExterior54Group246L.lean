import SubspaceBridge.SourceExterior54Lattice246L
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

def fourWeights246 (c : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  ∑ r : Fin 4, c (i.succAbove r)

def normalizedWeights4246 (c : Fin 5 → ℝ) (i : Fin 5) : ℝ := fourWeights246 c i / 4

theorem four_ceiling246 (p : ℕ) (Q : ℝ) (c : Fin 5 → ℝ) (i : Fin 5) :
    Nat.ceil (JSP000334.qThreshold p Q (fourWeights246 c i)) ≤
      ∑ r : Fin 4, Nat.ceil (JSP000334.qThreshold p Q (c (i.succAbove r))) := by
  simp only [fourWeights246, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    qThreshold_add42]
  exact (Nat.ceil_add_le _ _).trans (Nat.add_le_add_left
    ((Nat.ceil_add_le _ _).trans (Nat.add_le_add_left (Nat.ceil_add_le _ _) _)) _)

theorem local_ceiling_inclusion4246 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c : Fin 5 → ℝ) :
    lattice5 p (compound4246 A)
      (fun i => ∑ r : Fin 4, Nat.ceil (JSP000334.qThreshold p Q (c (i.succAbove r)))) ≤
    lattice5 p (compound4246 A)
      (fun i => Nat.ceil (JSP000334.qThreshold p Q (fourWeights246 c i))) := by
  intro z hz
  simp only [lattice5, AddSubgroup.mem_iInf, AddSubgroup.mem_comap] at hz ⊢
  intro i
  exact normBall_antitone42 p _ _ (four_ceiling246 p Q c i) (hz i)

theorem wedge_direct4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c2 c3 : Fin 5 → ℝ)
    (x : Fin 4 → originalSourceGroup5 A2 A3 Q c2 c3) :
    wedge4246 (fun j => (x j : Fin 5 → ℤ)) ∈
      originalSourceGroup5 (compound4246 A2) (compound4246 A3) Q
        (fourWeights246 c2) (fourWeights246 c3) := by
  let e2 : Fin 5 → ℕ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i))
  let e3 : Fin 5 → ℕ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))
  have hx2 : ∀ j, (x j : Fin 5 → ℤ) ∈ lattice5 2 A2 e2 := fun j => (x j).property.1
  have hx3 : ∀ j, (x j : Fin 5 → ℤ) ∈ lattice5 3 A3 e3 := fun j => (x j).property.2
  have h2 := local_wedge4246 2 A2 e2 (fun j => (x j : Fin 5 → ℤ)) hx2
  have h3 := local_wedge4246 3 A3 e3 (fun j => (x j : Fin 5 → ℤ)) hx3
  exact ⟨local_ceiling_inclusion4246 2 A2 Q c2 h2,
    local_ceiling_inclusion4246 3 A3 Q c3 h3⟩

theorem powered_threshold4246 (p : ℕ) (Q : ℝ) (c : Fin 5 → ℝ) (i : Fin 5) :
    JSP000334.qThreshold p (Q^4) (normalizedWeights4246 c i) =
      JSP000334.qThreshold p Q (fourWeights246 c i) := by
  unfold normalizedWeights4246 JSP000334.qThreshold
  rw [Real.log_pow]
  ring

theorem powered_group4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c2 c3 : Fin 5 → ℝ) :
    originalSourceGroup5 (compound4246 A2) (compound4246 A3) (Q^4)
      (normalizedWeights4246 c2) (normalizedWeights4246 c3) =
    originalSourceGroup5 (compound4246 A2) (compound4246 A3) Q
      (fourWeights246 c2) (fourWeights246 c3) := by
  unfold originalSourceGroup5
  simp_rw [powered_threshold4246]

theorem wedge_source_group4246 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c2 c3 : Fin 5 → ℝ)
    (x : Fin 4 → originalSourceGroup5 A2 A3 Q c2 c3) :
    wedge4246 (fun j => (x j : Fin 5 → ℤ)) ∈
      originalSourceGroup5 (compound4246 A2) (compound4246 A3) (Q^4)
        (normalizedWeights4246 c2) (normalizedWeights4246 c3) := by
  rw [powered_group4246]
  exact wedge_direct4246 A2 A3 Q c2 c3 x

end CompoundFeasibility.Exterior54_246
