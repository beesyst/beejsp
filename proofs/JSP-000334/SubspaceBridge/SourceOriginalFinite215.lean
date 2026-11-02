import SubspaceBridge.SourceOriginalNorms214
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalBounds215
open SourceOriginalVariable10 SourceOriginalSatz212 OriginalDual10 SourceOriginalDual10 SourceOriginalNorm214
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_p2_bound215 (h2 : A2.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k =>
      ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))) i‖ ≤
      ∏ k : Fin 9, (2 : ℝ)^(D.f2 (i.succAbove k)) := by
  rw [← original_p2_norm214 D i]
  exact SourceOriginalBudget10.finite_integer_cofactor10 2 (by decide) A2 h2 Q hQ
    D.f2 D.nonpos2 D.u D.member2 i

theorem original_p2_sum_bound215 (h2 : A2.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
      (lastDual10 (fun j i => (D.u j i : ℚ))
        (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))*
      (A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
      ∏ k : Fin 9, (2 : ℝ)^(D.f2 (i.succAbove k)) := by
  have he : (∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
      (lastDual10 (fun j i => (D.u j i : ℚ))
        (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))*
      (A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k) =
      ((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))) i := by
    simp only [Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [he]
  exact original_p2_bound215 h2 D i

theorem original_p3_bound215 (h3 : A3.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k =>
      ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[3])*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[3]))) i‖ ≤
      ∏ k : Fin 9, (3 : ℝ)^(D.f3 (i.succAbove k)) := by
  rw [← original_p3_norm214 D i]
  exact SourceOriginalBudget10.finite_integer_cofactor10 3 (by decide) A3 h3 Q hQ
    D.f3 D.nonpos3 D.u D.member3 i

theorem original_p3_sum_bound215 (h3 : A3.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[3])*
      (lastDual10 (fun j i => (D.u j i : ℚ))
        (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[3]))*
      (A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
      ∏ k : Fin 9, (3 : ℝ)^(D.f3 (i.succAbove k)) := by
  have he : (∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[3])*
      (lastDual10 (fun j i => (D.u j i : ℚ))
        (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[3]))*
      (A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k) =
      ((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k =>
        ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[3])*
          (lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[3]))) i := by
    simp only [Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [he]
  exact original_p3_bound215 h3 D i

end CompoundFeasibility.SourceOriginalBounds215
