import SubspaceBridge.SourceOriginalBounds215
import SubspaceBridge.SourceOriginalFinite215
import SubspaceBridge.SourceOriginalRationalVanishing10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalBounds215
open SourceOriginalVariable10 SourceOriginalSatz212 OriginalDual10 SourceOriginalDual10 SourceOriginalNorm214
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_indexed_bounds215 (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    0 < originalIndex212 D ∧ 0 < originalCovolume212 D ∧
      originalIndex212 D * (originalLattice212 D).index = ((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det).natAbs ∧
      |((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det : ℝ)| = (originalIndex212 D : ℝ)*originalCovolume212 D ∧
      originalCovolume212 D = ((originalLattice212 D).index : ℝ) ∧
      ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℝ) =
        (originalIndex212 D : ℝ)*originalCovolume212 D ∧
      ∀ i : Fin 10,
      ‖∑ k, (((originalIndex212 D : ℝ)*originalCovolume212 D)*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℝ))*L⁻¹.transpose i k‖ ≤
        362880 * (D.A i)⁻¹ * originalCovolume212 D * Q^(-9*delta) ∧
      ‖∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))*
        (A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
        ∏ k : Fin 9, (2 : ℝ)^(D.f2 (i.succAbove k)) ∧
      ‖∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[3])*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[3]))*
        (A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
        ∏ k : Fin 9, (3 : ℝ)^(D.f3 (i.succAbove k)) := by
  obtain ⟨hJ,hd,hN,hdet,hidx,hscale⟩ := original_index_normalization212 D
  refine ⟨hJ,hd,hN,hdet,hidx,hscale,?_⟩
  intro i
  exact ⟨original_real_bound215 h2 h3 hLd D i,
    original_p2_sum_bound215 h2 D i,original_p3_sum_bound215 h3 D i⟩

theorem original_satz41_fin10_two_places215
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (S0 : Finset SourceSelectedSet10.MixedIndex10) :
    ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ (Q : ℝ) (hQ : 1 < Q), Q0 < Q →
      ∀ D : OriginalData10 A2 A3 L hL Q hQ delta S0,
      originalSourceGroup10 A2 A3 Q (fun i => normalizedFinite10 2 Q (D.f2 i))
        (fun i => normalizedFinite10 3 Q (D.f3 i)) = originalLattice212 D ∧
      (0 < originalIndex212 D ∧ 0 < originalCovolume212 D ∧
      originalIndex212 D * (originalLattice212 D).index = ((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det).natAbs ∧
      |((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det : ℝ)| = (originalIndex212 D : ℝ)*originalCovolume212 D ∧
      originalCovolume212 D = ((originalLattice212 D).index : ℝ) ∧
      ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℝ) =
        (originalIndex212 D : ℝ)*originalCovolume212 D ∧
      ∀ i : Fin 10,
      ‖∑ k, (((originalIndex212 D : ℝ)*originalCovolume212 D)*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℝ))*L⁻¹.transpose i k‖ ≤
        362880 * (D.A i)⁻¹ * originalCovolume212 D * Q^(-9*delta) ∧
      ‖∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[2])*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[2]))*
        (A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose i k‖ ≤
        ∏ k : Fin 9, (2 : ℝ)^(D.f2 (i.succAbove k)) ∧
      ‖∑ k, (((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℚ_[3])*
        (lastDual10 (fun j i => (D.u j i : ℚ))
          (integer_frame_rational_independent10 D.u D.independent) k : ℚ_[3]))*
        (A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose i k‖ ≤
        ∏ k : Fin 9, (3 : ℝ)^(D.f3 (i.succAbove k))) ∧
      ∀ s : SourceSelectedSet10.MixedIndex10, s ∈ S0 → dataRationalDualProduct10 D s = 0 := by
  obtain ⟨Q0,hzero⟩ := SourceOriginalVanishing10.original_rational_selected_eventually_zero10
    A2 A3 L h2 h3 hLd hL hAlg delta hd S0
  refine ⟨max 1 Q0,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro Q hQ hQ0 D
  exact ⟨original_lattice_eq212 D,original_indexed_bounds215 h2 h3 hLd D,
    hzero Q hQ ((le_max_right _ _).trans_lt hQ0) D⟩

end CompoundFeasibility.SourceOriginalBounds215
