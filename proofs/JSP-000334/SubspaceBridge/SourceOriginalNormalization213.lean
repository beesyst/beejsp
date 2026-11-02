import SubspaceBridge.SourceOriginalMatrix213
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalSatz212
open SourceOriginalVariable10 SourceRelativeIndex6

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_index_pos212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    0 < originalIndex212 D := by
  obtain ⟨c⟩ := sourceLattice10_has_basis A2 A3 (fun i => (-D.f2 i).toNat) (fun i => (-D.f3 i).toNat)
  exact frameRelativeIndex_pos (originalLattice212 D) c (originalFrame212 D)
    (original_frame_independent212 D)

theorem original_covolume_pos212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    0 < originalCovolume212 D := by
  letI : IsZLattice ℝ (integerRealImage (originalLattice212 D)) :=
    sourceLattice10_isZLattice A2 A3 (fun i => (-D.f2 i).toNat) (fun i => (-D.f3 i).toNat)
  exact ZLattice.covolume_pos (integerRealImage (originalLattice212 D)) MeasureTheory.volume

theorem original_index_det212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    originalIndex212 D * (originalLattice212 D).index =
      (Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det.natAbs := by
  obtain ⟨c⟩ := sourceLattice10_has_basis A2 A3 (fun i => (-D.f2 i).toNat) (fun i => (-D.f3 i).toNat)
  have hn := frameRelativeIndex_mul_index (originalLattice212 D) c (originalFrame212 D)
    (original_frame_independent212 D)
  rw [original_frame_matrix_eq212 D] at hn
  exact hn

theorem original_abs_det_covolume212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    |((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det : ℝ)| =
      (originalIndex212 D : ℝ)*originalCovolume212 D := by
  obtain ⟨c⟩ := sourceLattice10_has_basis A2 A3 (fun i => (-D.f2 i).toNat) (fun i => (-D.f3 i).toNat)
  letI : IsZLattice ℝ (integerRealImage (originalLattice212 D)) :=
    sourceLattice10_isZLattice A2 A3 (fun i => (-D.f2 i).toNat) (fun i => (-D.f3 i).toNat)
  have hr := frame_abs_det_covolume (originalLattice212 D) c (originalFrame212 D)
    (original_frame_independent212 D)
  rw [original_frame_matrix_eq212 D] at hr
  exact hr

theorem original_covolume_index212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    originalCovolume212 D = ((originalLattice212 D).index : ℝ) := by
  exact sourceLattice10_covolume_index A2 A3 (fun i => (-D.f2 i).toNat) (fun i => (-D.f3 i).toNat)

theorem original_integer_scale212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℝ) =
      (originalIndex212 D : ℝ)*originalCovolume212 D := by
  rw [original_covolume_index212 D,Nat.cast_mul]

theorem original_index_normalization212 (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    0 < originalIndex212 D ∧ 0 < originalCovolume212 D ∧
      originalIndex212 D * (originalLattice212 D).index = ((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det).natAbs ∧
      |((Matrix.of D.u : Matrix (Fin 10) (Fin 10) ℤ).det : ℝ)| = (originalIndex212 D : ℝ)*originalCovolume212 D ∧
      originalCovolume212 D = ((originalLattice212 D).index : ℝ) ∧
      ((originalIndex212 D * (originalLattice212 D).index : ℕ) : ℝ) =
        (originalIndex212 D : ℝ)*originalCovolume212 D := by
  exact ⟨original_index_pos212 D,original_covolume_pos212 D,original_index_det212 D,
    original_abs_det_covolume212 D,original_covolume_index212 D,original_integer_scale212 D⟩

end CompoundFeasibility.SourceOriginalSatz212
