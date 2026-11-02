import SubspaceBridge.SourceShortWedges241
import SubspaceBridge.SchmidtNormal10
import SubspaceBridge.OriginalDual10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open SchmidtNormal10 OriginalDual10

variable (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
  (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)

theorem attaining_short_span241 (w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hw : LinearIndependent ℝ (fun i => integerReal (w i : Fin 10 → ℤ)))
    (hatt : ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (w i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i)
    (hgap : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9)
    (z : Fin 10 → ℤ) (hz : z ∈ originalSourceGroup10 A2 A3 Q c2 c3)
    (hzg : coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) (integerReal z) <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9) :
    integerReal z ∈ Submodule.span ℝ (Set.range (fun j : Fin 9 => integerReal (w j.castSucc : Fin 10 → ℤ))) := by
  apply sourceMinima10_short_span241 A2 A3 L hL Q hQ c0 c2 c3 _
    (hw.comp (fun j : Fin 9 => j.castSucc) (Fin.castSucc_injective _))
  · intro j
    exact ⟨(w j.castSucc : Fin 10 → ℤ),(w j.castSucc).property,rfl⟩
  · intro j
    change coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (w j.castSucc : Fin 10 → ℤ)) < _
    rw [hatt]
    exact ((sourceMinima10_pos_mono A2 A3 L hL Q hQ c0 c2 c3).2
      (show j.castSucc ≤ (8 : Fin 10) by change j.val ≤ 8; omega)).trans_lt hgap
  · exact ⟨z,hz,rfl⟩
  · exact hzg

theorem first_nine_span_eq241
    (w : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hw : LinearIndependent ℝ (fun i => integerReal (w i : Fin 10 → ℤ)))
    (hatt : ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (w i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 i)
    (hgap : sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9)
    (v : Fin 9 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j : Fin 10 → ℤ)))
    (hvg : ∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (v j : Fin 10 → ℤ)) < sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 9) :
    Submodule.span ℝ (Set.range (fun j => integerReal (v j : Fin 10 → ℤ))) =
      Submodule.span ℝ (Set.range (fun j : Fin 9 => integerReal (w j.castSucc : Fin 10 → ℤ))) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact attaining_short_span241 A2 A3 L hL Q hQ c0 c2 c3 w hw hatt hgap _ (v j).property (hvg j)
  · exact (finrank_span_eq_card hv).trans (finrank_span_eq_card
      (hw.comp (fun j : Fin 9 => j.castSucc) (Fin.castSucc_injective _))).symm

end CompoundFeasibility.SourceFlag241
