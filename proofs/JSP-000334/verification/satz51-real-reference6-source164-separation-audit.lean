import SubspaceBridge.SchlickeweiRealCompletion6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalPlaneRecovery42

theorem flag_last_eq_firstFive42 (v : Fin 6 → Fin 6 → ℝ) :
    minimaFlag6 v 5 = firstFiveSpan42 v := rfl

theorem separated_frame_span42 (v w : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j)))
    (hw : LinearIndependent ℝ (fun j => integerReal (w j)))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (a b : ℝ)
    (hsep : ∀ j : Fin 5, integerReal (w j.castSucc) ∉
      minimaFlag6 (fun i => integerReal (v i)) 5 →
      b ≤ coordinateGauge6 e (integerReal (w j.castSucc)))
    (hsmall : ∀ j : Fin 5, coordinateGauge6 e (integerReal (w j.castSucc)) ≤ a)
    (hab : a < b) :
    firstFiveSpan42 (fun j i => (w j i : ℚ)) =
      firstFiveSpan42 (fun j i => (v j i : ℚ)) := by
  have hm (j : Fin 5) : integerReal (w j.castSucc) ∈
      firstFiveSpan42 (fun i => integerReal (v i)) := by
    by_contra hn
    exact (not_le_of_gt ((hsmall j).trans_lt hab)) (hsep j hn)
  have he : firstFiveSpan42 (fun j => integerReal (w j)) =
      firstFiveSpan42 (fun j => integerReal (v j)) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact hm j
    · rw [firstFiveSpan42_finrank _ hw,firstFiveSpan42_finrank _ hv]
  exact integer_firstFive_span_eq42 w v hw hv he

#check flag_last_eq_firstFive42
#print flag_last_eq_firstFive42
#print axioms flag_last_eq_firstFive42
#check separated_frame_span42
#print separated_frame_span42
#print axioms separated_frame_span42
end CompoundFeasibility.OriginalPlaneRecovery42
