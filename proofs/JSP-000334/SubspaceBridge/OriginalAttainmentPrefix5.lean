import SubspaceBridge.RestrictedGeometry5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry5

theorem source_same_frame_restricted_prefix5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (j : Fin 4) (hPdim : Module.finrank ℚ P = j.val+1)
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)))
    (ha : ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
      (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i)
    (hflag : P = OriginalFlagAssembly5.originalFirstFlag5 j (fun i => (u i : Fin 5 → ℤ))) :
    (∀ i : Fin (Module.finrank ℚ P), integerReal (u (ambientPrefixIndex5 P hP i) : Fin 5 → ℤ) ∈ rationalRealSpan5 P) ∧
    ∀ k, restrictedMinima5 P A2 A3 L hL Q hQ c0 c2 c3 k =
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 (ambientPrefixIndex5 P hP k) := by
  let emb := ambientPrefixIndex5 P hP
  let v : Fin (Module.finrank ℚ P) → originalSourceGroup5 A2 A3 Q c2 c3 := fun i => u (emb i)
  have hv : LinearIndependent ℝ (fun i => integerReal (v i : Fin 5 → ℤ)) :=
    hu.comp emb (Fin.castLE_injective _)
  have hmem (i : Fin (Module.finrank ℚ P)) : integerReal (v i : Fin 5 → ℤ) ∈ rationalRealSpan5 P := by
    have hr : (fun k => ((u (emb i) : Fin 5 → ℤ) k : ℚ)) ∈ P := by
      rw [hflag]
      apply Submodule.subset_span
      refine ⟨⟨i.val,by omega⟩,?_⟩
      rfl
    apply Submodule.subset_span
    refine ⟨(fun k => ((u (emb i) : Fin 5 → ℤ) k : ℚ)),hr,?_⟩
    ext k
    simp [v,integerReal]
  exact ⟨hmem,source_restricted_prefix_eq5 P hP A2 A3 L hL Q hQ c0 c2 c3 v hv hmem (fun i => ha (emb i))⟩

end CompoundFeasibility.RestrictedGeometry5
