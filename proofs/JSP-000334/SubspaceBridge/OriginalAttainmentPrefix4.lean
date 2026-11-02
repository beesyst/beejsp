import SubspaceBridge.OriginalAttainmentFlag4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalAttainmentFlag4

theorem source_same_frame_restricted_prefix4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (d : Fin 4) (hPdim : Module.finrank ℚ P = d.val)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : ambientFrame4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ u)
    (hflag : P = OriginalFlagAssembly4.originalFirstFlag4 d (fun i => (u i : Fin 4 → ℤ))) :
    ∀ k, RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (RestrictedGeometry4.ambientPrefixIndex4 P hP k) := by
  let emb := RestrictedGeometry4.ambientPrefixIndex4 P hP
  let v : Fin (Module.finrank ℚ P) → originalSourceGroup4 A₂ A₃ Q c₂ c₃ := fun i => u (emb i)
  have hv : LinearIndependent ℝ (fun i => integerReal (v i : Fin 4 → ℤ)) :=
    hu.1.comp emb (Fin.castLE_injective _)
  have hmem (i : Fin (Module.finrank ℚ P)) : integerReal (v i : Fin 4 → ℤ) ∈
      RestrictedGeometry4.rationalRealSpan4 P := by
    have hr : (fun j => ((u (emb i) : Fin 4 → ℤ) j : ℚ)) ∈ P := by
      rw [hflag]
      apply Submodule.subset_span
      refine ⟨⟨i.val,by omega⟩,?_⟩
      rfl
    apply Submodule.subset_span
    refine ⟨(fun j => ((u (emb i) : Fin 4 → ℤ) j : ℚ)),hr,?_⟩
    ext j
    simp [v,integerReal]
  exact RestrictedGeometry4.source_restricted_prefix_eq4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ v hv hmem
    (fun i => hu.2 (emb i))

end CompoundFeasibility.OriginalAttainmentFlag4
