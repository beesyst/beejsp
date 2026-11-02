import SubspaceBridge.RestrictedSource4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedRationalMembership4
open RestrictedGeometry4
noncomputable section

theorem rationalRealSpan4_mem_rational (P : Submodule ℚ (Fin 4 → ℚ)) (x : Fin 4 → ℚ) :
    (fun i => (x i : ℝ)) ∈ rationalRealSpan4 P ↔ x ∈ P := by
  constructor
  · intro hx
    obtain ⟨g,hg⟩ := P.subtype.exists_leftInverse_of_injective P.ker_subtype
    let f : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) := P.subtype.comp g
    let M : Matrix (Fin 4) (Fin 4) ℚ := LinearMap.toMatrix' f
    let fR := Matrix.toLin' (M.map (algebraMap ℚ ℝ))
    have hfixQ : ∀ y ∈ P, M *ᵥ y = y := by
      intro y hy
      have h := congrArg (fun z : P => (z : Fin 4 → ℚ)) (LinearMap.congr_fun hg ⟨y,hy⟩)
      change (Matrix.toLin' (LinearMap.toMatrix' f)) y = y
      rw [Matrix.toLin'_toMatrix']
      exact h
    have hle : rationalRealSpan4 P ≤ LinearMap.ker (fR-LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨y,hy,rfl⟩
      change fR (fun i => (y i : ℝ)) - (fun i => (y i : ℝ)) = 0
      apply sub_eq_zero.mpr
      ext i
      have h := congrFun (hfixQ y hy) i
      change ∑ k, (M i k : ℝ)*(y k : ℝ) = (y i : ℝ)
      simp only [Matrix.mulVec,dotProduct] at h
      exact_mod_cast h
    have hfixR : fR (fun i => (x i : ℝ)) = (fun i => (x i : ℝ)) :=
      sub_eq_zero.mp (hle hx)
    have hfix : M *ᵥ x = x := by
      ext i
      have h := congrFun hfixR i
      change (∑ k, (M i k : ℝ)*(x k : ℝ)) = (x i : ℝ) at h
      simp only [Matrix.mulVec,dotProduct]
      exact_mod_cast h
    have hm : M *ᵥ x ∈ P := by
      change (Matrix.toLin' (LinearMap.toMatrix' f)) x ∈ P
      rw [Matrix.toLin'_toMatrix']
      exact (g x).property
    rwa [hfix] at hm
  · intro hx
    exact Submodule.subset_span ⟨x,hx,rfl⟩

end
end CompoundFeasibility.RestrictedRationalMembership4
