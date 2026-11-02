import SubspaceBridge.WeightedDiagonalReduction4
namespace JSP000334
open scoped BigOperators Matrix

def weightedDiagonalMap4 (t : Fin 4 → ℤ) : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) :=
  Matrix.toLin' (weightedIntegerDiagonal4 t)

theorem weighted_diagonal_comap_proper4 (t : Fin 4 → ℤ) (ht : ∀ i,t i≠0)
    (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P≠⊤) :
    P.comap (weightedDiagonalMap4 t)≠⊤ := by
  have hsurj : Function.Surjective (weightedDiagonalMap4 t) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (weighted_diagonal_invertible4 t ht)
  intro he
  apply hP
  apply top_unique
  intro x _
  obtain ⟨v,rfl⟩ := hsurj x
  have hv : v∈P.comap (weightedDiagonalMap4 t) := by rw [he];trivial
  exact hv

theorem weighted_diagonal_original_mem4 (t z y : Fin 4 → ℤ)
    (g : ℕ) (u : Fin 4 → fixedSUnitGroup) (s : fixedSUnitGroup)
    (hz : ∀ i,(z i : ℚ)=((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ))
    (he : ∀ i,t i*z i=(g : ℤ)*y i)
    (P : Submodule ℚ (Fin 4 → ℚ)) (hyP : (fun i => (y i : ℚ))∈P) :
    (fun i => ((u i : ℚˣ) : ℚ))∈P.comap (weightedDiagonalMap4 t) := by
  have hs : ((s : ℚˣ) : ℚ)≠0 := Units.ne_zero _
  have hm := P.smul_mem ((g : ℚ)/((s : ℚˣ) : ℚ)) hyP
  have heq : weightedDiagonalMap4 t (fun i => ((u i : ℚˣ) : ℚ))=
      ((g : ℚ)/((s : ℚˣ) : ℚ)) • (fun i => (y i : ℚ)) := by
    ext i
    change (weightedIntegerDiagonal4 t *ᵥ (fun i => ((u i : ℚˣ) : ℚ))) i=_
    simp only [weightedIntegerDiagonal4,Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]
    have hc := congrArg ((↑) : ℤ → ℚ) (he i)
    push_cast at hc
    rw [hz i] at hc
    apply (mul_left_cancel₀ hs)
    calc
      _=(t i : ℚ)*(((s : ℚˣ) : ℚ)*((u i : ℚˣ) : ℚ)) := by ring
      _=(g : ℚ)*(y i : ℚ) := hc
      _=_ := by field_simp
  change weightedDiagonalMap4 t (fun i => ((u i : ℚˣ) : ℚ))∈P
  rwa [heq]

end JSP000334
