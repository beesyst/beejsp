import SubspaceBridge.RestrictedBasis4
open scoped BigOperators
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry4
variable {P : Submodule ℚ (Fin 4 → ℚ)}
variable {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {Q : ℝ} {c₂ c₃ : Fin 4 → ℝ} {d : ℕ}

def restrictedIntegerPoint4
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (z : Fin d → ℤ) : rationalRealSpan4 P :=
  (c.equivFun.symm z : restrictedLattice4 P A₂ A₃ Q c₂ c₃)

theorem restrictedIntegerPoint4_mem
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)) (z : Fin d → ℤ) :
    restrictedIntegerPoint4 c z ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃ :=
  (c.equivFun.symm z).property

theorem restrictedIntegerPoint4_coord
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)) (z : Fin d → ℤ) (i : Fin d) :
    (c.ofZLatticeBasis ℝ _).repr (restrictedIntegerPoint4 c z) i = (z i : ℝ) := by
  rw [restrictedIntegerPoint4,Basis.ofZLatticeBasis_repr_apply]
  change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = (z i : ℝ)
  rw [LinearEquiv.apply_symm_apply]

theorem restrictedIntegerPoint4_outside
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P)
    (hadapt : ∀ k : Fin d, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
        rationalRealSpan4 P))) = intrinsicPrefix4 v k)
    (z : Fin d → ℤ) (k : Fin d) (hk : z k ≠ 0) :
    restrictedIntegerPoint4 c z ∉ intrinsicPrefix4 v k := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  have hle : intrinsicPrefix4 v k ≤ LinearMap.ker (b.coord k) := by
    rw [← hadapt k]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change b.repr ((c (Fin.castLE (by omega) j) : restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
      rationalRealSpan4 P) k = 0
    have hne : (Fin.castLE (by omega) j : Fin d) ≠ k := by
      intro h
      have heq := congrArg Fin.val h
      change j.val = k.val at heq
      omega
    simp [b,Basis.ofZLatticeBasis_repr_apply,hne]
  intro h
  have hzero := hle h
  change b.repr (restrictedIntegerPoint4 c z) k = 0 at hzero
  rw [restrictedIntegerPoint4_coord] at hzero
  exact hk (by exact_mod_cast hzero)

theorem restrictedIntegerPoint4_short_bound
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ)
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P)
    (hadapt : ∀ k : Fin d, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
        rationalRealSpan4 P))) = intrinsicPrefix4 v k)
    (hshort : ∀ i, ∀ y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix4 v i →
      restrictedGauge4 P L hL Q hQ c₀ (v i) ≤ restrictedGauge4 P L hL Q hQ c₀ y)
    (z : Fin d → ℤ) (k : Fin d) (hk : z k ≠ 0) :
    restrictedGauge4 P L hL Q hQ c₀ (v k) ≤
      restrictedGauge4 P L hL Q hQ c₀ (restrictedIntegerPoint4 c z) := by
  exact hshort k _ (restrictedIntegerPoint4_mem c z)
    (restrictedIntegerPoint4_outside c v hadapt z k hk)


theorem exists_restricted_short_coordinates4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ c : Basis (Fin (Module.finrank ℚ P)) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃),
      ∀ (z : Fin (Module.finrank ℚ P) → ℤ) (k : Fin (Module.finrank ℚ P)), z k ≠ 0 →
        restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k ≤
          restrictedGauge4 P L hL Q hQ c₀ (restrictedIntegerPoint4 c z) := by
  obtain ⟨v,hv,hvL,_,_,hatt,hshort⟩ :=
    exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let dim : Fin 4 := ⟨Module.finrank ℚ P,by omega⟩
  obtain ⟨c,hc⟩ := exists_restricted_adapted_integer_basis4 P A₂ A₃ Q c₂ c₃ hP dim rfl v hv hvL
  refine ⟨c,?_⟩
  intro z k hk
  rw [← hatt k]
  exact restrictedIntegerPoint4_short_bound L hL hQ c₀ c v hc hshort z k hk

end CompoundFeasibility.RestrictedGeometry4
