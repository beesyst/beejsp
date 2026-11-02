import SubspaceBridge.RestrictedGreedyRanks4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedRelaxed4
open RestrictedGeometry4
noncomputable section

def relaxedBody4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    Set (rationalRealSpan4 P) :=
  {x | ∀ k, |(L *ᵥ (x : Fin 4 → ℝ)) (s k)| ≤ Q^(c (s k))}

def selectedLocalGroup4 {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    AddSubgroup (Fin 4 → ℤ) :=
  ⨅ k, (normBall p (Nat.ceil (JSP000334.qThreshold p Q (c (s k))))).comap (row4 A (s k))

def selectedSourceGroup4 {d : ℕ} (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) : AddSubgroup (Fin 4 → ℤ) :=
  selectedLocalGroup4 2 A₂ Q c₂ s₂ ⊓ selectedLocalGroup4 3 A₃ Q c₃ s₃

def relaxedLattice4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ)
    (s₂ s₃ : Fin d → Fin 4) : Submodule ℤ (rationalRealSpan4 P) :=
  (integerRealImage (selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃)).comap
    ((rationalRealSpan4 P).subtype.restrictScalars ℤ)

theorem restrictedBody4_subset_relaxed {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    restrictedBody4 P L Q c ⊆ relaxedBody4 P L Q c s := by
  intro x hx k
  exact hx (s k)

theorem lattice4_le_selectedLocalGroup4 {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    lattice4 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))) ≤
      selectedLocalGroup4 p A Q c s := by
  intro x hx
  simp only [selectedLocalGroup4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  intro k
  exact (show x ∈ (normBall p (Nat.ceil (JSP000334.qThreshold p Q (c (s k))))).comap
    (row4 A (s k)) from (AddSubgroup.mem_iInf.mp hx) (s k))

theorem originalSourceGroup4_le_selected {d : ℕ}
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    originalSourceGroup4 A₂ A₃ Q c₂ c₃ ≤ selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃ := by
  exact inf_le_inf (lattice4_le_selectedLocalGroup4 2 A₂ Q c₂ s₂)
    (lattice4_le_selectedLocalGroup4 3 A₃ Q c₃ s₃)

theorem restrictedLattice4_le_relaxed {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    restrictedLattice4 P A₂ A₃ Q c₂ c₃ ≤ relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ := by
  rintro x ⟨z,hz,hx⟩
  exact ⟨z,originalSourceGroup4_le_selected A₂ A₃ Q c₂ c₃ s₂ s₃ hz,hx⟩

instance relaxedLattice4_discrete {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    DiscreteTopology (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) := by
  let G := integerRealImage (selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃)
  let f : relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ → G :=
    fun x => ⟨x.val.val,x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : G => (z : Fin 4 → ℝ)) h

instance relaxedLattice4_isZLattice {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    IsZLattice ℝ (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) where
  span_top := by
    apply top_unique
    calc
      ⊤ = Submodule.span ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃ : Set (rationalRealSpan4 P)) :=
        (IsZLattice.span_top (K := ℝ) (L := restrictedLattice4 P A₂ A₃ Q c₂ c₃)).symm
      _ ≤ _ := Submodule.span_mono (restrictedLattice4_le_relaxed P A₂ A₃ Q c₂ c₃ s₂ s₃)

theorem relaxedLattice4_rank {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    Module.finrank ℤ (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) = Module.finrank ℚ P := by
  rw [ZLattice.rank ℝ,rationalRealSpan4_finrank P hP]

theorem relaxedLattice4_covolume_pos {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    0 < ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) :=
  ZLattice.covolume_pos _ _

end
end CompoundFeasibility.RestrictedRelaxed4
