import SubspaceBridge.RestrictedGreedyRanks5
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedRelaxed5
open RestrictedGeometry5
noncomputable section

def relaxedBody5 {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c : Fin 5 → ℝ) (s : Fin d → Fin 5) :
    Set (rationalRealSpan5 P) :=
  {x | ∀ k, |(L *ᵥ (x : Fin 5 → ℝ)) (s k)| ≤ Q^(c (s k))}

def selectedLocalGroup5 {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c : Fin 5 → ℝ) (s : Fin d → Fin 5) :
    AddSubgroup (Fin 5 → ℤ) :=
  ⨅ k, (normBall p (Nat.ceil (JSP000334.qThreshold p Q (c (s k))))).comap (row5 A (s k))

def selectedSourceGroup5 {d : ℕ} (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) : AddSubgroup (Fin 5 → ℤ) :=
  selectedLocalGroup5 2 A₂ Q c₂ s₂ ⊓ selectedLocalGroup5 3 A₃ Q c₃ s₃

def relaxedLattice5 {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ)
    (s₂ s₃ : Fin d → Fin 5) : Submodule ℤ (rationalRealSpan5 P) :=
  (integerRealImage (selectedSourceGroup5 A₂ A₃ Q c₂ c₃ s₂ s₃)).comap
    ((rationalRealSpan5 P).subtype.restrictScalars ℤ)

theorem restrictedBody5_subset_relaxed {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c : Fin 5 → ℝ) (s : Fin d → Fin 5) :
    restrictedBody5 P L Q c ⊆ relaxedBody5 P L Q c s := by
  intro x hx k
  exact hx (s k)

theorem lattice5_le_selectedLocalGroup5 {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c : Fin 5 → ℝ) (s : Fin d → Fin 5) :
    lattice5 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))) ≤
      selectedLocalGroup5 p A Q c s := by
  intro x hx
  simp only [selectedLocalGroup5,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  intro k
  exact (show x ∈ (normBall p (Nat.ceil (JSP000334.qThreshold p Q (c (s k))))).comap
    (row5 A (s k)) from (AddSubgroup.mem_iInf.mp hx) (s k))

theorem originalSourceGroup5_le_selected {d : ℕ}
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    originalSourceGroup5 A₂ A₃ Q c₂ c₃ ≤ selectedSourceGroup5 A₂ A₃ Q c₂ c₃ s₂ s₃ := by
  exact inf_le_inf (lattice5_le_selectedLocalGroup5 2 A₂ Q c₂ s₂)
    (lattice5_le_selectedLocalGroup5 3 A₃ Q c₃ s₃)

theorem restrictedLattice5_le_relaxed {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    restrictedLattice5 P A₂ A₃ Q c₂ c₃ ≤ relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃ := by
  rintro x ⟨z,hz,hx⟩
  exact ⟨z,originalSourceGroup5_le_selected A₂ A₃ Q c₂ c₃ s₂ s₃ hz,hx⟩

instance relaxedLattice5_discrete {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    DiscreteTopology (relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃) := by
  let G := integerRealImage (selectedSourceGroup5 A₂ A₃ Q c₂ c₃ s₂ s₃)
  let f : relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃ → G :=
    fun x => ⟨x.val.val,x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : G => (z : Fin 5 → ℝ)) h

instance relaxedLattice5_isZLattice {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    IsZLattice ℝ (relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃) where
  span_top := by
    apply top_unique
    calc
      ⊤ = Submodule.span ℝ (restrictedLattice5 P A₂ A₃ Q c₂ c₃ : Set (rationalRealSpan5 P)) :=
        (IsZLattice.span_top (K := ℝ) (L := restrictedLattice5 P A₂ A₃ Q c₂ c₃)).symm
      _ ≤ _ := Submodule.span_mono (restrictedLattice5_le_relaxed P A₂ A₃ Q c₂ c₃ s₂ s₃)

theorem relaxedLattice5_rank {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    Module.finrank ℤ (relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃) = Module.finrank ℚ P := by
  rw [ZLattice.rank ℝ,rationalRealSpan5_finrank P hP]

theorem relaxedLattice5_covolume_pos {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    0 < ZLattice.covolume (relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure5 P) :=
  ZLattice.covolume_pos _ _

end
end CompoundFeasibility.RestrictedRelaxed5
