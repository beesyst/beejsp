import SubspaceBridge.CompoundPairProducts42
open scoped BigOperators Matrix
open MeasureTheory CompoundFeasibility
namespace PairProducts42Literal
noncomputable section

def threshold (p : ℕ) (Q c : ℝ) : ℕ := Nat.ceil (-c * Real.log Q / Real.log p)

def realMember (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (x : Fin 4 → ℝ) : Prop :=
  ∃ z : Fin 4 → ℤ, (fun i => (z i : ℝ)) = x ∧
    (∀ i, padicNorm 2 ((A₂ *ᵥ (fun j => (z j : ℚ))) i) ≤
      (2 : ℚ) ^ (-(threshold 2 Q (c₂ i) : ℤ))) ∧
    ∀ i, padicNorm 3 ((A₃ *ᵥ (fun j => (z j : ℚ))) i) ≤
      (3 : ℚ) ^ (-(threshold 3 Q (c₃ i) : ℤ))

def minima (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ u ∧
    (∀ j, realMember A₂ A₃ Q c₂ c₃ (u j)) ∧
    ∀ j, ‖fun i => (L *ᵥ u j) i / Q ^ c₀ i‖ ≤ r}

theorem membership (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    x ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃) ↔
      realMember A₂ A₃ Q c₂ c₃ x := by
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨z,he,(lattice4_spec 2 A₂ _ z).mp hz.1,(lattice4_spec 3 A₃ _ z).mp hz.2⟩
  · rintro ⟨z,he,h2,h3⟩
    exact ⟨z,⟨(lattice4_spec 2 A₂ _ z).mpr h2,(lattice4_spec 3 A₃ _ z).mpr h3⟩,he⟩

theorem minima_equality (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) :
    sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = minima A₂ A₃ L Q c₀ c₂ c₃ j := by
  unfold sourceMinima4 minima
  simp only [membership]
  rfl

def sorted (a : Fin 4 → ℝ) : Fin 6 → ℝ := fun j =>
  if j = 0 then a 0 * a 1 else if j = 1 then a 0 * a 2 else
  if j = 2 then min (a 0 * a 3) (a 1 * a 2) else
  if j = 3 then max (a 0 * a 3) (a 1 * a 2) else
  if j = 4 then a 1 * a 3 else a 2 * a 3

def leftIndex : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def rightIndex : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

theorem sorted_equality (a : Fin 4 → ℝ) : sortedPairProducts42 a = sorted a := by
  ext j
  fin_cases j <;> simp [sortedPairProducts42,sorted]

theorem middle_left (a : Fin 4 → ℝ) (h : a 0 * a 3 ≤ a 1 * a 2) :
    sorted a = ![a 0*a 1,a 0*a 2,a 0*a 3,a 1*a 2,a 1*a 3,a 2*a 3] := by
  rw [← sorted_equality]
  exact sortedPairProducts42_of_middle_le a h

theorem middle_right (a : Fin 4 → ℝ) (h : a 1 * a 2 ≤ a 0 * a 3) :
    sorted a = ![a 0*a 1,a 0*a 2,a 1*a 2,a 0*a 3,a 1*a 3,a 2*a 3] := by
  rw [← sorted_equality]
  exact sortedPairProducts42_of_middle_ge a h

theorem actual_source (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) :
    let a := minima A₂ A₃ L Q c₀ c₂ c₃
    (∀ j, 0 < sorted a j) ∧ Monotone (sorted a) ∧
    (∃ σ : Equiv.Perm (Fin 6), ∀ j,
      sorted a j = a (leftIndex (σ j)) * a (rightIndex (σ j))) ∧
    (∏ j : Fin 6, sorted a j) = (∏ i : Fin 4, a i) ^ 3 := by
  have he : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = minima A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have h := source_pair_products42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  simpa only [sourcePairProducts42,he,sorted_equality,lo,hi,leftIndex,rightIndex] using h

theorem source_link (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) :
    sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ =
      sorted (minima A₂ A₃ L Q c₀ c₂ c₃) := by
  unfold sourcePairProducts42
  rw [show sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = minima A₂ A₃ L Q c₀ c₂ c₃ from
    funext (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃)]
  exact sorted_equality _

end
#print axioms membership
#print axioms minima_equality
#print axioms sorted_equality
#print axioms middle_left
#print axioms middle_right
#print axioms actual_source
#print axioms source_link
end PairProducts42Literal
