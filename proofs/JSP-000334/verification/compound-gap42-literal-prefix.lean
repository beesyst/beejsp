import SubspaceBridge.CompoundGap42
open scoped BigOperators Matrix
open MeasureTheory CompoundFeasibility
namespace Gap42Literal
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


def C {R : Type*} [CommRing R] (L : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  fun s t => L (lo s) (lo t) * L (hi s) (hi t) - L (lo s) (hi t) * L (hi s) (lo t)

noncomputable def E (p : ℕ) (Q c : ℝ) : ℕ := Nat.ceil (-c * Real.log Q / Real.log p)

def H (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℤ) :=
  {z | (∀ s, padicNorm 2 (∑ t, C A₂ s t * (z t : ℚ)) ≤
      (2 : ℚ) ^ (-((E 2 Q (c₂ (lo s)) + E 2 Q (c₂ (hi s)) : ℕ) : ℤ))) ∧
    (∀ s, padicNorm 3 (∑ t, C A₃ s t * (z t : ℚ)) ≤
      (3 : ℚ) ^ (-((E 3 Q (c₃ (lo s)) + E 3 Q (c₃ (hi s)) : ℕ) : ℤ)))}

def realImage (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℝ) :=
  {x | ∃ z : Fin 6 → ℤ, z ∈ H A₂ A₃ Q c₂ c₃ ∧ (fun i => (z i : ℝ)) = x}

noncomputable def gauge (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) : ℝ :=
  ‖fun s : Fin 6 => (∑ t : Fin 6, C L s t * x t) / (Q ^ c₀ (lo s) * Q ^ c₀ (hi s))‖

noncomputable def nu (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
    (∀ i, v i ∈ realImage A₂ A₃ Q c₂ c₃) ∧ ∀ i, gauge L Q c₀ (v i) ≤ r}

theorem membership6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (z : Fin 6 → ℤ) :
    z ∈ compoundSourceGroup6 A₂ A₃ Q c₂ c₃ ↔ z ∈ H A₂ A₃ Q c₂ c₃ := by
  change (z ∈ lattice6 2 A₂ _ ∧ z ∈ lattice6 3 A₃ _) ↔ _
  rw [lattice6_spec,lattice6_spec]
  rfl

theorem image_eq6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    realImage A₂ A₃ Q c₂ c₃ = (integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃) : Set (Fin 6 → ℝ)) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(membership6 A₂ A₃ Q c₂ c₃ z).mpr hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(membership6 A₂ A₃ Q c₂ c₃ z).mp hz,rfl⟩

theorem gauge_eq6 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) :
    gauge L Q c₀ x = coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) x := rfl

theorem minima_eq6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = nu A₂ A₃ L Q c₀ c₂ c₃ j := by
  simp only [sourceMinima6,nu,image_eq6,gauge_eq6 L hL Q hQ c₀]
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

theorem top_products (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    let a := minima A₂ A₃ L Q c₀ c₂ c₃
    sorted a 4 = a 1 * a 3 ∧ sorted a 5 = a 2 * a 3 := by
  simp [sorted]

theorem summed_gap (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (κ Q delta : ℝ) (hk : 0 < κ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hcompare : ∀ j, κ * sorted (minima A₂ A₃ L Q c₀ c₂ c₃) j ≤ nu A₂ A₃ L Q c₀ c₂ c₃ j)
    (hgap : minima A₂ A₃ L Q c₀ c₂ c₃ 1 <
      minima A₂ A₃ L Q c₀ c₂ c₃ 2 * Q ^ (-delta)) :
    nu A₂ A₃ L Q c₀ c₂ c₃ 4 < (2 / κ) * nu A₂ A₃ L Q c₀ c₂ c₃ 5 * Q ^ (-delta) := by
  have he4 : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = minima A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have he6 : sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = nu A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_eq6 A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have hc : ∀ j, κ * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
      sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
    simpa only [sourcePairProducts42,he4,he6,sorted_equality] using hcompare
  have hg : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta) := by
    simpa only [he4] using hgap
  simpa only [he6] using source_summed_gap_bound42 A₂ A₃ L hL κ Q delta hk hQ c₀ c₂ c₃ hc hg

theorem literal_cutoff (B delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → B < Q ^ (delta / 2) :=
  compound_gap_cutoff42 B delta hd

theorem literal_absorption (x y B Q delta : ℝ) (hy : 0 < y) (hQ : 1 < Q)
    (hcut : B < Q ^ (delta / 2)) (hg : x < B * y * Q ^ (-delta)) :
    x < y * Q ^ (-delta / 2) := absorb_compound_gap42 x y B Q delta hy hQ hcut hg

end
#check top_products
#print axioms top_products
#check summed_gap
#print axioms summed_gap
#check literal_cutoff
#print axioms literal_cutoff
#check literal_absorption
#print axioms literal_absorption
end Gap42Literal
