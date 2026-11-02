import SubspaceBridge.CompoundMinima6
open scoped BigOperators Matrix
open CompoundFeasibility
namespace ActualMinimaLiteral6

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

theorem membership (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (z : Fin 6 → ℤ) :
    z ∈ compoundSourceGroup6 A₂ A₃ Q c₂ c₃ ↔ z ∈ H A₂ A₃ Q c₂ c₃ := by
  change (z ∈ lattice6 2 A₂ _ ∧ z ∈ lattice6 3 A₃ _) ↔ _
  rw [lattice6_spec,lattice6_spec]
  rfl

theorem image_eq (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    realImage A₂ A₃ Q c₂ c₃ = (integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃) : Set (Fin 6 → ℝ)) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(membership A₂ A₃ Q c₂ c₃ z).mpr hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(membership A₂ A₃ Q c₂ c₃ z).mp hz,rfl⟩

theorem gauge_eq (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) :
    gauge L Q c₀ x = coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) x := rfl

theorem minima_eq (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = nu A₂ A₃ L Q c₀ c₂ c₃ j := by
  simp only [sourceMinima6,nu,image_eq,gauge_eq L hL Q hQ c₀]
  rfl

theorem attaining (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ u : Fin 6 → Fin 6 → ℤ, (∀ j, u j ∈ H A₂ A₃ Q c₂ c₃) ∧
      LinearIndependent ℝ (fun j i => (u j i : ℝ)) ∧
      (∀ j, 0 < nu A₂ A₃ L Q c₀ c₂ c₃ j) ∧ Monotone (nu A₂ A₃ L Q c₀ c₂ c₃) ∧
      (∀ j, gauge L Q c₀ (fun i => (u j i : ℝ)) = nu A₂ A₃ L Q c₀ c₂ c₃ j) ∧
      ∀ j s, |∑ t, C L s t * (u j t : ℝ)| ≤
        nu A₂ A₃ L Q c₀ c₂ c₃ j * (Q ^ c₀ (lo s) * Q ^ c₀ (hi s)) := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima6_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have he : sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = nu A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_eq A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  rw [he] at hpos hmono hatt hpoint
  refine ⟨fun j => (u j : Fin 6 → ℤ),fun j => (membership A₂ A₃ Q c₂ c₃ _).mp (u j).property,
    hu,hpos,hmono,?_,hpoint⟩
  intro j
  rw [gauge_eq L hL Q hQ c₀]
  exact hatt j

theorem C_eq {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    C A = compound A := rfl

theorem uniform_product (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c₆ : ℝ, 0 < c₆ ∧
      c₆ = |(C L).det| * ((padicNorm 2 (C A₂).det : ℝ) * (padicNorm 3 (C A₃).det : ℝ)) / 720 ∧
      ∀ (Q : ℝ), 1 < Q → ∀ (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → c₆ ≤ ∏ j : Fin 6, nu A₂ A₃ L Q c₀ c₂ c₃ j := by
  simp only [C_eq]
  change ∃ c₆ : ℝ, 0 < c₆ ∧
    c₆ = |(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720 ∧
    ∀ (Q : ℝ), 1 < Q → ∀ (c₀ c₂ c₃ : Fin 4 → ℝ),
      (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → c₆ ≤ ∏ j : Fin 6, nu A₂ A₃ L Q c₀ c₂ c₃ j
  obtain ⟨c₆,hpos,hval,hbound⟩ := source_compound_uniform_minima_lower6 A₂ A₃ L h₂ h₃ hL
  refine ⟨c₆,hpos,hval,?_⟩
  intro Q hQ c₀ c₂ c₃ hb
  have he : sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = nu A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_eq A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  rw [← he]
  exact hbound Q hQ c₀ c₂ c₃ hb

end ActualMinimaLiteral6

#check ActualMinimaLiteral6.C
#print ActualMinimaLiteral6.C
#print axioms ActualMinimaLiteral6.C

#check ActualMinimaLiteral6.E
#print ActualMinimaLiteral6.E
#print axioms ActualMinimaLiteral6.E

#check ActualMinimaLiteral6.H
#print ActualMinimaLiteral6.H
#print axioms ActualMinimaLiteral6.H

#check ActualMinimaLiteral6.realImage
#print ActualMinimaLiteral6.realImage
#print axioms ActualMinimaLiteral6.realImage

#check ActualMinimaLiteral6.gauge
#print ActualMinimaLiteral6.gauge
#print axioms ActualMinimaLiteral6.gauge

#check ActualMinimaLiteral6.nu
#print ActualMinimaLiteral6.nu
#print axioms ActualMinimaLiteral6.nu

#check ActualMinimaLiteral6.membership
#print ActualMinimaLiteral6.membership
#print axioms ActualMinimaLiteral6.membership

#check ActualMinimaLiteral6.image_eq
#print ActualMinimaLiteral6.image_eq
#print axioms ActualMinimaLiteral6.image_eq

#check ActualMinimaLiteral6.gauge_eq
#print ActualMinimaLiteral6.gauge_eq
#print axioms ActualMinimaLiteral6.gauge_eq

#check ActualMinimaLiteral6.minima_eq
#print ActualMinimaLiteral6.minima_eq
#print axioms ActualMinimaLiteral6.minima_eq

#check ActualMinimaLiteral6.attaining
#print ActualMinimaLiteral6.attaining
#print axioms ActualMinimaLiteral6.attaining

#check ActualMinimaLiteral6.uniform_product
#print ActualMinimaLiteral6.uniform_product
#print axioms ActualMinimaLiteral6.uniform_product

#check ActualMinimaLiteral6.C_eq
#print ActualMinimaLiteral6.C_eq
#print axioms ActualMinimaLiteral6.C_eq
