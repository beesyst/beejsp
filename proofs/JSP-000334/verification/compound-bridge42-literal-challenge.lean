import SubspaceBridge.CompoundBridge42
open scoped BigOperators Matrix
open CompoundFeasibility
namespace CompoundBridgeLiteral42

def C {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  fun s t => A (lo s) (lo t) * A (hi s) (hi t) - A (lo s) (hi t) * A (hi s) (lo t)

def V (u : Fin 4 → Fin 4 → ℤ) : Fin 6 → Fin 6 → ℤ :=
  fun s t => u (lo s) (lo t) * u (hi s) (hi t) - u (lo s) (hi t) * u (hi s) (lo t)

def G4 (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 → ℕ) : Set (Fin 4 → ℤ) :=
  {x | ∀ i, padicNorm p (∑ j : Fin 4, A i j * (x j : ℚ)) ≤ (p : ℚ) ^ (-(e i : ℤ))}

def G6 (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 → ℕ) : Set (Fin 6 → ℤ) :=
  {z | ∀ s, padicNorm p (∑ t : Fin 6, C A s t * (z t : ℚ)) ≤
    (p : ℚ) ^ (-((e (lo s) + e (hi s) : ℕ) : ℤ))}

theorem invertible (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : IsUnit A) :
    IsUnit (C A) ∧ LinearIndependent ℚ (C A).row ∧ LinearIndependent ℚ (C A).col :=
  ⟨compound_unit A hA,compound_rows_independent A hA,compound_columns_independent A hA⟩

theorem action (A : Matrix (Fin 4) (Fin 4) ℚ) (x y : Fin 4 → ℚ) (s : Fin 6) :
    (∑ t : Fin 6, C A s t * (x (lo t) * y (hi t) - x (hi t) * y (lo t))) =
      (∑ j, A (lo s) j * x j) * (∑ j, A (hi s) j * y j) -
      (∑ j, A (hi s) j * x j) * (∑ j, A (lo s) j * y j) := by
  simpa only [C,compound,wedge,Matrix.mulVec,dotProduct] using congrFun (wedge_transform A x y) s

theorem frame_bridge (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ)
    (u : Fin 4 → Fin 4 → ℤ) (hum : ∀ j, u j ∈ G4 2 A₂ e₂ ∧ u j ∈ G4 3 A₃ e₃)
    (hu : LinearIndependent ℝ (fun j => fun i => (u j i : ℝ)))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (A r : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hr : ∀ j, 0 ≤ r j)
    (harch : ∀ j i, |(L *ᵥ (fun k => (u j k : ℝ))) i| ≤ r j * A i) :
    (∀ s, V u s ∈ G6 2 A₂ e₂ ∧ V u s ∈ G6 3 A₃ e₃) ∧
    LinearIndependent ℚ (fun s => fun t => (V u s t : ℚ)) ∧
    LinearIndependent ℝ (fun s => fun t => (V u s t : ℝ)) ∧
    (fun s t => (V u s t : ℚ)) = C (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ)) ∧
    (fun s t => (V u s t : ℝ)) = C (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℝ)) ∧
    ∀ s t, |(C L *ᵥ (fun q => (V u s q : ℝ))) t| ≤
      2 * r (lo s) * r (hi s) * A (lo t) * A (hi t) := by
  have hm : ∀ j, u j ∈ sourceLattice4 A₂ A₃ e₂ e₃ := by
    intro j
    exact ⟨(lattice4_spec 2 A₂ e₂ (u j)).mpr (hum j).1,
      (lattice4_spec 3 A₃ e₃ (u j)).mpr (hum j).2⟩
  have hh := source_compound_bridge42 A₂ A₃ e₂ e₃ u hm hu L A r hA hr harch
  simpa only [sourceLattice6,AddSubgroup.mem_inf,lattice6_spec,V,compoundFrame,C,compound,wedge,
    G6,Set.mem_setOf_eq,Matrix.mulVec,dotProduct] using hh

theorem rounding (p : ℕ) (hp : 1 ≤ p) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Nat.ceil (a + b) ≤ Nat.ceil a + Nat.ceil b ∧
    Nat.ceil a + Nat.ceil b ≤ Nat.ceil (a + b) + 1 ∧
    p ^ Nat.ceil (a + b) ≤ p ^ (Nat.ceil a + Nat.ceil b) ∧
    p ^ (Nat.ceil a + Nat.ceil b) ≤ p * p ^ Nat.ceil (a + b) := by
  obtain ⟨h₁,h₂⟩ := ceil_pair_bounds a b ha hb
  obtain ⟨h₃,h₄⟩ := ceil_pair_prime_powers p hp a b ha hb
  exact ⟨h₁,h₂,h₃,h₄⟩

theorem normalization (A : Fin 4 → ℝ) (e : Fin 4 → ℕ) :
    (∏ s : Fin 6, A (lo s) * A (hi s)) = (∏ i : Fin 4, A i) ^ (3 : ℕ) ∧
    (∑ s : Fin 6, (e (lo s) + e (hi s))) = 3 * ∑ i : Fin 4, e i :=
  ⟨compound_width_product A,compound_exponent_sum e⟩

set_option pp.proofs false
#check C
#print C
#print axioms C
#check V
#print V
#print axioms V
#check G4
#print G4
#print axioms G4
#check G6
#print G6
#print axioms G6
#check invertible
#print invertible
#print axioms invertible
#check action
#print action
#print axioms action
#check frame_bridge
#print frame_bridge
#print axioms frame_bridge
#check rounding
#print rounding
#print axioms rounding
#check normalization
#print normalization
#print axioms normalization
end CompoundBridgeLiteral42
