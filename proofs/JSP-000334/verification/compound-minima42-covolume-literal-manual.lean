import SubspaceBridge.CompoundMinima42
open scoped BigOperators Matrix
open CompoundFeasibility
namespace CompoundCovolumeLiteral42

def C {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  fun s t => A (lo s) (lo t) * A (hi s) (hi t) - A (lo s) (hi t) * A (hi s) (lo t)

noncomputable def E (p : ℕ) (Q c : ℝ) : ℕ := Nat.ceil (-c * Real.log Q / Real.log p)

def H (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ) : Set (Fin 6 → ℤ) :=
  {x | (∀ s, padicNorm 2 (∑ t, C A₂ s t * (x t : ℚ)) ≤
      (2 : ℚ) ^ (-((e₂ (lo s) + e₂ (hi s) : ℕ) : ℤ))) ∧
    (∀ s, padicNorm 3 (∑ t, C A₃ s t * (x t : ℚ)) ≤
      (3 : ℚ) ^ (-((e₃ (lo s) + e₃ (hi s) : ℕ) : ℤ)))}

def ZR : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 6 → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp [Int.cast_mul]

theorem C_eq {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : C A = compound A := rfl

theorem ZR_eq : ZR = (integerReal (n := 6)) := rfl

theorem membership (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ) (x : Fin 6 → ℤ) :
    x ∈ sourceLattice6 A₂ A₃ e₂ e₃ ↔ x ∈ H A₂ A₃ e₂ e₃ := by
  change (x ∈ lattice6 2 A₂ e₂ ∧ x ∈ lattice6 3 A₃ e₃) ↔ _
  rw [lattice6_spec,lattice6_spec]
  rfl

theorem multiple (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ j : Fin 6, Pi.single j D ∈ H A₂ A₃ e₂ e₃ := by
  obtain ⟨D,hd,hm⟩ := sourceLattice6_multiple A₂ A₃ e₂ e₃
  exact ⟨D,hd,fun j => (membership A₂ A₃ e₂ e₃ _).mp (hm j)⟩

theorem basis_covolume (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ) :
    ∃ c : Basis (Fin 6) ℤ (sourceLattice6 A₂ A₃ e₂ e₃),
      (∀ j, (c j : Fin 6 → ℤ) ∈ H A₂ A₃ e₂ e₃) ∧
      ZLattice.covolume ((sourceLattice6 A₂ A₃ e₂ e₃).toIntSubmodule.map ZR) =
        |(Matrix.of (fun j i => ((c j : Fin 6 → ℤ) i : ℝ))).det| ∧
      ZLattice.covolume ((sourceLattice6 A₂ A₃ e₂ e₃).toIntSubmodule.map ZR) =
        ((sourceLattice6 A₂ A₃ e₂ e₃).index : ℝ) := by
  obtain ⟨c⟩ := sourceLattice6_has_basis A₂ A₃ e₂ e₃
  refine ⟨c,fun j => (membership A₂ A₃ e₂ e₃ _).mp (c j).property,?_,?_⟩
  · change ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) = _
    exact sourceLattice6_covolume_det A₂ A₃ e₂ e₃ c
  · change ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) = _
    exact sourceLattice6_covolume_index A₂ A₃ e₂ e₃

theorem local_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ) :
    (padicNorm 2 (C A₂).det : ℝ) * (padicNorm 3 (C A₃).det : ℝ) *
      (2 : ℝ) ^ (∑ s : Fin 6, (e₂ (lo s) + e₂ (hi s))) *
      3 ^ (∑ s : Fin 6, (e₃ (lo s) + e₃ (hi s))) ≤
      ZLattice.covolume ((sourceLattice6 A₂ A₃ e₂ e₃).toIntSubmodule.map ZR) := by
  rw [C_eq, C_eq, ZR_eq]
  simp only [compound_exponent_sum]
  exact sourceLattice6_covolume_lower A₂ A₃ e₂ e₃


theorem uniform_frame (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c : ℝ, 0 < c ∧
      c = |(C L).det| * ((padicNorm 2 (C A₂).det : ℝ) * (padicNorm 3 (C A₃).det : ℝ)) / 720 ∧
      ∀ (Q : ℝ) (_hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        ∀ (u : Fin 6 → sourceLattice6 A₂ A₃ (fun i => E 2 Q (c₂ i)) (fun i => E 3 Q (c₃ i))),
          LinearIndependent ℝ (fun j i => ((u j : Fin 6 → ℤ) i : ℝ)) →
          ∀ r : Fin 6 → ℝ,
            (∀ j s, |∑ k, C L s k * ((u j : Fin 6 → ℤ) k : ℝ)| ≤
              r j * (Q ^ c₀ (lo s) * Q ^ c₀ (hi s))) → c ≤ ∏ j, r j := by
  rw [C_eq,C_eq,C_eq]
  refine ⟨|(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720,
    source_compound_lower_constant_pos42 A₂ A₃ L h₂ h₃ hL,rfl,?_⟩
  intro Q hQ c₀ c₂ c₃ hb u hu r hp
  apply sourceLattice6_Q_frame_product_lower A₂ A₃ L Q hQ c₀ c₂ c₃ hb u hu r
  intro j s
  exact hp j s


end CompoundCovolumeLiteral42
#check CompoundCovolumeLiteral42.C
#print axioms CompoundCovolumeLiteral42.C
#check CompoundCovolumeLiteral42.E
#print axioms CompoundCovolumeLiteral42.E
#check CompoundCovolumeLiteral42.H
#print axioms CompoundCovolumeLiteral42.H
#check CompoundCovolumeLiteral42.ZR
#print axioms CompoundCovolumeLiteral42.ZR
#check CompoundCovolumeLiteral42.membership
#print CompoundCovolumeLiteral42.membership
#print axioms CompoundCovolumeLiteral42.membership
#check CompoundCovolumeLiteral42.multiple
#print CompoundCovolumeLiteral42.multiple
#print axioms CompoundCovolumeLiteral42.multiple
#check CompoundCovolumeLiteral42.basis_covolume
#print CompoundCovolumeLiteral42.basis_covolume
#print axioms CompoundCovolumeLiteral42.basis_covolume
#check CompoundCovolumeLiteral42.local_lower
#print CompoundCovolumeLiteral42.local_lower
#print axioms CompoundCovolumeLiteral42.local_lower
#check CompoundCovolumeLiteral42.uniform_frame
#print CompoundCovolumeLiteral42.uniform_frame
#print axioms CompoundCovolumeLiteral42.uniform_frame
