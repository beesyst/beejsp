import SubspaceBridge.OriginalMinima4
open scoped BigOperators Matrix
open MeasureTheory CompoundFeasibility
namespace Original4Literal
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

theorem attaining (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ u : Fin 4 → (Fin 4 → ℤ),
      LinearIndependent ℝ (fun j i => (u j i : ℝ)) ∧
      (∀ j, realMember A₂ A₃ Q c₂ c₃ (fun i => (u j i : ℝ))) ∧
      (∀ j, 0 < minima A₂ A₃ L Q c₀ c₂ c₃ j) ∧
      Monotone (minima A₂ A₃ L Q c₀ c₂ c₃) ∧
      ∀ j i, |(L *ᵥ (fun k => (u j k : ℝ))) i| ≤
        minima A₂ A₃ L Q c₀ c₂ c₃ j * Q ^ c₀ i := by
  obtain ⟨u,hu,hpos,hmono,hatt,hbound⟩ := exists_sourceMinima4_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  refine ⟨fun j => (u j : Fin 4 → ℤ),hu,?_,?_,?_,?_⟩
  · intro j
    apply (membership A₂ A₃ Q c₂ c₃ _).mp
    exact ⟨(u j : Fin 4 → ℤ),(u j).property,rfl⟩
  · simpa only [minima_equality] using hpos
  · intro i j hij
    simpa only [minima_equality] using hmono hij
  · simpa only [minima_equality] using hbound

theorem volume (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    MeasureTheory.volume.real {x : Fin 4 → ℝ | ∀ i, |(L *ᵥ x) i| ≤ Q ^ c₀ i} =
      16 * (∏ i, Q ^ c₀ i) / |L.det| := originalBody4_volume L hL Q hQ c₀

theorem upper (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ (K : ℕ) (C : ℝ), 0 < K ∧ 0 < C ∧ C = |L.det| * (K : ℝ) * 1296 ∧
      ∀ Q : ℝ, 1 < Q → ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∏ j : Fin 4, minima A₂ A₃ L Q c₀ c₂ c₃ j) ≤ C := by
  obtain ⟨K,C,hK,hC,he,hbound⟩ := source_original_uniform_minima_upper4 A₂ A₃ L h₂ h₃ hL
  refine ⟨K,C,hK,hC,he,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  simpa only [minima_equality] using hbound Q hQ c₀ c₂ c₃ hc₂ hc₃ hb

theorem normalized_covolume (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) :
    ∃ K : ℕ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q → ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
      (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
      (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
      ((sourceLattice4 A₂ A₃ (fun i => threshold 2 Q (c₂ i))
        (fun i => threshold 3 Q (c₃ i))).index : ℝ) /
        (∏ i, Q ^ c₀ i) ≤ (K : ℝ) * 1296 := by
  obtain ⟨K,hK,hbound⟩ := sourceLattice4_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  refine ⟨K,hK,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  simpa only [sourceLattice4_covolume_index] using hbound Q hQ c₀ c₂ c₃ hc₂ hc₃ hb

theorem determinant_one_upper (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) :
    ∃ K : ℕ, 0 < K ∧ ∀ Q : ℝ, 1 < Q → ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
      (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
      (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
      (∏ j : Fin 4, minima A₂ A₃ L Q c₀ c₂ c₃ j) ≤ (K : ℝ) * 1296 := by
  have hu₂ : IsUnit A₂ := (Matrix.isUnit_iff_isUnit_det A₂).mpr (by rw [h₂]; exact isUnit_one)
  have hu₃ : IsUnit A₃ := (Matrix.isUnit_iff_isUnit_det A₃).mpr (by rw [h₃]; exact isUnit_one)
  have huL : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (by rw [hL]; exact isUnit_one)
  obtain ⟨K,C,hK,hC,he,hbound⟩ := upper A₂ A₃ L hu₂ hu₃ huL
  have hCeq : C = (K : ℝ) * 1296 := by simpa only [hL,abs_one,one_mul] using he
  refine ⟨K,hK,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  simpa only [hCeq] using hbound Q hQ c₀ c₂ c₃ hc₂ hc₃ hb

end
#print axioms membership
#print axioms minima_equality
#print axioms attaining
#print axioms volume
#print axioms upper
#print axioms normalized_covolume
#print axioms determinant_one_upper
end Original4Literal
