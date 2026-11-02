import SubspaceBridge.CompoundDualLine42
open scoped BigOperators Matrix
open MeasureTheory CompoundFeasibility
namespace DualIntegrationLiteral
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

theorem literal_local_inclusion (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (a : Fin 4 → ℝ) (z : Fin 6 → ℤ)
    (hz : ∀ s, padicNorm p (∑ t, C A s t * (z t : ℚ)) ≤
      ((p : ℚ) ^ (Nat.ceil (a (lo s)) + Nat.ceil (a (hi s))))⁻¹) :
    ∀ s, padicNorm p (∑ t, C A s t * (z t : ℚ)) ≤
      ((p : ℚ) ^ Nat.ceil (a (lo s) + a (hi s)))⁻¹ := by
  have hx : z ∈ lattice6 p A (fun i => Nat.ceil (a i)) := by
    simpa [lattice6,AddSubgroup.mem_iInf,AddSubgroup.mem_comap,normBall,row6,C,compound] using hz
  have hd := summed_le_directLocal42 p A a hx
  simpa [directLocal42,AddSubgroup.mem_iInf,AddSubgroup.mem_comap,normBall,row6,C,compound] using hd

theorem literal_cutoff (B delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ Q : ℝ, T < Q → B < Q ^ (delta / 2) :=
  compound_gap_cutoff42 B delta hd

theorem literal_absorption (x y B Q delta : ℝ) (hy : 0 < y) (hQ : 1 < Q)
    (hcut : B < Q ^ (delta / 2)) (hg : x < B * y * Q ^ (-delta)) :
    x < y * Q ^ (-delta / 2) := absorb_compound_gap42 x y B Q delta hy hQ hcut hg

def D (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℤ) :=
  {z | (∀ s, (padicNorm 2 (∑ t, C A₂ s t * (z t : ℚ)) : ℝ) ≤ Q ^ (c₂ (lo s) + c₂ (hi s))) ∧
    ∀ s, (padicNorm 3 (∑ t, C A₃ s t * (z t : ℚ)) : ℝ) ≤ Q ^ (c₃ (lo s) + c₃ (hi s))}

def DImage (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℝ) :=
  {x | ∃ z : Fin 6 → ℤ, z ∈ D A₂ A₃ Q c₂ c₃ ∧ (fun i => (z i : ℝ)) = x}

theorem direct_group_equality (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (z : Fin 6 → ℤ) :
    z ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃ ↔ z ∈ D A₂ A₃ Q c₂ c₃ := by
  simpa only [D,Set.mem_setOf_eq,C,compound] using directCompoundGroup42_raw A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z

theorem direct_image_equality (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    DImage A₂ A₃ Q c₂ c₃ = (integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃) : Set (Fin 6 → ℝ)) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z).mpr hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z).mp hz,rfl⟩

theorem raw_group_inclusion (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    H A₂ A₃ Q c₂ c₃ ⊆ D A₂ A₃ Q c₂ c₃ := by
  intro z hz
  exact (direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z).mp
    (summed_le_directCompoundGroup42 A₂ A₃ Q c₂ c₃ ((membership6 A₂ A₃ Q c₂ c₃ z).mpr hz))

theorem raw_full_span (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    Submodule.span ℝ (DImage A₂ A₃ Q c₂ c₃) = ⊤ := by
  rw [direct_image_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃]
  exact (directCompoundGroup42_isZLattice A₂ A₃ Q c₂ c₃).span_top

noncomputable def directGauge (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ)
    (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) : ℝ :=
  ‖fun s : Fin 6 => (∑ t : Fin 6, C L s t * x t) / Q ^ (c₀ (lo s) + c₀ (hi s))‖

theorem directGauge_eq (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (hQ : 1 < Q)
    (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) : directGauge L Q c₀ x = gauge L Q c₀ x := by
  simp only [directGauge,gauge,Real.rpow_add (lt_trans zero_lt_one hQ)]

noncomputable def rho (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
    (∀ i, v i ∈ DImage A₂ A₃ Q c₂ c₃) ∧ ∀ i, directGauge L Q c₀ (v i) ≤ r}

theorem rho_equality (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (j : Fin 6) :
    rho A₂ A₃ L Q c₀ c₂ c₃ j = directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  simp only [rho,directMinima42,direct_image_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃,
    directGauge_eq L Q hQ c₀,gauge_eq6 L hL Q hQ c₀]
  rfl

theorem raw_scaling (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (z : Fin 6 → ℤ) (hz : z ∈ D A₂ A₃ Q c₂ c₃) :
    (fun i => 6 * z i) ∈ H A₂ A₃ Q c₂ c₃ := by
  exact (membership6 A₂ A₃ Q c₂ c₃ ((6 : ℤ) • z)).mp
    (directCompoundGroup42_six_mem A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z
      ((direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ z).mpr hz))

theorem raw_attainment (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∃ z : Fin 6 → (Fin 6 → ℤ), LinearIndependent ℝ (fun j i => (z j i : ℝ)) ∧
      (∀ j, z j ∈ D A₂ A₃ Q c₂ c₃) ∧
      (∀ j, 0 < rho A₂ A₃ L Q c₀ c₂ c₃ j) ∧ Monotone (rho A₂ A₃ L Q c₀ c₂ c₃) ∧
      ∀ j, directGauge L Q c₀ (fun i => (z j i : ℝ)) = rho A₂ A₃ L Q c₀ c₂ c₃ j := by
  obtain ⟨u,hu,hp,hm,ha⟩ := exists_directMinima42_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have he : rho A₂ A₃ L Q c₀ c₂ c₃ = directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ :=
    funext (rho_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃)
  refine ⟨fun j => (u j : Fin 6 → ℤ),hu,?_,?_,?_,?_⟩
  · intro j
    exact (direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ _).mp (u j).property
  · simpa only [he] using hp
  · simpa only [he] using hm
  · intro j
    simpa only [he,directGauge_eq L Q hQ c₀,gauge_eq6 L hL Q hQ c₀] using ha j

theorem raw_admissibility (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (j : Fin 6) :
    ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ DImage A₂ A₃ Q c₂ c₃) ∧
      ∀ i, directGauge L Q c₀ (v i) ≤ rho A₂ A₃ L Q c₀ c₂ c₃ j := by
  simpa only [direct_image_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃,
    rho_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃,directGauge_eq L Q hQ c₀,
    gauge_eq6 L hL Q hQ c₀] using directMinima42_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j

theorem raw_comparison (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∀ j, rho A₂ A₃ L Q c₀ c₂ c₃ j ≤ nu A₂ A₃ L Q c₀ c₂ c₃ j ∧
      nu A₂ A₃ L Q c₀ c₂ c₃ j ≤ 6 * rho A₂ A₃ L Q c₀ c₂ c₃ j := by
  simpa only [rho_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃,
    ← minima_eq6 A₂ A₃ L hL Q hQ c₀ c₂ c₃] using
      directMinima42_comparison A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃

theorem raw_gap_bound (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (κ Q delta : ℝ) (hk : 0 < κ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hcompare : ∀ j, κ * sorted (minima A₂ A₃ L Q c₀ c₂ c₃) j ≤ nu A₂ A₃ L Q c₀ c₂ c₃ j)
    (hgap : minima A₂ A₃ L Q c₀ c₂ c₃ 1 < minima A₂ A₃ L Q c₀ c₂ c₃ 2 * Q ^ (-delta)) :
    rho A₂ A₃ L Q c₀ c₂ c₃ 4 < (12 / κ) * rho A₂ A₃ L Q c₀ c₂ c₃ 5 * Q ^ (-delta) := by
  have ht := raw_comparison A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃
  calc
    _ ≤ nu A₂ A₃ L Q c₀ c₂ c₃ 4 := (ht 4).1
    _ < (2 / κ) * nu A₂ A₃ L Q c₀ c₂ c₃ 5 * Q ^ (-delta) :=
      summed_gap A₂ A₃ L hL κ Q delta hk hQ c₀ c₂ c₃ hcompare hgap
    _ ≤ (2 / κ) * (6 * rho A₂ A₃ L Q c₀ c₂ c₃ 5) * Q ^ (-delta) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht 5).2 (by positivity))
        (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).le
    _ = _ := by ring

theorem raw_uniform_gap (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) (delta : ℝ) (hd : 0 < delta) :
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → T < Q →
        minima A₂ A₃ L Q c₀ c₂ c₃ 1 < minima A₂ A₃ L Q c₀ c₂ c₃ 2 * Q ^ (-delta) →
        rho A₂ A₃ L Q c₀ c₂ c₃ 4 < (12 / κ) * rho A₂ A₃ L Q c₀ c₂ c₃ 5 * Q ^ (-delta) ∧
        rho A₂ A₃ L Q c₀ c₂ c₃ 4 < rho A₂ A₃ L Q c₀ c₂ c₃ 5 * Q ^ (-delta / 2) := by
  obtain ⟨_,_,κ,_,_,hk,_,hcomp⟩ := source_compound_uniform_comparison42 A₂ A₃ L h₂ h₃ hL
  obtain ⟨T,hT,hcut⟩ := literal_cutoff (12 / κ) delta hd
  refine ⟨κ,T,hk,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb hTQ hgap
  have he4 : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = minima A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have hc : ∀ j, κ * sorted (minima A₂ A₃ L Q c₀ c₂ c₃) j ≤ nu A₂ A₃ L Q c₀ c₂ c₃ j := by
    simpa only [sourcePairProducts42,he4,
      minima_eq6 A₂ A₃ L hL Q hQ c₀ c₂ c₃,sorted_equality] using
        (fun j => (hcomp Q hQ c₀ c₂ c₃ hc₂ hc₃ hb j).1)
  have hg := raw_gap_bound A₂ A₃ L hL κ Q delta hk hQ c₀ c₂ c₃ hc₂ hc₃ hc hgap
  obtain ⟨_,_,_,hp,_,_⟩ := raw_attainment A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃
  exact ⟨hg,literal_absorption _ _ (12 / κ) Q delta (hp 5) hQ (hcut Q hTQ) hg⟩

def originalMemberQ (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (x : Fin 4 → ℝ) : Prop :=
  ∃ z : Fin 4 → ℤ, (fun i => (z i : ℝ)) = x ∧
    (∀ i, (padicNorm 2 ((A₂ *ᵥ (fun j => (z j : ℚ))) i) : ℝ) ≤ Q ^ c₂ i) ∧
    ∀ i, (padicNorm 3 ((A₃ *ᵥ (fun j => (z j : ℚ))) i) : ℝ) ≤ Q ^ c₃ i

theorem originalMemberQ_iff (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (x : Fin 4 → ℝ) :
    originalMemberQ A₂ A₃ Q c₂ c₃ x ↔ realMember A₂ A₃ Q c₂ c₃ x := by
  have he2 (z : Fin 4 → ℤ) (i : Fin 4) :
      (padicNorm 2 ((A₂ *ᵥ (fun j => (z j : ℚ))) i) : ℝ) ≤ Q ^ c₂ i ↔
        padicNorm 2 ((A₂ *ᵥ (fun j => (z j : ℚ))) i) ≤ (2 : ℚ) ^ (-(threshold 2 Q (c₂ i) : ℤ)) := by
    simpa only [threshold,JSP000334.qThreshold,zpow_neg,zpow_natCast] using
      padic_rpow_ceil42 2 Q (c₂ i) hQ (hc₂ i) ((A₂ *ᵥ (fun j => (z j : ℚ))) i)
  have he3 (z : Fin 4 → ℤ) (i : Fin 4) :
      (padicNorm 3 ((A₃ *ᵥ (fun j => (z j : ℚ))) i) : ℝ) ≤ Q ^ c₃ i ↔
        padicNorm 3 ((A₃ *ᵥ (fun j => (z j : ℚ))) i) ≤ (3 : ℚ) ^ (-(threshold 3 Q (c₃ i) : ℤ)) := by
    simpa only [threshold,JSP000334.qThreshold,zpow_neg,zpow_natCast] using
      padic_rpow_ceil42 3 Q (c₃ i) hQ (hc₃ i) ((A₃ *ᵥ (fun j => (z j : ℚ))) i)
  simp only [originalMemberQ,realMember,he2,he3]

noncomputable def lambdaQ (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ u ∧
    (∀ j, originalMemberQ A₂ A₃ Q c₂ c₃ (u j)) ∧
    ∀ j, ‖fun i => (L *ᵥ u j) i / Q ^ c₀ i‖ ≤ r}

theorem lambdaQ_equality (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (k : Fin 4) :
    lambdaQ A₂ A₃ L Q c₀ c₂ c₃ k = minima A₂ A₃ L Q c₀ c₂ c₃ k := by
  simp only [lambdaQ,minima,originalMemberQ_iff A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃]

theorem expanded_source_endpoint (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) (delta : ℝ) (hd : 0 < delta) :
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → T < Q →
        lambdaQ A₂ A₃ L Q c₀ c₂ c₃ 1 < lambdaQ A₂ A₃ L Q c₀ c₂ c₃ 2 * Q ^ (-delta) →
        rho A₂ A₃ L Q c₀ c₂ c₃ 4 < (12 / κ) * rho A₂ A₃ L Q c₀ c₂ c₃ 5 * Q ^ (-delta) ∧
        rho A₂ A₃ L Q c₀ c₂ c₃ 4 < rho A₂ A₃ L Q c₀ c₂ c₃ 5 * Q ^ (-delta / 2) := by
  obtain ⟨κ,T,hk,hT,hcut,hgap⟩ := raw_uniform_gap A₂ A₃ L h₂ h₃ hL delta hd
  refine ⟨κ,T,hk,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb hTQ hg
  apply hgap Q hQ c₀ c₂ c₃ hc₂ hc₃ hb hTQ
  simpa only [lambdaQ_equality A₂ A₃ L Q hQ c₀ c₂ c₃ hc₂ hc₃] using hg


def order (a : Fin 4 → ℝ) : Equiv.Perm (Fin 6) :=
  if a 0 * a 3 ≤ a 1 * a 2 then Equiv.refl _ else Equiv.swap 2 3

def W (u : Fin 4 → Fin 4 → ℤ) (a : Fin 4 → ℝ) : Fin 6 → Fin 6 → ℤ :=
  fun j s => u (lo (order a j)) (lo s) * u (hi (order a j)) (hi s) -
    u (lo (order a j)) (hi s) * u (hi (order a j)) (lo s)

theorem W_eq (u : Fin 4 → Fin 4 → ℤ) (a : Fin 4 → ℝ) : W u a = orderedWedges42 u a := rfl

def HR (v : Fin 6 → Fin 6 → ℤ) : Submodule ℝ (Fin 6 → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : Fin 5 => fun i => (v j.castSucc i : ℝ)))

def HQ (v : Fin 6 → Fin 6 → ℤ) : Submodule ℚ (Fin 6 → ℚ) :=
  Submodule.span ℚ (Set.range (fun j : Fin 5 => fun i => (v j.castSucc i : ℚ)))

theorem raw_dimension (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ))) : Module.finrank ℝ (HR v) = 5 := by
  have hi : LinearIndependent ℝ (fun j : Fin 5 => fun i : Fin 6 => (v j.castSucc i : ℝ)) :=
    hv.comp Fin.castSucc (Fin.castSucc_injective 5)
  simpa only [HR,Fintype.card_fin] using finrank_span_eq_card hi

def g4 (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ : Fin 4 → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ‖fun i => (L *ᵥ x) i / Q ^ c₀ i‖

theorem g4_eq (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ : Fin 4 → ℝ) (x : Fin 4 → ℝ) : g4 L Q c₀ x = coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) x := rfl

def O (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 4 → ℤ) :=
  {z | (∀ i, (padicNorm 2 ((A₂ *ᵥ (fun j => (z j : ℚ))) i) : ℝ) ≤ Q ^ c₂ i) ∧
    ∀ i, (padicNorm 3 ((A₃ *ᵥ (fun j => (z j : ℚ))) i) : ℝ) ≤ Q ^ c₃ i}

theorem original_raw_mem (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (z : originalSourceGroup4 A₂ A₃ Q c₂ c₃) : (z : Fin 4 → ℤ) ∈ O A₂ A₃ Q c₂ c₃ := by
  constructor
  · intro i
    apply (padic_rpow_ceil42 2 Q (c₂ i) hQ (hc₂ i) _).mpr
    simpa only [zpow_neg,zpow_natCast] using (lattice4_spec 2 A₂ _ (z : Fin 4 → ℤ)).mp z.property.1 i
  · intro i
    apply (padic_rpow_ceil42 3 Q (c₃ i) hQ (hc₃ i) _).mpr
    simpa only [zpow_neg,zpow_natCast] using (lattice4_spec 3 A₃ _ (z : Fin 4 → ℤ)).mp z.property.2 i

def RawData (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (κ : ℝ)
    (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ) : Prop :=
  let w := W u (lambdaQ A₂ A₃ L Q c₀ c₂ c₃)
  LinearIndependent ℝ (fun j i => (u j i : ℝ)) ∧
  (∀ j, g4 L Q c₀ (fun i => (u j i : ℝ)) = lambdaQ A₂ A₃ L Q c₀ c₂ c₃ j) ∧
  LinearIndependent ℝ (fun j i => (v j i : ℝ)) ∧
  (∀ j, directGauge L Q c₀ (fun i => (v j i : ℝ)) = rho A₂ A₃ L Q c₀ c₂ c₃ j) ∧
  (∀ j, w j ∈ H A₂ A₃ Q c₂ c₃) ∧ (∀ j, w j ∈ D A₂ A₃ Q c₂ c₃) ∧
  LinearIndependent ℝ (fun j i => (w j i : ℝ)) ∧ LinearIndependent ℚ (fun j i => (w j i : ℚ)) ∧
  (∀ j, directGauge L Q c₀ (fun i => (w j i : ℝ)) ≤ 2 * sorted (lambdaQ A₂ A₃ L Q c₀ c₂ c₃) j) ∧
  (∀ i : Fin 5, directGauge L Q c₀ (fun s => (w i.castSucc s : ℝ)) ≤ (12 / κ) * rho A₂ A₃ L Q c₀ c₂ c₃ 4) ∧
  (∀ i : Fin 5, directGauge L Q c₀ (fun s => (v i.castSucc s : ℝ)) ≤ rho A₂ A₃ L Q c₀ c₂ c₃ 4) ∧
  (12 / κ) * rho A₂ A₃ L Q c₀ c₂ c₃ 4 < rho A₂ A₃ L Q c₀ c₂ c₃ 5 ∧
  Module.finrank ℝ (HR v) = 5 ∧ Module.finrank ℚ (HQ v) = 5 ∧ HR w = HR v ∧ HQ w = HQ v ∧
  w 5 = (fun s => u 2 (lo s) * u 3 (hi s) - u 2 (hi s) * u 3 (lo s))

theorem raw_data (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (κ : ℝ)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hs : sourceHyperplane42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ κ u v) :
    RawData A₂ A₃ L Q c₀ c₂ c₃ κ (fun j => (u j : Fin 4 → ℤ)) (fun j => (v j : Fin 6 → ℤ)) := by
  have he4 : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = lambdaQ A₂ A₃ L Q c₀ c₂ c₃ := by
    funext j
    exact (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃ j).trans (lambdaQ_equality A₂ A₃ L Q hQ c₀ c₂ c₃ hc₂ hc₃ j).symm
  have he6 : directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = rho A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (fun j => (rho_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃ j).symm)
  have hg6 (x : Fin 6 → ℝ) : coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) x = directGauge L Q c₀ x :=
    ((directGauge_eq L Q hQ c₀ x).trans (gauge_eq6 L hL Q hQ c₀ x)).symm
  simpa only [sourceHyperplane42,RawData,← W_eq,sourcePairProducts42,he4,he6,hg6,
    ← g4_eq L hL Q hQ c₀,membership6,direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃,
    HR,HQ,firstFiveSpan42,sorted_equality] using hs

theorem literal_uniform_endpoint (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) (delta : ℝ) (hd : 0 < delta) :
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → T < Q →
        lambdaQ A₂ A₃ L Q c₀ c₂ c₃ 1 < lambdaQ A₂ A₃ L Q c₀ c₂ c₃ 2 * Q ^ (-delta) →
        ∃ (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ),
          (∀ j, u j ∈ O A₂ A₃ Q c₂ c₃) ∧ (∀ j, v j ∈ D A₂ A₃ Q c₂ c₃) ∧
          RawData A₂ A₃ L Q c₀ c₂ c₃ κ u v := by
  obtain ⟨κ,T,hk,hT,hcut,h⟩ := source_uniform_hyperplane42 A₂ A₃ L h₂ h₃ hL delta hd
  refine ⟨κ,T,hk,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal hTQ hg
  have hg' : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 < sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta) := by
    simpa only [minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃,← lambdaQ_equality A₂ A₃ L Q hQ c₀ c₂ c₃ hc₂ hc₃] using hg
  obtain ⟨u,v,hs⟩ := h Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal hTQ hg'
  exact ⟨(fun j => (u j : Fin 4 → ℤ)),(fun j => (v j : Fin 6 → ℤ)),
    (fun j => original_raw_mem A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ (u j)),
    (fun j => (direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ _).mp (v j).property),
    raw_data A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃ κ u v hs⟩


def minors (x y : Fin 4 → ℚ) : Fin 6 → ℚ :=
  ![x 0*y 1-x 1*y 0,x 0*y 2-x 2*y 0,x 0*y 3-x 3*y 0,
    x 1*y 2-x 2*y 1,x 1*y 3-x 3*y 1,x 2*y 3-x 3*y 2]

def coefficients (f g : Module.Dual ℚ (Fin 4 → ℚ)) : Fin 6 → ℚ :=
  minors (fun i => f (Pi.single i 1)) (fun i => g (Pi.single i 1))

def exteriorFunctional (f g : Module.Dual ℚ (Fin 4 → ℚ)) : Module.Dual ℚ (Fin 6 → ℚ) :=
  ∑ s : Fin 6, coefficients f g s • LinearMap.proj s

theorem raw_minors (x y : Fin 4 → ℚ) : minors x y = CompoundFeasibility.wedge x y := by
  ext s
  fin_cases s <;> rfl

theorem raw_functional (f g : Module.Dual ℚ (Fin 4 → ℚ)) :
    exteriorFunctional f g = CompoundFeasibility.wedgeDual42 f g := by
  unfold exteriorFunctional CompoundFeasibility.wedgeDual42
  congr 1
  funext s
  rw [coefficients,raw_minors]
  rfl

theorem determinant_pairing (f g : Module.Dual ℚ (Fin 4 → ℚ)) (x y : Fin 4 → ℚ) :
    exteriorFunctional f g (minors x y) = f x * g y - f y * g x := by
  rw [raw_functional,raw_minors]
  exact CompoundFeasibility.wedgeDual42_pairing f g x y

theorem rational_duals {n : ℕ} (u : Fin n → Fin n → ℚ) (hu : LinearIndependent ℚ u) :
    ∃ D : Fin n → Module.Dual ℚ (Fin n → ℚ), ∀ i j,
      D i (u j) = if j = i then 1 else 0 :=
  ⟨CompoundFeasibility.rationalFrameDual42 u hu,
    CompoundFeasibility.rationalFrameDual42_pairing u hu⟩

theorem last_annihilator (v : Fin 6 → Fin 6 → ℚ) (hv : LinearIndependent ℚ v) :
    ∃ d : Module.Dual ℚ (Fin 6 → ℚ),
      d ≠ 0 ∧ (∀ j, d (v j) = if j = 5 then 1 else 0) ∧
      LinearMap.ker d = Submodule.span ℚ (Set.range (fun i : Fin 5 => v i.castSucc)) ∧
      ∀ f : Module.Dual ℚ (Fin 6 → ℚ), (∀ i : Fin 5, f (v i.castSucc) = 0) →
        f = f (v 5) • d :=
  ⟨CompoundFeasibility.rationalFrameDual42 v hv 5,
    CompoundFeasibility.lastDual42_nonzero v hv,
    CompoundFeasibility.rationalFrameDual42_pairing v hv 5,
    CompoundFeasibility.lastDual42_kernel v hv,
    CompoundFeasibility.functional_lastDual42 v hv⟩


def DualData (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ) (a : Fin 4 → ℝ) : Prop :=
  ∃ (U : Fin 4 → Module.Dual ℚ (Fin 4 → ℚ)) (V : Fin 6 → Module.Dual ℚ (Fin 6 → ℚ)),
    (∀ i j, U i (fun t => (u j t : ℚ)) = if j = i then 1 else 0) ∧
    (∀ i j, V i (fun t => (v j t : ℚ)) = if j = i then 1 else 0) ∧
    let f := exteriorFunctional (U 2) (U 3)
    (∀ j, f (fun t => (W u a j t : ℚ)) = if j = 5 then 1 else 0) ∧
    f ≠ 0 ∧ V 5 ≠ 0 ∧ LinearMap.ker f = HQ v ∧ LinearMap.ker (V 5) = HQ v ∧
    f (fun t => (v 5 t : ℚ)) ≠ 0 ∧ f = f (fun t => (v 5 t : ℚ)) • V 5 ∧
    Submodule.span ℚ {V 5} = Submodule.span ℚ {f} ∧
    Module.finrank ℚ (Submodule.span ℚ {V 5}) = 1

theorem raw_dual_data (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ)
    (a : Fin 4 → ℝ) (h : rationalDualLine42 u v a) : DualData u v a := by
  simpa only [rationalDualLine42,DualData,raw_functional,W_eq,HQ,firstFiveSpan42] using h

theorem literal_uniform_dual_endpoint (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → T < Q →
        lambdaQ A₂ A₃ L Q c₀ c₂ c₃ 1 < lambdaQ A₂ A₃ L Q c₀ c₂ c₃ 2 * Q ^ (-delta) →
        ∃ (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ),
          (∀ j, u j ∈ O A₂ A₃ Q c₂ c₃) ∧ (∀ j, v j ∈ D A₂ A₃ Q c₂ c₃) ∧
          RawData A₂ A₃ L Q c₀ c₂ c₃ κ u v ∧
          DualData u v (lambdaQ A₂ A₃ L Q c₀ c₂ c₃) := by
  obtain ⟨κ,T,hk,hT,hcut,h⟩ := source_uniform_dual_line42 A₂ A₃ L h₂ h₃ hL delta hd
  refine ⟨κ,T,hk,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal hTQ hg
  have he4 : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = lambdaQ A₂ A₃ L Q c₀ c₂ c₃ := by
    funext j
    exact (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃ j).trans
      (lambdaQ_equality A₂ A₃ L Q hQ c₀ c₂ c₃ hc₂ hc₃ j).symm
  have hg' : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta) := by
    simpa only [he4] using hg
  obtain ⟨u,v,hs,hd⟩ := h Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal hTQ hg'
  refine ⟨(fun j => (u j : Fin 4 → ℤ)),(fun j => (v j : Fin 6 → ℤ)),
    (fun j => original_raw_mem A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ (u j)),
    (fun j => (direct_group_equality A₂ A₃ Q hQ c₂ c₃ hc₂ hc₃ _).mp (v j).property),
    raw_data A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃ κ u v hs,?_⟩
  apply raw_dual_data
  simpa only [he4] using hd

end
#check threshold
#print axioms threshold
#check realMember
#print axioms realMember
#check minima
#print axioms minima
#check membership
#print axioms membership
#check minima_equality
#print axioms minima_equality
#check C
#print axioms C
#check E
#print axioms E
#check H
#print axioms H
#check realImage
#print axioms realImage
#check gauge
#print axioms gauge
#check nu
#print axioms nu
#check membership6
#print axioms membership6
#check image_eq6
#print axioms image_eq6
#check gauge_eq6
#print axioms gauge_eq6
#check minima_eq6
#print axioms minima_eq6
#check sorted
#print axioms sorted
#check leftIndex
#print axioms leftIndex
#check rightIndex
#print axioms rightIndex
#check sorted_equality
#print axioms sorted_equality
#check top_products
#print axioms top_products
#check summed_gap
#print axioms summed_gap
#check literal_local_inclusion
#print axioms literal_local_inclusion
#check literal_cutoff
#print axioms literal_cutoff
#check literal_absorption
#print axioms literal_absorption
#check D
#print axioms D
#check DImage
#print axioms DImage
#check direct_group_equality
#print axioms direct_group_equality
#check direct_image_equality
#print axioms direct_image_equality
#check raw_group_inclusion
#print axioms raw_group_inclusion
#check raw_full_span
#print axioms raw_full_span
#check directGauge
#print axioms directGauge
#check directGauge_eq
#print axioms directGauge_eq
#check rho
#print axioms rho
#check rho_equality
#print axioms rho_equality
#check raw_scaling
#print axioms raw_scaling
#check raw_attainment
#print axioms raw_attainment
#check raw_admissibility
#print axioms raw_admissibility
#check raw_comparison
#print axioms raw_comparison
#check raw_gap_bound
#print axioms raw_gap_bound
#check raw_uniform_gap
#print axioms raw_uniform_gap
#check originalMemberQ
#print axioms originalMemberQ
#check originalMemberQ_iff
#print axioms originalMemberQ_iff
#check lambdaQ
#print axioms lambdaQ
#check lambdaQ_equality
#print axioms lambdaQ_equality
#check expanded_source_endpoint
#print axioms expanded_source_endpoint
#check order
#print axioms order
#check W
#print axioms W
#check W_eq
#print axioms W_eq
#check HR
#print axioms HR
#check HQ
#print axioms HQ
#check raw_dimension
#print axioms raw_dimension
#check g4
#print axioms g4
#check g4_eq
#print axioms g4_eq
#check O
#print axioms O
#check original_raw_mem
#print axioms original_raw_mem
#check RawData
#print axioms RawData
#check raw_data
#print axioms raw_data
#check literal_uniform_endpoint
#print axioms literal_uniform_endpoint
#check minors
#print axioms minors
#check coefficients
#print axioms coefficients
#check exteriorFunctional
#print axioms exteriorFunctional
#check raw_minors
#print axioms raw_minors
#check raw_functional
#print axioms raw_functional
#check determinant_pairing
#print axioms determinant_pairing
#check rational_duals
#print axioms rational_duals
#check last_annihilator
#print axioms last_annihilator
#check DualData
#print axioms DualData
#check raw_dual_data
#print axioms raw_dual_data
#check literal_uniform_dual_endpoint
#print axioms literal_uniform_dual_endpoint
end DualIntegrationLiteral
