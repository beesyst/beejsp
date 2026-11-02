import SubspaceBridge.Davenport6
open scoped BigOperators Matrix
open CompoundFeasibility
namespace Davenport6Literal
noncomputable section

def first : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def second : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
def C {K : Type*} [CommRing K] (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  fun s t => A (first s) (first t) * A (second s) (second t) -
    A (first s) (second t) * A (second s) (first t)
def threshold (p : ℕ) (Q c : ℝ) : ℝ := -c * Real.log Q / Real.log p

def G (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℤ) :=
  {z | (∀ s, padicNorm 2 (∑ t, C A₂ s t * (z t : ℚ)) ≤
      ((2 : ℚ) ^ Nat.ceil (threshold 2 Q (c₂ (first s)) + threshold 2 Q (c₂ (second s))))⁻¹) ∧
    (∀ s, padicNorm 3 (∑ t, C A₃ s t * (z t : ℚ)) ≤
      ((3 : ℚ) ^ Nat.ceil (threshold 3 Q (c₃ (first s)) + threshold 3 Q (c₃ (second s))))⁻¹)}

def image (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℝ) :=
  {x | ∃ z : Fin 6 → ℤ, z ∈ G A₂ A₃ Q c₂ c₃ ∧ (fun i => (z i : ℝ)) = x}

def coords (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun s => (∑ t, C L s t * x t) / Q ^ (c₀ (first s) + c₀ (second s))

def radius (H : Set (Fin 6 → ℝ)) (f : (Fin 6 → ℝ) → (Fin 6 → ℝ)) (j : Fin 6) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
    (∀ i, v i ∈ H) ∧ ∀ i, ‖f (v i)‖ ≤ r}

def factors (rho : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  (rho 0 * rho 1 * rho 2 * rho 3 * rho 4 ^ 2) ^ ((1 : ℝ)/6) / rho (min i 4)

def flag (u : Fin 6 → (Fin 6 → ℝ)) (j : Fin 6) : Submodule ℝ (Fin 6 → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin j.val => u (Fin.castLE (by omega) i)))

def changed (f : (Fin 6 → ℝ) → (Fin 6 → ℝ)) (d : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6))
    (x : Fin 6 → ℝ) : Fin 6 → ℝ := fun i => d (sigma i) * f x i

def body (f : (Fin 6 → ℝ) → (Fin 6 → ℝ)) : Set (Fin 6 → ℝ) := {x | ∀ i, |f x i| ≤ 1}

theorem group_identity (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ)
    (z : Fin 6 → ℤ) : z ∈ G A₂ A₃ Q c₂ c₃ ↔ z ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃ := by
  change _ ↔ z ∈ directLocal42 2 A₂ _ ∧ z ∈ directLocal42 3 A₃ _
  rw [directLocal42_spec, directLocal42_spec]
  rfl

theorem image_identity (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    image A₂ A₃ Q c₂ c₃ = (integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃) : Set (Fin 6 → ℝ)) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(group_identity A₂ A₃ Q c₂ c₃ z).mp hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(group_identity A₂ A₃ Q c₂ c₃ z).mpr hz,rfl⟩

theorem coords_identity (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    coords L Q c₀ = compoundCoordinates42 L hL Q hQ c₀ := by
  funext x s
  simp only [coords, Real.rpow_add (lt_trans zero_lt_one hQ)]
  rfl

theorem radius_identity (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) j =
      directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  simp only [radius, image_identity, coords_identity L hL Q hQ c₀, directMinima42, coordinateGauge6]
  rfl

theorem changed_identity (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (d : Fin 6 → ℝ)
    (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < d i) :
    changed (coords L Q c₀) d sigma = davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) d sigma hd := by
  funext x i
  rw [davenportCoordinates6_apply]
  rw [← coords_identity L hL Q hQ c₀]
  rfl

theorem changed_radius_identity (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (d : Fin 6 → ℝ)
    (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < d i) (j : Fin 6) :
    radius (image A₂ A₃ Q c₂ c₃) (changed (coords L Q c₀) d sigma) j =
      directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ d sigma hd j := by
  rw [directDavenportMinima42_eq_inf]
  simp only [radius, image_identity, changed_identity L hL Q hQ c₀ d sigma hd, coordinateGauge6]
  rfl

theorem body_identity (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) : body e = parallelepipedBody6 e := by
  ext x
  simp only [body, Set.mem_setOf_eq, mem_parallelepipedBody6_iff, coordinateGauge6,
    pi_norm_le_iff_of_nonempty, Real.norm_eq_abs]

theorem source_comparison (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₀ : ∀ i, |c₀ i| ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (Q : ℝ) (hQ : 1 < Q)
    (u : Fin 6 → (Fin 6 → ℤ)) (huG : ∀ i, u i ∈ G A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun i => (fun t => (u i t : ℝ))))
    (hatt : ∀ i, ‖coords L Q c₀ (fun t => (u i t : ℝ))‖ =
      radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) i) :
    let H := image A₂ A₃ Q c₂ c₃
    let f := coords L Q c₀
    let rho := radius H f
    let d := factors rho
    (∀ i, 0 < d i) ∧ (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i*rho i) ∧
    ∃ sigma : Equiv.Perm (Fin 6),
      (∀ j, d j*rho j/64 ≤ radius H (changed f d sigma) j ∧
        radius H (changed f d sigma) j ≤ 64*(d j*rho j)) ∧
      MeasureTheory.volume.real (body (changed f d sigma)) = MeasureTheory.volume.real (body f) ∧
      ∀ j x, x ∈ H → x ∉ flag (fun i => (fun t => (u i t : ℝ))) j →
        d j*rho j/64 ≤ ‖changed f d sigma x‖ := by
  dsimp only
  let hU := sourceUnit42 L hL
  let v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃ :=
    fun i => ⟨u i, (group_identity A₂ A₃ Q c₂ c₃ (u i)).mp (huG i)⟩
  have hr : radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) =
      directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃ :=
    funext (radius_identity A₂ A₃ L hU Q hQ c₀ c₂ c₃)
  have ha : ∀ i, coordinateGauge6 (compoundCoordinates42 L hU Q hQ c₀)
      (integerReal (v i : Fin 6 → ℤ)) = directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃ i := by
    intro i
    simpa only [← hr, ← coords_identity L hU Q hQ c₀, coordinateGauge6] using hatt i
  obtain ⟨hd, hp, hanti, hm, sigma, hbounds, hvol, hsep⟩ :=
    source_davenport42 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₀ hc₂ hc₃ hb Q hQ v hu ha
  have hd' : ∀ i, 0 < factors (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀)) i := by
    simpa only [hr, factors, gapDeformation6, gapRadius6] using hd
  have hf : factors (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀)) =
      gapDeformation6 (directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃) := by
    rw [hr]; rfl
  have hchange : changed (coords L Q c₀)
      (factors (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀))) sigma =
      davenportCoordinates6 (compoundCoordinates42 L hU Q hQ c₀)
        (gapDeformation6 (directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃)) sigma hd := by
    simpa only [hr, factors, gapDeformation6, gapRadius6] using
      changed_identity L hU Q hQ c₀ _ sigma hd
  have hrad (j : Fin 6) : radius (image A₂ A₃ Q c₂ c₃)
      (changed (coords L Q c₀) (factors (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀))) sigma) j =
      directDavenportMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃
        (gapDeformation6 (directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃)) sigma hd j := by
    rw [hchange]
    simp only [radius, image_identity, directDavenportMinima42, successiveRadius6,
      directRealBasis42_span, coordinateGauge6]
    rfl
  refine ⟨hd', ?_, ?_, ?_, sigma, ?_, ?_, ?_⟩
  · simpa only [hf] using hp
  · simpa only [hf] using hanti
  · simpa only [hr, factors, gapDeformation6, gapRadius6] using hm
  · intro j
    rw [hrad j]
    simpa only [hr, factors, gapDeformation6, gapRadius6] using hbounds j
  · rw [hchange, coords_identity L hU Q hQ c₀, body_identity, body_identity]
    exact davenportBody6_volume (compoundCoordinates42 L hU Q hQ c₀) _ sigma hd hp
  · intro j x hx hxout
    rw [image_identity] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hs := hsep j ⟨z,hz⟩ hxout
    rw [hchange]
    simpa only [hr, factors, gapDeformation6, gapRadius6, coordinateGauge6] using hs

theorem source_constant : (64 : ℝ) ≤ 2^(36 : ℕ) * (Nat.factorial 6 : ℝ) := by norm_num [Nat.factorial]

end
end Davenport6Literal
#check Davenport6Literal.first
#print axioms Davenport6Literal.first
#check Davenport6Literal.second
#print axioms Davenport6Literal.second
#check Davenport6Literal.C
#print axioms Davenport6Literal.C
#check Davenport6Literal.threshold
#print axioms Davenport6Literal.threshold
#check Davenport6Literal.G
#print axioms Davenport6Literal.G
#check Davenport6Literal.image
#print axioms Davenport6Literal.image
#check Davenport6Literal.coords
#print axioms Davenport6Literal.coords
#check Davenport6Literal.radius
#print axioms Davenport6Literal.radius
#check Davenport6Literal.factors
#print axioms Davenport6Literal.factors
#check Davenport6Literal.flag
#print axioms Davenport6Literal.flag
#check Davenport6Literal.changed
#print axioms Davenport6Literal.changed
#check Davenport6Literal.body
#print axioms Davenport6Literal.body
#check Davenport6Literal.group_identity
#print axioms Davenport6Literal.group_identity
#check Davenport6Literal.image_identity
#print axioms Davenport6Literal.image_identity
#check Davenport6Literal.coords_identity
#print axioms Davenport6Literal.coords_identity
#check Davenport6Literal.radius_identity
#print axioms Davenport6Literal.radius_identity
#check Davenport6Literal.changed_identity
#print axioms Davenport6Literal.changed_identity
#check Davenport6Literal.changed_radius_identity
#print axioms Davenport6Literal.changed_radius_identity
#check Davenport6Literal.body_identity
#print axioms Davenport6Literal.body_identity
#check Davenport6Literal.source_comparison
#print axioms Davenport6Literal.source_comparison
#check Davenport6Literal.source_constant
#print axioms Davenport6Literal.source_constant
