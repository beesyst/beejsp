import SubspaceBridge.AnalyticReadiness6
open scoped BigOperators Matrix
open CompoundFeasibility
namespace AnalyticReady6Literal
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

def root (rho : Fin 6 → ℝ) : ℝ :=
  (rho 0*rho 1*rho 2*rho 3*rho 4^2)^((1 : ℝ)/6)

def decay (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (delta : ℝ) (v : Fin 6 → (Fin 6 → ℤ)) : Prop :=
  let H := image A₂ A₃ Q c₂ c₃
  let f := coords L Q c₀
  let rho := radius H f
  let d := factors rho
  ∃ sigma : Equiv.Perm (Fin 6),
    radius H (changed f d sigma) 4 ≤ 64*root rho ∧
    radius H (changed f d sigma) 4 < Q ^ (-delta/24) ∧
    (∀ j x, x ∈ H → x ∉ flag (fun i t => (v i t : ℝ)) j →
      d j*rho j/64 ≤ ‖changed f d sigma x‖) ∧
    ∃ w : Fin 6 → (Fin 6 → ℤ), (∀ i, w i ∈ G A₂ A₃ Q c₂ c₃) ∧
      LinearIndependent ℝ (fun i t => (w i t : ℝ)) ∧
      ∀ j, ‖changed f d sigma (fun t => (w j t : ℝ))‖ = radius H (changed f d sigma) j

theorem decay_bridge (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (delta : ℝ)
    (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (h : sourceDavenportDecay42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ delta v) :
    decay A₂ A₃ L Q c₀ c₂ c₃ delta (fun i => (v i : Fin 6 → ℤ)) := by
  obtain ⟨hd,hp,ha,hm,sigma,hbounds,hvol,hsep,hupper,hsmall,w,hw,_,_,hatt⟩ := h
  have hr : radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) =
      directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ :=
    funext (radius_identity A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have hc : changed (coords L Q c₀)
      (factors (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀))) sigma =
      davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀)
        (gapDeformation6 (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃)) sigma hd := by
    simpa only [hr, factors, gapDeformation6, gapRadius6] using changed_identity L hL Q hQ c₀ _ sigma hd
  have hrad (j : Fin 6) : radius (image A₂ A₃ Q c₂ c₃)
      (changed (coords L Q c₀) (factors (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀))) sigma) j =
      directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
        (gapDeformation6 (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃)) sigma hd j := by
    rw [hc]
    simp only [radius, image_identity, directDavenportMinima42, successiveRadius6,
      directRealBasis42_span, coordinateGauge6]
    rfl
  dsimp only [decay]
  refine ⟨sigma,?_,?_,?_,fun i => (w i : Fin 6 → ℤ),?_,hw,?_⟩
  · rw [hrad 4]
    simpa only [hr,root,gapRadius6] using hupper
  · rw [hrad 4]
    exact hsmall
  · intro j x hx hout
    rw [image_identity] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    rw [hc]
    simpa only [hr,factors,gapDeformation6,gapRadius6,coordinateGauge6] using hsep j ⟨z,hz⟩ hout
  · intro i
    exact (group_identity A₂ A₃ Q c₂ c₃ _).mpr (w i).property
  · intro j
    rw [hrad j,hc]
    exact hatt j

theorem uniform_decay (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    ∃ C₄ T : ℝ, 0 < C₄ ∧ 1 < T ∧
      (∀ Q : ℝ, T < Q → (64 : ℝ)^6*(64*C₄^3) < Q ^ (delta/4)) ∧
      ∀ (Q : ℝ) (_hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) → T < Q →
        ∀ v : Fin 6 → (Fin 6 → ℤ), (∀ i, v i ∈ G A₂ A₃ Q c₂ c₃) →
          LinearIndependent ℝ (fun i t => (v i t : ℝ)) →
          (∀ i, ‖coords L Q c₀ (fun t => (v i t : ℝ))‖ = radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) i) →
          radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) 4 <
            radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) 5 * Q ^ (-delta/2) →
          let rho := radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀)
          (0 < ∏ i, rho i) ∧ (∏ i, rho i) ≤ 64*C₄^3 ∧
            root rho^(6 : ℕ) < (64*C₄^3)*Q ^ (-delta/2) ∧ decay A₂ A₃ L Q c₀ c₂ c₃ delta v := by
  obtain ⟨C₄,T,hC,hT,hcut,hdec⟩ := source_uniform_davenport_decay42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨C₄,T,hC,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃ hb hTQ v hvG hv hatt hgap
  let hU := sourceUnit42 L hL
  let w : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃ :=
    fun i => ⟨v i,(group_identity A₂ A₃ Q c₂ c₃ _).mp (hvG i)⟩
  have hr : radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) =
      directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃ := funext (radius_identity A₂ A₃ L hU Q hQ c₀ c₂ c₃)
  have hatt' : ∀ i, coordinateGauge6 (compoundCoordinates42 L hU Q hQ c₀) (integerReal (w i : Fin 6 → ℤ)) =
      directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃ i := by
    intro i
    simpa only [← hr,← coords_identity L hU Q hQ c₀,coordinateGauge6] using hatt i
  have hgap' : directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃ 4 <
      directMinima42 A₂ A₃ L hU Q hQ c₀ c₂ c₃ 5 * Q ^ (-delta/2) := by simpa only [hr] using hgap
  obtain ⟨hp,hprod,hroot,hdecay⟩ := hdec Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃ hb hTQ w hv hatt' hgap'
  dsimp only
  refine ⟨?_,?_,?_,decay_bridge A₂ A₃ L hU Q hQ c₀ c₂ c₃ delta w hdecay⟩
  · simpa only [hr] using hp
  · simpa only [hr] using hprod
  · simpa only [hr,root,gapRadius6] using hroot

theorem unbounded_decay (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    (∀ s t, IsAlgebraic ℚ (compound L s t)) ∧
    IsUnit (compound A₂) ∧ IsUnit (compound A₃) ∧ IsUnit (compound L) ∧
    ∃ κ C₄ T : ℝ, 0 < κ ∧ 0 < C₄ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s, |pairWeights42 c₀ s| ≤ 2) ∧
        (∀ s, -2 ≤ pairWeights42 c₂ s ∧ pairWeights42 c₂ s ≤ 0) ∧
        (∀ s, -2 ≤ pairWeights42 c₃ s ∧ pairWeights42 c₃ s ≤ 0) ∧
        (∑ s, (pairWeights42 c₀ s + pairWeights42 c₂ s + pairWeights42 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hUb : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hmem : Q ∈ U),
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 1 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 2 * Q ^ (-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧
            ∃ (u : (t : V) → Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃)
              (v : (t : V) → Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃),
              ∀ t : V, T < t.val ∧
                sourceHyperplane42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property))
                  c₀ c₂ c₃ κ (u t) (v t) ∧
                rationalDualLine42 (fun i => (u t i : Fin 4 → ℤ)) (fun j => (v t j : Fin 6 → ℤ))
                  (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃) ∧
                radius (image A₂ A₃ t.val c₂ c₃) (coords L t.val c₀) 4 <
                radius (image A₂ A₃ t.val c₂ c₃) (coords L t.val c₀) 5 *
                  t.val ^ (-delta / 2) ∧
                let rho := radius (image A₂ A₃ t.val c₂ c₃) (coords L t.val c₀)
                (0 < ∏ i, rho i) ∧ (∏ i, rho i) ≤ 64*C₄^3 ∧
                  root rho^(6 : ℕ) < (64*C₄^3)*t.val ^ (-delta/2) ∧
                  decay A₂ A₃ L t.val c₀ c₂ c₃ delta (fun i => (v t i : Fin 6 → ℤ)) := by
  obtain ⟨halg,hu₂,hu₃,huL,κ,C₄,T,hk,hC,hT,hcut,hfam⟩ :=
    source_compound_unbounded_davenport_decay42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨halg,hu₂,hu₃,huL,κ,C₄,T,hk,hC,hT,hcut,?_⟩
  intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨hw₀,hw₂,hw₃,hwb,hfamily⟩ := hfam c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  refine ⟨hw₀,hw₂,hw₃,hwb,?_⟩
  intro U hUb hQU horiginal
  obtain ⟨V,hVU,hVb,u,v,hframes⟩ := hfamily U hUb hQU horiginal
  refine ⟨V,hVU,hVb,u,v,?_⟩
  intro t
  obtain ⟨hTQ,hH,hD,hG,hp,hprod,hroot,hdec⟩ := hframes t
  have hr : radius (image A₂ A₃ t.val c₂ c₃) (coords L t.val c₀) =
      directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ :=
    funext (radius_identity A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃)
  refine ⟨hTQ,hH,hD,?_,?_,?_,?_,decay_bridge A₂ A₃ L (sourceUnit42 L hL) t.val
    (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) hdec⟩
  · simpa only [hr] using hG
  · simpa only [hr] using hp
  · simpa only [hr] using hprod
  · simpa only [hr,root,gapRadius6] using hroot

def widths (Q : ℝ) (c₀ : Fin 4 → ℝ) (rho : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) : Fin 6 → ℝ :=
  fun s => Q^(c₀ (first s)+c₀ (second s))/factors rho (sigma s)

def analyticCoords (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Fin 6 → ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun s => (∑ t, C L s t*x t)/W s

def prepared (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (delta : ℝ) : Prop :=
  let rho := radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀)
  1 < Q^(11 : ℕ) ∧ ∃ sigma : Equiv.Perm (Fin 6),
    (∀ i, 0 < widths Q c₀ rho sigma i ∧ widths Q c₀ rho sigma i < Q^(11 : ℕ) ∧
      (widths Q c₀ rho sigma i)⁻¹ < Q^(11 : ℕ)) ∧
    (∀ i : Fin 6, (-1 ≤ (c₂ (first i)+c₂ (second i))/11 ∧ (c₂ (first i)+c₂ (second i))/11 ≤ 0) ∧
      (-1 ≤ (c₃ (first i)+c₃ (second i))/11 ∧ (c₃ (first i)+c₃ (second i))/11 ≤ 0)) ∧
    (∏ i, widths Q c₀ rho sigma i*(Q^(11 : ℕ))^((c₂ (first i)+c₂ (second i))/11)*
      (Q^(11 : ℕ))^((c₃ (first i)+c₃ (second i))/11)) = 1 ∧
    ∃ w : Fin 6 → (Fin 6 → ℤ), (∀ i, w i ∈ G A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11)) ∧
      LinearIndependent ℝ (fun i t => (w i t : ℝ)) ∧
      (∀ j, ‖analyticCoords L (widths Q c₀ rho sigma) (fun i => (w j i : ℝ))‖ =
        radius (image A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11))
          (analyticCoords L (widths Q c₀ rho sigma)) j) ∧
      radius (image A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11))
        (analyticCoords L (widths Q c₀ rho sigma)) 4 < (Q^(11 : ℕ))^(-(delta/264))

theorem widths_identity (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (rho : Fin 6 → ℝ)
    (sigma : Equiv.Perm (Fin 6)) : widths Q c₀ rho sigma = davenportWidths42 Q c₀ (gapDeformation6 rho) sigma := by
  funext i
  simp only [widths,davenportWidths42,Real.rpow_add (lt_trans zero_lt_one hQ),factors,gapDeformation6,gapRadius6]
  rfl

theorem rescaled_raw_group (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    G A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11) = G A₂ A₃ Q c₂ c₃ := by
  ext z
  rw [group_identity,group_identity,davenport_rescaled_group42]

theorem prepared_bridge (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (delta : ℝ)
    (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (h : sourceAnalyticReady42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ delta v) :
    prepared A₂ A₃ L Q c₀ c₂ c₃ delta := by
  obtain ⟨hd,sigma,hw,hQnew,hc₂,hc₃,hcut,hnorm,hmin,hsep,w,hwi,hatt,hsmall⟩ := h
  have hr : radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) =
      directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ := funext (radius_identity A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have hW : widths Q c₀ (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀)) sigma =
      davenportWidths42 Q c₀ (gapDeformation6 (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃)) sigma := by
    rw [hr]
    exact widths_identity Q hQ c₀ _ sigma
  have hE : analyticCoords L (widths Q c₀ (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀)) sigma) =
      weightedCoordinates6 (compoundFormEquiv42 L hL)
        (davenportWidths42 Q c₀ (gapDeformation6 (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃)) sigma) hw := by
    rw [hW]
    rfl
  have hrad (j : Fin 6) : radius (image A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11))
      (analyticCoords L (widths Q c₀ (radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀)) sigma)) j =
      successiveRadius6 (directRealBasis42 A₂ A₃ (Q^(11 : ℕ)) (fun i => c₂ i/11) (fun i => c₃ i/11))
        (weightedCoordinates6 (compoundFormEquiv42 L hL)
          (davenportWidths42 Q c₀ (gapDeformation6 (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃)) sigma) hw) j := by
    rw [hE]
    simp only [radius,image_identity,successiveRadius6,directRealBasis42_span,coordinateGauge6]
    rfl
  dsimp only [prepared]
  refine ⟨hQnew,sigma,?_,?_,?_,fun i => (w i : Fin 6 → ℤ),?_,hwi,?_,?_⟩
  · intro i
    rw [hW]
    exact ⟨hw i,(hcut i).1,(hcut i).2⟩
  · intro i
    exact ⟨hc₂ i,hc₃ i⟩
  · rw [hW]
    exact hnorm
  · intro i
    exact (group_identity A₂ A₃ _ _ _ _).mpr (w i).property
  · intro j
    rw [hrad j,hE]
    exact hatt j
  · rw [hrad 4]
    exact hsmall

theorem raw_first_last_bounds (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (Q : ℝ) (_hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
      (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) → (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) →
      1/(C*Q^(2 : ℕ)) ≤ radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) 0 ∧
      radius (image A₂ A₃ Q c₂ c₃) (coords L Q c₀) 5 ≤ K*Q^(6 : ℕ) := by
  obtain ⟨C,hC,hfirst⟩ := source_direct_first_lower42 L hL
  obtain ⟨K,hK,hlast⟩ := source_direct_last_upper42 A₂ A₃ L hL
  refine ⟨C,K,hC,hK,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃
  rw [radius_identity A₂ A₃ L hL Q hQ c₀ c₂ c₃ 0,radius_identity A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5]
  exact ⟨hfirst A₂ A₃ Q hQ c₀ c₂ c₃ hc₀,hlast Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃⟩

def parameters (U : Set ℝ) (C : ℝ) : Set ℝ :=
  {t | ∃ Q ∈ U, C < Q ∧ 1 < Q ∧ Q^(11 : ℕ) = t}

theorem parameters_identity (U : Set ℝ) (C : ℝ) : parameters U C = davenportRescaledDomain42 U C := by
  ext t
  constructor
  · rintro ⟨Q,hQU,hC,h1,rfl⟩
    exact ⟨Q,⟨hQU,hC,h1⟩,rfl⟩
  · rintro ⟨Q,⟨hQU,hC,h1⟩,rfl⟩
    exact ⟨Q,hQU,hC,h1,rfl⟩

theorem fixed_coefficients (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    (C A₂).det = 1 ∧ (C A₃).det = 1 ∧ (C L).det = 1 ∧ ∀ s t, IsAlgebraic ℚ (C L s t) := by
  have h₂c : C A₂ = compound A₂ := rfl
  have h₃c : C A₃ = compound A₃ := rfl
  have hLc : C L = compound L := rfl
  rw [h₂c,h₃c,hLc]
  exact source_compound_admissible42 A₂ A₃ L h₂ h₃ hL hAlg

theorem unbounded_prepared (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    (∀ s t, IsAlgebraic ℚ (compound L s t)) ∧
    IsUnit (compound A₂) ∧ IsUnit (compound A₃) ∧ IsUnit (compound L) ∧
    ∃ κ C₄ C K T : ℝ, 0 < κ ∧ 0 < C₄ ∧ 0 < C ∧ 0 < K ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        (∀ s, |pairWeights42 c₀ s| ≤ 2) ∧
        (∀ s, -2 ≤ pairWeights42 c₂ s ∧ pairWeights42 c₂ s ≤ 0) ∧
        (∀ s, -2 ≤ pairWeights42 c₃ s ∧ pairWeights42 c₃ s ≤ 0) ∧
        (∑ s, (pairWeights42 c₀ s + pairWeights42 c₂ s + pairWeights42 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hUb : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hmem : Q ∈ U),
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 1 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hmem) c₀ c₂ c₃ 2 * Q ^ (-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧ ¬ BddAbove (parameters V T) ∧
            ∃ (u : (t : V) → Fin 4 → originalSourceGroup4 A₂ A₃ t.val c₂ c₃)
              (v : (t : V) → Fin 6 → directCompoundGroup42 A₂ A₃ t.val c₂ c₃),
              ∀ t : V, T < t.val ∧
                sourceHyperplane42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property))
                  c₀ c₂ c₃ κ (u t) (v t) ∧
                rationalDualLine42 (fun i => (u t i : Fin 4 → ℤ)) (fun j => (v t j : Fin 6 → ℤ))
                  (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃) ∧
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 4 <
                directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ 5 *
                  t.val ^ (-delta / 2) ∧
                let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) t.val
                  (hQU t.val (hVU t.property)) c₀ c₂ c₃
                (0 < ∏ i, rho i) ∧ (∏ i, rho i) ≤ 64*C₄^3 ∧
                  gapRadius6 rho^(6 : ℕ) < (64*C₄^3)*t.val ^ (-delta/2) ∧
                  sourceDavenportDecay42 A₂ A₃ L (sourceUnit42 L hL) t.val
                    (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) ∧
                  1/(C*t.val^(2 : ℕ)) ≤ rho 0 ∧ rho 5 ≤ K*t.val^(6 : ℕ) ∧
                  (∀ sigma : Equiv.Perm (Fin 6), ∀ i,
                    davenportWidths42 t.val c₀ (gapDeformation6 rho) sigma i ≤ C*K*t.val^(10 : ℕ) ∧
                    (davenportWidths42 t.val c₀ (gapDeformation6 rho) sigma i)⁻¹ ≤ C*K*t.val^(10 : ℕ)) ∧
                  prepared A₂ A₃ L t.val c₀ c₂ c₃ delta := by
  obtain ⟨halg,hu₂,hu₃,huL,κ,C₄,C,K,T,hk,hC₄,hC,hK,hT,hcut,hfam⟩ :=
    source_compound_unbounded_analytic_ready42 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨halg,hu₂,hu₃,huL,κ,C₄,C,K,T,hk,hC₄,hC,hK,hT,hcut,?_⟩
  intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨hw₀,hw₂,hw₃,hwb,hfamily⟩ := hfam c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  refine ⟨hw₀,hw₂,hw₃,hwb,?_⟩
  intro U hUb hQU horiginal
  obtain ⟨V,hVU,hVb,hNb,u,v,hframes⟩ := hfamily U hUb hQU horiginal
  refine ⟨V,hVU,hVb,?_,u,v,?_⟩
  · rw [parameters_identity]
    exact hNb
  · intro t
    obtain ⟨hTQ,hH,hD,hgap,hp,hprod,hroot,hdec,hfirst,hlast,hpoly,hready⟩ := hframes t
    exact ⟨hTQ,hH,hD,hgap,hp,hprod,hroot,hdec,hfirst,hlast,hpoly,
      prepared_bridge A₂ A₃ L (sourceUnit42 L hL) t.val (hQU t.val (hVU t.property)) c₀ c₂ c₃ delta (v t) hready⟩

end
end AnalyticReady6Literal
#check AnalyticReady6Literal.first
#print axioms AnalyticReady6Literal.first
#check AnalyticReady6Literal.second
#print axioms AnalyticReady6Literal.second
#check AnalyticReady6Literal.C
#print axioms AnalyticReady6Literal.C
#check AnalyticReady6Literal.threshold
#print axioms AnalyticReady6Literal.threshold
#check AnalyticReady6Literal.G
#print axioms AnalyticReady6Literal.G
#check AnalyticReady6Literal.image
#print axioms AnalyticReady6Literal.image
#check AnalyticReady6Literal.coords
#print axioms AnalyticReady6Literal.coords
#check AnalyticReady6Literal.radius
#print axioms AnalyticReady6Literal.radius
#check AnalyticReady6Literal.factors
#print axioms AnalyticReady6Literal.factors
#check AnalyticReady6Literal.flag
#print axioms AnalyticReady6Literal.flag
#check AnalyticReady6Literal.changed
#print axioms AnalyticReady6Literal.changed
#check AnalyticReady6Literal.body
#print axioms AnalyticReady6Literal.body
#check AnalyticReady6Literal.group_identity
#print axioms AnalyticReady6Literal.group_identity
#check AnalyticReady6Literal.image_identity
#print axioms AnalyticReady6Literal.image_identity
#check AnalyticReady6Literal.coords_identity
#print axioms AnalyticReady6Literal.coords_identity
#check AnalyticReady6Literal.radius_identity
#print axioms AnalyticReady6Literal.radius_identity
#check AnalyticReady6Literal.changed_identity
#print axioms AnalyticReady6Literal.changed_identity
#check AnalyticReady6Literal.changed_radius_identity
#print axioms AnalyticReady6Literal.changed_radius_identity
#check AnalyticReady6Literal.body_identity
#print axioms AnalyticReady6Literal.body_identity
#check AnalyticReady6Literal.source_comparison
#print axioms AnalyticReady6Literal.source_comparison
#check AnalyticReady6Literal.source_constant
#print axioms AnalyticReady6Literal.source_constant
#check AnalyticReady6Literal.root
#print axioms AnalyticReady6Literal.root
#check AnalyticReady6Literal.decay
#print axioms AnalyticReady6Literal.decay
#check AnalyticReady6Literal.decay_bridge
#print axioms AnalyticReady6Literal.decay_bridge
#check AnalyticReady6Literal.uniform_decay
#print axioms AnalyticReady6Literal.uniform_decay
#check AnalyticReady6Literal.unbounded_decay
#print axioms AnalyticReady6Literal.unbounded_decay
#check AnalyticReady6Literal.widths
#print axioms AnalyticReady6Literal.widths
#check AnalyticReady6Literal.analyticCoords
#print axioms AnalyticReady6Literal.analyticCoords
#check AnalyticReady6Literal.prepared
#print axioms AnalyticReady6Literal.prepared
#check AnalyticReady6Literal.widths_identity
#print axioms AnalyticReady6Literal.widths_identity
#check AnalyticReady6Literal.rescaled_raw_group
#print axioms AnalyticReady6Literal.rescaled_raw_group
#check AnalyticReady6Literal.prepared_bridge
#print axioms AnalyticReady6Literal.prepared_bridge
#check AnalyticReady6Literal.raw_first_last_bounds
#print axioms AnalyticReady6Literal.raw_first_last_bounds
#check AnalyticReady6Literal.parameters
#print axioms AnalyticReady6Literal.parameters
#check AnalyticReady6Literal.parameters_identity
#print axioms AnalyticReady6Literal.parameters_identity
#check AnalyticReady6Literal.fixed_coefficients
#print axioms AnalyticReady6Literal.fixed_coefficients
#check AnalyticReady6Literal.unbounded_prepared
#print axioms AnalyticReady6Literal.unbounded_prepared
