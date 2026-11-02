import SubspaceBridge.SchmidtParameters6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSchmidtParameters6
open SourceNormalIndex SourceWeights Auxiliary6 SourceMultiblock SourceMixed6 SourceHeightBounds6
open SourceNormalHeight SourceProper6 SourceMinorIntegration6 SourceLocalUpperIntegration6 SourceFieldLower6
open SourceFieldLowerIntegration6 SourceHeightUpper6 SourceHeightEnvelopes6
open Auxiliary6.SourceExpansion Auxiliary6.SourceBalance Auxiliary6.SourceVanishing
open Auxiliary6.SourceGrid Auxiliary6.SourceEvaluation

open SourceHeightIntegration6 SourceBlocks SourceLocalUpper6

open SourceReadiness6 SchmidtParameters6

def auxiliaryPolynomialData6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (K : IntermediateField ℚ ℝ)
    (hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K) (D E : ℝ)
    (m : ℕ) (eta : ℝ) (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) ℤ) : Prop :=
  P ≠ 0 ∧ homogeneous6 r P ∧ (height6 P : ℝ) ≤ D^(∑ h, r h) ∧
        FieldIndex A2 A3 L K hmem r eta P ∧ RealIndex A2 A3 L r eta P ∧
        (Claims r eta (compound L) P ∧ Claims r eta (finiteMatrix 2 A2) P ∧
          Claims r eta (finiteMatrix 3 A3) P) ∧
        (∀ J b : Vars6 m →₀ ℕ,
          ‖(expansion (compound L) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
          ‖(expansion (finiteMatrix 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
          ‖(expansion (finiteMatrix 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) ∧
        (∀ (Q : Fin m → ℝ), (∀ h,1<Q h) → ∀ h0 : Fin m,
          ∀ delta : ℝ, 1728*eta<delta → delta<1 →
          (∀ h,64*E<(Q h)^eta) → (∀ h,6*(eta⁻¹+1)<(Q h)^eta) →
          (∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0))) →
          ∀ c : Fin 3 → Fin 6 → ℝ, (∀ tau i,|c tau i|≤1) → (∑ tau,∑ i,c tau i)=0 →
          ∀ w : Fin m → Fin 5 → Fin 6 → ℤ,
          (∀ h j i,‖(compound L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta)) →
          (∀ h j i,‖(finiteMatrix 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i)) →
          (∀ h j i,‖(finiteMatrix 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i)) →
          ∀ a : Fin m → Fin 5 → ℕ, (∀ h j,1≤a h j ∧ a h j≤Nat.floor eta⁻¹+1) →
          ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J<2*eta*m →
          integerValue J P (gridPoint w a)=0)

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

def sourceAlpha6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) : ℝ :=
  heightAlpha6 R.delta (Module.finrank ℚ R.K)

def sourceQ6 {m : ℕ} (t : Fin m → V) (h : Fin m) : ℝ := (t h).val^(11 : ℕ)

def sourceH6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    {m : ℕ} (t : Fin m → V) (h : Fin m) : ℝ := max 1 (normalHeight6 (R.M (t h)) : ℝ)

def sourceCutoff6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (m : ℕ) (eta theta gamma : ℝ) : ℝ :=
  originalCutoff6 (sourceHeightCutoff6 L R.C R.delta) m eta (sourceAlpha6 R)
    (JSP000334.omega65 m theta) gamma R.D R.E

structure SchmidtPackage6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (s : MixedIndex6) where
  ready : R.nonzeroReady s
  eta : ℝ
  theta : ℝ
  m : ℕ
  eta_eq : eta = R.delta/3456
  theta_eq : theta = eta/2
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  eta_slack : 1728*eta < R.delta
  m_pos : 0 < m
  m_auxiliary : 4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ R.K : ℝ)) ≤ (m : ℝ)
  theta_pos : 0 < theta
  theta_lt : theta < 1/12
  theta_index : theta < (m : ℝ)*eta
  omega_pos : 0 < JSP000334.omega65 m theta
  gamma : ℝ
  gamma_pos : 0 < gamma
  gamma_le_five : gamma ≤ 5
  gamma_compatible : 6*gamma*(1+eta) ≤ sourceAlpha6 R
  t : Fin m → V
  member : ∀ h, (t h).val ∈ nonzeroFamily6 A2 A3 L V R.M s
  monotone : StrictMono (fun h => (t h).val)
  finite : Set.Finite (Set.range t)
  above_cutoff : ∀ h, sourceCutoff6 R m eta theta gamma < (t h).val
  source_points : ∀ h, R.restrictedPoint s ⟨(t h).val,member h⟩
  growth : ∀ h, 1 < sourceQ6 t h ∧ 64*R.E < (sourceQ6 t h)^eta ∧
    6*(eta⁻¹+1) < (sourceQ6 t h)^eta
  log_separation : ∀ (h : Fin m) (hh : h.val+1 < m),
    (1+eta)*Real.log (sourceQ6 t h) ≤
      JSP000334.omega65 m theta*Real.log (sourceQ6 t ⟨h.val+1,hh⟩)
  r : Fin m → ℕ
  degrees_pos : ∀ h, 0 < r h
  degrees_separation : ∀ (h : Fin m) (hh : h.val+1 < m),
    (r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(r h : ℝ)
  degree_balance : ∀ h,
    (r ⟨0,m_pos⟩ : ℝ)*Real.log (sourceQ6 t ⟨0,m_pos⟩) ≤ (r h : ℝ)*Real.log (sourceQ6 t h) ∧
    (r h : ℝ)*Real.log (sourceQ6 t h) ≤ (1+eta)*((r ⟨0,m_pos⟩ : ℝ)*Real.log (sourceQ6 t ⟨0,m_pos⟩))
  degree_sum : ((∑ h, r h : ℕ) : ℝ) ≤ (m : ℝ)*(1+eta)*(r ⟨0,m_pos⟩ : ℝ)
  envelopes : ∀ h, (sourceQ6 t h)^(sourceAlpha6 R) ≤ sourceH6 R t h ∧
    sourceH6 R t h ≤ (sourceQ6 t h)^(6 : ℝ)
  normal_height_convention : ∀ h, sourceH6 R t h = (normalHeight6 (R.M (t h)) : ℝ)
  height_comparison : ∀ h, (sourceH6 R t ⟨0,m_pos⟩)^(gamma*(r ⟨0,m_pos⟩ : ℝ)) ≤ (sourceH6 R t h)^(r h)
  normal_budget : ∀ h, (2 : ℝ)^(75*m) ≤ (sourceH6 R t h)^(JSP000334.omega65 m theta*gamma)
  P : MvPolynomial (Vars6 m) ℤ
  auxiliary : auxiliaryPolynomialData6 A2 A3 L R.K R.hmem R.D R.E m eta r P
  grid : ∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
    ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
      integerValue J P (gridPoint (fun h j => (R.w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0
  kernels : ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
    (∀ y : Fin m → Fin 6 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm6 (R.M (t h)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℚ))) = 0) ∧
    (∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (R.M (t h)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℝ))) = 0)
  high_index : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (fun h => R.M (t h)) r ((m : ℝ)*eta)
  polynomial_height_convention : max 1 (height6 P : ℝ) = (height6 P : ℝ)
  polynomial_budget : (height6 P : ℝ)^(25 : ℕ) ≤
    (sourceH6 R t ⟨0,m_pos⟩)^(JSP000334.omega65 m theta*gamma*(r ⟨0,m_pos⟩ : ℝ))

theorem construct_schmidt_package6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (s : MixedIndex6) (hready : R.nonzeroReady s) : Nonempty (SchmidtPackage6 R s) := by
  have hreadyKeep := hready
  obtain ⟨hs,hu,hsub,hpoints,haux,hcof,T,hT,hT1,henv,hfar⟩ := hready
  obtain ⟨eta,theta,m,hee,hte,he,he1,hed,hm,hmb,ht,ht1,htm,ho⟩ :=
    eta_m_theta6 R.delta R.delta_pos R.delta_lt_one R.K
  have ha : 0 < sourceAlpha6 R := heightAlpha6_pos R.delta R.delta_pos _
  obtain ⟨gamma,hg,hg5,hcompat,hcompat'⟩ := positive_gamma6 (sourceAlpha6 R) eta ha he
  let omega := JSP000334.omega65 m theta
  let cut := sourceCutoff6 R m eta theta gamma
  obtain ⟨u,huMono,hfinite,hgrowth,hsep⟩ := original_blocks_cutoff6
    (nonzeroFamily6 A2 A3 L V R.M s) hu cut eta R.E omega he R.E_ge_one ho m
  let t : Fin m → V := fun h => nonzeroFamily6_lift A2 A3 L V R.M s (u h)
  have hmember (h) : (t h).val ∈ nonzeroFamily6 A2 A3 L V R.M s := (u h).property
  have hmono : StrictMono (fun h => (t h).val) := huMono
  have hQ (h) : 1 < sourceQ6 t h := (hgrowth h).2.1
  have hcut (h) := cutoff_budgets6 (sourceHeightCutoff6 L R.C R.delta) m eta
    (sourceAlpha6 R) omega gamma R.D R.E (t h).val ha ho hg (hgrowth h).1
  have henvActual (h) : (sourceQ6 t h)^(sourceAlpha6 R) ≤ sourceH6 R t h ∧
      sourceH6 R t h ≤ (sourceQ6 t h)^(6 : ℝ) := by
    exact henv (u h) (by rw [hT]; exact (hcut h).1)
  have hQmono : Monotone (sourceQ6 t) := by
    intro i j hij
    exact pow_le_pow_left₀ (by linarith [hQV (t i).val (t i).property]) (hmono.monotone hij) 11
  obtain ⟨r,hr,hrsep,hrbal,hrsum⟩ := anchored_degrees6 m hm eta omega he ho
    (sourceQ6 t) hQ hQmono hsep
  have hcompare := height_comparison6 m hm (sourceAlpha6 R) gamma ha hg hcompat'
    (sourceQ6 t) (sourceH6 R t) hQ henvActual r (fun h => (hrbal h).1)
  have hnormal (h) := normal_budget6 m (sourceAlpha6 R) omega gamma
    (sourceQ6 t h) (sourceH6 R t h) ho hg (hQ h) (henvActual h).1 (hcut h).2.2.1
  obtain ⟨P,hP,hhom,hheight,hfield,hreal,hclaims,hcfs,hvan⟩ := R.construct eta he m hmb r hr
  have hgrid := hvan (sourceQ6 t) hQ ⟨0,hm⟩ R.delta hed R.delta_lt_one
    (fun h => (hgrowth h).2.2.1) (fun h => (hgrowth h).2.2.2)
    hrbal R.c R.weights_bounded R.weights_balance
    (fun h j => (R.w (t h) j.castSucc : Fin 6 → ℤ))
    (fun h => (R.frames (t h)).2.2.2.2.1)
    (fun h => (R.frames (t h)).2.2.2.2.2.1)
    (fun h => (R.frames (t h)).2.2.2.2.2.2)
  obtain ⟨hkernels,hindex⟩ := integer_grid_high_normal_index6 r hr P hhom
    (fun h j => (R.w (t h) j.castSucc : Fin 6 → ℤ)) (fun h => R.M (t h))
    (fun h => (R.normals (t h)).1) (fun h => (R.normals (t h)).2.2.2.2.1)
    (fun h => (R.normals (t h)).2.2.2.2.2) eta he hgrid
  have hpoly := polynomial_budget6 m (r ⟨0,hm⟩) (∑ h, r h) eta (sourceAlpha6 R) omega gamma
    R.D (sourceQ6 t ⟨0,hm⟩) (sourceH6 R t ⟨0,hm⟩) (height6 P : ℝ)
    ho hg R.D_ge_one (hQ _) (henvActual _).1 (Nat.cast_nonneg _) hheight hrsum (hcut ⟨0,hm⟩).2.2.2
  exact ⟨{
    ready := hreadyKeep, eta := eta, theta := theta, m := m, eta_eq := hee, theta_eq := hte,
    eta_pos := he, eta_lt_one := he1, eta_slack := hed, m_pos := hm, m_auxiliary := hmb,
    theta_pos := ht, theta_lt := ht1, theta_index := htm, omega_pos := ho,
    gamma := gamma, gamma_pos := hg, gamma_le_five := hg5, gamma_compatible := hcompat,
    t := t, member := hmember, monotone := hmono, finite := Set.finite_range t,
    above_cutoff := fun h => (hgrowth h).1,
    source_points := fun h => R.restrict_point s hs ⟨(t h).val,hmember h⟩,
    growth := fun h => (hgrowth h).2, log_separation := hsep,
    r := r, degrees_pos := hr, degrees_separation := hrsep, degree_balance := hrbal, degree_sum := hrsum,
    envelopes := henvActual,
    normal_height_convention := fun h => normal_height_convention6 _ (R.normals (t h)).1,
    height_comparison := hcompare, normal_budget := hnormal, P := P,
    auxiliary := ⟨hP,hhom,hheight,hfield,hreal,hclaims,hcfs,hvan⟩,
    grid := hgrid, kernels := hkernels, high_index := hindex,
    polynomial_height_convention := polynomial_height_convention6 P hP,
    polynomial_budget := hpoly }⟩

structure SchmidtSourceResult42
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) where
  branches : (∃ s, Nonempty (SchmidtPackage6 R s)) ∨
    (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      actualNormProduct6 A2 A3 L (R.M q) s = 0)

theorem source_schmidt_parameters42
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    Nonempty (SchmidtSourceResult42 R) := by
  rcases R.branches with ⟨s,hready⟩ | hz
  · exact ⟨⟨Or.inl ⟨s,construct_schmidt_package6 R s hready⟩⟩⟩
  · exact ⟨⟨Or.inr hz⟩⟩

def SchmidtSourceResult42.readiness
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV}
    (_S : SchmidtSourceResult42 R) : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV := R

theorem SchmidtSourceResult42.readiness_eq
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV}
    (S : SchmidtSourceResult42 R) : S.readiness = R := rfl

theorem SchmidtSourceResult42.height_projection
    {R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV}
    (S : SchmidtSourceResult42 R) : sourceHeightEnvelopeReduction42 A2 A3 L hL c0 c2 c3 V hQV :=
  S.readiness.height_projection

end CompoundFeasibility.SourceSchmidtParameters6
