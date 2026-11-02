import SubspaceBridge.SourceHeightIntegration6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceReadiness6
open SourceNormalIndex SourceWeights Auxiliary6 SourceMultiblock SourceMixed6 SourceHeightBounds6
open SourceNormalHeight SourceProper6 SourceMinorIntegration6 SourceLocalUpperIntegration6 SourceFieldLower6
open SourceFieldLowerIntegration6 SourceHeightUpper6 SourceHeightEnvelopes6
open Auxiliary6.SourceExpansion Auxiliary6.SourceBalance Auxiliary6.SourceVanishing
open Auxiliary6.SourceGrid Auxiliary6.SourceEvaluation

open SourceHeightIntegration6 SourceBlocks SourceLocalUpper6

def universalAuxiliary6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (K : IntermediateField ℚ ℝ)
    (hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K) (D E : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars6 m) ℤ,
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

def sourceFrames6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q) (delta6 : ℝ) (c : Fin 3 → Fin 6 → ℝ)
    (sigma : V → Equiv.Perm (Fin 6))
    (hW : ∀ (q : V) i, 0 < actualWidths A2 A3 L hL q.val
      (hQV q.val q.property) c0 c2 c3 (sigma q) i)
    (w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3) (q : V) : Prop :=
      let W := actualWidths A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 (sigma q)
      let b := directRealBasis42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)
      let e := weightedCoordinates6 (compoundFormEquiv42 L hL) W (hW q)
      LinearIndependent ℝ (fun j => integerReal (w q j : Fin 6 → ℤ)) ∧
      LinearIndependent ℚ (fun j : Fin 5 => fun i => ((w q j.castSucc : Fin 6 → ℤ) i : ℚ)) ∧
      directCompoundGroup42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11) =
        directCompoundGroup42 A2 A3 q.val c2 c3 ∧
      (∀ j, coordinateGauge6 e (integerReal (w q j : Fin 6 → ℤ)) = successiveRadius6 b e j) ∧
      (∀ j : Fin 5, ∀ i, ‖(compound L *ᵥ integerReal (w q j.castSucc : Fin 6 → ℤ)) i‖ ≤
        (q.val^(11 : ℕ))^(c 0 i-delta6)) ∧
      (∀ j : Fin 5, ∀ i, ‖(finiteMatrix 2 A2 *ᵥ
        (fun k => ((w q j.castSucc : Fin 6 → ℤ) k : ℚ_[2]))) i‖ ≤ (q.val^(11 : ℕ))^(c 1 i)) ∧
      (∀ j : Fin 5, ∀ i, ‖(finiteMatrix 3 A3 *ᵥ
        (fun k => ((w q j.castSucc : Fin 6 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^(11 : ℕ))^(c 2 i))

def sourceNormals6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
    (M a : V → Fin 6 → ℤ) (q : V) : Prop :=
  M q ≠ 0 ∧ (∑ i, a q i*M q i) = 1 ∧
      Ideal.span (Set.range (M q)) = ⊤ ∧
      (∀ j : Fin 5, (∑ i, M q i*(w q j.castSucc : Fin 6 → ℤ) i) = 0) ∧
      LinearMap.ker (normalForm6 (M q)) =
        firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) ∧
      LinearMap.ker (realNormalForm6 (M q)) =
        firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℝ))

structure SourceReadiness42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (delta4 : ℝ) (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q) where
  unbounded : ¬ BddAbove V
  delta : ℝ
  delta_eq : delta = selectionSlack delta4
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  c : Fin 3 → Fin 6 → ℝ
  weights_bounded : ∀ tau i, |c tau i| ≤ 1
  weights_balance : (∑ tau, ∑ i, c tau i) = 0
  finite_weights : ∀ i, c 1 i = finiteWeight c2 i ∧ c 2 i = finiteWeight c3 i
  sigma : V → Equiv.Perm (Fin 6)
  widths_pos : ∀ (q : V) i, 0 < actualWidths A2 A3 L hL q.val
    (hQV q.val q.property) c0 c2 c3 (sigma q) i
  w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3
  q0 : V
  anchor : ∀ i, c 0 i = logWeight (q0.val^(11 : ℕ))
    (actualWidths A2 A3 L hL q0.val (hQV q0.val q0.property) c0 c2 c3 (sigma q0) i)
  frames : ∀ q, sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV delta c sigma widths_pos w q
  M : V → Fin 6 → ℤ
  a : V → Fin 6 → ℤ
  normals : ∀ q, sourceNormals6 A2 A3 c2 c3 V w M a q
  minors : ∀ q : V, minorNormalization6 (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q) ∧
    actualTransformedCofactors6 A2 A3 L (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q)
  upper : ∀ (q : V) s, s ∈ admissibleMixed6 c (delta/2) →
    actualNormProduct6 A2 A3 L (M q) s ≤ 120*(q.val^(11 : ℕ))^(-delta/8)
  mixed : (∃ s ∈ admissibleMixed6 c (delta/2), ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s)) ∨
    (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 c (delta/2),
      actualNormProduct6 A2 A3 L (M q) s = 0)
  K : IntermediateField ℚ ℝ
  finite_dimensional : FiniteDimensional ℚ K
  hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K
  cofactors_mem : ∀ i j, cofactor6 (compound L) i j ∈ K
  C : ℝ
  C_pos : 0 < C
  lower : ∀ (q : V) s, actualNonzero6 A2 A3 L (M q) s →
    C ≤ actualNormProduct6 A2 A3 L (M q) s*(max 1 (normalHeight6 (M q) : ℝ))^(Module.finrank ℚ K+1) ∧
    C ≤ actualNormProduct6 A2 A3 L (M q) s*(max 1 (normalHeight6 (M q) : ℝ))^(3*Module.finrank ℚ K-1)
  envelopes : heightEnvelopeBranch6 A2 A3 L V M c delta K C
  D : ℝ
  E : ℝ
  D_ge_one : 1 ≤ D
  E_ge_one : 1 ≤ E
  auxiliary : universalAuxiliary6 A2 A3 L K hmem D E

theorem fixed_family_readiness42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c0 c2 c3 : Fin 4 → ℝ) (delta4 : ℝ) (V : Set ℝ)
    (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hf : fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V hQV) :
    Nonempty (SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V hQV) := by
  obtain ⟨_,epsilon,delta,_,hdelta,_,hd,hd1,_,c,hc,hbal,hfin,sigma,hW,w,q0,hanchor,hframe⟩ := hf
  have hw : ∀ q, sourceFrames6 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V hQV delta c sigma hW w q := by
    intro q
    obtain ⟨_,_,_,_,hli,hlq,hgroup,hatt,_,hw0,hw2,hw3⟩ := hframe q
    exact ⟨hli,hlq,hgroup,hatt,hw0,hw2,hw3⟩
  obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ :=
    source_auxiliary6_grid_vanishing A2 A3 L h2 h3 hL hAlg
  letI : FiniteDimensional ℚ K := hK
  have hex (q : V) := primitive_normal6 (fun j => (w q j : Fin 6 → ℤ))
    ((integer6_independent_iff42 _).mpr (hw q).1)
  choose M a hM ha hspan hann hker using hex
  have hn : ∀ q, sourceNormals6 A2 A3 c2 c3 V w M a q := by
    intro q
    exact ⟨hM q,ha q,hspan q,hann q,hker q,
      real_normal_kernel6 _ (hw q).1 _ (hM q) (hann q)⟩
  have hminor (q : V) : minorNormalization6 (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q) ∧
      actualTransformedCofactors6 A2 A3 L (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q) := by
    have hv := (integer6_independent_iff42 (fun j => (w q j : Fin 6 → ℤ))).mpr (hw q).1
    exact ⟨primitive_minor_data6 _ hv (M q) (a q) (hM q) (ha q) (hann q),
      actual_primitive_transformed6 A2 A3 L _ hv (M q) (a q) (hM q) (ha q) (hann q)⟩
  have hu (q : V) (s : MixedIndex6) (hs : s ∈ admissibleMixed6 c (delta/2)) :
      actualNormProduct6 A2 A3 L (M q) s ≤ 120*(q.val^(11 : ℕ))^(-delta/8) := by
    rcases hw q with ⟨_,_,_,_,hR,hp2,hp3⟩
    exact (actual_mixed_upper6 A2 A3 L (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q)
      (hminor q).1 (hminor q).2 (q.val^(11 : ℕ)) delta
      (one_lt_pow₀ (hQV q.val q.property) (by decide)) hd c hbal hR hp2 hp3 s hs).2.le
  have hb := finite_mixed_reduction6 A2 A3 L V M c (delta/2)
  obtain ⟨C,hC,hlower⟩ := actual_mixed_field_lower6 K A2 A3 L hmem
  have he := source_height_branch6 A2 A3 L (sourceUnit42 L hL) V hQV delta hd c hc
    (fun q j => (w q j : Fin 6 → ℤ)) M a (fun q => (hminor q).1)
    (fun q => (hw q).2.2.2.2.1) hu hb K C hC (fun q s hs => (hlower (M q) s hs).1)
  exact ⟨{
    unbounded := hV, delta := delta, delta_eq := hdelta, delta_pos := hd, delta_lt_one := hd1,
    c := c, weights_bounded := hc, weights_balance := hbal, finite_weights := hfin,
    sigma := sigma, widths_pos := hW, w := w, q0 := q0, anchor := hanchor, frames := hw,
    M := M, a := a, normals := hn, minors := hminor, upper := hu, mixed := hb,
    K := K, finite_dimensional := hK, hmem := hmem,
    cofactors_mem := actual_cofactor_mem6 K A2 A3 L hmem,
    C := C, C_pos := hC, lower := fun q s hs => hlower (M q) s hs, envelopes := he,
    D := D, E := E, D_ge_one := hD, E_ge_one := hE, auxiliary := haux }⟩

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem SourceReadiness42.construct
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (eta : ℝ) (he : 0 < eta) (m : ℕ)
    (hm : 4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ R.K : ℝ)) ≤ (m : ℝ))
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) :
  ∃ P : MvPolynomial (Vars6 m) ℤ,
        P ≠ 0 ∧ homogeneous6 r P ∧ (height6 P : ℝ) ≤ R.D^(∑ h, r h) ∧
        FieldIndex A2 A3 L R.K R.hmem r eta P ∧ RealIndex A2 A3 L r eta P ∧
        (Claims r eta (compound L) P ∧ Claims r eta (finiteMatrix 2 A2) P ∧
          Claims r eta (finiteMatrix 3 A3) P) ∧
        (∀ J b : Vars6 m →₀ ℕ,
          ‖(expansion (compound L) J P).coeff b‖ ≤ R.E^(∑ h, r h) ∧
          ‖(expansion (finiteMatrix 2 A2) J P).coeff b‖ ≤ R.E^(∑ h, r h) ∧
          ‖(expansion (finiteMatrix 3 A3) J P).coeff b‖ ≤ R.E^(∑ h, r h)) ∧
        (∀ (Q : Fin m → ℝ), (∀ h,1<Q h) → ∀ h0 : Fin m,
          ∀ delta : ℝ, 1728*eta<delta → delta<1 →
          (∀ h,64*R.E<(Q h)^eta) → (∀ h,6*(eta⁻¹+1)<(Q h)^eta) →
          (∀ h,(r h0 : ℝ)*Real.log (Q h0)≤(r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h)≤(1+eta)*((r h0 : ℝ)*Real.log (Q h0))) →
          ∀ c : Fin 3 → Fin 6 → ℝ, (∀ tau i,|c tau i|≤1) → (∑ tau,∑ i,c tau i)=0 →
          ∀ w : Fin m → Fin 5 → Fin 6 → ℤ,
          (∀ h j i,‖(compound L *ᵥ (fun k => (w h j k : ℝ))) i‖≤(Q h)^(c 0 i-delta)) →
          (∀ h j i,‖(finiteMatrix 2 A2 *ᵥ (fun k => (w h j k : ℚ_[2]))) i‖≤(Q h)^(c 1 i)) →
          (∀ h j i,‖(finiteMatrix 3 A3 *ᵥ (fun k => (w h j k : ℚ_[3]))) i‖≤(Q h)^(c 2 i)) →
          ∀ a : Fin m → Fin 5 → ℕ, (∀ h j,1≤a h j ∧ a h j≤Nat.floor eta⁻¹+1) →
          ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J<2*eta*m →
          integerValue J P (gridPoint w a)=0) :=
  R.auxiliary eta he m hm r hr

theorem SourceReadiness42.height_projection
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    sourceHeightEnvelopeReduction42 A2 A3 L hL c0 c2 c3 V hQV := by
  refine ⟨R.delta,R.delta_pos,R.delta_lt_one,R.c,R.weights_bounded,R.weights_balance,
    R.finite_weights,R.sigma,R.widths_pos,R.w,R.M,R.a,R.normals,R.frames,R.minors,
    R.upper,R.mixed,R.K,R.finite_dimensional,R.hmem,R.cofactors_mem,R.C,R.C_pos,
    R.lower,R.envelopes,R.D,R.E,R.D_ge_one,R.E_ge_one,?_⟩
  let eta := R.delta/3456
  have he : 0 < eta := by dsimp [eta]; linarith [R.delta_pos]
  have he1 : eta < 1 := by dsimp [eta]; linarith [R.delta_lt_one]
  have hde : 1728*eta < R.delta := by dsimp [eta]; linarith [R.delta_pos]
  obtain ⟨m,hm⟩ := exists_nat_gt
    (max 1 (4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ R.K : ℝ))))
  have hmp : 0 < m := by
    have h1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast (lt_trans zero_lt_one h1)
  have hcut := (lt_of_le_of_lt (le_max_right _ _) hm).le
  refine ⟨eta,he,he1,hde,m,hmp,hcut,?_⟩
  intro rho hp
  obtain ⟨t,ht,hfinite,hgrowth,hsep⟩ := original_blocks V R.unbounded eta R.E rho he R.E_ge_one hp m
  let Q : Fin m → ℝ := fun h => (t h).val^(11 : ℕ)
  have hQ : ∀ h, 1 < Q h := fun h => (hgrowth h).1
  obtain ⟨h0,r,hr,hlogs,hA,hrsep,hrbal⟩ := positive_degrees m hmp eta rho he hp Q hQ hsep
  obtain ⟨P,hP,hhom,hheight,hfield,hreal,hclaims,hcfs,hvan⟩ := R.auxiliary eta he m hcut r hr
  have hgrid := hvan Q hQ h0 R.delta hde R.delta_lt_one (fun h => (hgrowth h).2.1)
    (fun h => (hgrowth h).2.2) hrbal R.c R.weights_bounded R.weights_balance
    (fun h j => (R.w (t h) j.castSucc : Fin 6 → ℤ))
    (fun h => (R.frames (t h)).2.2.2.2.1)
    (fun h => (R.frames (t h)).2.2.2.2.2.1)
    (fun h => (R.frames (t h)).2.2.2.2.2.2)
  refine ⟨t,ht,hfinite,hgrowth,hsep,h0,r,hr,hlogs,hA,hrsep,hrbal,
    P,hP,hhom,hheight,hfield,hreal,hclaims,hcfs,hgrid,?_⟩
  exact integer_grid_high_normal_index6 r hr P hhom
    (fun h j => (R.w (t h) j.castSucc : Fin 6 → ℤ)) (fun h => R.M (t h))
    (fun h => (R.normals (t h)).1) (fun h => (R.normals (t h)).2.2.2.2.1)
    (fun h => (R.normals (t h)).2.2.2.2.2) eta he hgrid

def SourceReadiness42.restrictedPoint
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (s : MixedIndex6) (q : nonzeroFamily6 A2 A3 L V R.M s) : Prop :=
  let b := nonzeroFamily6_lift A2 A3 L V R.M s q
  b.val = q.val ∧ b.val^(11 : ℕ) = q.val^(11 : ℕ) ∧
  (sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV R.delta R.c R.sigma R.widths_pos R.w b) ∧
  (sourceNormals6 A2 A3 c2 c3 V R.w R.M R.a b) ∧
  minorNormalization6 (fun j => (R.w b j : Fin 6 → ℤ)) (R.M b) (R.a b) ∧
  actualTransformedCofactors6 A2 A3 L (fun j => (R.w b j : Fin 6 → ℤ)) (R.M b) (R.a b) ∧
  actualNonzero6 A2 A3 L (R.M b) s ∧
  actualNormProduct6 A2 A3 L (R.M b) s ≤ 120*(q.val^(11 : ℕ))^(-R.delta/8) ∧
  (R.C ≤ actualNormProduct6 A2 A3 L (R.M b) s*
    (max 1 (normalHeight6 (R.M b) : ℝ))^(Module.finrank ℚ R.K+1) ∧
   R.C ≤ actualNormProduct6 A2 A3 L (R.M b) s*
    (max 1 (normalHeight6 (R.M b) : ℝ))^(3*Module.finrank ℚ R.K-1))

theorem SourceReadiness42.restrict_point
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (s : MixedIndex6) (hs : s ∈ admissibleMixed6 R.c (R.delta/2))
    (q : nonzeroFamily6 A2 A3 L V R.M s) : R.restrictedPoint s q := by
  let b := nonzeroFamily6_lift A2 A3 L V R.M s q
  have hn := nonzeroFamily6_actual_nonzero A2 A3 L V R.M s q
  exact ⟨rfl,rfl,R.frames b,R.normals b,(R.minors b).1,(R.minors b).2,
    hn,R.upper b s hs,R.lower b s hn⟩

def SourceReadiness42.nonzeroReady
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (s : MixedIndex6) : Prop :=
  s ∈ admissibleMixed6 R.c (R.delta/2) ∧ ¬ BddAbove (nonzeroFamily6 A2 A3 L V R.M s) ∧
  nonzeroFamily6 A2 A3 L V R.M s ⊆ V ∧
  (∀ q : nonzeroFamily6 A2 A3 L V R.M s, R.restrictedPoint s q) ∧
  universalAuxiliary6 A2 A3 L R.K R.hmem R.D R.E ∧
  (∀ i j, cofactor6 (compound L) i j ∈ R.K) ∧
  ∃ T : ℝ, T = sourceHeightCutoff6 L R.C R.delta ∧ 1 < T ∧
    (∀ q : nonzeroFamily6 A2 A3 L V R.M s, T < q.val →
      let b := nonzeroFamily6_lift A2 A3 L V R.M s q
      (q.val^(11 : ℕ))^(heightAlpha6 R.delta (Module.finrank ℚ R.K)) ≤
        max 1 (normalHeight6 (R.M b) : ℝ) ∧
      max 1 (normalHeight6 (R.M b) : ℝ) ≤ (q.val^(11 : ℕ))^(6 : ℝ)) ∧
    (∀ S : ℝ, ∃ q : nonzeroFamily6 A2 A3 L V R.M s, max T S < q.val ∧
      let b := nonzeroFamily6_lift A2 A3 L V R.M s q
      (q.val^(11 : ℕ))^(heightAlpha6 R.delta (Module.finrank ℚ R.K)) ≤
        max 1 (normalHeight6 (R.M b) : ℝ) ∧
      max 1 (normalHeight6 (R.M b) : ℝ) ≤ (q.val^(11 : ℕ))^(6 : ℝ))

theorem SourceReadiness42.ready_on
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (s : MixedIndex6) (hs : s ∈ admissibleMixed6 R.c (R.delta/2))
    (hu : ¬ BddAbove (nonzeroFamily6 A2 A3 L V R.M s)) : R.nonzeroReady s := by
  letI : FiniteDimensional ℚ R.K := R.finite_dimensional
  have he (q : nonzeroFamily6 A2 A3 L V R.M s)
      (hq : sourceHeightCutoff6 L R.C R.delta < q.val) :
      let b := nonzeroFamily6_lift A2 A3 L V R.M s q
      (q.val^(11 : ℕ))^(heightAlpha6 R.delta (Module.finrank ℚ R.K)) ≤
        max 1 (normalHeight6 (R.M b) : ℝ) ∧
      max 1 (normalHeight6 (R.M b) : ℝ) ≤ (q.val^(11 : ℕ))^(6 : ℝ) := by
    let b := nonzeroFamily6_lift A2 A3 L V R.M s q
    exact same_normal_envelopes6 A2 A3 L hL (fun j => (R.w b j : Fin 6 → ℤ))
      (R.M b) (R.a b) (R.minors b).1 s R.K R.C R.delta q.val (R.c 0)
      R.C_pos R.delta_pos (hQV b.val b.property) (R.weights_bounded 0)
      (R.frames b).2.2.2.2.1 (R.upper b s hs)
      ((R.lower b s (nonzeroFamily6_actual_nonzero A2 A3 L V R.M s q)).1) hq
  refine ⟨hs,hu,nonzeroFamily6_subset A2 A3 L V R.M s,R.restrict_point s hs,
    R.auxiliary,R.cofactors_mem,sourceHeightCutoff6 L R.C R.delta,rfl,
    sourceHeightCutoff6_gt_one L R.C R.delta,he,?_⟩
  intro S
  obtain ⟨q,hq⟩ := unbounded_original_q_cutoff6 _ hu (sourceHeightCutoff6 L R.C R.delta) S
  exact ⟨q,hq,he q ((le_max_left _ _).trans_lt hq)⟩

theorem SourceReadiness42.branches
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    (∃ s, R.nonzeroReady s) ∨
    (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      actualNormProduct6 A2 A3 L (R.M q) s = 0) := by
  rcases R.mixed with ⟨s,hs,hu⟩ | hz
  · exact Or.inl ⟨s,R.ready_on s hs hu⟩
  · exact Or.inr hz

theorem source_compound_unbounded_readiness42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (delta4 : ℝ) (hd : 0 < delta4) (c0 c2 c3 : Fin 4 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hbalance : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ U),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 1 <
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 2 * q^(-delta4)) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)) ∧
      Nonempty (SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq))) := by
  obtain ⟨_,_,_,_,kappa,C4,C,K,T,_,_,_,_,_,_,hfamily⟩ :=
    source_compound_unbounded_fixed_weights42 A2 A3 L h2 h3 hL hAlg delta4 hd
  obtain ⟨_,_,_,_,hF⟩ := hfamily c0 c2 c3 hc0 hc2 hc3 hbalance
  obtain ⟨V,hVU,hV,_,u,v,_,hf⟩ := hF U hU hQU hgap
  exact ⟨V,hVU,hV,hf,fixed_family_readiness42 A2 A3 L h2 h3 hL hAlg
    c0 c2 c3 delta4 V hV (fun q hq => hQU q (hVU hq)) hf⟩

end CompoundFeasibility.SourceReadiness6
