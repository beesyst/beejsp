import SubspaceBridge.SourceHeightUpper6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightIntegration6
open SourceNormalIndex SourceWeights Auxiliary6 SourceMultiblock SourceMixed6 SourceHeightBounds6
open SourceNormalHeight SourceProper6 SourceMinorIntegration6 SourceLocalUpperIntegration6 SourceFieldLower6
open SourceFieldLowerIntegration6 SourceHeightUpper6 SourceHeightEnvelopes6
open Auxiliary6.SourceExpansion Auxiliary6.SourceBalance Auxiliary6.SourceVanishing
open Auxiliary6.SourceGrid Auxiliary6.SourceEvaluation

def heightEnvelopeBranch6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ) (K : IntermediateField ℚ ℝ) (C : ℝ) : Prop :=
  0 < heightAlpha6 delta (Module.finrank ℚ K) ∧ 1 ≤ Module.finrank ℚ K ∧
  ∃ T : ℝ, T = sourceHeightCutoff6 L C delta ∧ 1 < T ∧
    ((∃ s ∈ admissibleMixed6 c (delta/2), ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s) ∧
      (∀ q : nonzeroFamily6 A2 A3 L V M s, T < q.val →
        let b := nonzeroFamily6_lift A2 A3 L V M s q
        (q.val^(11 : ℕ))^(heightAlpha6 delta (Module.finrank ℚ K)) ≤ max 1 (normalHeight6 (M b) : ℝ) ∧
          max 1 (normalHeight6 (M b) : ℝ) ≤ (q.val^(11 : ℕ))^(6 : ℝ)) ∧
      (∀ R : ℝ, ∃ q : nonzeroFamily6 A2 A3 L V M s,
        max T R < q.val ∧
        let b := nonzeroFamily6_lift A2 A3 L V M s q
        (q.val^(11 : ℕ))^(heightAlpha6 delta (Module.finrank ℚ K)) ≤ max 1 (normalHeight6 (M b) : ℝ) ∧
          max 1 (normalHeight6 (M b) : ℝ) ≤ (q.val^(11 : ℕ))^(6 : ℝ))) ∨
      (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 c (delta/2),
        actualNormProduct6 A2 A3 L (M q) s = 0))

theorem source_height_branch6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (delta : ℝ) (hd : 0 < delta) (c : Fin 3 → Fin 6 → ℝ) (hc : ∀ tau i, |c tau i| ≤ 1)
    (v : V → Matrix (Fin 6) (Fin 6) ℤ) (M a : V → Fin 6 → ℤ)
    (hn : ∀ q, minorNormalization6 (v q) (M q) (a q))
    (hR : ∀ (q : V) (j : Fin 5) i,
      ‖(compound L *ᵥ (fun k => (v q j.castSucc k : ℝ))) i‖ ≤ (q.val^(11 : ℕ))^(c 0 i-delta))
    (hu : ∀ (q : V) s, s ∈ admissibleMixed6 c (delta/2) →
      actualNormProduct6 A2 A3 L (M q) s ≤ 120*(q.val^(11 : ℕ))^(-delta/8))
    (hb : (∃ s ∈ admissibleMixed6 c (delta/2), ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s)) ∨
      (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 c (delta/2),
        actualNormProduct6 A2 A3 L (M q) s = 0))
    (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] (C : ℝ) (hC : 0 < C)
    (hl : ∀ (q : V) s, actualNonzero6 A2 A3 L (M q) s →
      C ≤ actualNormProduct6 A2 A3 L (M q) s*
        (max 1 (normalHeight6 (M q) : ℝ))^(Module.finrank ℚ K+1)) :
    heightEnvelopeBranch6 A2 A3 L V M c delta K C := by
  have hdK : 0 < Module.finrank ℚ K := Module.finrank_pos
  refine ⟨heightAlpha6_pos delta hd _,by omega,sourceHeightCutoff6 L C delta,rfl,
    sourceHeightCutoff6_gt_one L C delta,?_⟩
  rcases hb with ⟨s,hs,hunbdd⟩ | hz
  · left
    have he : ∀ q : nonzeroFamily6 A2 A3 L V M s, sourceHeightCutoff6 L C delta < q.val →
        let b := nonzeroFamily6_lift A2 A3 L V M s q
        (q.val^(11 : ℕ))^(heightAlpha6 delta (Module.finrank ℚ K)) ≤ max 1 (normalHeight6 (M b) : ℝ) ∧
          max 1 (normalHeight6 (M b) : ℝ) ≤ (q.val^(11 : ℕ))^(6 : ℝ) := by
      intro q hq
      let b := nonzeroFamily6_lift A2 A3 L V M s q
      exact same_normal_envelopes6 A2 A3 L hL (v b) (M b) (a b) (hn b) s K C delta q.val
        (c 0) hC hd (hQV b.val b.property) (hc 0) (hR b) (hu b s hs)
        (hl b s (nonzeroFamily6_actual_nonzero A2 A3 L V M s q)) hq
    refine ⟨s,hs,hunbdd,he,?_⟩
    intro R
    obtain ⟨q,hq⟩ := unbounded_original_q_cutoff6 _ hunbdd (sourceHeightCutoff6 L C delta) R
    exact ⟨q,hq,he q ((le_max_left _ _).trans_lt hq)⟩
  · exact Or.inr hz

def sourceHeightEnvelopeReduction42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q) : Prop :=
  ∃ delta6 : ℝ, 0 < delta6 ∧ delta6 < 1 ∧
  ∃ c : Fin 3 → Fin 6 → ℝ, (∀ tau i, |c tau i| ≤ 1) ∧
    (∑ tau, ∑ i, c tau i) = 0 ∧
    (∀ i, c 1 i = finiteWeight c2 i ∧ c 2 i = finiteWeight c3 i) ∧
  ∃ sigma : V → Equiv.Perm (Fin 6),
  ∃ hW : ∀ (q : V) i, 0 < actualWidths A2 A3 L hL q.val
    (hQV q.val q.property) c0 c2 c3 (sigma q) i,
  ∃ w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3,
  ∃ M a : V → Fin 6 → ℤ,
    (∀ q, M q ≠ 0 ∧ (∑ i, a q i*M q i) = 1 ∧
      Ideal.span (Set.range (M q)) = ⊤ ∧
      (∀ j : Fin 5, (∑ i, M q i*(w q j.castSucc : Fin 6 → ℤ) i) = 0) ∧
      LinearMap.ker (normalForm6 (M q)) =
        firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) ∧
      LinearMap.ker (realNormalForm6 (M q)) =
        firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℝ))) ∧
    (∀ q : V,
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
        (fun k => ((w q j.castSucc : Fin 6 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^(11 : ℕ))^(c 2 i))) ∧
  (∀ q : V, minorNormalization6 (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q) ∧
    actualTransformedCofactors6 A2 A3 L (fun j => (w q j : Fin 6 → ℤ)) (M q) (a q)) ∧
  (∀ (q : V) (s : MixedIndex6), s ∈ admissibleMixed6 c (delta6/2) →
    actualNormProduct6 A2 A3 L (M q) s ≤ 120*(q.val^(11 : ℕ))^(-delta6/8)) ∧
  ((∃ s ∈ admissibleMixed6 c (delta6/2), ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s)) ∨
    (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 c (delta6/2),
      actualNormProduct6 A2 A3 L (M q) s = 0)) ∧
  ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
  ∃ hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K,
  (∀ i j, cofactor6 (compound L) i j ∈ K) ∧
  ∃ C : ℝ, 0 < C ∧
    (∀ (q : V) (s : MixedIndex6), actualNonzero6 A2 A3 L (M q) s →
      C ≤ actualNormProduct6 A2 A3 L (M q) s*(max 1 (normalHeight6 (M q) : ℝ))^(Module.finrank ℚ K+1) ∧
      C ≤ actualNormProduct6 A2 A3 L (M q) s*(max 1 (normalHeight6 (M q) : ℝ))^(3*Module.finrank ℚ K-1)) ∧
  heightEnvelopeBranch6 A2 A3 L V M c delta6 K C ∧
  ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
  ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ 1728*eta < delta6 ∧
  ∃ m : ℕ, 0 < m ∧ 4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
  ∀ rho : ℝ, 0 < rho →
  ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧ Set.Finite (Set.range t) ∧
    let Q : Fin m → ℝ := fun h => (t h).val^(11 : ℕ)
    (∀ h, 1 < Q h ∧ 64*E < (Q h)^eta ∧ 6*(eta⁻¹+1) < (Q h)^eta) ∧
    (∀ (h : Fin m) (hh : h.val+1 < m),
      (1+eta)*Real.log (Q h) ≤ rho*Real.log (Q ⟨h.val+1,hh⟩)) ∧
  ∃ (h0 : Fin m) (r : Fin m → ℕ), (∀ h, 0 < r h) ∧
    (∀ h, 0 < Real.log (Q h)) ∧ 0 < (r h0 : ℝ)*Real.log (Q h0) ∧
    (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
    (∀ h, (r h0 : ℝ)*Real.log (Q h0) ≤ (r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*((r h0 : ℝ)*Real.log (Q h0))) ∧
  ∃ P : MvPolynomial (Vars6 m) ℤ, P ≠ 0 ∧ homogeneous6 r P ∧
    (height6 P : ℝ) ≤ D^(∑ h, r h) ∧ FieldIndex A2 A3 L K hmem r eta P ∧
    RealIndex A2 A3 L r eta P ∧
    (Claims r eta (compound L) P ∧ Claims r eta (finiteMatrix 2 A2) P ∧
      Claims r eta (finiteMatrix 3 A3) P) ∧
    (∀ J b : Vars6 m →₀ ℕ,
      ‖(expansion (compound L) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (finiteMatrix 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (finiteMatrix 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) ∧
    (∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
    ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
      integerValue J P (gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0) ∧
    (∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 6 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm6 (M (t h)))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M (t h)))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (fun h => M (t h)) r ((m : ℝ)*eta)

theorem source_actual_height_envelopes42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : sourceFieldLowerReduction42 A2 A3 L hL c0 c2 c3 V hQV) :
    sourceHeightEnvelopeReduction42 A2 A3 L hL c0 c2 c3 V hQV := by
  rcases hs with ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,hminor,hupper,hbranch,K,hK,hmem,
    hcof,C,hC,hlower,hrest⟩
  letI : FiniteDimensional ℚ K := hK
  refine ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,hminor,hupper,hbranch,K,hK,hmem,
    hcof,C,hC,hlower,?_,hrest⟩
  apply source_height_branch6 A2 A3 L hL V hQV delta hd c hc
    (fun q j => (w q j : Fin 6 → ℤ)) M a (fun q => (hminor q).1) ?_ hupper hbranch K C hC
  · intro q s hn
    exact (hlower q s hn).1
  · intro q j i
    rcases hw q with ⟨hli,hli5,hgroup,hatt,hR,h2,h3⟩
    exact hR j i

theorem sourceHeightEnvelopeReduction42_lower (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : sourceHeightEnvelopeReduction42 A2 A3 L hL c0 c2 c3 V hQV) :
    sourceFieldLowerReduction42 A2 A3 L hL c0 c2 c3 V hQV := by
  rcases hs with ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,hminor,hupper,hbranch,K,hK,hmem,
    hcof,C,hC,hlower,henvelopes,hrest⟩
  exact ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,hminor,hupper,hbranch,K,hK,hmem,
    hcof,C,hC,hlower,hrest⟩

theorem source_compound_unbounded_height_envelopes42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
      sourceHeightEnvelopeReduction42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V
        (fun q hq => hQU q (hVU hq)) := by
  obtain ⟨V,hVU,hV,hfixed,hs⟩ := source_compound_unbounded_field_lower42
    A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  exact ⟨V,hVU,hV,hfixed,source_actual_height_envelopes42 A2 A3 L (sourceUnit42 L hL)
    c0 c2 c3 V (fun q hq => hQU q (hVU hq)) hs⟩

end CompoundFeasibility.SourceHeightIntegration6
