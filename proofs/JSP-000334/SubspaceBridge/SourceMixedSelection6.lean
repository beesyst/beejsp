import SubspaceBridge.SourceProperCofactor6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceMixed6
open SourceProper6 Auxiliary6.SourceExpansion

abbrev MixedIndex6 := Fin 3 → Fin 6

def admissibleMixed6 (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ) : Finset MixedIndex6 :=
  Finset.univ.filter (fun s => -(3*delta)/4 ≤ ∑ tau, c tau (s tau))

theorem mem_admissibleMixed6 (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ) (s : MixedIndex6) :
    s ∈ admissibleMixed6 c delta ↔ -(3*delta)/4 ≤ ∑ tau, c tau (s tau) := by
  simp [admissibleMixed6]

theorem admissibleMixed6_card (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ) :
    (admissibleMixed6 c delta).card ≤ 216 := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun s : MixedIndex6 => -(3*delta)/4 ≤ ∑ tau, c tau (s tau)) Finset.univ)
  simpa [admissibleMixed6,MixedIndex6,Fintype.card_fun] using h

def actualNonzero6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 6 → ℤ) (s : MixedIndex6) : Prop :=
  cofactorValue6 (compound L) M (s 0) ≠ 0 ∧
  cofactorValue6 (finiteMatrix 2 A2) M (s 1) ≠ 0 ∧
  cofactorValue6 (finiteMatrix 3 A3) M (s 2) ≠ 0

def actualNormProduct6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 6 → ℤ) (s : MixedIndex6) : ℝ :=
  ‖cofactorValue6 (compound L) M (s 0)‖ *
  ‖cofactorValue6 (finiteMatrix 2 A2) M (s 1)‖ *
  ‖cofactorValue6 (finiteMatrix 3 A3) M (s 2)‖

theorem actualNormProduct6_ne_zero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 6 → ℤ) (s : MixedIndex6) :
    actualNormProduct6 A2 A3 L M s ≠ 0 ↔ actualNonzero6 A2 A3 L M s := by
  simp [actualNormProduct6,actualNonzero6,mul_ne_zero_iff,and_assoc]

def nonzeroFamily6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (s : MixedIndex6) : Set ℝ :=
  {q | ∃ hq : q ∈ V, actualNonzero6 A2 A3 L (M ⟨q,hq⟩) s}

theorem nonzeroFamily6_subset (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ) (s : MixedIndex6) :
    nonzeroFamily6 A2 A3 L V M s ⊆ V := fun _ h => h.choose

theorem mem_nonzeroFamily6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (s : MixedIndex6) (q : V) :
    q.val ∈ nonzeroFamily6 A2 A3 L V M s ↔ actualNonzero6 A2 A3 L (M q) s := by
  constructor
  · rintro ⟨hq,h⟩
    exact h
  · intro h
    exact ⟨q.property,h⟩

theorem finite_mixed_reduction6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ) :
    (∃ s ∈ admissibleMixed6 c delta, ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s)) ∨
    (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 c delta,
      actualNormProduct6 A2 A3 L (M q) s = 0) := by
  by_cases h : ∃ s ∈ admissibleMixed6 c delta, ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s)
  · exact Or.inl h
  · right
    have hb : ∀ s ∈ admissibleMixed6 c delta, BddAbove (nonzeroFamily6 A2 A3 L V M s) := by
      intro s hs
      by_contra hn
      exact h ⟨s,hs,hn⟩
    have hu : BddAbove (⋃ s ∈ admissibleMixed6 c delta, nonzeroFamily6 A2 A3 L V M s) :=
      (Finset.finite_toSet (admissibleMixed6 c delta)).bddAbove_biUnion.mpr hb
    obtain ⟨B,hB⟩ := hu
    refine ⟨B,?_⟩
    intro q hq s hs
    by_contra hn
    have hmem : q.val ∈ nonzeroFamily6 A2 A3 L V M s :=
      (mem_nonzeroFamily6 A2 A3 L V M s q).mpr
        ((actualNormProduct6_ne_zero A2 A3 L (M q) s).mp hn)
    have hle := hB (Set.mem_iUnion₂.mpr ⟨s,hs,hmem⟩)
    exact (not_le_of_gt hq) hle

theorem actualNormProduct6_eq_zero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 6 → ℤ) (s : MixedIndex6) :
    actualNormProduct6 A2 A3 L M s = 0 ↔
      cofactorValue6 (compound L) M (s 0) = 0 ∨
      cofactorValue6 (finiteMatrix 2 A2) M (s 1) = 0 ∨
      cofactorValue6 (finiteMatrix 3 A3) M (s 2) = 0 := by
  simp [actualNormProduct6,mul_eq_zero,or_assoc]

theorem source_half_margin6 (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ) (s : MixedIndex6)
    (hs : s ∈ admissibleMixed6 c (delta/2)) :
    -(3*delta)/8 ≤ ∑ tau, c tau (s tau) := by
  have h := (mem_admissibleMixed6 c (delta/2) s).mp hs
  linarith

theorem strict_local_slack6 (Q c delta x : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (hx : x ≤ Q^(c-delta)) : x < Q^(c-delta/2) :=
  hx.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hQ (by linarith))

def nonzeroFamily6_lift (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ) (s : MixedIndex6) :
    nonzeroFamily6 A2 A3 L V M s → V :=
  fun q => ⟨q.val,nonzeroFamily6_subset A2 A3 L V M s q.property⟩

theorem nonzeroFamily6_lift_val (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (s : MixedIndex6) (q : nonzeroFamily6 A2 A3 L V M s) :
    (nonzeroFamily6_lift A2 A3 L V M s q).val = q.val := rfl

theorem nonzeroFamily6_actual_nonzero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (s : MixedIndex6) (q : nonzeroFamily6 A2 A3 L V M s) :
    actualNonzero6 A2 A3 L (M (nonzeroFamily6_lift A2 A3 L V M s q)) s :=
  (mem_nonzeroFamily6 A2 A3 L V M s _).mp q.property

theorem nonzeroFamily6_original_blocks (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (s : MixedIndex6) (hU : ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s))
    (eta E rho : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho) (m : ℕ) :
    ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧ Set.Finite (Set.range t) ∧
      (∀ h, (t h).val ∈ nonzeroFamily6 A2 A3 L V M s) ∧
      (∀ h, actualNonzero6 A2 A3 L (M (t h)) s) ∧
      (∀ h, 1 < (t h).val^(11 : ℕ) ∧ 64*E < ((t h).val^(11 : ℕ))^eta ∧
        6*(eta⁻¹+1) < ((t h).val^(11 : ℕ))^eta) ∧
      ∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log ((t h).val^(11 : ℕ)) ≤
          rho*Real.log ((t ⟨h.val+1,hh⟩).val^(11 : ℕ)) := by
  obtain ⟨u,hu,hf,hg,hs⟩ := SourceBlocks.original_blocks
    (nonzeroFamily6 A2 A3 L V M s) hU eta E rho he hE hp m
  let t : Fin m → V := fun h => nonzeroFamily6_lift A2 A3 L V M s (u h)
  exact ⟨t,hu,Set.finite_range t,fun h => (u h).property,
    fun h => nonzeroFamily6_actual_nonzero A2 A3 L V M s (u h),hg,hs⟩

theorem bounded_nonzeroFamily6_eventually_zero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (s : MixedIndex6) (hb : BddAbove (nonzeroFamily6 A2 A3 L V M s)) :
    ∃ B : ℝ, ∀ q : V, B < q.val → actualNormProduct6 A2 A3 L (M q) s = 0 := by
  obtain ⟨B,hB⟩ := hb
  refine ⟨B,?_⟩
  intro q hq
  by_contra hn
  have hmem := (mem_nonzeroFamily6 A2 A3 L V M s q).mpr
    ((actualNormProduct6_ne_zero A2 A3 L (M q) s).mp hn)
  exact (not_le_of_gt hq) (hB hmem)

theorem nonzeroFamily6_power11_unbounded (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (V : Set ℝ) (M : V → Fin 6 → ℤ)
    (s : MixedIndex6) (hu : ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s)) :
    ¬ BddAbove ((fun q : ℝ => q^(11 : ℕ)) '' nonzeroFamily6 A2 A3 L V M s) :=
  SourceWeights.power11_unbounded _ hu

open SourceNormalIndex SourceWeights Auxiliary6 SourceMultiblock
open Auxiliary6.SourceBalance Auxiliary6.SourceVanishing Auxiliary6.SourceGrid Auxiliary6.SourceEvaluation

def sourceMixedReduction42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
  ((∃ s ∈ admissibleMixed6 c (delta6/2), ¬ BddAbove (nonzeroFamily6 A2 A3 L V M s)) ∨
    (∃ B : ℝ, ∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 c (delta6/2),
      actualNormProduct6 A2 A3 L (M q) s = 0)) ∧
  ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
  ∃ hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K,
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

theorem source_actual_mixed_reduction42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : sourceHighNormalIndex42 A2 A3 L hL c0 c2 c3 V hQV) :
    sourceMixedReduction42 A2 A3 L hL c0 c2 c3 V hQV := by
  rcases hs with ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,hrest⟩
  exact ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,
    finite_mixed_reduction6 A2 A3 L V M c (delta/2),hrest⟩

theorem sourceMixedReduction42_high_index (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : sourceMixedReduction42 A2 A3 L hL c0 c2 c3 V hQV) :
    sourceHighNormalIndex42 A2 A3 L hL c0 c2 c3 V hQV := by
  rcases hs with ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,hbranch,hrest⟩
  exact ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,hrest⟩

theorem source_compound_unbounded_mixed_reduction42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
      sourceMixedReduction42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V
        (fun q hq => hQU q (hVU hq)) := by
  obtain ⟨V,hVU,hV,hfixed,hindex⟩ := source_compound_unbounded_high_normal_index42
    A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  exact ⟨V,hVU,hV,hfixed,source_actual_mixed_reduction42 A2 A3 L (sourceUnit42 L hL)
    c0 c2 c3 V (fun q hq => hQU q (hVU hq)) hindex⟩

end CompoundFeasibility.SourceMixed6
