import SubspaceBridge.SourceWeights6
import SubspaceBridge.SourceVanishing6
import SubspaceBridge.ParameterSelection3
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceBlocks
open SourceWeights Auxiliary6 Auxiliary6.SourceExpansion Auxiliary6.SourceBalance
  Auxiliary6.SourceVanishing Auxiliary6.SourceGrid Auxiliary6.SourceEvaluation

theorem original_blocks (V : Set ℝ) (hV : ¬ BddAbove V)
    (eta E rho : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho) (m : ℕ) :
    ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧
      Set.Finite (Set.range t) ∧
      (∀ h, 1 < (t h).val^(11 : ℕ) ∧
        64*E < ((t h).val^(11 : ℕ))^eta ∧
        6*(eta⁻¹+1) < ((t h).val^(11 : ℕ))^eta) ∧
      ∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log ((t h).val^(11 : ℕ)) ≤
          rho*Real.log ((t ⟨h.val+1,hh⟩).val^(11 : ℕ)) := by
  let B := max (Real.log (64*E)/eta) (Real.log (6*(eta⁻¹+1))/eta)
  obtain ⟨q,hq,hmono,hsep⟩ := JSP000334.parameter_sparse_Q V hV (Real.exp B)
    ((1+eta)/rho) m
  let t : Fin m → V := fun h => ⟨q h,(hq h).1⟩
  have hlog (h) : B < Real.log (q h) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) (hq h).2.1
  have hQ (h) : 1 < (q h)^(11 : ℕ) := one_lt_pow₀ (hq h).2.2 (by decide)
  have hlogpow (h) : B < Real.log ((q h)^(11 : ℕ)) := by
    rw [Real.log_pow]
    have hl := Real.log_pos (hq h).2.2
    norm_num only [Nat.cast_ofNat]
    linarith [hlog h]
  refine ⟨t,hmono,Set.finite_range t,?_,?_⟩
  · intro h
    refine ⟨hQ h,?_,?_⟩
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by linarith)
        (lt_of_le_of_lt (le_max_left _ _) (hlogpow h))
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by positivity)
        (lt_of_le_of_lt (le_max_right _ _) (hlogpow h))
  · intro h hh
    have hs0 := hsep h hh
    rw [div_mul_eq_mul_div] at hs0
    have hs := (div_lt_iff₀ hp).mp hs0
    dsimp [t]
    rw [Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith

theorem positive_degrees (m : ℕ) (hm : 0 < m) (eta rho : ℝ)
    (he : 0 < eta) (hp : 0 < rho) (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (1+eta)*Real.log (Q h) ≤ rho*Real.log (Q ⟨h.val+1,hh⟩)) :
    ∃ (h0 : Fin m) (r : Fin m → ℕ),
      (∀ h, 0 < r h) ∧ (∀ h, 0 < Real.log (Q h)) ∧
      (0 < (r h0 : ℝ)*Real.log (Q h0)) ∧
      (∀ (h : Fin m) (hh : h.val+1 < m),
        (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
      ∀ h, (r h0 : ℝ)*Real.log (Q h0) ≤ (r h : ℝ)*Real.log (Q h) ∧
        (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*((r h0 : ℝ)*Real.log (Q h0)) := by
  obtain ⟨r,hr,hgap,hbal⟩ := JSP000334.parameter_integer_degrees m hm eta rho he hp Q hQ hsep
  refine ⟨⟨0,hm⟩,r,hr,fun h => Real.log_pos (hQ h),?_,hgap,?_⟩
  · exact mul_pos (by exact_mod_cast hr ⟨0,hm⟩) (Real.log_pos (hQ ⟨0,hm⟩))
  · intro h
    simpa only [mul_assoc] using hbal h




theorem source_separation (eta omega x y a b : ℝ) (he : 0 < eta) (ho : 0 < omega)
    (hx : 0 < x) (ha : 0 ≤ a)
    (hgap : (1+eta)*x ≤ (omega/2)*y) (hdegree : b ≤ (omega/2)*a) :
    x < (1/2)*omega*y ∧ b ≤ omega*a := by
  constructor
  · nlinarith [mul_pos he hx]
  · nlinarith [mul_nonneg ho.le ha]

def sourceBlockVanishing42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
    ∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
    ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
      integerValue J P (gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0

theorem fixed_family_grid_vanishing (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c0 c2 c3 : Fin 4 → ℝ) (delta4 : ℝ) (V : Set ℝ)
    (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hf : fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V hQV) :
    sourceBlockVanishing42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V hQV := by
  obtain ⟨_,epsilon,delta6,_,_,_,hd,hd1,_,c,hc,hbal,hfin,sigma,hW,w,q0,_,hframe⟩ := hf
  refine ⟨delta6,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,?_,?_⟩
  · intro q
    obtain ⟨_,_,_,_,hli,hlq,hgroup,hatt,_,hw0,hw2,hw3⟩ := hframe q
    exact ⟨hli,hlq,hgroup,hatt,hw0,hw2,hw3⟩
  · obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ :=
      source_auxiliary6_grid_vanishing A2 A3 L h2 h3 hL hAlg
    let eta := delta6/3456
    have he : 0 < eta := by dsimp [eta]; positivity
    have he1 : eta < 1 := by dsimp [eta]; linarith
    have hde : 1728*eta < delta6 := by dsimp [eta]; linarith
    obtain ⟨m,hm⟩ := exists_nat_gt
      (max 1 (4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ K : ℝ))))
    have hmp : 0 < m := by
      have h1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
      exact_mod_cast (lt_trans zero_lt_one h1)
    have hcut := (lt_of_le_of_lt (le_max_right _ _) hm).le
    refine ⟨K,hK,hmem,D,E,hD,hE,eta,he,he1,hde,m,hmp,hcut,?_⟩
    intro rho hp
    obtain ⟨t,ht,hfinite,hgrowth,hsep⟩ := original_blocks V hV eta E rho he hE hp m
    let Q : Fin m → ℝ := fun h => (t h).val^(11 : ℕ)
    have hQ : ∀ h, 1 < Q h := fun h => (hgrowth h).1
    obtain ⟨h0,r,hr,hlogs,hA,hrsep,hrbal⟩ := positive_degrees m hmp eta rho he hp Q hQ hsep
    obtain ⟨P,hP,hhom,hheight,hfield,hreal,hclaims,hcfs,hvan⟩ := haux eta he m hcut r hr
    refine ⟨t,ht,hfinite,hgrowth,hsep,h0,r,hr,hlogs,hA,hrsep,hrbal,
      P,hP,hhom,hheight,hfield,hreal,hclaims,hcfs,?_⟩
    apply hvan Q hQ h0 delta6 hde hd1 (fun h => (hgrowth h).2.1)
      (fun h => (hgrowth h).2.2) hrbal c hc hbal
      (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ))
    · intro h j i
      obtain ⟨_,_,_,_,_,_,_,_,_,hw0,_,_⟩ := hframe (t h)
      exact hw0 j i
    · intro h j i
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hw2,_⟩ := hframe (t h)
      exact hw2 j i
    · intro h j i
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hw3⟩ := hframe (t h)
      exact hw3 j i

theorem source_compound_unbounded_roth_blocks42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
      sourceBlockVanishing42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V
        (fun q hq => hQU q (hVU hq)) := by
  obtain ⟨_,_,_,_,kappa,C4,C,K,T,_,_,_,_,_,_,hfamily⟩ :=
    source_compound_unbounded_fixed_weights42 A2 A3 L h2 h3 hL hAlg delta4 hd
  obtain ⟨_,_,_,_,hF⟩ := hfamily c0 c2 c3 hc0 hc2 hc3 hbalance
  obtain ⟨V,hVU,hV,_,u,v,_,hf⟩ := hF U hU hQU hgap
  exact ⟨V,hVU,hV,hf,fixed_family_grid_vanishing A2 A3 L h2 h3 hL hAlg
    c0 c2 c3 delta4 V hV (fun q hq => hQU q (hVU hq)) hf⟩

end CompoundFeasibility.SourceBlocks
