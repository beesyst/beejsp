import SubspaceBridge.Exterior3Normalization4
import SubspaceBridge.OriginalSpanTransport4
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.Exterior3
open OriginalDeformedSource4 OriginalLastDual4 OriginalSelectedSystem4 OriginalDeformation4 SourceSelectedDual4
noncomputable section

def fixedCompoundData3_4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hLdet : L.det = 1) (delta : ℝ) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q) : Prop :=
    ∃ U : Set ℝ, ∃ hUV : U ⊆ V, ¬ BddAbove U ∧
      ∃ u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ∃ F : (q : U) → DeformedAttaining4 A2 A3 L (sourceUnit42 L hLdet) q.val
        (hQV q.val (hUV q.property)) c0 c2 c3 delta (u q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ W : Set ℝ, ∃ hWU : W ⊆ U, ¬ BddAbove W ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
        (∀ q : U, q.val ∈ W →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
            (OriginalDeformation4.deformedWidths4 q.val c0
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q.val
                  (hQV q.val (hUV q.property)) c0 c2 c3)) (F q).sigma) (fun i => c2 i/5) (fun i => c3 i/5) = S) ∧
        ∃ (q1 : U) (b : Fin 4 → ℤ) (B : ℝ), q1.val ∈ W ∧
          b = integerLastDual4 (fun j => ((F q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
          Submodule.span ℚ {fun i => (b i : ℚ)} =
            Submodule.span ℚ {lastDual4 (fun j i => (((F q1).w j : Fin 4 → ℤ) i : ℚ)) (F q1).rational_independent} ∧
          (∀ s ∈ S, mixedProduct4 A2 A3 L b s = 0) ∧
          1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ W ∧ B < q} ∧
          (∀ q : U, q.val ∈ W → B < q.val →
            Submodule.span ℚ {lastDual4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) (F q).rational_independent} =
              Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
          ∃ (Tspan : ℝ) (Vprime : Set ℝ) (P : Submodule ℚ (Fin 4 → ℚ)),
            1 < Tspan ∧ Vprime = {Q | Q ∈ W ∧ max B Tspan < Q} ∧
            ¬ BddAbove Vprime ∧ P = LinearMap.ker (normalForm4 b) ∧
            Module.finrank ℚ P = 3 ∧
            ∀ q : U, q.val ∈ Vprime →
              P = firstThreeSpan4 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) ∧
              P = firstThreeSpan4 (fun j i => (((F q).w j : Fin 4 → ℤ) i : ℚ)) ∧
              minimaFlag4 (fun j => integerReal (u q j : Fin 4 → ℤ)) 3 =
                minimaFlag4 (fun j => integerReal ((F q).w j : Fin 4 → ℤ)) 3 ∧
              Module.finrank ℝ (minimaFlag4 (fun j => integerReal (u q j : Fin 4 → ℤ)) 3) = 3 ∧
              LinearIndependent ℚ (fun j : Fin 3 => fun i => ((u q j.castSucc : Fin 4 → ℤ) i : ℚ))

theorem normalized_persistence_boundary3
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L (sourceUnit42 L hLdet) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    fixedCompoundData3_4 A2 A3 L hLdet delta c0 c2 c3 V hQV := by
  exact OriginalSpanTransport4.source_original_fixed_rank3_4 A2 A3 L h2 h3 hLdet hAlg delta hd
    c0 c2 c3 hc0 hc2 hc3 hb V hV hQV hgap

def cubePreimage3_4 (V Wfixed : Set ℝ) : Set ℝ :=
  {Q | Q ∈ V ∧ Q^(3 : ℕ) ∈ Wfixed}

theorem cubePreimage3_unbounded (V W Wfixed : Set ℝ) (hW : W = cubeImage3_4 V)
    (hFW : Wfixed ⊆ W) (hF : ¬ BddAbove Wfixed) (hQ : ∀ Q ∈ V, 1 < Q) :
    ¬ BddAbove (cubePreimage3_4 V Wfixed) := by
  intro hbound
  obtain ⟨M,hM⟩ := hbound
  apply hF
  refine ⟨(max M 1)^(3 : ℕ),?_⟩
  intro R hRF
  have hRW := hFW hRF
  rw [hW] at hRW
  obtain ⟨Q,hQV,hRQ⟩ := hRW
  have hQF : Q ∈ cubePreimage3_4 V Wfixed := ⟨hQV,by simpa only [hRQ] using hRF⟩
  rw [hRQ]
  exact pow_le_pow_left₀ (zero_lt_one.trans (hQ Q hQV)).le
    ((hM hQF).trans (le_max_left M 1)) 3

theorem source_exterior3_persistence_data4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    let hBunit := sourceUnit42 B₀ hBdet
    ∃ Told T : ℝ, 1 < Told ∧ 1 < T ∧ Told ≤ T ∧ 0 < delta/12 ∧
      (∀ Q : ℝ, T < Q → 36 < Q^(delta/4)) ∧
      B₂.det = 1 ∧ B₃.det = 1 ∧ B₀.det = 1 ∧ IsUnit B₂ ∧ IsUnit B₃ ∧ IsUnit B₀ ∧
      (∀ s t, IsAlgebraic ℚ (B₀ s t)) ∧
      ∀ (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
        (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
        (_hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0),
        (∀ s, |normalizedWeights3_4 c₀ s| ≤ 1) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₂ s ∧ normalizedWeights3_4 c₂ s ≤ 0) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₃ s ∧ normalizedWeights3_4 c₃ s ≤ 0) ∧
        (∑ s, (normalizedWeights3_4 c₀ s+normalizedWeights3_4 c₂ s+normalizedWeights3_4 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 0 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 1*Q^(-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), V = {Q | Q ∈ U ∧ Told < Q} ∧ ¬ BddAbove V ∧
            ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              (∀ q : V, originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q) ∧ Told < q.val ∧
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 2 <
                  compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 3*q.val^(-delta/2)) ∧
              ∃ (Vprime : Set ℝ) (hVpV : Vprime ⊆ V), Vprime = {Q | Q ∈ V ∧ T < Q} ∧ ¬ BddAbove Vprime ∧
                ∃ (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R), W = cubeImage3_4 Vprime ∧ ¬ BddAbove W ∧
                  (∀ q : Vprime,
                    normalizationTransport3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ ∧
                    (∀ s, tripleFrame4 (fun j => (u ⟨q.val,hVpV q.property⟩ j : Fin 4 → ℤ)) s ∈
                      normalizedGroup3_4 A₂ A₃ q.val c₂ c₃) ∧
                    normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 2 <
                      normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 3*(q.val^(3 : ℕ))^(-delta/12)) ∧
                  (∀ (R : ℝ) (hR : R ∈ W), ∃ q : Vprime, R = q.val^(3 : ℕ) ∧
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 2 <
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 3*R^(-delta/12)) ∧
                  fixedCompoundData3_4 B₂ B₃ B₀ hBdet (delta/12)
                    (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) W hWR := by
  classical
  dsimp only
  obtain ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,htails⟩ :=
    source_exterior3_normalized_gap4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,?_⟩
  intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨ha₀,ha₂,ha₃,hab,hfamilies⟩ := htails c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  refine ⟨ha₀,ha₂,ha₃,hab,?_⟩
  intro U hU hQU hgap
  obtain ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre⟩ :=
    hfamilies U hU hQU hgap
  have hnormgap (R : ℝ) (hR : R ∈ W) :
      sourceMinima4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L)
        (sourceUnit42 _ hB₀) R (hWR R hR)
        (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 2 <
      sourceMinima4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L)
        (sourceUnit42 _ hB₀) R (hWR R hR)
        (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 3*R^(-(delta/12)) := by
    obtain ⟨q,hRq,hg⟩ := hpre R hR
    simpa only [neg_div] using hg
  have hpersist := normalized_persistence_boundary3 (compound3Matrix4 A₂) (compound3Matrix4 A₃)
    (compound3Matrix4 L) hB₂ hB₃ hB₀ hBalg (delta/12) hdNew
    (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃)
    ha₀ ha₂ ha₃ hab W hW hWR hnormgap
  exact ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre,hpersist⟩

def retainedOriginalWedges3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (kappa delta : ℝ)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃) : Prop :=
  originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ u ∧
  normalizationTransport3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ ∧
  (∀ j, tripleFrame4 (fun i => (u i : Fin 4 → ℤ)) j ∈ normalizedGroup3_4 A₂ A₃ Q c₂ c₃) ∧
  (∀ j, kappa*tripleProducts3_4 (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃) j ≤
    compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ j ∧
    compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ j ≤
    6*tripleProducts3_4 (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃) j) ∧
  normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 2 <
    normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 3*(Q^(3 : ℕ))^(-delta/12)

def fixedCompoundPreimages3_4
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (delta : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (U V : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) (hVU : V ⊆ U)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃)
    (Vprime : Set ℝ) (hVpV : Vprime ⊆ V) (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R) : Prop :=
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    ∃ Uc : Set ℝ, ∃ hUcW : Uc ⊆ W, ¬ BddAbove Uc ∧
      ∃ uc : (q : Uc) → Fin 4 → originalSourceGroup4 B₂ B₃ q.val (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃),
      ∃ Fc : (q : Uc) → DeformedAttaining4 B₂ B₃ B₀ (sourceUnit42 B₀ hBdet) q.val
        (hWR q.val (hUcW q.property)) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) (delta/12) (uc q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ Wc : Set ℝ, ∃ hWcU : Wc ⊆ Uc, ¬ BddAbove Wc ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' Wc) ∧
        (∀ q : Uc, q.val ∈ Wc →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) ((delta/12)/24)
            (OriginalDeformation4.deformedWidths4 q.val (normalizedWeights3_4 c₀)
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 B₂ B₃ B₀ (sourceUnit42 B₀ hBdet) q.val
                  (hWR q.val (hUcW q.property)) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃))) (Fc q).sigma) (fun i => (normalizedWeights3_4 c₂) i/5) (fun i => (normalizedWeights3_4 c₃) i/5) = S) ∧
        ∃ (q1 : Uc) (b : Fin 4 → ℤ) (B : ℝ), q1.val ∈ Wc ∧
          b = integerLastDual4 (fun j => ((Fc q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
          Submodule.span ℚ {fun i => (b i : ℚ)} =
            Submodule.span ℚ {lastDual4 (fun j i => (((Fc q1).w j : Fin 4 → ℤ) i : ℚ)) (Fc q1).rational_independent} ∧
          (∀ s ∈ S, mixedProduct4 B₂ B₃ B₀ b s = 0) ∧
          1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ Wc ∧ B < q} ∧
          (∀ q : Uc, q.val ∈ Wc → B < q.val →
            Submodule.span ℚ {lastDual4 (fun j i => (((Fc q).w j : Fin 4 → ℤ) i : ℚ)) (Fc q).rational_independent} =
              Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
          ∃ (Tspan : ℝ) (Wfixed : Set ℝ) (P : Submodule ℚ (Fin 4 → ℚ)),
            1 < Tspan ∧ Wfixed = {Q | Q ∈ Wc ∧ max B Tspan < Q} ∧
            ¬ BddAbove Wfixed ∧ P = LinearMap.ker (normalForm4 b) ∧
            Module.finrank ℚ P = 3 ∧
            (∀ q : Uc, q.val ∈ Wfixed →
              P = firstThreeSpan4 (fun j i => ((uc q j : Fin 4 → ℤ) i : ℚ)) ∧
              P = firstThreeSpan4 (fun j i => (((Fc q).w j : Fin 4 → ℤ) i : ℚ)) ∧
              minimaFlag4 (fun j => integerReal (uc q j : Fin 4 → ℤ)) 3 =
                minimaFlag4 (fun j => integerReal ((Fc q).w j : Fin 4 → ℤ)) 3 ∧
              Module.finrank ℝ (minimaFlag4 (fun j => integerReal (uc q j : Fin 4 → ℤ)) 3) = 3 ∧
              LinearIndependent ℚ (fun j : Fin 3 => fun i => ((uc q j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
            ∃ C₄ kappa : ℝ, 0 < C₄ ∧ 0 < kappa ∧ kappa = ((1 : ℝ)/24)/(216*C₄^3) ∧
              ∃ (Qfixed : Set ℝ) (hQfV : Qfixed ⊆ Vprime),
                Qfixed = cubePreimage3_4 Vprime Wfixed ∧ ¬ BddAbove Qfixed ∧
                (∀ Q ∈ Qfixed, Q^(3 : ℕ) ∈ Wfixed) ∧
                ∀ q : Qfixed,
                  let qV : V := ⟨q.val,hVpV (hQfV q.property)⟩
                  let hq := hQU q.val (hVU qV.property)
                  retainedOriginalWedges3_4 A₂ A₃ L hL q.val hq c₀ c₂ c₃ kappa delta (u qV)

theorem fixedCompoundPreimages3_of_data
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (delta : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (U V : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) (hVU : V ⊆ U)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃)
    (Vprime : Set ℝ) (hVpV : Vprime ⊆ V) (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (hc₀ : ∀ i, |c₀ i| ≤ 1) (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0)
    (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hu : ∀ q : V, originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
      (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q))
    (hpoint : ∀ q : Vprime,
      normalizationTransport3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ ∧
      (∀ s, tripleFrame4 (fun j => (u ⟨q.val,hVpV q.property⟩ j : Fin 4 → ℤ)) s ∈
        normalizedGroup3_4 A₂ A₃ q.val c₂ c₃) ∧
      normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 2 <
      normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 3*(q.val^(3 : ℕ))^(-delta/12))
    (hWeq : W = cubeImage3_4 Vprime)
    (hpersist : fixedCompoundData3_4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L)
      (by rw [compound3_det,hL,one_pow]) (delta/12)
      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) W hWR) :
    fixedCompoundPreimages3_4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR := by
  classical
  dsimp only [fixedCompoundPreimages3_4]
  obtain ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,b,B,hq1,hbint,hbn,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,P,hTspan,hF_eq,hF,hP,hPdim,hflags⟩ := hpersist
  have hFW : Wfixed ⊆ W := by
    intro R hRF
    rw [hF_eq] at hRF
    exact hUcW (hWcU hRF.1)
  let Qfixed := cubePreimage3_4 Vprime Wfixed
  have hQfV : Qfixed ⊆ Vprime := fun _ h => h.1
  have hQfixed : ¬ BddAbove Qfixed := cubePreimage3_unbounded Vprime W Wfixed hWeq hFW hF
    (fun Q hQ => hQU Q (hVU (hVpV hQ)))
  obtain ⟨C₄,kappa,hC₄,hk,hkeq,hcompare⟩ := source_compound_uniform_comparison3 A₂ A₃ L h₂ h₃ hL hAlg
  refine ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,b,B,hq1,hbint,hbn,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,P,hTspan,hF_eq,hF,hP,hPdim,hflags,C₄,kappa,hC₄,hk,hkeq,
    Qfixed,hQfV,rfl,hQfixed,fun Q hQ => hQ.2,?_⟩
  intro q
  dsimp only [retainedOriginalWedges3_4]
  let qV : V := ⟨q.val,hVpV (hQfV q.property)⟩
  have hq := hQU q.val (hVU qV.property)
  obtain ⟨_,_,hcomp⟩ := hcompare q.val hq c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  exact ⟨hu qV,(hpoint ⟨q.val,hQfV q.property⟩).1,
    (hpoint ⟨q.val,hQfV q.property⟩).2.1,hcomp,(hpoint ⟨q.val,hQfV q.property⟩).2.2⟩

theorem source_exterior3_fixed_compound_rank3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    let hBunit := sourceUnit42 B₀ hBdet
    ∃ Told T : ℝ, 1 < Told ∧ 1 < T ∧ Told ≤ T ∧ 0 < delta/12 ∧
      (∀ Q : ℝ, T < Q → 36 < Q^(delta/4)) ∧
      B₂.det = 1 ∧ B₃.det = 1 ∧ B₀.det = 1 ∧ IsUnit B₂ ∧ IsUnit B₃ ∧ IsUnit B₀ ∧
      (∀ s t, IsAlgebraic ℚ (B₀ s t)) ∧
      ∀ (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
        (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
        (_hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0),
        (∀ s, |normalizedWeights3_4 c₀ s| ≤ 1) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₂ s ∧ normalizedWeights3_4 c₂ s ≤ 0) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₃ s ∧ normalizedWeights3_4 c₃ s ≤ 0) ∧
        (∑ s, (normalizedWeights3_4 c₀ s+normalizedWeights3_4 c₂ s+normalizedWeights3_4 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 0 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 1*Q^(-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), V = {Q | Q ∈ U ∧ Told < Q} ∧ ¬ BddAbove V ∧
            ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              (∀ q : V, originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q) ∧ Told < q.val ∧
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 2 <
                  compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 3*q.val^(-delta/2)) ∧
              ∃ (Vprime : Set ℝ) (hVpV : Vprime ⊆ V), Vprime = {Q | Q ∈ V ∧ T < Q} ∧ ¬ BddAbove Vprime ∧
                ∃ (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R), W = cubeImage3_4 Vprime ∧ ¬ BddAbove W ∧
                  (∀ q : Vprime,
                    normalizationTransport3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ ∧
                    (∀ s, tripleFrame4 (fun j => (u ⟨q.val,hVpV q.property⟩ j : Fin 4 → ℤ)) s ∈
                      normalizedGroup3_4 A₂ A₃ q.val c₂ c₃) ∧
                    normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 2 <
                      normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 3*(q.val^(3 : ℕ))^(-delta/12)) ∧
                  (∀ (R : ℝ) (hR : R ∈ W), ∃ q : Vprime, R = q.val^(3 : ℕ) ∧
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 2 <
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 3*R^(-delta/12)) ∧
fixedCompoundPreimages3_4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR := by
  classical
  dsimp only
  obtain ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,htails⟩ :=
    source_exterior3_persistence_data4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,?_⟩
  intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨ha₀,ha₂,ha₃,hab,hfamilies⟩ := htails c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  refine ⟨ha₀,ha₂,ha₃,hab,?_⟩
  intro U hU hQU hgap
  obtain ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre,hpersist⟩ :=
    hfamilies U hU hQU hgap
  exact ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre,
    fixedCompoundPreimages3_of_data A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR
      h₂ h₃ hAlg hc₀ hc₂ hc₃ hb (fun q => (hu q).1) hpoint hWeq hpersist⟩

end
end CompoundFeasibility.Exterior3
