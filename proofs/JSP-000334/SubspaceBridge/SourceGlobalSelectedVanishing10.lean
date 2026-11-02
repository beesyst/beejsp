import SubspaceBridge.SourceSelectedNormalTransport10
import SubspaceBridge.SourceSelectedTail10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceGlobalSelected10
open SourceSampling10 OriginalDual10 SourceSelectedSet10 SourceSelectedUpper10 SchmidtNormal10
open SourceSchmidtContradiction10

theorem fixed_weight_original_cofactor_eventually_zero10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c2 c3 : Fin 10 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (c : Fin 3 → Fin 10 → ℝ) (hc : ∀ tau i, |c tau i| ≤ 1)
    (hb : (∑ tau, ∑ i, c tau i) = 0) (hf : ∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1)
    (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
    (hv : ∀ q, LinearIndependent ℝ (fun j => integerReal (v q j)))
    (w : (q : V) → Fin 10 → originalSourceGroup10 A2 A3 q.val c2 c3)
    (hw : ∀ q, LinearIndependent ℝ (fun j => integerReal (w q j : Fin 10 → ℤ)))
    (hflag : ∀ q, minimaFlag10 (fun j => integerReal (v q j)) 9 =
      minimaFlag10 (fun j => integerReal (w q j : Fin 10 → ℤ)) 9)
    (hw0 : ∀ q : V, ∀ (j : Fin 9) i, ‖(L *ᵥ integerReal (w q j.castSucc : Fin 10 → ℤ)) i‖ ≤
      (q.val^5)^(c 0 i-epsilon))
    (hw2 : ∀ q : V, ∀ (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ
      (fun k => ((w q j.castSucc : Fin 10 → ℤ) k : ℚ_[2]))) i‖ ≤ (q.val^5)^(c 1 i))
    (hw3 : ∀ q : V, ∀ (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ
      (fun k => ((w q j.castSucc : Fin 10 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^5)^(c 2 i)) :
    ∃ B : ℝ, ∀ q : V, B < q.val →
      ∀ s ∈ roundedSelector10 (q.val^5) (epsilon/2) (fun i => (q.val^5)^(c 0 i)) (c 1) (c 2),
        mixedProduct10 A2 A3 L (integerLastDual10 (v q)) s = 0 := by
  by_contra hfail
  let F := fun q : V => roundedSelector10 (q.val^5) (epsilon/2)
    (fun i => (q.val^5)^(c 0 i)) (c 1) (c 2)
  let P := fun (q : V) s => mixedProduct10 A2 A3 L (integerLastDual10 (v q)) s
  let W : Set ℝ := {q | ∃ hq : q ∈ V, ∃ s ∈ F ⟨q,hq⟩, P ⟨q,hq⟩ s ≠ 0}
  have hW : ¬ BddAbove W := unbounded_selected_nonzero_tail10 V F P hfail
  have hWV : W ⊆ V := fun _ h => h.choose
  let lift : W → V := fun q => ⟨q.val,hWV q.property⟩
  let vW := fun (q : W) => v (lift q)
  let wW := fun (q : W) => w (lift q)
  obtain ⟨K,hK,D,E,hD,hE,haux⟩ := source_auxiliary_samples10 A2 A3 L h2 h3 hL hAlg
  obtain ⟨eta,heta,_hmargin,m,hm,_hcount,hfamily⟩ := haux c2 c3 W hW vW
    (fun q => hv (lift q)) wW (fun q => hw (lift q)) (fun q => hflag (lift q))
    c epsilon he he1 hc hb (fun q => hw0 (lift q)) (fun q => hw2 (lift q)) (fun q => hw3 (lift q))
  obtain ⟨a,Cu,T,Cs,beta,_ha,_hCu,_hT,_hCs,_hCspos,_hCsone,_hbeta,hresult⟩ :=
    original_sample_schmidt_exclusion10 A2 A3 L h2 h3 hL hAlg c2 c3 hc2 hc3
      c (hc 0) hb hf epsilon he
  obtain ⟨B0,_hB0,_hBpos,_ht,_htu,_hte,_hr,_hrhalf,_hrw,_hw,_hdpos,_hppos,hsamples,hexclude⟩ :=
    hresult W vW eta D E heta hD m hm hfamily
  let S := Classical.choice (hsamples B0)
  have hbad (h : Fin m) : ∃ s ∈ F (lift (S.data.t h)), P (lift (S.data.t h)) s ≠ 0 := by
    obtain ⟨hq,s,hs,hn⟩ := (S.data.t h).property
    exact ⟨s,hs,hn⟩
  choose s hs hn using hbad
  have hnM (h : Fin m) : mixedProduct10 A2 A3 L (S.data.M h) (s h) ≠ 0 :=
    original_cofactor_sample_nonzero10 (fun q => hv (lift q)) S h (s h) (hn h)
  have hnative (h) := (mixedProduct10_ne_zero_iff A2 A3 L (S.data.M h) (s h)).mp (hnM h)
  exact (hexclude B0 le_rfl S).1 ⟨s,hs,fun h => (hnative h).1,
    fun h => (hnative h).2.1,fun h => (hnative h).2.2⟩

end CompoundFeasibility.SourceGlobalSelected10
