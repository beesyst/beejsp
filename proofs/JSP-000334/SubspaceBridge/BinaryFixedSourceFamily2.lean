import SubspaceBridge.BinaryFixedSourcePoint2
import SubspaceBridge.AllPointFixedFamily3
open scoped BigOperators Classical
namespace JSP000334

theorem binary_fixed_source_family (B C : ℚ) (d : ℕ) (hd : 0<d) (b c : ℤ)
    (hb : (b : ℚ)=(d : ℚ)*B) (hc : (c : ℚ)=(d : ℚ)*C) :
    ∃ cut : ℝ,1≤cut ∧ ∀ U : Set ℝ,¬BddAbove U →
    ∀ z : U → Fin 2 → ℤ,(∀ q,PrimitivePair (z q)) →
    (∀ q,z q 0 ≠ 0 ∧ z q 1 ≠ 0 ∧ B*(z q 0 : ℚ)+C*(z q 1 : ℚ) ≠ 0) →
    (∀ q,cut<(archPairHeight (z q) : ℝ)) →
    (∀ q,(weightedNormalizedProduct2 B C (z q 0 : ℚ) (z q 1 : ℚ) : ℝ)<
      Real.rpow (archPairHeight (z q) : ℝ) (-(5 : ℝ)/2)) →
    (∀ q,q.val=(archPairHeight (z q) : ℝ)^4) →
    ∃ k : Fin 3 → Fin 2,∃ v ∈ binaryWeightCandidates,∃ W : Set ℝ,W ⊆ U ∧ ¬BddAbove W ∧
    ∀ q : U,q.val ∈ W → 1<q.val ∧ ∀ tau i,
      binaryPatternNorms d b c k (z q) tau i≤Real.rpow q.val (v tau i-if tau=0 then (1 : ℝ)/384 else 0) := by
  obtain ⟨cut,hcut,hpoint⟩ := binary_weighted_fixed_source_point B C d hd b c hb hc
  refine ⟨cut,hcut,?_⟩
  intro U hU z hz hn htail hproduct hparam
  have hp (q : U) : ∃ k : Fin 3 → Fin 2,∃ v ∈ binaryWeightCandidates,
      1<q.val ∧ (∑ tau : Fin 3,∑ i : Fin 2,v tau i)=0 ∧ (∀ tau i,|v tau i|≤1) ∧
      ∀ tau i,binaryPatternNorms d b c k (z q) tau i≤
        Real.rpow q.val (v tau i-if tau=0 then (1 : ℝ)/384 else 0) := by
    simpa only [← hparam q] using hpoint (z q) (hz q) (hn q).1 (hn q).2.1 (hn q).2.2 (htail q) (hproduct q)
  choose k v hv hQ hbal hbound hlocal using hp
  let F : Set ((Fin 3 → Fin 2) × (Fin 3 → Fin 2 → ℝ)) := Set.univ ×ˢ binaryWeightCandidates
  have hF : F.Finite := Set.finite_univ.prod binary_weight_candidates_finite
  let a (Q : ℝ) := if h : Q ∈ U then (k ⟨Q,h⟩,v ⟨Q,h⟩) else (fun _ => 0,fun _ _ => 0)
  have ha : ∀ Q ∈ U,a Q ∈ F := by
    intro Q h
    simp only [a,dif_pos h,F,Set.mem_prod,Set.mem_univ,true_and]
    exact hv ⟨Q,h⟩
  obtain ⟨⟨K,V⟩,hKV,hW⟩ := allpoint_finite_parameter_fiber3 F hF U hU a ha
  let W : Set ℝ := {Q | Q ∈ U ∧ a Q=(K,V)}
  refine ⟨K,V,hKV.2,W,fun Q h => h.1,hW,?_⟩
  intro q hq
  have hh := hq.2
  simp only [a,dif_pos q.property] at hh
  have he : k q=K ∧ v q=V := Prod.mk.inj hh
  exact ⟨hQ q,by simpa only [he.1,he.2] using hlocal q⟩

end JSP000334
