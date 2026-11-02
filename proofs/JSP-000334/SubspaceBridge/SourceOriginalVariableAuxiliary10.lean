import SubspaceBridge.SourceOriginalPowerFrame10
import SubspaceBridge.SourceOriginalFixedWeights10
import SubspaceBridge.SourceOriginalAuxiliary10
import SubspaceBridge.SourceOriginalEnvelope10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSampling10 SourceSelectedSet10 OriginalDual10 OriginalDeformation10
noncomputable section

theorem original_variable_auxiliary_family10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ D0 E0 : ℝ, 1 ≤ D0 ∧ 1 ≤ E0 ∧
      ∀ (U : Set ℝ), ¬ BddAbove U → ∀ (hQU : ∀ q ∈ U, 1 < q)
        (D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0),
      ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
      ∃ e : ℝ, 0 < e ∧ e < 1 ∧ ∃ c : Fin 3 → Fin 10 → ℝ,
        (∀ tau i, |c tau i| ≤ 1) ∧ (∑ tau, ∑ i, c tau i) = 0 ∧
        (∀ i, c 1 i ≤ 0 ∧ c 2 i ≤ 0) ∧
      ∃ eta : ℝ, 0 < eta ∧ 4000*eta < e ∧ ∃ m : ℕ, ∃ hm : 0 < m,
        4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
        ∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
          Nonempty (OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm) := by
  obtain ⟨K,hK,D0,E0,hD0,hE0,haux⟩ := source_auxiliary_samples10 A2 A3 L h2 h3 hLd hAlg
  refine ⟨K,hK,D0,E0,hD0,hE0,?_⟩
  intro U hU hQU D
  have hprops (q : U) := original_power_weights_bounds10 (D q)
  obtain ⟨V,hVU,hV,e,he,he1,c,hc,hbal,hcf,hbounds⟩ := select_original_balanced_weights10
    U hU (fun q => originalPowerWeights10 (D q)) (fun q => (hprops q).1)
    (fun q => (hprops q).2.1) (fun q => (hprops q).2.2.1) (fun q => (hprops q).2.2.2) delta hd
  let v : V → Fin 10 → Fin 10 → ℤ := fun q => (D ⟨q.val,hVU q.property⟩).u
  have hv (q : V) : LinearIndependent ℝ (fun j => integerReal (v q j)) := (D ⟨q.val,hVU q.property⟩).independent
  have hQ (q : V) : 1 < q.val := hQU q.val (hVU q.property)
  have hQ5 (q : V) : 1 < q.val^5 := one_lt_pow₀ (hQ q) (by decide)
  have hpoint (q : V) := original_power_frame_bounds10 (D ⟨q.val,hVU q.property⟩)
  have hreal (q : V) (j : Fin 9) (i : Fin 10) :
      ‖(L *ᵥ integerReal (v q j.castSucc)) i‖ ≤ (q.val^5)^(c 0 i-e) :=
    ((hpoint q).1 j i).trans (Real.rpow_le_rpow_of_exponent_le (hQ5 q).le (hbounds q i).1)
  have htwo (q : V) (j i : Fin 10) :
      ‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ (fun k => (v q j k : ℚ_[2]))) i‖ ≤ (q.val^5)^(c 1 i) :=
    ((hpoint q).2.1 j i).trans (Real.rpow_le_rpow_of_exponent_le (hQ5 q).le (hbounds q i).2.1)
  have hthree (q : V) (j i : Fin 10) :
      ‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ (fun k => (v q j k : ℚ_[3]))) i‖ ≤ (q.val^5)^(c 2 i) :=
    ((hpoint q).2.2 j i).trans (Real.rpow_le_rpow_of_exponent_le (hQ5 q).le (hbounds q i).2.2)
  have hmem (q : V) (j : Fin 10) : v q j ∈ originalSourceGroup10 A2 A3 q.val
      (fun i => 5*c 1 i) (fun i => 5*c 2 i) := by
    let Dq := D ⟨q.val,hVU q.property⟩
    have hsource := (normalized_source_group_exact10 A2 A3 q.val (hQ q) Dq.f2 Dq.f3
      Dq.nonpos2 Dq.nonpos3 (v q j)).mpr ⟨Dq.member2 j,Dq.member3 j⟩
    apply original_source_group_envelope10 A2 A3 q.val (hQ q)
      (fun i => normalizedFinite10 2 q.val (Dq.f2 i))
      (fun i => normalizedFinite10 3 q.val (Dq.f3 i))
      (fun i => 5*c 1 i) (fun i => 5*c 2 i) _ _
      (fun i => by change 5*c 1 i ≤ 0; linarith [(hcf i).1])
      (fun i => by change 5*c 2 i ≤ 0; linarith [(hcf i).2]) hsource
    · intro i
      have hh := (hbounds q i).2.1
      change normalizedFinite10 2 q.val (Dq.f2 i)/5 ≤ c 1 i at hh
      change normalizedFinite10 2 q.val (Dq.f2 i) ≤ 5*c 1 i
      linarith
    · intro i
      have hh := (hbounds q i).2.2
      change normalizedFinite10 3 q.val (Dq.f3 i)/5 ≤ c 2 i at hh
      change normalizedFinite10 3 q.val (Dq.f3 i) ≤ 5*c 2 i
      linarith
  let w : (q : V) → Fin 10 → originalSourceGroup10 A2 A3 q.val
      (fun i => 5*c 1 i) (fun i => 5*c 2 i) := fun q j => ⟨v q j,hmem q j⟩
  obtain ⟨eta,heta,hmargin,m,hm,hcount,hsamples⟩ := haux _ _ V hV v hv w hv (fun _ => rfl)
    c e he he1 hc hbal hreal (fun q j => htwo q j.castSucc) (fun q j => hthree q j.castSucc)
  exact ⟨V,hVU,hV,e,he,he1,c,hc,hbal,hcf,eta,heta,hmargin,m,hm,hcount,hsamples⟩

end
end CompoundFeasibility.SourceOriginalVariable10
