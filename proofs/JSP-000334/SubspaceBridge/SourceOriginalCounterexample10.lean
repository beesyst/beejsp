import SubspaceBridge.SourceOriginalBadTail10
import SubspaceBridge.SourceOriginalSampleHeight10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSampling10 SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10 SchmidtNormal10
noncomputable section

theorem original_counterexample_schmidt_inputs10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) (S0 : Finset MixedIndex10) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ D0 E0 alpha C_upper T : ℝ, 1 ≤ D0 ∧ 1 ≤ E0 ∧ 0 < alpha ∧ 0 < C_upper ∧ 1 < T ∧
      ∀ (U : Set ℝ) (hQU : ∀ q ∈ U, 1 < q)
        (D : (q : U) → OriginalData10 A2 A3 L hL q.val (hQU q.val q.property) delta S0),
      (¬ ∃ B : ℝ, ∀ q : U, B < q.val → ∀ s ∈ S0,
        mixedProduct10 A2 A3 L (integerLastDual10 (D q).u) s = 0) →
      ∀ B1 : ℝ, ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
        (∀ q : V, max T B1 < q.val) ∧
      ∃ e : ℝ, 0 < e ∧ e < 1 ∧ ∃ c : Fin 3 → Fin 10 → ℝ,
        (∀ tau i, |c tau i| ≤ 1) ∧ (∑ tau, ∑ i, c tau i) = 0 ∧
        (∀ i, c 1 i ≤ 0 ∧ c 2 i ≤ 0) ∧
      ∃ eta : ℝ, 0 < eta ∧ 4000*eta < e ∧ ∃ m : ℕ, ∃ hm : 0 < m,
        4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
        (∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
          Nonempty (OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm)) ∧
        ∀ (rho B : ℝ)
          (S : OriginalAuxiliarySample10 A2 A3 L (fun i => 5*c 1 i) (fun i => 5*c 2 i)
            V (fun q => (D ⟨q.val,hVU q.property⟩).u) c e eta D0 E0 B rho m hm) (h : Fin m),
          ((S.data.t h).val^5)^alpha ≤ (normalHeight10 (S.data.M h) : ℝ) ∧
          (normalHeight10 (S.data.M h) : ℝ) ≤ C_upper*((S.data.t h).val^5)^9 ∧
          ∃ s ∈ S0, mixedProduct10 A2 A3 L (S.data.M h) s ≠ 0 ∧
            mixedProduct10 A2 A3 L (S.data.M h) s ≤ 362880*((S.data.t h).val^5)^(-17*delta/10) := by
  have h2u : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [h2]; exact isUnit_one)
  have h3u : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [h3]; exact isUnit_one)
  obtain ⟨alpha,C_upper,Tg,halpha,hCu,hTg,hheight⟩ :=
    original_fixed_set_sample_height10 A2 A3 L h2 h3 hLd hL hAlg delta hd
  obtain ⟨T,hT,htail⟩ := original_fixed_selector_bad_tail10 A2 A3 L h2 h3 hLd h2u h3u hL delta hd S0
  obtain ⟨K,hK,D0,E0,hD0,hE0,hfamily⟩ := original_variable_auxiliary_family10 A2 A3 L h2 h3 hLd hL hAlg delta hd S0
  refine ⟨K,hK,D0,E0,alpha,C_upper,max T Tg,hD0,hE0,halpha,hCu,hT.trans_le (le_max_left _ _),?_⟩
  intro U hQU D hfail B1
  obtain ⟨W,hWU,hW,hbad⟩ := htail U hQU D hfail (max B1 Tg)
  let hQW : ∀ q ∈ W, 1 < q := fun q hq => hQU q (hWU hq)
  let DW : (q : W) → OriginalData10 A2 A3 L hL q.val (hQW q.val q.property) delta S0 :=
    fun q => D ⟨q.val,hWU q.property⟩
  obtain ⟨V,hVW,hV,e,he,he1,c,hc,hbal,hcf,eta,heta,hmargin,m,hm,hcount,hsamples⟩ :=
    hfamily W hW hQW DW
  let hVU : V ⊆ U := fun q hq => hWU (hVW hq)
  have hlarge (q : V) : max (max T Tg) B1 < q.val := by
    have hh := (hbad ⟨q.val,hVW q.property⟩).1
    exact max_lt_iff.mpr ⟨max_lt_iff.mpr ⟨(le_max_left _ _).trans_lt hh,
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hh⟩,
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hh⟩
  refine ⟨V,hVU,hV,hlarge,
    e,he,he1,c,hc,hbal,hcf,eta,heta,hmargin,m,hm,hcount,hsamples,?_⟩
  intro rho B S h
  let hQV : ∀ q ∈ V, 1 < q := fun q hq => hQU q (hVU hq)
  let DV : (q : V) → OriginalData10 A2 A3 L hL q.val (hQV q.val q.property) delta S0 :=
    fun q => D ⟨q.val,hVU q.property⟩
  have hbadV (q : V) : ∃ s ∈ S0, mixedProduct10 A2 A3 L (integerLastDual10 (DV q).u) s ≠ 0 :=
    (hbad ⟨q.val,hVW q.property⟩).2.1
  have hTq : Tg < (S.data.t h).val :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans_lt (hlarge (S.data.t h))
  have hTQ : Tg < (S.data.t h).val^5 := hTq.trans_le
    (le_self_pow₀ (hQV _ (S.data.t h).property).le (by decide))
  have hgrowth := hheight S0 V hQV DV hbadV _ _ c (fun i => hc 0 i) e he
    eta D0 E0 B rho m hm S h hTQ
  exact ⟨hgrowth.1,hgrowth.2,original_fixed_set_sample_transfer10 h2 h3 hLd hQV DV hbadV S h⟩

end
end CompoundFeasibility.SourceOriginalVariable10
