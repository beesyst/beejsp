import SubspaceBridge.SourceOriginalAuxiliaryInternal10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10

theorem source_fin10_original_auxiliary_family10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    : ∃ hLu : IsUnit L,
    ∀ (c0 c2 c3 : Fin 10 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) (delta : ℝ) (hd : 0 < delta)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (u : (q : U) → Fin 10 → originalSourceGroup10 A2 A3 q.val c2 c3)
    (hu : ∀ q : U, LinearIndependent ℝ (fun i => integerReal (u q i : Fin 10 → ℤ)))
    (hatt : ∀ (q : U) (i : Fin 10), coordinateGauge10
      (originalCoordinates10 L hLu q.val (hQU q.val q.property) c0)
      (integerReal (u q i : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L
        hLu q.val (hQU q.val q.property) c0 c2 c3 i)
    (hgap : ∀ q : U, sourceMinima10 A2 A3 L hLu
      q.val (hQU q.val q.property) c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hLu
        q.val (hQU q.val q.property) c0 c2 c3 9*q.val^(-delta)),
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
    ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
    ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
    ∃ c : Fin 3 → Fin 10 → ℝ, (∀ tau i, |c tau i| ≤ 1) ∧
      (∑ tau, ∑ i, c tau i) = 0 ∧ (∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5) ∧
    ∃ eta : ℝ, 0 < eta ∧ 4000*eta < epsilon ∧
    ∃ m : ℕ, ∃ hm : 0 < m,
      4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
      ∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
        Nonempty (OriginalAuxiliarySample10 A2 A3 L c2 c3 V
          (fun q j => (u ⟨q.val,hVU q.property⟩ j : Fin 10 → ℤ))
          c epsilon eta D E B rho m hm) := by
  have h2u : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2]; exact isUnit_one)
  have h3u : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3]; exact isUnit_one)
  have hLu : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (by rw [hLd]; exact isUnit_one)
  refine ⟨hLu,?_⟩
  exact source_original_auxiliary_family10_internal A2 A3 L h2 h3 hLd ha h2u h3u hLu

end CompoundFeasibility.SourceSampling10
