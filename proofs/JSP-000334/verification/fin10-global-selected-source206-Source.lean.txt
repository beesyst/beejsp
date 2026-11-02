import SubspaceBridge.SourceGlobalSelectedVanishing10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceGlobalSelected10
open SourceSampling10 OriginalDual10 SourceSelectedSet10 SourceSelectedUpper10 SchmidtNormal10

theorem original_refined_selected_vanishing10
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
    ∃ V : Set ℝ, ∃ hVU : V ⊆ U, ¬ BddAbove V ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
    ∃ c : Fin 3 → Fin 10 → ℝ, (∀ tau i, |c tau i| ≤ 1) ∧
      (∑ tau, ∑ i, c tau i) = 0 ∧ (∀ i, c 1 i = c2 i/5 ∧ c 2 i = c3 i/5) ∧
    ∃ B : ℝ, ∀ q : V, B < q.val →
      ∀ s ∈ roundedSelector10 (q.val^5) (epsilon/2) (fun i => (q.val^5)^(c 0 i)) (c 1) (c 2),
        mixedProduct10 A2 A3 L
          (integerLastDual10 (fun j => (u ⟨q.val,hVU q.property⟩ j : Fin 10 → ℤ))) s = 0 ∧
        ∀ M a : Fin 10 → ℤ, M ≠ 0 → (∑ i, a i*M i) = 1 →
          (∀ j : Fin 9, (∑ i, M i*(u ⟨q.val,hVU q.property⟩ j.castSucc : Fin 10 → ℤ) i) = 0) →
          mixedProduct10 A2 A3 L M s = 0 := by
  have h2u : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2]; exact isUnit_one)
  have h3u : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3]; exact isUnit_one)
  have hLu : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (by rw [hLd]; exact isUnit_one)
  refine ⟨hLu,?_⟩
  intro c0 c2 c3 hc0 hc2 hc3 hb delta hd U hU hQU u hu hatt hgap
  obtain ⟨V,hVU,hV,epsilon,he,he1,c,hc,hbalance,hfinite,hframes⟩ :=
    source_original_fixed_weight_family10 A2 A3 L h2u h3u hLu c0 c2 c3 hc0 hc2 hc3
      hb delta hd U hU hQU u hu hatt hgap
  choose w hw hflag hw0 hw2 hw3 using hframes
  let v := fun (q : V) j => (u ⟨q.val,hVU q.property⟩ j : Fin 10 → ℤ)
  have hv (q : V) : LinearIndependent ℝ (fun j => integerReal (v q j)) := hu ⟨q.val,hVU q.property⟩
  obtain ⟨B,hzero⟩ := fixed_weight_original_cofactor_eventually_zero10 A2 A3 L h2 h3 hLd ha
    c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) c hc hbalance hfinite epsilon he he1
    V v hv w hw hflag hw0 hw2 hw3
  refine ⟨V,hVU,hV,epsilon,he,he1,c,hc,hbalance,hfinite,B,?_⟩
  intro q hq s hs
  have hz := hzero q hq s hs
  refine ⟨hz,?_⟩
  intro M a hM hbez hann
  let f : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hvQ : LinearIndependent ℚ (fun j i => (v q j i : ℚ)) := by
    apply LinearIndependent.of_comp f
    convert (hv q).restrict_scalars' ℚ using 1
  obtain ⟨hg,hscale,_hgcd⟩ := SourcePrimitiveHeight10.primitive_original_cofactor_factor10
    (v q) hvQ M a hM hbez hann
  by_contra hn
  have hn' := (mixedProduct10_int_mul_ne_zero_iff A2 A3 L _ hg M s).mpr hn
  have heq : integerLastDual10 (v q) = fun i => (∑ i, a i*integerLastDual10 (v q) i)*M i := funext hscale
  rw [← heq] at hn'
  exact hn' hz

end CompoundFeasibility.SourceGlobalSelected10
