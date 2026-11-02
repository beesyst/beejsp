import SubspaceBridge.CompoundGap42
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

def firstFiveSpan42 {K : Type*} [Field K] (v : Fin 6 → Fin 6 → K) : Submodule K (Fin 6 → K) :=
  Submodule.span K (Set.range (fun i : Fin 5 => v i.castSucc))

theorem firstFiveSpan42_finrank {K : Type*} [Field K] (v : Fin 6 → Fin 6 → K)
    (hv : LinearIndependent K v) : Module.finrank K (firstFiveSpan42 v) = 5 := by
  simpa [firstFiveSpan42] using finrank_span_eq_card (hv.comp Fin.castSucc (Fin.castSucc_injective _))

theorem gap_margin42 (B x y Q delta : ℝ) (hB : 0 < B) (hy : 0 < y) (hQ : 1 < Q)
    (hcut : B < Q ^ (delta / 2)) (hgap : x < y * Q ^ (-delta / 2)) : B * x < y := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have he : Q ^ (delta / 2) * Q ^ (-delta / 2) = 1 := by
    rw [← Real.rpow_add hq]
    rw [show delta / 2 + -delta / 2 = 0 by ring,Real.rpow_zero]
  calc
    _ < B * (y * Q ^ (-delta / 2)) := mul_lt_mul_of_pos_left hgap hB
    _ < Q ^ (delta / 2) * (y * Q ^ (-delta / 2)) :=
      mul_lt_mul_of_pos_right hcut (mul_pos hy (Real.rpow_pos_of_pos hq _))
    _ = y * (Q ^ (delta / 2) * Q ^ (-delta / 2)) := by ring
    _ = _ := by rw [he,mul_one]

theorem pairProductOrder42_last (a : Fin 4 → ℝ) : pairProductOrder42 a 5 = 5 := by
  unfold pairProductOrder42
  split_ifs <;> simp [Equiv.swap_apply_def]

private theorem integer_det_cast_iff42
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℤ) :
    (U.map (Int.castRingHom ℚ)).det ≠ 0 ↔
    (U.map (Int.castRingHom ℝ)).det ≠ 0 := by

  have hq :
      (U.map (Int.castRingHom ℚ)).det = (U.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det U).symm

  have hr :
      (U.map (Int.castRingHom ℝ)).det = (U.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det U).symm

  rw [hq, hr]
  norm_cast


theorem integer6_independent_iff42 (u : Fin 6 → Fin 6 → ℤ) :
    LinearIndependent ℚ (fun j i => (u j i : ℚ)) ↔
    LinearIndependent ℝ (fun j i => (u j i : ℝ)) := by

  let U : Matrix (Fin 6) (Fin 6) ℤ := u

  let UQ : Matrix (Fin 6) (Fin 6) ℚ :=
    U.map (Int.castRingHom ℚ)

  let UR : Matrix (Fin 6) (Fin 6) ℝ :=
    U.map (Int.castRingHom ℝ)

  change LinearIndependent ℚ (Matrix.row UQ) ↔
    LinearIndependent ℝ (Matrix.row UR)

  rw [
    Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det,
    Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero,
    isUnit_iff_ne_zero
  ]

  have hdet : UQ.det ≠ 0 ↔ UR.det ≠ 0 := by
    simpa only [UQ, UR] using (integer_det_cast_iff42 U)

  exact hdet

theorem integer_firstFive_mem_iff42 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ))) (x : Fin 6 → ℤ) :
    (fun i => (x i : ℚ)) ∈ firstFiveSpan42 (fun j i => (v j i : ℚ)) ↔
      (fun i => (x i : ℝ)) ∈ firstFiveSpan42 (fun j i => (v j i : ℝ)) := by
  have hvq := (integer6_independent_iff42 v).mpr hv
  let w : Fin 6 → Fin 6 → ℤ := Fin.snoc (fun i : Fin 5 => v i.castSucc) x
  have heq : LinearIndependent ℚ (Fin.snoc (fun j : Fin 5 => fun i => (v j.castSucc i : ℚ)) (fun i => (x i : ℚ))) ↔
      LinearIndependent ℝ (Fin.snoc (fun j : Fin 5 => fun i => (v j.castSucc i : ℝ)) (fun i => (x i : ℝ))) := by
    have hq : (fun j i => (w j i : ℚ)) = Fin.snoc (fun j : Fin 5 => fun i => (v j.castSucc i : ℚ)) (fun i => (x i : ℚ)) := by
      funext j i
      fin_cases j <;> norm_num [w,Fin.snoc]
    have hr : (fun j i => (w j i : ℝ)) = Fin.snoc (fun j : Fin 5 => fun i => (v j.castSucc i : ℝ)) (fun i => (x i : ℝ)) := by
      funext j i
      fin_cases j <;> norm_num [w,Fin.snoc]
    rw [← hq,← hr]
    exact integer6_independent_iff42 w
  rw [linearIndependent_fin_snoc,linearIndependent_fin_snoc] at heq
  have hpq := hvq.comp Fin.castSucc (Fin.castSucc_injective _)
  have hpr := hv.comp Fin.castSucc (Fin.castSucc_injective _)
  have hn : ((fun i => (x i : ℚ)) ∉ firstFiveSpan42 (fun j i => (v j i : ℚ))) ↔
      ((fun i => (x i : ℝ)) ∉ firstFiveSpan42 (fun j i => (v j i : ℝ))) :=
    ⟨fun h => (heq.mp ⟨hpq,h⟩).2,fun h => (heq.mpr ⟨hpr,h⟩).2⟩
  exact not_iff_not.mp hn

theorem integer_firstFive_span_eq42 (v w : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ)))
    (hw : LinearIndependent ℝ (fun j i => (w j i : ℝ)))
    (he : firstFiveSpan42 (fun j i => (v j i : ℝ)) = firstFiveSpan42 (fun j i => (w j i : ℝ))) :
    firstFiveSpan42 (fun j i => (v j i : ℚ)) = firstFiveSpan42 (fun j i => (w j i : ℚ)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply (integer_firstFive_mem_iff42 w hw (v i.castSucc)).mpr
    rw [← he]
    exact Submodule.subset_span ⟨i,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply (integer_firstFive_mem_iff42 v hv (w i.castSucc)).mpr
    rw [he]
    exact Submodule.subset_span ⟨i,rfl⟩

theorem direct_short_mem_firstFive42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j : Fin 6 → ℤ)))
    (hatt : ∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀)
      (integerReal (v j : Fin 6 → ℤ)) = directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j)
    (hgap : directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5)
    (x : directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hx : coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (x : Fin 6 → ℤ)) <
      directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5) :
    integerReal (x : Fin 6 → ℤ) ∈ firstFiveSpan42 (fun j => integerReal (v j : Fin 6 → ℤ)) := by
  classical
  by_contra hnot
  let u : Fin 5 → Fin 6 → ℝ := fun i => integerReal (v i.castSucc : Fin 6 → ℤ)
  let w : Fin 6 → Fin 6 → ℝ := Fin.snoc u (integerReal (x : Fin 6 → ℤ))
  have hi : LinearIndependent ℝ w := linearIndependent_fin_snoc.mpr
    ⟨hv.comp Fin.castSucc (Fin.castSucc_injective _),hnot⟩
  let r := max (directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4)
    (coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (x : Fin 6 → ℤ)))
  have hr : r < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 := max_lt hgap hx
  have hm := (directMinima42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).2
  have hle : directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 ≤ r := by
    apply (directMinima42_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5).2.2.2
    refine ⟨w,hi,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [w] using (show integerReal (x : Fin 6 → ℤ) ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃) from ⟨_,x.property,rfl⟩)
      · simpa [w,u] using (show integerReal (v j.castSucc : Fin 6 → ℤ) ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃) from ⟨_,(v j.castSucc).property,rfl⟩)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (x : Fin 6 → ℤ)) ≤ r
        exact le_max_right _ _
      · have hj : j.castSucc ≤ (4 : Fin 6) := by
          change j.val ≤ 4
          omega

        have hw :
            w j.castSucc =
              integerReal (v j.castSucc : Fin 6 → ℤ) := by
          simp only [w, Fin.snoc_castSucc, u]

        rw [hw, hatt]
        exact (hm hj).trans (le_max_left _ _)
  exact (not_lt_of_ge hle) hr


def orderedWedges42 (u : Fin 4 → Fin 4 → ℤ) (a : Fin 4 → ℝ) : Fin 6 → Fin 6 → ℤ :=
  fun j => compoundFrame u (pairProductOrder42 a j)

def sourceHyperplane42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (κ : ℝ)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃) : Prop :=
  let w := orderedWedges42 (fun i => (u i : Fin 4 → ℤ)) (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  LinearIndependent ℝ (fun j => integerReal (u j : Fin 4 → ℤ)) ∧
  (∀ j, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal (u j : Fin 4 → ℤ)) =
    sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
  LinearIndependent ℝ (fun j => integerReal (v j : Fin 6 → ℤ)) ∧
  (∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (v j : Fin 6 → ℤ)) =
    directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
  (∀ j, w j ∈ compoundSourceGroup6 A₂ A₃ Q c₂ c₃) ∧
  (∀ j, w j ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃) ∧
  LinearIndependent ℝ (fun j => integerReal (w j)) ∧
  LinearIndependent ℚ (fun j i => (w j i : ℚ)) ∧
  (∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (w j)) ≤
    2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
  (∀ i : Fin 5, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (w i.castSucc)) ≤
    (12 / κ) * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4) ∧
  (∀ i : Fin 5, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (v i.castSucc : Fin 6 → ℤ)) ≤
    directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4) ∧
  (12 / κ) * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 ∧
  Module.finrank ℝ (firstFiveSpan42 (fun j => integerReal (v j : Fin 6 → ℤ))) = 5 ∧
  Module.finrank ℚ (firstFiveSpan42 (fun j i => ((v j : Fin 6 → ℤ) i : ℚ))) = 5 ∧
  firstFiveSpan42 (fun j => integerReal (w j)) = firstFiveSpan42 (fun j => integerReal (v j : Fin 6 → ℤ)) ∧
  firstFiveSpan42 (fun j i => (w j i : ℚ)) = firstFiveSpan42 (fun j i => ((v j : Fin 6 → ℤ) i : ℚ)) ∧
  w 5 = wedge (u 2 : Fin 4 → ℤ) (u 3 : Fin 4 → ℤ)

theorem ordered_source_wedges42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j : Fin 4 → ℤ)))
    (hatt : ∀ j, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal (u j : Fin 4 → ℤ)) =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) :
    let w := orderedWedges42 (fun i => (u i : Fin 4 → ℤ)) (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃)
    (∀ j, w j ∈ compoundSourceGroup6 A₂ A₃ Q c₂ c₃) ∧
    LinearIndependent ℚ (fun j i => (w j i : ℚ)) ∧ LinearIndependent ℝ (fun j => integerReal (w j)) ∧
    ∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (w j)) ≤
      2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  classical
  let a := sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let σ := pairProductOrder42 a
  have harch j : ∀ i, |(L *ᵥ integerReal (u j : Fin 4 → ℤ)) i| ≤ a j * Q ^ c₀ i :=
    (originalCoordinates4_bounds L hL Q hQ c₀ _ _).mp (hatt j).le
  obtain ⟨hmem,hq,hr,_,_,hbound⟩ := source_compound_bridge42 A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
    (fun j => (u j : Fin 4 → ℤ)) (fun j => (u j).property) hu L (fun i => Q ^ c₀ i) a
    (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
    (fun i => ((sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 i).le) harch
  refine ⟨fun j => hmem (σ j),hq.comp σ σ.injective,hr.comp σ σ.injective,?_⟩
  intro j
  apply (compoundCoordinates42_bounds L hL Q hQ c₀ _ _).mpr
  intro s
  have hp := sourcePairProducts42_reindex A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  change sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = a (lo (σ j)) * a (hi (σ j)) at hp
  change |(compound L *ᵥ (fun k => (compoundFrame (fun i => (u i : Fin 4 → ℤ)) (σ j) k : ℝ))) s| ≤ _
  rw [hp]
  convert hbound (σ j) s using 1 <;> ring

theorem source_pointwise_hyperplane42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (κ Q : ℝ) (hk : 0 < κ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j : Fin 4 → ℤ)))
    (ha : ∀ j, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal (u j : Fin 4 → ℤ)) = sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j)
    (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j : Fin 6 → ℤ)))
    (hb : ∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (v j : Fin 6 → ℤ)) = directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j)
    (hcomp : κ * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 ≤ sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4)
    (hgap : directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5)
    (hmargin : (12 / κ) * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5) :
    sourceHyperplane42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ κ u v := by
  let w := orderedWedges42 (fun i => (u i : Fin 4 → ℤ)) (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  obtain ⟨hw,hq,hr,hbound⟩ := ordered_source_wedges42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ u hu ha
  have hd j : w j ∈ directCompoundGroup42 A₂ A₃ Q c₂ c₃ := summed_le_directCompoundGroup42 A₂ A₃ Q c₂ c₃ (hw j)
  have hscale : κ * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 ≤ 6 * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 :=
    hcomp.trans (directMinima42_comparison A₂ A₃ L hL Q hQ c₀ c₂ c₃ hc₂ hc₃ 4).2
  have hmu : 2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 ≤ (12 / κ) * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 := by
    apply (mul_le_mul_left hk).mp
    calc
      _ = 2 * (κ * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4) := by ring
      _ ≤ 2 * (6 * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4) := mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = _ := by field_simp; ring
  have hpref (i : Fin 5) : coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (w i.castSucc)) ≤ (12 / κ) * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 :=
    (hbound i.castSucc).trans ((mul_le_mul_of_nonneg_left
      ((sourcePairProducts42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).2
        (show i.castSucc ≤ (4 : Fin 6) by change i.val ≤ 4; omega)) (by norm_num)).trans hmu)
  have hmem (i : Fin 5) : integerReal (w i.castSucc) ∈ firstFiveSpan42 (fun j => integerReal (v j : Fin 6 → ℤ)) :=
    direct_short_mem_firstFive42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ v hv hb hgap ⟨w i.castSucc,hd _⟩ ((hpref i).trans_lt hmargin)
  have he : firstFiveSpan42 (fun j => integerReal (w j)) = firstFiveSpan42 (fun j => integerReal (v j : Fin 6 → ℤ)) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hmem i
    · rw [firstFiveSpan42_finrank _ hr,firstFiveSpan42_finrank _ hv]
  have hvq := (integer6_independent_iff42 (fun j => (v j : Fin 6 → ℤ))).mpr hv
  refine ⟨hu,ha,hv,hb,hw,hd,hr,hq,hbound,hpref,?_,hmargin,
    firstFiveSpan42_finrank _ hv,firstFiveSpan42_finrank _ hvq,he,?_,?_⟩
  · intro i
    rw [hb]
    exact (directMinima42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).2 (show i.castSucc ≤ (4 : Fin 6) by change i.val ≤ 4; omega)
  · exact integer_firstFive_span_eq42 w (fun j => (v j : Fin 6 → ℤ)) hr hv he
  · change compoundFrame (fun i => (u i : Fin 4 → ℤ)) (pairProductOrder42 _ 5) = _
    rw [pairProductOrder42_last]
    rfl

theorem source_uniform_hyperplane42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → T < Q →
        sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 < sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta) →
        ∃ (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
          (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃),
          sourceHyperplane42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ κ u v := by
  obtain ⟨_,_,κ,_,_,hk,_,hcomp⟩ := source_compound_uniform_comparison42 A₂ A₃ L h₂ h₃ hL
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (12 / κ) delta hd
  refine ⟨κ,T,hk,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal hTQ hg
  have hbound := source_direct_gap_bound42 A₂ A₃ L hL κ Q delta hk hQ c₀ c₂ c₃ hc₂ hc₃
    (fun j => (hcomp Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal j).1) hg
  have hp := (directMinima42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
  have hgap := absorb_compound_gap42 _ _ (12 / κ) Q delta (hp 5) hQ (hcut Q hTQ) hbound
  have hmargin := gap_margin42 (12 / κ) _ _ Q delta (by positivity) (hp 5) hQ (hcut Q hTQ) hgap
  have hplain : directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 4 < directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 5 := by
    apply hgap.trans_le
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hQ.le (show -delta / 2 ≤ 0 by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (hp 5).le
  obtain ⟨u,hu,_,_,ha,_⟩ := exists_sourceMinima4_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  obtain ⟨v,hv,_,_,hb⟩ := exists_directMinima42_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨u,v,source_pointwise_hyperplane42 A₂ A₃ L hL κ Q hk hQ c₀ c₂ c₃ hc₂ hc₃
    u hu ha v hv hb (hcomp Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal 4).1 hplain hmargin⟩

end
end CompoundFeasibility
