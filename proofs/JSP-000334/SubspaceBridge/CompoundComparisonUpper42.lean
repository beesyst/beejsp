import SubspaceBridge.CompoundPairProducts42
open scoped BigOperators Matrix
namespace CompoundFeasibility

theorem exists_source_compound_ordered_frame42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ w : Fin 6 → compoundSourceGroup6 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 6 → ℤ)) ∧
      ∀ j, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀)
        (integerReal (w j : Fin 6 → ℤ)) ≤
          2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  classical
  obtain ⟨u,hu,hpos,_,_,harch⟩ := exists_sourceMinima4_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let v : Fin 4 → Fin 4 → ℤ := fun j => (u j : Fin 4 → ℤ)
  let a := sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let σ := pairProductOrder42 a
  obtain ⟨hmem,_,hind,_,_,hbound⟩ := source_compound_bridge42 A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
    v (fun j => (u j).property) hu L (fun i => Q ^ c₀ i) a
    (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) (fun i => (hpos i).le) harch
  let w : Fin 6 → compoundSourceGroup6 A₂ A₃ Q c₂ c₃ :=
    fun j => ⟨compoundFrame v (σ j),hmem (σ j)⟩
  refine ⟨w,hind.comp σ σ.injective,?_⟩
  intro j
  apply (compoundCoordinates42_bounds L hL Q hQ c₀ _ _).mpr
  intro s
  have h := hbound (σ j) s
  have hp := sourcePairProducts42_reindex A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  change sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = a (lo (σ j)) * a (hi (σ j)) at hp
  change |(compound L *ᵥ (fun k => (compoundFrame v (σ j) k : ℝ))) s| ≤ _
  rw [hp]
  convert h using 1 <;> ring

theorem source_compound_prefix_admissible42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    ∃ w : Fin (j.val+1) → compoundSourceGroup6 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun i => integerReal (w i : Fin 6 → ℤ)) ∧
      ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀)
        (integerReal (w i : Fin 6 → ℤ)) ≤
          2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨w,hw,hbound⟩ := exists_source_compound_ordered_frame42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let f : Fin (j.val+1) → Fin 6 := Fin.castLE (by omega)
  refine ⟨fun i => w (f i),hw.comp f (Fin.castLE_injective _),?_⟩
  intro i
  apply (hbound (f i)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (sourcePairProducts42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).2
    (show f i ≤ j from (by change i.val ≤ j.val; omega))

theorem source_compound_minima_upper42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∀ j : Fin 6, sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
      2 * sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  intro j
  obtain ⟨w,hw,hbound⟩ := source_compound_prefix_admissible42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  apply (sourceMinima6_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃ j).2.2.2
  exact ⟨fun i => integerReal (w i : Fin 6 → ℤ),hw,
    fun i => ⟨(w i : Fin 6 → ℤ),(w i).property,rfl⟩,hbound⟩

end CompoundFeasibility
