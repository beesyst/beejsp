import SubspaceBridge.SourceAdjugateRecovery247
import SubspaceBridge.SourceFin5Dual245
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag247
open OriginalDual10 SourceFlag241

theorem sourceMinima5_short_span247
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (v : Fin 4 → Fin 5 → ℝ) (hv : LinearIndependent ℝ v)
    (hvL : ∀ j, v j ∈ integerRealImage (originalSourceGroup5 A2 A3 Q c2 c3))
    (hvg : ∀ j, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (v j) <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4)
    (z : Fin 5 → ℝ) (hz : z ∈ integerRealImage (originalSourceGroup5 A2 A3 Q c2 c3))
    (hzg : coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) z <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4) :
    z ∈ Submodule.span ℝ (Set.range v) := by
  classical
  by_contra hout
  let w : Fin 5 → Fin 5 → ℝ := Fin.snoc v z
  have hi : LinearIndependent ℝ w := linearIndependent_fin_snoc.mpr ⟨hv,hout⟩
  have hwL : ∀ i, w i ∈ integerRealImage (originalSourceGroup5 A2 A3 Q c2 c3) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [w,Fin.snoc_last] using hz
    · simpa only [w,Fin.snoc_castSucc] using hvL j
  have hwg : ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (w i) <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [w,Fin.snoc_last] using hzg
    · simpa only [w,Fin.snoc_castSucc] using hvg j
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (w i)) Finset.univ_nonempty
  have hle := (sourceMinima5_radius_set_properties A2 A3 L hL Q hQ c0 c2 c3 4).2.2.2
    ⟨w,hi,hwL,fun j => hmax j (Finset.mem_univ j)⟩
  exact (not_lt_of_ge hle) (hwg i)

theorem attaining_short_span247
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)
    (w : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j : Fin 5 → ℤ)))
    (ha : ∀ j, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
      (integerReal (w j : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 j)
    (hgap : sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 3 <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4)
    (z : Fin 5 → ℤ) (hz : z ∈ originalSourceGroup5 A2 A3 Q c2 c3)
    (hzg : coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal z) <
      sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 4) :
    integerReal z ∈ Submodule.span ℝ (Set.range
      (fun j : Fin 4 => integerReal (w j.castSucc : Fin 5 → ℤ))) := by
  apply sourceMinima5_short_span247 A2 A3 L hL Q hQ c0 c2 c3 _
    (hw.comp (fun j : Fin 4 => j.castSucc) (Fin.castSucc_injective _))
  · intro j
    exact ⟨(w j.castSucc : Fin 5 → ℤ),(w j.castSucc).property,rfl⟩
  · intro j
    change coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
      (integerReal (w j.castSucc : Fin 5 → ℤ)) < _
    rw [ha]
    exact ((sourceMinima5_pos_mono A2 A3 L hL Q hQ c0 c2 c3).2
      (show j.castSucc ≤ (3 : Fin 5) by change j.val ≤ 3; omega)).trans_lt hgap
  · exact ⟨z,hz,rfl⟩
  · exact hzg

theorem rational_span_of_real247 (w : Fin 5 → Fin 5 → ℤ)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j))) (z : Fin 5 → ℤ)
    (hz : integerReal z ∈ Submodule.span ℝ (Set.range
      (fun j : Fin 4 => integerReal (w j.castSucc)))) :
    (fun i => (z i : ℚ)) ∈ Submodule.span ℚ (Set.range
      (fun j : Fin 4 => fun i => (w j.castSucc i : ℚ))) := by
  let v : Fin 5 → Fin 5 → ℚ := fun j i => (w j i : ℚ)
  have hv := original_rational_independent241 w hw
  let f : Module.Dual ℚ (Fin 5 → ℚ) := rationalFrameDual42 v hv 4
  let g : Module.Dual ℝ (Fin 5 → ℝ) := ∑ i, (f (Pi.single i 1) : ℝ) • LinearMap.proj i
  have hc (x : Fin 5 → ℤ) : g (integerReal x) = (f (fun i => (x i : ℚ)) : ℝ) := by
    rw [functional_coordinates_dual10 f]
    simp [g,integerReal,mul_comm]
  have hk : Submodule.span ℝ (Set.range (fun j : Fin 4 => integerReal (w j.castSucc))) ≤
      LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change g (integerReal (w j.castSucc)) = 0
    rw [hc]
    have hh : f (fun i => (w j.castSucc i : ℚ)) = 0 := by
      change rationalFrameDual42 v hv 4 (v j.castSucc) = 0
      rw [rationalFrameDual42_pairing,if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    rw [hh,Rat.cast_zero]
  have hcast : (f (fun i => (z i : ℚ)) : ℝ) = 0 := (hc z).symm.trans (hk hz)
  have hf : f (fun i => (z i : ℚ)) = 0 := by exact_mod_cast hcast
  rw [← SourceRank4_245.last_dual_kernel245 v hv]
  exact hf

end CompoundFeasibility.SourceFlag247
