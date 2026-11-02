import SubspaceBridge.SourceTripleProducts242
import SubspaceBridge.SourceTripleGauge242
import SubspaceBridge.MinimaProduct5
import SubspaceBridge.MinimaProduct10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior53_242

variable (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
  (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
  (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)

def compoundMinima3242 : Fin 10 → ℝ :=
  sourceMinima10 (compound3242 A2) (compound3242 A3) (compound3242 L) (compound_real_unit3242 L hL)
    (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0)
    (normalizedWeights3242 c2) (normalizedWeights3242 c3)

theorem compoundMinima_sInf3242 (j : Fin 10) :
    compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j =
      sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 10 → ℝ), LinearIndependent ℝ v ∧
        (∀ i, v i ∈ integerRealImage (directGroup3242 A2 A3 Q c2 c3)) ∧
        ∀ i s, |(compound3242 L *ᵥ v i) s| ≤ r*Q^(tripleWeights242 c0 s)} := by
  unfold compoundMinima3242 sourceMinima10
  rw [powered_group3242]
  congr 1
  ext r
  constructor <;> rintro ⟨v,hv,hm,hb⟩ <;> refine ⟨v,hv,hm,?_⟩
  · intro i
    exact (powered_body3242 L hL Q hQ c0 (v i) r).mp (hb i)
  · intro i
    exact (powered_body3242 L hL Q hQ c0 (v i) r).mpr (hb i)

theorem compoundMinima_pos_mono3242 :
    (∀ j, 0 < compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
    Monotone (compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3) :=
  sourceMinima10_pos_mono _ _ _ _ _ _ _ _ _

theorem compoundMinima_attaining3242 :
    ∃ w : Fin 10 → directGroup3242 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)) ∧
      ∀ j, coordinateGauge10 (originalCoordinates10 (compound3242 L) (compound_real_unit3242 L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0))
        (integerReal (w j : Fin 10 → ℤ)) = compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j := by
  obtain ⟨w,hw,_,_,hatt,_⟩ := exists_sourceMinima10_attaining (compound3242 A2) (compound3242 A3)
    (compound3242 L) (compound_real_unit3242 L hL) (Q^3) (powered_gt_one3242 Q hQ)
    (normalizedWeights3242 c0) (normalizedWeights3242 c2) (normalizedWeights3242 c3)
  let v : Fin 10 → directGroup3242 A2 A3 Q c2 c3 := fun j =>
    ⟨(w j : Fin 10 → ℤ), by rw [← powered_group3242]; exact (w j).property⟩
  exact ⟨v,hw,hatt⟩

def orderedWedge3242 (u : Fin 5 → Fin 5 → ℤ) (a : Fin 5 → ℝ) (j : Fin 10) : Fin 10 → ℤ :=
  wedge3242 (u (lo242 (tripleOrder242 a j))) (u (mid242 (tripleOrder242 a j))) (u (hi242 (tripleOrder242 a j)))

theorem actual_wedge_frame3242 :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
      (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
      let w := orderedWedge3242 (fun i => (u i : Fin 5 → ℤ)) (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3)
      (∀ j, w j ∈ directGroup3242 A2 A3 Q c2 c3) ∧
      LinearIndependent ℝ (fun j => integerReal (w j)) ∧
      (∀ j s, |(compound3242 L *ᵥ integerReal (w j)) s| ≤
        6*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j*Q^(tripleWeights242 c0 s)) ∧
      ∀ j, coordinateGauge10 (originalCoordinates10 (compound3242 L) (compound_real_unit3242 L hL)
        (Q^3) (powered_gt_one3242 Q hQ) (normalizedWeights3242 c0)) (integerReal (w j)) ≤
          6*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  classical
  obtain ⟨u,hu,hpos,_,hatt,hpoint⟩ := exists_sourceMinima5_attaining A2 A3 L hL Q hQ c0 c2 c3
  let a := sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3
  let w := orderedWedge3242 (fun i => (u i : Fin 5 → ℤ)) a
  have hb (j s : Fin 10) : |(compound3242 L *ᵥ integerReal (w j)) s| ≤
      6*tripleProducts242 a j*Q^(tripleWeights242 c0 s) := by
    let i := lo242 (tripleOrder242 a j)
    let k := mid242 (tripleOrder242 a j)
    let l := hi242 (tripleOrder242 a j)
    have he : integerReal (w j) = wedge3242 (integerReal (u i : Fin 5 → ℤ))
        (integerReal (u k : Fin 5 → ℤ)) (integerReal (u l : Fin 5 → ℤ)) := wedge_cast3242 _ _ _
    rw [he,wedge_transform3242]
    have hq : 0<Q := zero_lt_one.trans hQ
    have h := det3_abs_bound242
      (fun r => (L *ᵥ integerReal (u i : Fin 5 → ℤ)) (tripleIndex242 s r))
      (fun r => (L *ᵥ integerReal (u k : Fin 5 → ℤ)) (tripleIndex242 s r))
      (fun r => (L *ᵥ integerReal (u l : Fin 5 → ℤ)) (tripleIndex242 s r))
      (fun r => Q^(c0 (tripleIndex242 s r))) (a i) (a k) (a l)
      (hpos i).le (hpos k).le (hpos l).le
      (fun _ => (Real.rpow_pos_of_pos hq _).le)
      (fun r => hpoint i (tripleIndex242 s r))
      (fun r => hpoint k (tripleIndex242 s r))
      (fun r => hpoint l (tripleIndex242 s r))
    change |wedge3242 (L *ᵥ integerReal (u i : Fin 5 → ℤ))
      (L *ᵥ integerReal (u k : Fin 5 → ℤ)) (L *ᵥ integerReal (u l : Fin 5 → ℤ)) s| ≤
      6*(a i*a k*a l)*(Q^(c0 (lo242 s))*Q^(c0 (mid242 s))*Q^(c0 (hi242 s))) at h
    change _ ≤ 6*(a i*a k*a l)*Q^(c0 (lo242 s)+c0 (mid242 s)+c0 (hi242 s))
    rw [Real.rpow_add hq,Real.rpow_add hq]
    exact h
  refine ⟨u,hu,hatt,?_,?_,hb,?_⟩
  · intro j
    exact wedge_direct3242 A2 A3 Q c2 c3 _ _ _
  · exact (compoundFrame_independent3242 (fun i => (u i : Fin 5 → ℤ)) hu).comp
      (tripleOrder242 a) (tripleOrder242 a).injective
  · intro j
    exact (powered_body3242 L hL Q hQ c0 _ _).mpr (hb j)

theorem compoundMinima_upper3242 : ∀ j,
    compoundMinima3242 A2 A3 L hL Q hQ c0 c2 c3 j ≤
      6*tripleProducts242 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  intro j
  obtain ⟨u,_,_,hm,hi,_,hg⟩ := actual_wedge_frame3242 A2 A3 L hL Q hQ c0 c2 c3
  let a := sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3
  let w := orderedWedge3242 (fun i => (u i : Fin 5 → ℤ)) a
  let f : Fin (j.val+1) → Fin 10 := Fin.castLE (by omega)
  apply (sourceMinima10_radius_set_properties (compound3242 A2) (compound3242 A3) (compound3242 L)
    (compound_real_unit3242 L hL) (Q^3) (powered_gt_one3242 Q hQ)
    (normalizedWeights3242 c0) (normalizedWeights3242 c2) (normalizedWeights3242 c3) j).2.2.2
  refine ⟨fun i => integerReal (w (f i)),hi.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    refine ⟨w (f i),?_,rfl⟩
    rw [powered_group3242]
    exact hm (f i)
  · intro i
    exact (hg (f i)).trans (mul_le_mul_of_nonneg_left
      (tripleProducts_mono242 a (show f i ≤ j by change i.val ≤ j.val; omega)) (by norm_num))

end CompoundFeasibility.Exterior53_242
