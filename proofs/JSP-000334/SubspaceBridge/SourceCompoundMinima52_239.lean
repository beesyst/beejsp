import SubspaceBridge.SourcePairProducts52_239
import SubspaceBridge.MinimaProduct5
import SubspaceBridge.MinimaProduct10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.ExteriorGap52_239
open Exterior52_237 Exterior52_238

variable (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
  (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
  (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 5 → ℝ)

def compoundMinima239 : Fin 10 → ℝ :=
  sourceMinima10 (compound237 A2) (compound237 A3) (compound237 L) (compound_unit238 L hL)
    (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0)
    (normalizedWeights238 c2) (normalizedWeights238 c3)

theorem compoundMinima_sInf239 (j : Fin 10) :
    compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j =
      sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 10 → ℝ), LinearIndependent ℝ v ∧
        (∀ i, v i ∈ integerRealImage (directGroup238 A2 A3 Q c2 c3)) ∧
        ∀ i s, |(compound237 L *ᵥ v i) s| ≤ r*Q^(pairWeights238 c0 s)} := by
  unfold compoundMinima239 sourceMinima10
  rw [powered_group238]
  congr 1
  ext r
  constructor <;> rintro ⟨v,hv,hm,hb⟩ <;> refine ⟨v,hv,hm,?_⟩
  · intro i
    exact (powered_body238 L hL Q hQ c0 (v i) r).mp (hb i)
  · intro i
    exact (powered_body238 L hL Q hQ c0 (v i) r).mpr (hb i)

theorem compoundMinima_pos_mono239 :
    (∀ j, 0 < compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j) ∧
    Monotone (compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3) :=
  sourceMinima10_pos_mono _ _ _ _ _ _ _ _ _

theorem compoundMinima_attaining239 :
    ∃ w : Fin 10 → directGroup238 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 10 → ℤ)) ∧
      ∀ j, coordinateGauge10 (originalCoordinates10 (compound237 L) (compound_unit238 L hL)
        (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0))
        (integerReal (w j : Fin 10 → ℤ)) = compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j := by
  obtain ⟨w,hw,_,_,hatt,_⟩ := exists_sourceMinima10_attaining (compound237 A2) (compound237 A3)
    (compound237 L) (compound_unit238 L hL) (Q^2) (powered_gt_one238 Q hQ)
    (normalizedWeights238 c0) (normalizedWeights238 c2) (normalizedWeights238 c3)
  let v : Fin 10 → directGroup238 A2 A3 Q c2 c3 := fun j =>
    ⟨(w j : Fin 10 → ℤ), by rw [← powered_group238]; exact (w j).property⟩
  exact ⟨v,hw,hatt⟩

def orderedWedge239 (u : Fin 5 → Fin 5 → ℤ) (a : Fin 5 → ℝ) (j : Fin 10) : Fin 10 → ℤ :=
  wedge237 (u (lo237 (pairOrder239 a j))) (u (hi237 (pairOrder239 a j)))

theorem actual_wedge_frame239 :
    ∃ u : Fin 5 → originalSourceGroup5 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)) ∧
      (∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c0)
        (integerReal (u i : Fin 5 → ℤ)) = sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
      let w := orderedWedge239 (fun i => (u i : Fin 5 → ℤ)) (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3)
      (∀ j, w j ∈ directGroup238 A2 A3 Q c2 c3) ∧
      LinearIndependent ℝ (fun j => integerReal (w j)) ∧
      (∀ j s, |(compound237 L *ᵥ integerReal (w j)) s| ≤
        2*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j*Q^(pairWeights238 c0 s)) ∧
      ∀ j, coordinateGauge10 (originalCoordinates10 (compound237 L) (compound_unit238 L hL)
        (Q^2) (powered_gt_one238 Q hQ) (normalizedWeights238 c0)) (integerReal (w j)) ≤
          2*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  classical
  obtain ⟨u,hu,hpos,_,hatt,hpoint⟩ := exists_sourceMinima5_attaining A2 A3 L hL Q hQ c0 c2 c3
  let a := sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3
  let w := orderedWedge239 (fun i => (u i : Fin 5 → ℤ)) a
  have hb (j s : Fin 10) : |(compound237 L *ᵥ integerReal (w j)) s| ≤
      2*pairProducts239 a j*Q^(pairWeights238 c0 s) := by
    let i := lo237 (pairOrder239 a j)
    let k := hi237 (pairOrder239 a j)
    have he : integerReal (w j) = wedge237 (integerReal (u i : Fin 5 → ℤ))
        (integerReal (u k : Fin 5 → ℤ)) := wedge_cast237 _ _
    rw [he,wedge_transform237]
    change |(L *ᵥ integerReal (u i : Fin 5 → ℤ)) (lo237 s)*
      (L *ᵥ integerReal (u k : Fin 5 → ℤ)) (hi237 s)-
      (L *ᵥ integerReal (u i : Fin 5 → ℤ)) (hi237 s)*
      (L *ᵥ integerReal (u k : Fin 5 → ℤ)) (lo237 s)| ≤ _
    have hq : 0 < Q := zero_lt_one.trans hQ
    have h1 := mul_le_mul (hpoint i (lo237 s)) (hpoint k (hi237 s)) (abs_nonneg _)
      (mul_nonneg (hpos i).le (Real.rpow_pos_of_pos hq _).le)
    have h2 := mul_le_mul (hpoint i (hi237 s)) (hpoint k (lo237 s)) (abs_nonneg _)
      (mul_nonneg (hpos i).le (Real.rpow_pos_of_pos hq _).le)
    calc
      _ ≤ |(L *ᵥ integerReal (u i : Fin 5 → ℤ)) (lo237 s)*
          (L *ᵥ integerReal (u k : Fin 5 → ℤ)) (hi237 s)|+
          |(L *ᵥ integerReal (u i : Fin 5 → ℤ)) (hi237 s)*
          (L *ᵥ integerReal (u k : Fin 5 → ℤ)) (lo237 s)| := abs_sub _ _
      _ ≤ (a i*Q^(c0 (lo237 s)))*(a k*Q^(c0 (hi237 s)))+
          (a i*Q^(c0 (hi237 s)))*(a k*Q^(c0 (lo237 s))) := by
        simpa only [abs_mul] using add_le_add h1 h2
      _ = _ := by
        change _ = 2*(a i*a k)*Q^(c0 (lo237 s)+c0 (hi237 s))
        rw [Real.rpow_add hq]
        ring
  refine ⟨u,hu,hatt,?_,?_,hb,?_⟩
  · intro j
    exact wedge_direct238 A2 A3 Q c2 c3 _ _
  · exact (compoundFrame_independent238 (fun i => (u i : Fin 5 → ℤ)) hu).comp
      (pairOrder239 a) (pairOrder239 a).injective
  · intro j
    exact (powered_body238 L hL Q hQ c0 _ _).mpr (hb j)

theorem compoundMinima_upper239 : ∀ j,
    compoundMinima239 A2 A3 L hL Q hQ c0 c2 c3 j ≤
      2*pairProducts239 (sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3) j := by
  intro j
  obtain ⟨u,_,_,hm,hi,_,hg⟩ := actual_wedge_frame239 A2 A3 L hL Q hQ c0 c2 c3
  let a := sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3
  let w := orderedWedge239 (fun i => (u i : Fin 5 → ℤ)) a
  let f : Fin (j.val+1) → Fin 10 := Fin.castLE (by omega)
  apply (sourceMinima10_radius_set_properties (compound237 A2) (compound237 A3) (compound237 L)
    (compound_unit238 L hL) (Q^2) (powered_gt_one238 Q hQ)
    (normalizedWeights238 c0) (normalizedWeights238 c2) (normalizedWeights238 c3) j).2.2.2
  refine ⟨fun i => integerReal (w (f i)),hi.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    refine ⟨w (f i),?_,rfl⟩
    rw [powered_group238]
    exact hm (f i)
  · intro i
    exact (hg (f i)).trans (mul_le_mul_of_nonneg_left
      (pairProducts_mono239 a (show f i ≤ j by change i.val ≤ j.val; omega)) (by norm_num))

end CompoundFeasibility.ExteriorGap52_239
