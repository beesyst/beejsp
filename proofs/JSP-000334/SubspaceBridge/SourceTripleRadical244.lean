import SubspaceBridge.SourceTripleForm244
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag244
open Exterior53_242

theorem tripleForm_basis_pattern244 (b : Fin 10 → ℤ) (u : Fin 5 → Fin 5 → ℚ)
    (hz : ∀ s : Fin 10, s ≠ 9 → tripleForm244 b (u (lo242 s)) (u (mid242 s)) (u (hi242 s)) = 0) :
    (∀ (i : Fin 2) (j k : Fin 5), tripleForm244 b (u (Fin.castLE (by decide) i)) (u j) (u k) = 0) ∧
    (∀ i : Fin 5, tripleForm244 b (u i) (u 3) (u 4) =
      if i=2 then tripleForm244 b (u 2) (u 3) (u 4) else 0) ∧
    (∀ i : Fin 5, tripleForm244 b (u i) (u 2) (u 4) =
      if i=3 then -tripleForm244 b (u 2) (u 3) (u 4) else 0) ∧
    (∀ i : Fin 5, tripleForm244 b (u i) (u 2) (u 3) =
      if i=4 then tripleForm244 b (u 2) (u 3) (u 4) else 0) := by
  have h012 : tripleForm244 b (u 0) (u 1) (u 2) = 0 := hz 0 (by decide)
  have h013 : tripleForm244 b (u 0) (u 1) (u 3) = 0 := hz 1 (by decide)
  have h014 : tripleForm244 b (u 0) (u 1) (u 4) = 0 := hz 2 (by decide)
  have h023 : tripleForm244 b (u 0) (u 2) (u 3) = 0 := hz 3 (by decide)
  have h024 : tripleForm244 b (u 0) (u 2) (u 4) = 0 := hz 4 (by decide)
  have h034 : tripleForm244 b (u 0) (u 3) (u 4) = 0 := hz 5 (by decide)
  have h123 : tripleForm244 b (u 1) (u 2) (u 3) = 0 := hz 6 (by decide)
  have h124 : tripleForm244 b (u 1) (u 2) (u 4) = 0 := hz 7 (by decide)
  have h134 : tripleForm244 b (u 1) (u 3) (u 4) = 0 := hz 8 (by decide)
  refine ⟨?_,?_,?_,?_⟩
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k
    · change tripleForm244 b (u 0) (u 0) (u 0) = 0
      exact tripleForm_12_244 b (u 0) (u 0)
    · change tripleForm244 b (u 0) (u 0) (u 1) = 0
      exact tripleForm_12_244 b (u 0) (u 1)
    · change tripleForm244 b (u 0) (u 0) (u 2) = 0
      exact tripleForm_12_244 b (u 0) (u 2)
    · change tripleForm244 b (u 0) (u 0) (u 3) = 0
      exact tripleForm_12_244 b (u 0) (u 3)
    · change tripleForm244 b (u 0) (u 0) (u 4) = 0
      exact tripleForm_12_244 b (u 0) (u 4)
    · change tripleForm244 b (u 0) (u 1) (u 0) = 0
      exact tripleForm_13_244 b (u 0) (u 1)
    · change tripleForm244 b (u 0) (u 1) (u 1) = 0
      exact tripleForm_23_244 b (u 1) (u 0)
    · change tripleForm244 b (u 0) (u 1) (u 2) = 0
      rw [h012]
    · change tripleForm244 b (u 0) (u 1) (u 3) = 0
      rw [h013]
    · change tripleForm244 b (u 0) (u 1) (u 4) = 0
      rw [h014]
    · change tripleForm244 b (u 0) (u 2) (u 0) = 0
      exact tripleForm_13_244 b (u 0) (u 2)
    · change tripleForm244 b (u 0) (u 2) (u 1) = 0
      rw [tripleForm_swap23_244 b (u 0) (u 2) (u 1),h012]
      ring
    · change tripleForm244 b (u 0) (u 2) (u 2) = 0
      exact tripleForm_23_244 b (u 2) (u 0)
    · change tripleForm244 b (u 0) (u 2) (u 3) = 0
      rw [h023]
    · change tripleForm244 b (u 0) (u 2) (u 4) = 0
      rw [h024]
    · change tripleForm244 b (u 0) (u 3) (u 0) = 0
      exact tripleForm_13_244 b (u 0) (u 3)
    · change tripleForm244 b (u 0) (u 3) (u 1) = 0
      rw [tripleForm_swap23_244 b (u 0) (u 3) (u 1),h013]
      ring
    · change tripleForm244 b (u 0) (u 3) (u 2) = 0
      rw [tripleForm_swap23_244 b (u 0) (u 3) (u 2),h023]
      ring
    · change tripleForm244 b (u 0) (u 3) (u 3) = 0
      exact tripleForm_23_244 b (u 3) (u 0)
    · change tripleForm244 b (u 0) (u 3) (u 4) = 0
      rw [h034]
    · change tripleForm244 b (u 0) (u 4) (u 0) = 0
      exact tripleForm_13_244 b (u 0) (u 4)
    · change tripleForm244 b (u 0) (u 4) (u 1) = 0
      rw [tripleForm_swap23_244 b (u 0) (u 4) (u 1),h014]
      ring
    · change tripleForm244 b (u 0) (u 4) (u 2) = 0
      rw [tripleForm_swap23_244 b (u 0) (u 4) (u 2),h024]
      ring
    · change tripleForm244 b (u 0) (u 4) (u 3) = 0
      rw [tripleForm_swap23_244 b (u 0) (u 4) (u 3),h034]
      ring
    · change tripleForm244 b (u 0) (u 4) (u 4) = 0
      exact tripleForm_23_244 b (u 4) (u 0)
    · change tripleForm244 b (u 1) (u 0) (u 0) = 0
      exact tripleForm_23_244 b (u 0) (u 1)
    · change tripleForm244 b (u 1) (u 0) (u 1) = 0
      exact tripleForm_13_244 b (u 1) (u 0)
    · change tripleForm244 b (u 1) (u 0) (u 2) = 0
      rw [tripleForm_swap12_244 b (u 1) (u 0) (u 2),h012]
      ring
    · change tripleForm244 b (u 1) (u 0) (u 3) = 0
      rw [tripleForm_swap12_244 b (u 1) (u 0) (u 3),h013]
      ring
    · change tripleForm244 b (u 1) (u 0) (u 4) = 0
      rw [tripleForm_swap12_244 b (u 1) (u 0) (u 4),h014]
      ring
    · change tripleForm244 b (u 1) (u 1) (u 0) = 0
      exact tripleForm_12_244 b (u 1) (u 0)
    · change tripleForm244 b (u 1) (u 1) (u 1) = 0
      exact tripleForm_12_244 b (u 1) (u 1)
    · change tripleForm244 b (u 1) (u 1) (u 2) = 0
      exact tripleForm_12_244 b (u 1) (u 2)
    · change tripleForm244 b (u 1) (u 1) (u 3) = 0
      exact tripleForm_12_244 b (u 1) (u 3)
    · change tripleForm244 b (u 1) (u 1) (u 4) = 0
      exact tripleForm_12_244 b (u 1) (u 4)
    · change tripleForm244 b (u 1) (u 2) (u 0) = 0
      rw [tripleForm_swap23_244 b (u 1) (u 2) (u 0),tripleForm_swap12_244 b (u 1) (u 0) (u 2),h012]
      ring
    · change tripleForm244 b (u 1) (u 2) (u 1) = 0
      exact tripleForm_13_244 b (u 1) (u 2)
    · change tripleForm244 b (u 1) (u 2) (u 2) = 0
      exact tripleForm_23_244 b (u 2) (u 1)
    · change tripleForm244 b (u 1) (u 2) (u 3) = 0
      rw [h123]
    · change tripleForm244 b (u 1) (u 2) (u 4) = 0
      rw [h124]
    · change tripleForm244 b (u 1) (u 3) (u 0) = 0
      rw [tripleForm_swap23_244 b (u 1) (u 3) (u 0),tripleForm_swap12_244 b (u 1) (u 0) (u 3),h013]
      ring
    · change tripleForm244 b (u 1) (u 3) (u 1) = 0
      exact tripleForm_13_244 b (u 1) (u 3)
    · change tripleForm244 b (u 1) (u 3) (u 2) = 0
      rw [tripleForm_swap23_244 b (u 1) (u 3) (u 2),h123]
      ring
    · change tripleForm244 b (u 1) (u 3) (u 3) = 0
      exact tripleForm_23_244 b (u 3) (u 1)
    · change tripleForm244 b (u 1) (u 3) (u 4) = 0
      rw [h134]
    · change tripleForm244 b (u 1) (u 4) (u 0) = 0
      rw [tripleForm_swap23_244 b (u 1) (u 4) (u 0),tripleForm_swap12_244 b (u 1) (u 0) (u 4),h014]
      ring
    · change tripleForm244 b (u 1) (u 4) (u 1) = 0
      exact tripleForm_13_244 b (u 1) (u 4)
    · change tripleForm244 b (u 1) (u 4) (u 2) = 0
      rw [tripleForm_swap23_244 b (u 1) (u 4) (u 2),h124]
      ring
    · change tripleForm244 b (u 1) (u 4) (u 3) = 0
      rw [tripleForm_swap23_244 b (u 1) (u 4) (u 3),h134]
      ring
    · change tripleForm244 b (u 1) (u 4) (u 4) = 0
      exact tripleForm_23_244 b (u 4) (u 1)
  · intro i
    fin_cases i
    · change tripleForm244 b (u 0) (u 3) (u 4) = 0
      rw [h034]
    · change tripleForm244 b (u 1) (u 3) (u 4) = 0
      rw [h134]
    · change tripleForm244 b (u 2) (u 3) (u 4) = tripleForm244 b (u 2) (u 3) (u 4)
      ring
    · change tripleForm244 b (u 3) (u 3) (u 4) = 0
      exact tripleForm_12_244 b (u 3) (u 4)
    · change tripleForm244 b (u 4) (u 3) (u 4) = 0
      exact tripleForm_13_244 b (u 4) (u 3)
  · intro i
    fin_cases i
    · change tripleForm244 b (u 0) (u 2) (u 4) = 0
      rw [h024]
    · change tripleForm244 b (u 1) (u 2) (u 4) = 0
      rw [h124]
    · change tripleForm244 b (u 2) (u 2) (u 4) = 0
      exact tripleForm_12_244 b (u 2) (u 4)
    · change tripleForm244 b (u 3) (u 2) (u 4) = -tripleForm244 b (u 2) (u 3) (u 4)
      rw [tripleForm_swap12_244 b (u 3) (u 2) (u 4)]
    · change tripleForm244 b (u 4) (u 2) (u 4) = 0
      exact tripleForm_13_244 b (u 4) (u 2)
  · intro i
    fin_cases i
    · change tripleForm244 b (u 0) (u 2) (u 3) = 0
      rw [h023]
    · change tripleForm244 b (u 1) (u 2) (u 3) = 0
      rw [h123]
    · change tripleForm244 b (u 2) (u 2) (u 3) = 0
      exact tripleForm_12_244 b (u 2) (u 3)
    · change tripleForm244 b (u 3) (u 2) (u 3) = 0
      exact tripleForm_13_244 b (u 3) (u 2)
    · change tripleForm244 b (u 4) (u 2) (u 3) = tripleForm244 b (u 2) (u 3) (u 4)
      rw [tripleForm_swap12_244 b (u 4) (u 2) (u 3),tripleForm_swap23_244 b (u 2) (u 4) (u 3)]
      ring

theorem radical_rank2_244 (b : Fin 10 → ℤ) (u : Fin 5 → Fin 5 → ℚ)
    (hu : LinearIndependent ℚ u)
    (hz : ∀ s : Fin 10, s ≠ 9 → tripleForm244 b (u (lo242 s)) (u (mid242 s)) (u (hi242 s)) = 0)
    (hc : tripleForm244 b (u 2) (u 3) (u 4) ≠ 0) :
    radical244 b = Submodule.span ℚ (Set.range (fun j : Fin 2 => u (Fin.castLE (by decide) j))) ∧
      Module.finrank ℚ (radical244 b) = 2 := by
  let B := rationalFrameBasis42 u hu
  have hp := tripleForm_basis_pattern244 b u hz
  let f1 (y z : Fin 5 → ℚ) : Module.Dual ℚ (Fin 5 → ℚ) :=
    { toFun := fun x => tripleForm244 b x y z
      map_add' := fun x w => tripleForm_add1_244 b x y z w
      map_smul' := by
        intro c x
        change tripleForm244 b (c • x) y z = c*tripleForm244 b x y z
        exact tripleForm_smul1_244 b c x y z }
  let f2 (x z : Fin 5 → ℚ) : Module.Dual ℚ (Fin 5 → ℚ) :=
    { toFun := fun y => tripleForm244 b x y z
      map_add' := fun y w => tripleForm_add2_244 b x y z w
      map_smul' := by
        intro c y
        change tripleForm244 b x (c • y) z = c*tripleForm244 b x y z
        exact tripleForm_smul2_244 b c x y z }
  let f3 (x y : Fin 5 → ℚ) : Module.Dual ℚ (Fin 5 → ℚ) :=
    { toFun := fun z => tripleForm244 b x y z
      map_add' := fun z w => tripleForm_add3_244 b x y z w
      map_smul' := by
        intro c z
        change tripleForm244 b x y (c • z) = c*tripleForm244 b x y z
        exact tripleForm_smul3_244 b c x y z }
  have heval (x y z : Fin 5 → ℚ) : tripleForm244 b x y z =
      ∑ i, B.repr x i * tripleForm244 b (u i) y z := by
    change f1 y z x = _
    conv_lhs => rw [← B.sum_repr x]
    simp only [map_sum,map_smul,smul_eq_mul,B,rationalFrameBasis42_apply]
    rfl
  have hcoords (x : Fin 5 → ℚ) (hx : x ∈ radical244 b) :
      B.repr x 2=0 ∧ B.repr x 3=0 ∧ B.repr x 4=0 := by
    have hzero : ∀ y z, tripleForm244 b x y z=0 := hx
    have h2 : B.repr x 2 * tripleForm244 b (u 2) (u 3) (u 4)=0 := by
      have h := hzero (u 3) (u 4)
      rw [heval] at h
      have he : (∑ i, B.repr x i * tripleForm244 b (u i) (u 3) (u 4)) =
          B.repr x 2 * tripleForm244 b (u 2) (u 3) (u 4) := by
        calc
          _ = ∑ i, B.repr x i * (if i=2 then tripleForm244 b (u 2) (u 3) (u 4) else 0) :=
            Finset.sum_congr rfl (fun i _ => congrArg (fun q : ℚ => B.repr x i*q) (hp.2.1 i))
          _ = _ := by simp [mul_ite]
      rw [he] at h
      exact h
    have h3 : B.repr x 3 * (-tripleForm244 b (u 2) (u 3) (u 4))=0 := by
      have h := hzero (u 2) (u 4)
      rw [heval] at h
      have he : (∑ i, B.repr x i * tripleForm244 b (u i) (u 2) (u 4)) =
          B.repr x 3 * (-tripleForm244 b (u 2) (u 3) (u 4)) := by
        calc
          _ = ∑ i, B.repr x i * (if i=3 then -tripleForm244 b (u 2) (u 3) (u 4) else 0) :=
            Finset.sum_congr rfl (fun i _ => congrArg (fun q : ℚ => B.repr x i*q) (hp.2.2.1 i))
          _ = _ := by simp [mul_ite]
      rw [he] at h
      exact h
    have h4 : B.repr x 4 * tripleForm244 b (u 2) (u 3) (u 4)=0 := by
      have h := hzero (u 2) (u 3)
      rw [heval] at h
      have he : (∑ i, B.repr x i * tripleForm244 b (u i) (u 2) (u 3)) =
          B.repr x 4 * tripleForm244 b (u 2) (u 3) (u 4) := by
        calc
          _ = ∑ i, B.repr x i * (if i=4 then tripleForm244 b (u 2) (u 3) (u 4) else 0) :=
            Finset.sum_congr rfl (fun i _ => congrArg (fun q : ℚ => B.repr x i*q) (hp.2.2.2 i))
          _ = _ := by simp [mul_ite]
      rw [he] at h
      exact h
    exact ⟨(mul_eq_zero.mp h2).resolve_right hc,(mul_eq_zero.mp h3).resolve_right (neg_ne_zero.mpr hc),
      (mul_eq_zero.mp h4).resolve_right hc⟩
  have heq : radical244 b = Submodule.span ℚ
      (Set.range (fun j : Fin 2 => u (Fin.castLE (by decide) j))) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨h2,h3,h4⟩ := hcoords x hx
      rw [← B.sum_repr x]
      apply Submodule.sum_mem
      intro i _
      rw [show B i=u i from rationalFrameBasis42_apply u hu i]
      by_cases hi : i.val<2
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨⟨i.val,hi⟩,rfl⟩
      · have hi' : i=2 ∨ i=3 ∨ i=4 := by
          have := i.isLt
          have hv : i.val=2 ∨ i.val=3 ∨ i.val=4 := by omega
          exact hv.imp (fun h => Fin.ext h) (fun h => h.imp (fun h => Fin.ext h) (fun h => Fin.ext h))
        rcases hi' with rfl | rfl | rfl <;> simp [h2,h3,h4]
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change ∀ y z, tripleForm244 b (u (Fin.castLE (by decide) i)) y z=0
      intro y z
      have hthird (j : Fin 5) : f3 (u (Fin.castLE (by decide) i)) (u j)=0 := by
        apply B.ext
        intro k
        change tripleForm244 b (u (Fin.castLE (by decide) i)) (u j) (B k)=0
        rw [show B k=u k from rationalFrameBasis42_apply u hu k]
        exact hp.1 i j k
      have hsecond : f2 (u (Fin.castLE (by decide) i)) z=0 := by
        apply B.ext
        intro j
        change tripleForm244 b (u (Fin.castLE (by decide) i)) (B j) z=0
        rw [show B j=u j from rationalFrameBasis42_apply u hu j]
        exact congrArg (fun f : Module.Dual ℚ (Fin 5 → ℚ) => f z) (hthird j)
      exact congrArg (fun f : Module.Dual ℚ (Fin 5 → ℚ) => f y) hsecond
  refine ⟨heq,?_⟩
  rw [heq]
  exact (finrank_span_eq_card (hu.comp (Fin.castLE (by decide) : Fin 2 → Fin 5)
    (Fin.castLE_injective _))).trans (Fintype.card_fin 2)

end CompoundFeasibility.SourceFlag244
