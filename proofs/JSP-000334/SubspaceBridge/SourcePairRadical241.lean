import SubspaceBridge.SourcePairForm241
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open Exterior52_237

theorem pairForm_basis_pattern241 (b : Fin 10 → ℤ) (u : Fin 5 → Fin 5 → ℚ)
    (hz : ∀ s : Fin 10, s ≠ 9 → pairForm241 b (u (lo237 s)) (u (hi237 s)) = 0)
    (i j : Fin 5) :
    pairForm241 b (u i) (u j) =
      if i = 3 ∧ j = 4 then pairForm241 b (u 3) (u 4)
      else if i = 4 ∧ j = 3 then -pairForm241 b (u 3) (u 4) else 0 := by
  have h01 : pairForm241 b (u 0) (u 1) = 0 := hz 0 (by decide)
  have h10 : pairForm241 b (u 1) (u 0) = -pairForm241 b (u 0) (u 1) := pairForm_swap241 b (u 1) (u 0)
  have h02 : pairForm241 b (u 0) (u 2) = 0 := hz 1 (by decide)
  have h20 : pairForm241 b (u 2) (u 0) = -pairForm241 b (u 0) (u 2) := pairForm_swap241 b (u 2) (u 0)
  have h03 : pairForm241 b (u 0) (u 3) = 0 := hz 2 (by decide)
  have h30 : pairForm241 b (u 3) (u 0) = -pairForm241 b (u 0) (u 3) := pairForm_swap241 b (u 3) (u 0)
  have h04 : pairForm241 b (u 0) (u 4) = 0 := hz 3 (by decide)
  have h40 : pairForm241 b (u 4) (u 0) = -pairForm241 b (u 0) (u 4) := pairForm_swap241 b (u 4) (u 0)
  have h12 : pairForm241 b (u 1) (u 2) = 0 := hz 4 (by decide)
  have h21 : pairForm241 b (u 2) (u 1) = -pairForm241 b (u 1) (u 2) := pairForm_swap241 b (u 2) (u 1)
  have h13 : pairForm241 b (u 1) (u 3) = 0 := hz 5 (by decide)
  have h31 : pairForm241 b (u 3) (u 1) = -pairForm241 b (u 1) (u 3) := pairForm_swap241 b (u 3) (u 1)
  have h14 : pairForm241 b (u 1) (u 4) = 0 := hz 6 (by decide)
  have h41 : pairForm241 b (u 4) (u 1) = -pairForm241 b (u 1) (u 4) := pairForm_swap241 b (u 4) (u 1)
  have h23 : pairForm241 b (u 2) (u 3) = 0 := hz 7 (by decide)
  have h32 : pairForm241 b (u 3) (u 2) = -pairForm241 b (u 2) (u 3) := pairForm_swap241 b (u 3) (u 2)
  have h24 : pairForm241 b (u 2) (u 4) = 0 := hz 8 (by decide)
  have h42 : pairForm241 b (u 4) (u 2) = -pairForm241 b (u 2) (u 4) := pairForm_swap241 b (u 4) (u 2)
  have h43 : pairForm241 b (u 4) (u 3) = -pairForm241 b (u 3) (u 4) := pairForm_swap241 b (u 4) (u 3)
  fin_cases i <;> fin_cases j
  · change pairForm241 b (u 0) (u 0) = 0
    exact pairForm_self241 b (u 0)
  · change pairForm241 b (u 0) (u 1) = 0
    exact h01
  · change pairForm241 b (u 0) (u 2) = 0
    exact h02
  · change pairForm241 b (u 0) (u 3) = 0
    exact h03
  · change pairForm241 b (u 0) (u 4) = 0
    exact h04
  · change pairForm241 b (u 1) (u 0) = 0
    simpa only [h01,neg_zero] using h10
  · change pairForm241 b (u 1) (u 1) = 0
    exact pairForm_self241 b (u 1)
  · change pairForm241 b (u 1) (u 2) = 0
    exact h12
  · change pairForm241 b (u 1) (u 3) = 0
    exact h13
  · change pairForm241 b (u 1) (u 4) = 0
    exact h14
  · change pairForm241 b (u 2) (u 0) = 0
    simpa only [h02,neg_zero] using h20
  · change pairForm241 b (u 2) (u 1) = 0
    simpa only [h12,neg_zero] using h21
  · change pairForm241 b (u 2) (u 2) = 0
    exact pairForm_self241 b (u 2)
  · change pairForm241 b (u 2) (u 3) = 0
    exact h23
  · change pairForm241 b (u 2) (u 4) = 0
    exact h24
  · change pairForm241 b (u 3) (u 0) = 0
    simpa only [h03,neg_zero] using h30
  · change pairForm241 b (u 3) (u 1) = 0
    simpa only [h13,neg_zero] using h31
  · change pairForm241 b (u 3) (u 2) = 0
    simpa only [h23,neg_zero] using h32
  · change pairForm241 b (u 3) (u 3) = 0
    exact pairForm_self241 b (u 3)
  · change pairForm241 b (u 3) (u 4) = pairForm241 b (u 3) (u 4)
    rfl
  · change pairForm241 b (u 4) (u 0) = 0
    simpa only [h04,neg_zero] using h40
  · change pairForm241 b (u 4) (u 1) = 0
    simpa only [h14,neg_zero] using h41
  · change pairForm241 b (u 4) (u 2) = 0
    simpa only [h24,neg_zero] using h42
  · change pairForm241 b (u 4) (u 3) = -pairForm241 b (u 3) (u 4)
    exact h43
  · change pairForm241 b (u 4) (u 4) = 0
    exact pairForm_self241 b (u 4)

theorem radical_rank3_241 (b : Fin 10 → ℤ) (u : Fin 5 → Fin 5 → ℚ)
    (hu : LinearIndependent ℚ u)
    (hz : ∀ s : Fin 10, s ≠ 9 → pairForm241 b (u (lo237 s)) (u (hi237 s)) = 0)
    (hc : pairForm241 b (u 3) (u 4) ≠ 0) :
    radical241 b = Submodule.span ℚ (Set.range (fun j : Fin 3 => u (Fin.castLE (by decide) j))) ∧
      Module.finrank ℚ (radical241 b) = 3 := by
  let B := rationalFrameBasis42 u hu
  have hp := pairForm_basis_pattern241 b u hz
  have heval (x y : Fin 5 → ℚ) : pairForm241 b x y =
      ∑ i, B.repr x i * pairForm241 b (u i) y := by
    conv_lhs => rw [← B.sum_repr x]
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      B,rationalFrameBasis42_apply]
  have heq : radical241 b = Submodule.span ℚ
      (Set.range (fun j : Fin 3 => u (Fin.castLE (by decide) j))) := by
    apply le_antisymm
    · intro x hx
      have hzero (y : Fin 5 → ℚ) : pairForm241 b x y = 0 := by
        exact congrArg (fun f : Module.Dual ℚ (Fin 5 → ℚ) => f y) hx
      have h3 : B.repr x 3 * (pairForm241 b (u 3) (u 4)) = 0 := by
        have h := hzero (u 4)
        rw [heval] at h
        have hv (i : Fin 5) : pairForm241 b (u i) (u 4) =
            if i = 3 then pairForm241 b (u 3) (u 4) else 0 := by
          rw [hp]
          simp
        have he : (∑ i, B.repr x i * pairForm241 b (u i) (u 4)) =
            B.repr x 3 * (pairForm241 b (u 3) (u 4)) := by
          calc
            _ = ∑ i, B.repr x i * (if i = 3 then pairForm241 b (u 3) (u 4) else 0) :=
              Finset.sum_congr rfl (fun i _ => congrArg (fun q : ℚ => B.repr x i * q) (hv i))
            _ = _ := by simp [mul_ite]
        rw [he] at h
        exact h
      have h4 : B.repr x 4 * (-pairForm241 b (u 3) (u 4)) = 0 := by
        have h := hzero (u 3)
        rw [heval] at h
        have hv (i : Fin 5) : pairForm241 b (u i) (u 3) =
            if i = 4 then -pairForm241 b (u 3) (u 4) else 0 := by
          rw [hp]
          simp
        have he : (∑ i, B.repr x i * pairForm241 b (u i) (u 3)) =
            B.repr x 4 * (-pairForm241 b (u 3) (u 4)) := by
          calc
            _ = ∑ i, B.repr x i * (if i = 4 then -pairForm241 b (u 3) (u 4) else 0) :=
              Finset.sum_congr rfl (fun i _ => congrArg (fun q : ℚ => B.repr x i * q) (hv i))
            _ = _ := by simp [mul_ite]
        rw [he] at h
        exact h
      have hc3 := (mul_eq_zero.mp h3).resolve_right hc
      have hc4 := (mul_eq_zero.mp h4).resolve_right (neg_ne_zero.mpr hc)
      rw [← B.sum_repr x]
      apply Submodule.sum_mem
      intro i _
      rw [show B i = u i from rationalFrameBasis42_apply u hu i]
      by_cases hi : i.val < 3
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨⟨i.val,hi⟩,rfl⟩
      · have hi' : i = 3 ∨ i = 4 := by
          have := i.isLt
          have hv : i.val = 3 ∨ i.val = 4 := by omega
          exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
        rcases hi' with rfl | rfl <;> simp [hc3,hc4]
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change pairForm241 b (u (Fin.castLE (by decide) j)) = 0
      apply B.ext
      intro i
      change pairForm241 b (u (Fin.castLE (by decide) j)) (B i) = 0
      rw [show B i = u i from rationalFrameBasis42_apply u hu i,hp]
      have h3 : (Fin.castLE (by decide) j : Fin 5) ≠ 3 := by
        intro h
        have hj : j.val = 3 := congrArg Fin.val h
        have := j.isLt
        omega
      have h4 : (Fin.castLE (by decide) j : Fin 5) ≠ 4 := by
        intro h
        have hj : j.val = 4 := congrArg Fin.val h
        have := j.isLt
        omega
      simp [h3,h4]
  refine ⟨heq,?_⟩
  rw [heq]
  exact (finrank_span_eq_card (hu.comp (Fin.castLE (by decide) : Fin 3 → Fin 5)
    (Fin.castLE_injective _))).trans (Fintype.card_fin 3)

end CompoundFeasibility.SourceFlag241
