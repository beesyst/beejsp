import SubspaceBridge.CofactorOriginalRankOne3
open scoped BigOperators Matrix
namespace JSP000334

theorem allpoint_rational_flag3 (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℝ (fun j => integerTripleReal3 (w j)))
    (k : Fin 3) (z : IntegerTriple)
    (hz : integerTripleReal3 z ∈ minimaFlag3 (fun j => integerTripleReal3 (w j)) k) :
    (fun i => (z i : ℚ)) ∈ Submodule.span ℚ
      (Set.range (fun j : Fin k.val => fun i => (w (Fin.castLE (by omega) j) i : ℚ))) := by
  classical
  let v : Fin 3 → Fin 3 → ℚ := fun j i => (w j i : ℚ)
  have hQ := dualFrameMatrix3_rational_independent w hw
  let b := basisOfLinearIndependentOfCardEqFinrank hQ (by simp)
  have hb (i : Fin 3) : b i = v i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hQ _) i
  have hzero (j : Fin 3) (hj : k ≤ j) : b.repr (fun i => (z i : ℚ)) j = 0 := by
    let f : (Fin 3 → ℚ) →ₗ[ℚ] ℚ := originalPlanePairing3 (dualFrameVector3 w j)
    let g : RealTriple →ₗ[ℝ] ℝ :=
      { toFun := fun x => ∑ i, x i*(dualFrameVector3 w j i : ℝ)
        map_add' := by intro x y; simp [add_mul,Finset.sum_add_distrib]
        map_smul' := by intro c x; simp [Finset.mul_sum,mul_assoc] }
    have hc (x : IntegerTriple) : g (integerTripleReal3 x) = (f (fun i => (x i : ℚ)) : ℝ) := by
      simp [g,f,originalPlanePairing3,integerTripleReal3]
    have hpair (i : Fin 3) : f (v i) = if i = j then 1 else 0 :=
      dualFrameVector3_pairing w hQ i j
    have hcoord : f = b.coord j := by
      apply b.ext
      intro i
      rw [hb,hpair]
      rw [← hb i]
      simp [Basis.coord_apply,Finsupp.single_apply,eq_comm]
    have hk : minimaFlag3 (fun i => integerTripleReal3 (w i)) k ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have hij : (Fin.castLE (by omega) i : Fin 3) ≠ j := by
        intro he
        have hval := congrArg Fin.val he
        have hji := hj
        change k.val ≤ j.val at hji
        change i.val = j.val at hval
        omega
      change g (integerTripleReal3 (w (Fin.castLE (by omega) i))) = 0
      rw [hc,hpair,if_neg hij,Rat.cast_zero]
    have hh := hk hz
    change g (integerTripleReal3 z) = 0 at hh
    rw [hc] at hh
    have hf : f (fun i => (z i : ℚ)) = 0 := by exact_mod_cast hh
    rw [hcoord] at hf
    exact hf
  rw [← b.sum_repr (fun i => (z i : ℚ))]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i.val < k.val
  · apply Submodule.smul_mem
    rw [hb]
    apply Submodule.subset_span
    refine ⟨⟨i.val,hi⟩,?_⟩
    rfl
  · have hij : k ≤ i := by omega
    rw [hzero i hij,zero_smul]
    exact Submodule.zero_mem _

end JSP000334
