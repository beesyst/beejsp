import SubspaceBridge.OriginalDual10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open SchmidtNormal10 OriginalDual10

def realNormal241 (b : Fin 10 → ℤ) : Module.Dual ℝ (Fin 10 → ℝ) :=
  ∑ i, (b i : ℝ) • LinearMap.proj i

theorem realNormal_cast241 (b x : Fin 10 → ℤ) :
    realNormal241 b (integerReal x) = (normalForm10 b (fun i => (x i : ℚ)) : ℝ) := by
  simp [realNormal241,normalForm10_apply,integerReal]

theorem fixed_normal_first_nine241 (w : Fin 10 → Fin 10 → ℚ)
    (hw : LinearIndependent ℚ w) (b : Fin 10 → ℤ)
    (hline : Submodule.span ℚ {lastDual10 w hw} = Submodule.span ℚ {fun i => (b i : ℚ)}) :
    ∀ j : Fin 9, normalForm10 b (w j.castSucc) = 0 := by
  have hm : (fun i => (b i : ℚ)) ∈ Submodule.span ℚ {lastDual10 w hw} := by
    rw [hline]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  have he : normalForm10 b = a • rationalFrameDual42 w hw 9 := by
    apply LinearMap.ext
    intro x
    rw [normalForm10_apply,LinearMap.smul_apply,functional_coordinates10
      (rationalFrameDual42 w hw 9) x]
    simp only [smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrFun ha i
    change a*lastDual10 w hw i = (b i : ℚ) at hi
    rw [← hi]
    dsimp [lastDual10]
    ring
  intro j
  rw [he,LinearMap.smul_apply,rationalFrameDual42_pairing,if_neg]
  · simp
  · intro h
    have hj : j.val = 9 := congrArg Fin.val h
    have := j.isLt
    omega

theorem rational_annihilation_from_real_span241 (w : Fin 10 → Fin 10 → ℤ)
    (hw : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (b : Fin 10 → ℤ)
    (hline : Submodule.span ℚ {lastDual10 (fun j i => (w j i : ℚ)) hw} =
      Submodule.span ℚ {fun i => (b i : ℚ)}) (z : Fin 10 → ℤ)
    (hz : integerReal z ∈ Submodule.span ℝ (Set.range (fun j : Fin 9 => integerReal (w j.castSucc)))) :
    normalForm10 b (fun i => (z i : ℚ)) = 0 := by
  have hker : Submodule.span ℝ (Set.range (fun j : Fin 9 => integerReal (w j.castSucc))) ≤
      LinearMap.ker (realNormal241 b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change realNormal241 b (integerReal (w j.castSucc)) = 0
    rw [realNormal_cast241,fixed_normal_first_nine241 _ hw b hline j,Rat.cast_zero]
  have h := hker hz
  change realNormal241 b (integerReal z) = 0 at h
  rw [realNormal_cast241] at h
  exact_mod_cast h

end CompoundFeasibility.SourceFlag241
