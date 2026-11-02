import SubspaceBridge.SourceNormalizedHighIndex4
import SubspaceBridge.SchmidtNormalCoordinates4
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSelectedDual4
open OriginalSelectedSystem4 OriginalLastDual4 OriginalAuxiliaryDual4 SourceNormalIndex4

def dualValue4 {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (M : Fin 4 → ℤ) (i : Fin 4) : K :=
  (B⁻¹.transpose *ᵥ (fun k => (M k : K))) i

def mixedProduct4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 4 → ℤ) (s : MixedIndex4) : ℝ :=
  ‖dualValue4 L M (s 0)‖ *
    ‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) M (s 1)‖ *
    ‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) M (s 2)‖

def mixedNonzero4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 4 → ℤ) (s : MixedIndex4) : Prop :=
  dualValue4 L M (s 0) ≠ 0 ∧
    dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) M (s 1) ≠ 0 ∧
    dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) M (s 2) ≠ 0

theorem mixedProduct4_nonzero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (M : Fin 4 → ℤ) (s : MixedIndex4) :
    mixedProduct4 A2 A3 L M s ≠ 0 ↔ mixedNonzero4 A2 A3 L M s := by
  simp [mixedProduct4,mixedNonzero4,mul_ne_zero_iff,and_assoc]

theorem dualValue4_scaling {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (z M : Fin 4 → ℤ) (g : ℤ)
    (h : ∀ i, z i = g*M i) (i : Fin 4) :
    dualValue4 B z i = (g : K)*dualValue4 B M i := by
  simp only [dualValue4,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [h k,Int.cast_mul]
  ring

theorem dualValue4_scaling_zero {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (z M : Fin 4 → ℤ) (g : ℤ)
    (hg : g ≠ 0) (h : ∀ i, z i = g*M i) (i : Fin 4) :
    dualValue4 B z i = 0 ↔ dualValue4 B M i = 0 := by
  rw [dualValue4_scaling B z M g h i]
  exact mul_eq_zero_iff_left (show (g : K) ≠ 0 by exact_mod_cast hg)

def lastDualValue4 {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (i : Fin 4) : K :=
  ∑ k, B⁻¹ k i * (lastDual4 (fun j i => (v j i : ℚ)) hv k : K)

def lastDualProduct4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (s : MixedIndex4) : ℝ :=
  ‖lastDualValue4 L v hv (s 0)‖ *
    ‖lastDualValue4 (A2.map (algebraMap ℚ ℚ_[2])) v hv (s 1)‖ *
    ‖lastDualValue4 (A3.map (algebraMap ℚ ℚ_[3])) v hv (s 2)‖

theorem primitive_lastDualValue4_zero {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (h : ∀ i, integerLastDual4 v i = g*M i) (i : Fin 4) :
    dualValue4 B M i = 0 ↔ lastDualValue4 B v hv i = 0 := by
  rw [← dualValue4_scaling_zero B (integerLastDual4 v) M g hg h i]
  change (B⁻¹.transpose *ᵥ (fun k => (integerLastDual4 v k : K))) i = 0 ↔ _
  rw [cofactor_dual_coordinates4 B v hv i]
  exact mul_eq_zero_iff_left (show ((Matrix.det v : ℤ) : K) ≠ 0 by exact_mod_cast integerFrame4_det_ne_zero v hv)

theorem primitive_lastDualProduct4_zero (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (h : ∀ i, integerLastDual4 v i = g*M i) (s : MixedIndex4) :
    mixedProduct4 A2 A3 L M s = 0 ↔ lastDualProduct4 A2 A3 L v hv s = 0 := by
  simp only [mixedProduct4,lastDualProduct4,mul_eq_zero,norm_eq_zero,
    primitive_lastDualValue4_zero _ v hv M g hg h]

def nonzeroBranch4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (s : MixedIndex4) : Set ℝ :=
  {q | ∃ hq : q ∈ W, mixedNonzero4 A2 A3 L (M ⟨q,hq⟩) s}

theorem nonzeroBranch4_subset (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (s : MixedIndex4) : nonzeroBranch4 A2 A3 L W M s ⊆ W := fun _ h => h.choose

theorem mem_nonzeroBranch4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (s : MixedIndex4) (q : W) :
    q.val ∈ nonzeroBranch4 A2 A3 L W M s ↔ mixedNonzero4 A2 A3 L (M q) s := by
  constructor
  · rintro ⟨hq,h⟩
    exact h
  · intro h
    exact ⟨q.property,h⟩

theorem failure_eventual_zero_branch4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Set ℝ) (M : W → Fin 4 → ℤ)
    (S : Finset MixedIndex4)
    (hfail : ¬ ∃ T : ℝ, ∀ q : W, T < q.val → ∀ s ∈ S,
      mixedProduct4 A2 A3 L (M q) s = 0) :
    ∃ s ∈ S, ¬ BddAbove (nonzeroBranch4 A2 A3 L W M s) := by
  by_contra! hb
  have hu : BddAbove (⋃ s ∈ S, nonzeroBranch4 A2 A3 L W M s) :=
    S.finite_toSet.bddAbove_biUnion.mpr hb
  obtain ⟨T,hT⟩ := hu
  apply hfail
  refine ⟨T,?_⟩
  intro q hq s hs
  by_contra hn
  have hmem := (mem_nonzeroBranch4 A2 A3 L W M s q).mpr
    ((mixedProduct4_nonzero A2 A3 L (M q) s).mp hn)
  exact (not_le_of_gt hq) (hT (Set.mem_iUnion₂.mpr ⟨s,hs,hmem⟩))


theorem same_frame_primitive_normals4 {W : Set ℝ}
    (v : W → Fin 4 → Fin 4 → ℤ)
    (hv : ∀ q, LinearIndependent ℝ (fun j => integerReal (v q j))) :
    ∃ (g : W → ℤ) (M a : W → Fin 4 → ℤ), ∀ q,
      g q ≠ 0 ∧ M q ≠ 0 ∧
      (∀ i, integerLastDual4 (v q) i = g q*M q i) ∧
      (∑ i, a q i*M q i) = 1 ∧ Ideal.span (Set.range (M q)) = ⊤ ∧
      (∀ j : Fin 3, (∑ i, M q i*v q j.castSucc i) = 0) ∧
      LinearMap.ker (normalForm4 (M q)) =
        Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (v q j.castSucc i : ℚ))) ∧
      LinearMap.ker (realNormalForm4 (M q)) =
        Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (v q j.castSucc))) ∧
      0 < SchmidtNormalCoordinates4.normalHeight4 (M q) := by
  have hp (q : W) := primitive_cofactor_normal4 (v q) (hv q)
  choose g M a h using hp
  refine ⟨g,M,a,?_⟩
  intro q
  exact ⟨(h q).1,(h q).2.1,(h q).2.2.1,(h q).2.2.2.1,
    (h q).2.2.2.2.1,(h q).2.2.2.2.2.1,(h q).2.2.2.2.2.2.1,
    (h q).2.2.2.2.2.2.2,
    SchmidtNormalCoordinates4.normalHeight4_pos (M q) (h q).2.1⟩

theorem same_frame_high_index_transfer4 {m : ℕ}
    (M N : Fin m → Fin 4 → ℤ) (hN : ∀ h, N h ≠ 0)
    (hker : ∀ h, LinearMap.ker (realNormalForm4 (M h)) =
      LinearMap.ker (realNormalForm4 (N h)))
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock4.Vars4 m) ℤ)
    (hrestr : ∀ J : SourceMultiblock4.Vars4 m →₀ ℕ,
      Auxiliary4.rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2)
          (SourceMultiblock4.derivative4 J (P.map (Int.castRingHom ℝ))) = 0) :
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 N r c := by
  apply sourceNormalIdeal4_of_derivative_restrictions N hN r c
  intro J hJ y hy
  exact hrestr J hJ y (fun h => (hker h).symm ▸ hy h)

end CompoundFeasibility.SourceSelectedDual4
