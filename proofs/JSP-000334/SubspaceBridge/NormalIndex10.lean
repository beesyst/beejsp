import SubspaceBridge.SchmidtNormal10
import SubspaceBridge.OriginalSpanTransport10
open scoped BigOperators Matrix
namespace CompoundFeasibility.SchmidtNormal10
noncomputable section

def realNormalForm10 (M : Fin 10 → ℤ) : Module.Dual ℝ (Fin 10 → ℝ) :=
  ∑ i, (M i : ℝ) • LinearMap.proj i

theorem realNormalForm10_apply (M : Fin 10 → ℤ) (x : Fin 10 → ℝ) :
    realNormalForm10 M x = ∑ i, (M i : ℝ)*x i := by
  simp [realNormalForm10]

theorem real_normal_kernel10 (v : Fin 10 → Fin 10 → ℤ)
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ)))
    (M : Fin 10 → ℤ) (hM : M ≠ 0)
    (hann : ∀ j : Fin 9, (∑ i, M i*v j.castSucc i) = 0) :
    LinearMap.ker (realNormalForm10 M) =
      Submodule.span ℝ (Set.range (fun j : Fin 9 => fun i => (v j.castSucc i : ℝ))) := by
  classical
  let u : Fin 10 → Fin 10 → ℝ := fun j i => (v j i : ℝ)
  let b := basisOfPiSpaceOfLinearIndependent hv
  have hb (i : Fin 10) : b i = u i := congrFun (coe_basisOfPiSpaceOfLinearIndependent hv) i
  have hf (j : Fin 9) : realNormalForm10 M (u j.castSucc) = 0 := by
    rw [realNormalForm10_apply]
    change (∑ i, (M i : ℝ)*(v j.castSucc i : ℝ)) = 0
    exact_mod_cast hann j
  have hfn : realNormalForm10 M ≠ 0 := by
    intro hz
    apply hM
    funext i
    have he := congrArg (fun f : Module.Dual ℝ (Fin 10 → ℝ) => f (Pi.single i 1)) hz
    have hi : (M i : ℝ) = 0 := by simpa [realNormalForm10,Pi.single_apply] using he
    exact_mod_cast hi
  have hlast : realNormalForm10 M (u 9) ≠ 0 := by
    intro hz
    apply hfn
    apply b.ext
    intro j
    rw [hb]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hz
    · exact hf i
  have hvalue (x : Fin 10 → ℝ) :
      realNormalForm10 M x = b.repr x 9 * realNormalForm10 M (u 9) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum,Fin.sum_univ_castSucc]
    simp only [map_smul,hb,hf,smul_zero,Finset.sum_const_zero,zero_add]
    rfl
  apply le_antisymm
  · intro x hx
    have hz : b.repr x 9 = 0 := (mul_eq_zero.mp ((hvalue x).symm.trans hx)).resolve_right hlast
    have he := b.sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 9 = (9 : Fin 10) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [hb]
    exact Submodule.subset_span ⟨j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hf j


theorem same_real_flag_rational_kernel10 (v w : Fin 10 → Fin 10 → ℤ)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j)))
    (hw : LinearIndependent ℝ (fun j => integerReal (w j)))
    (hflag : minimaFlag10 (fun j => integerReal (v j)) 9 =
      minimaFlag10 (fun j => integerReal (w j)) 9) :
    ∃ M a : Fin 10 → ℤ, M ≠ 0 ∧ (∑ i, a i*M i) = 1 ∧
      Ideal.span (Set.range M) = ⊤ ∧
      LinearMap.ker (normalForm10 M) = firstNineSpan10 (fun j i => (v j i : ℚ)) ∧
      LinearMap.ker (normalForm10 M) = firstNineSpan10 (fun j i => (w j i : ℚ)) ∧
      Module.finrank ℚ (LinearMap.ker (normalForm10 M)) = 9 := by
  let f : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hvQ : LinearIndependent ℚ (fun j i => (v j i : ℚ)) := by
    apply LinearIndependent.of_comp f
    convert hv.restrict_scalars' ℚ using 1
  have hwQ : LinearIndependent ℚ (fun j i => (w j i : ℚ)) := by
    apply LinearIndependent.of_comp f
    convert hw.restrict_scalars' ℚ using 1
  obtain ⟨M,a,hM,ha,hprim,hann,hker⟩ := primitive_normal10 w hwQ
  have hreal : LinearMap.ker (realNormalForm10 M) = minimaFlag10 (fun j => integerReal (w j)) 9 :=
    real_normal_kernel10 w hw M hM hann
  have hinc : firstNineSpan10 (fun j i => (v j i : ℚ)) ≤ LinearMap.ker (normalForm10 M) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have hmem : integerReal (v j.castSucc) ∈ minimaFlag10 (fun j => integerReal (w j)) 9 := by
      rw [← hflag]
      exact Submodule.subset_span ⟨j,rfl⟩
    rw [← hreal] at hmem
    have hz : (∑ i, (M i : ℝ)*(v j.castSucc i : ℝ)) = 0 := hmem
    change (∑ i, (M i : ℚ)*(v j.castSucc i : ℚ)) = 0
    exact_mod_cast hz
  have hvdim : Module.finrank ℚ (firstNineSpan10 (fun j i => (v j i : ℚ))) = 9 := by
    simpa only [firstNineSpan10,Fintype.card_fin] using
      finrank_span_eq_card (hvQ.comp Fin.castSucc (Fin.castSucc_injective 9))
  have hwdim : Module.finrank ℚ (firstNineSpan10 (fun j i => (w j i : ℚ))) = 9 := by
    simpa only [firstNineSpan10,Fintype.card_fin] using
      finrank_span_eq_card (hwQ.comp Fin.castSucc (Fin.castSucc_injective 9))
  have hdim : Module.finrank ℚ (LinearMap.ker (normalForm10 M)) = 9 := by rw [hker]; exact hwdim
  have heq := Submodule.eq_of_le_of_finrank_eq hinc (hvdim.trans hdim.symm)
  exact ⟨M,a,hM,ha,hprim,heq.symm,hker,hdim⟩

end
end CompoundFeasibility.SchmidtNormal10
