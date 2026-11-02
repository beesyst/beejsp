import SubspaceBridge.NormalIndex10
import SubspaceBridge.SourceOriginalFamily10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open SchmidtNormal10

theorem actual_frame_normals10 (u w : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j)))
    (hw : LinearIndependent ℝ (fun j => integerReal (w j)))
    (hflag : minimaFlag10 (fun j => integerReal (u j)) 9 =
      minimaFlag10 (fun j => integerReal (w j)) 9) :
    ∃ M a : Fin 10 → ℤ, M ≠ 0 ∧ (∑ i, a i*M i) = 1 ∧
      Ideal.span (Set.range M) = ⊤ ∧
      LinearMap.ker (normalForm10 M) = firstNineSpan10 (fun j i => (u j i : ℚ)) ∧
      LinearMap.ker (normalForm10 M) = firstNineSpan10 (fun j i => (w j i : ℚ)) ∧
      LinearMap.ker (realNormalForm10 M) = minimaFlag10 (fun j => integerReal (u j)) 9 ∧
      LinearMap.ker (realNormalForm10 M) = minimaFlag10 (fun j => integerReal (w j)) 9 := by
  obtain ⟨M,a,hM,ha,hprim,hku,hkw,hdim⟩ := same_real_flag_rational_kernel10 u w hu hw hflag
  have hann (j : Fin 9) : (∑ i, M i*w j.castSucc i) = 0 := by
    have hm : (fun i => (w j.castSucc i : ℚ)) ∈ LinearMap.ker (normalForm10 M) := by
      rw [hkw]
      exact Submodule.subset_span ⟨j,rfl⟩
    have hh : (∑ i, (M i : ℚ)*(w j.castSucc i : ℚ)) = 0 := hm
    exact_mod_cast hh
  have hreal := real_normal_kernel10 w hw M hM hann
  exact ⟨M,a,hM,ha,hprim,hku,hkw,hreal.trans hflag.symm,hreal⟩

theorem normalized_tail_parameters10 (V : Set ℝ) (hV : ¬ BddAbove V)
    (eta E rho B : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho)
    (m : ℕ) (hm : 0 < m) :
    ∃ (t : Fin m → V) (r : Fin m → ℕ),
      StrictMono (fun h => (t h).val) ∧
      (∀ h, B < (t h).val ∧ 1 < (t h).val ∧
        1 < (t h).val^5 ∧ 1060*E < ((t h).val^5)^eta ∧
        10*(eta⁻¹+1) < ((t h).val^5)^eta) ∧
      (∀ h, 0 < r h) ∧
      (∀ (h : Fin m) (hh : h.val+1 < m),
        (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
      ∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log ((t ⟨0,hm⟩).val^5) ≤
        (r h : ℝ)*Real.log ((t h).val^5) ∧
        (r h : ℝ)*Real.log ((t h).val^5) ≤
          (1+eta)*((r ⟨0,hm⟩ : ℝ)*Real.log ((t ⟨0,hm⟩).val^5)) := by
  obtain ⟨t,r,hmono,hgrowth,hr,hrho,hbal⟩ := original_tail_parameters10 V hV eta E rho B he hE hp m hm
  have hpow (h) : (t h).val^eta ≤ ((t h).val^5)^eta := by
    apply Real.rpow_le_rpow (zero_lt_one.trans (hgrowth h).2.1).le _ he.le
    exact le_self_pow₀ (hgrowth h).2.1.le (by decide : 5 ≠ 0)
  refine ⟨t,r,hmono,?_,hr,hrho,?_⟩
  · intro h
    exact ⟨(hgrowth h).1,(hgrowth h).2.1,one_lt_pow₀ (hgrowth h).2.1 (by decide),
      (hgrowth h).2.2.1.trans_le (hpow h),(hgrowth h).2.2.2.trans_le (hpow h)⟩
  · intro h
    simp only [Real.log_pow]
    constructor <;> nlinarith [(hbal h).1,(hbal h).2]

end CompoundFeasibility.SourceSampling10
