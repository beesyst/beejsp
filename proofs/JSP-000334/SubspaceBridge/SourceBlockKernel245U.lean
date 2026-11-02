import SubspaceBridge.SourceBlockLattice245Q
import SubspaceBridge.SourceFixedNormal241
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockRank4_245U
open BlockReduction245P BlockReduction245Q

def originalNormal245U (b : Fin 10 → ℤ) : Module.Dual ℚ (Fin 5 → ℚ) :=
  ∑ i, ((first245Q b i : ℤ) : ℚ) • LinearMap.proj i

theorem original_nonzero245U (b : Fin 10 → ℤ) (hb : b ≠ 0)
    (hdummy : ∀ i, second245Q b i = 0) : first245Q b ≠ 0 := by
  intro h
  apply hb
  funext j
  obtain ⟨s,rfl⟩ := blockIndex245P.surjective j
  cases s with
  | inl i => exact congrFun h i
  | inr i => exact hdummy i

theorem original_kernel_rank245U (b : Fin 10 → ℤ) (hb : first245Q b ≠ 0) :
    Module.finrank ℚ (LinearMap.ker (originalNormal245U b)) = 4 := by
  have hn : originalNormal245U b ≠ 0 := by
    intro hz
    apply hb
    funext i
    have hi := LinearMap.congr_fun hz (Pi.single i 1)
    have hc : ((first245Q b i : ℤ) : ℚ) = 0 := by
      simpa [originalNormal245U, Pi.single_apply] using hi
    exact_mod_cast hc
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have ht : Module.finrank ℚ (Fin 5 → ℚ) = 5 := by simp
  omega

theorem original_kernel_span245U (b : Fin 10 → ℤ) (hb : first245Q b ≠ 0)
    (u : Fin 5 → Fin 5 → ℚ) (hu : LinearIndependent ℚ u)
    (hz : ∀ j : Fin 4, originalNormal245U b (u j.castSucc) = 0) :
    LinearMap.ker (originalNormal245U b) =
      Submodule.span ℚ (Set.range (fun j : Fin 4 => u j.castSucc)) := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hz j
  · rw [original_kernel_rank245U b hb]
    simpa only [Function.comp_def, Fintype.card_fin] using
      finrank_span_eq_card (hu.comp (fun j : Fin 4 => j.castSucc) (Fin.castSucc_injective _))

end CompoundFeasibility.BlockRank4_245U
