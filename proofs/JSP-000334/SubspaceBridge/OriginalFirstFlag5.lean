import SubspaceBridge.SourceOriginalRank1Flag247
import SubspaceBridge.SourceOriginalRank2Flag244
import SubspaceBridge.SourceOriginalFlag241
import SubspaceBridge.SourceOriginalRank4Flag245U
import SubspaceBridge.OriginalVariableGap5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalFlagAssembly5

def originalFirstFlag5 (d : Fin 4) (u : Fin 5 → Fin 5 → ℤ) : Submodule ℚ (Fin 5 → ℚ) :=
  Submodule.span ℚ (Set.range (fun j : Fin (d.val+1) => fun i =>
    (u (Fin.castLE (by omega) j) i : ℚ)))

theorem originalFirstFlag5_one (u : Fin 5 → Fin 5 → ℤ) :
    originalFirstFlag5 0 u = Submodule.span ℚ {fun i => (u 0 i : ℚ)} := by
  unfold originalFirstFlag5
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,rfl⟩
    have hj : j = 0 := by omega
    subst j
    rfl
  · intro hx
    exact ⟨0,hx.symm⟩

theorem originalFirstFlag5_two (u : Fin 5 → Fin 5 → ℤ) :
    originalFirstFlag5 1 u = Submodule.span ℚ (Set.range
      (fun j : Fin 2 => fun i => (u (Fin.castLE (by decide) j) i : ℚ))) := rfl

theorem originalFirstFlag5_three (u : Fin 5 → Fin 5 → ℤ) :
    originalFirstFlag5 2 u = Submodule.span ℚ (Set.range
      (fun j : Fin 3 => fun i => (u (Fin.castLE (by decide) j) i : ℚ))) := rfl

theorem originalFirstFlag5_four (u : Fin 5 → Fin 5 → ℤ) :
    originalFirstFlag5 3 u = Submodule.span ℚ (Set.range
      (fun j : Fin 4 => fun i => (u (j.castSucc) i : ℚ))) := rfl

end CompoundFeasibility.OriginalFlagAssembly5
