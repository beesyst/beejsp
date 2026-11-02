import SubspaceBridge.SourceAuxiliarySample10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
variable {c2 c3 : Fin 10 → ℝ} {V : Set ℝ} {v : V → Fin 10 → Fin 10 → ℤ}
variable {c : Fin 3 → Fin 10 → ℝ} {epsilon eta D E B rho : ℝ} {m : ℕ} {hm : 0 < m}

def OriginalAuxiliarySample10.latticeFrame10
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (h : Fin m) (j : Fin 10) : originalSourceGroup10 A2 A3 (S.data.t h).val c2 c3 :=
  ⟨S.data.w h j,S.conditions.member h j⟩

theorem OriginalAuxiliarySample10.latticeFrame10_coe
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm)
    (h : Fin m) (j : Fin 10) :
    (S.latticeFrame10 h j : Fin 10 → ℤ) = S.data.w h j := rfl

end CompoundFeasibility.SourceSampling10
