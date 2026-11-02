import SubspaceBridge.SourceCofactorReal231
import SubspaceBridge.SourceCofactorSigns231
import SubspaceBridge.SourceDualBody222
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceCofactorGeometry233
open OriginalDual10 SourceOriginalDual10 SourceSatz51Entry218 SourceLastDual231 SourceDualAnnihilation222

theorem cofactor_cutoff233 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ q : ℝ, T < q → 362880 * q^(-9*delta) ≤ 1 := by
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_neg_atTop (show 0 < 9*delta by positivity)).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1/362880 by norm_num)))
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro q hq
  have hb := hB q ((le_max_left B 2).trans hq.le)
  have he : -9*delta = -(9*delta) := by ring
  rw [he]
  linarith

theorem cofactor_cast233 (u : Fin 10 → Fin 10 → ℤ) :
    ratReal222 (fun i => (integerLastDual10 u i : ℚ)) = integerReal (integerLastDual10 u) := by
  funext i
  change (((integerLastDual10 u i : ℤ) : ℚ) : ℝ) = (integerLastDual10 u i : ℝ)
  simp only [Rat.cast_intCast]

variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}

theorem source_cofactor_body233 (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta)
    (hcut : 362880 * q^(-9*delta) ≤ 1) :
    ratReal222 (fun i => (integerLastDual10 D.u i : ℚ)) ∈ dualBody222 L
      (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3))) A := by
  rw [cofactor_cast233 D.u]
  change ∀ i, |(L⁻¹.transpose *ᵥ integerReal (integerLastDual10 D.u)) i| ≤
    ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)) / A i
  intro i
  have hb := source_real_cofactor231 h2 h3 hLd D i
  have hw : 0 ≤ ZLattice.covolume
      (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)) / A i :=
    (div_pos (ZLattice.covolume_pos _ MeasureTheory.volume) (D.positive i)).le
  exact hb.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcut hw)

end CompoundFeasibility.SourceCofactorGeometry233
