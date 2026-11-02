import SubspaceBridge.SourceOriginalNormalTransport10
import SubspaceBridge.SourceOriginalVariableAuxiliary10
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceOriginalVariable10
open SourceSampling10 SourceSelectedSet10 SourceSelectedUpper10 OriginalDual10 SourceGlobalSelected10
noncomputable section

theorem original_fixed_set_sample_transfer10
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {delta : ℝ} {S0 : Finset MixedIndex10}
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    {V : Set ℝ} (hQV : ∀ q ∈ V, 1 < q)
    (D : (q : V) → OriginalData10 A2 A3 L hL q.val (hQV q.val q.property) delta S0)
    (hbad : ∀ q : V, ∃ s ∈ S0, mixedProduct10 A2 A3 L (integerLastDual10 (D q).u) s ≠ 0)
    {c2 c3 : Fin 10 → ℝ} {c : Fin 3 → Fin 10 → ℝ}
    {e eta D0 E0 B rho : ℝ} {m : ℕ} {hm : 0 < m}
    (S : OriginalAuxiliarySample10 A2 A3 L c2 c3 V (fun q => (D q).u) c e eta D0 E0 B rho m hm)
    (h : Fin m) :
    ∃ s ∈ S0, mixedProduct10 A2 A3 L (S.data.M h) s ≠ 0 ∧
      mixedProduct10 A2 A3 L (S.data.M h) s ≤ 362880*((S.data.t h).val^5)^(-17*delta/10) := by
  obtain ⟨s,hs,hn⟩ := hbad (S.data.t h)
  have hv (q : V) : LinearIndependent ℝ (fun j => integerReal ((D q).u j)) := (D q).independent
  obtain ⟨g,hg,hscale⟩ := original_attaining_cofactor_factor10 hv S h
  have hu := original_data_cofactor_upper10 h2 h3 hLd (D (S.data.t h)) s hs
  have hle := mixedProduct10_le_int_mul10 A2 A3 L g hg (S.data.M h) s
  rw [← hscale] at hle
  have heq : (S.data.t h).val^(-17*delta/2) = ((S.data.t h).val^5)^(-17*delta/10) := by
    rw [← Real.rpow_natCast_mul (zero_lt_one.trans (hQV _ (S.data.t h).property)).le]
    congr 1
    ring
  rw [heq] at hu
  exact ⟨s,hs,original_cofactor_sample_nonzero10 hv S h s hn,hle.trans hu⟩

end
end CompoundFeasibility.SourceOriginalVariable10
