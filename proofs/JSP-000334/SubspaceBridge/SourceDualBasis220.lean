import SubspaceBridge.SourceDualMatrix220
import SubspaceBridge.SourceDualLattice219
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceDualGeometry219
open SourceDualBasis220

theorem dual_reconstruction220 (W : Matrix (Fin 10) (Fin 10) ℚ)
    (hW : IsUnit W) (v : Fin 10 → ℚ) :
    v = ∑ j, (W *ᵥ v) j • dualVector219 W j := by
  exact (inverse_reconstruction220 W hW v).symm.trans (inverse_columns220 W (W *ᵥ v))

theorem scale_integer_sum220 (d : ℚ) (a : Fin 10 → ℤ) (v : Fin 10 → Fin 10 → ℚ) :
    d • (∑ j, (a j : ℚ) • v j) = ∑ j, a j • (d • v j) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ext i
  simp only [Pi.smul_apply,smul_eq_mul]
  simp only [zsmul_eq_mul]
  ring

theorem scaledDual_subset_basis219
    (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))
    (z : Fin 10 → ℚ) (hz : z ∈ scaledDual219 G) : z ∈ basisDualSpan219 G c := by
  obtain ⟨v,hv,rfl⟩ := hz
  let W : Matrix (Fin 10) (Fin 10) ℚ := fun j i => ((c j : Fin 10 → ℤ) i : ℚ)
  have hW : IsUnit W := Matrix.linearIndependent_rows_iff_isUnit.mp hc
  have hh (j : Fin 10) : ∃ a : ℤ, (W *ᵥ v) j = (a : ℚ) := hv (c j)
  choose a ha using hh
  have hcoords : W *ᵥ v = fun j => (a j : ℚ) := funext ha
  have hrepr := dual_reconstruction220 W hW v
  rw [hcoords] at hrepr
  change (G.index : ℚ) • v ∈ basisDualSpan219 G c
  rw [hrepr,scale_integer_sum220]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

theorem dual_row_sum220 (W : Matrix (Fin 10) (Fin 10) ℚ) (hW : IsUnit W)
    (a : Fin 10 → ℚ) (j : Fin 10) :
    (∑ i, (∑ k, a k*W k i)*dualVector219 W j i) = a j := by
  rw [row_sum_pairing220]
  simp_rw [dualVector_pairing219 W hW]
  simp

theorem basis_dual_pairing220
    (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))
    (x : G) (j : Fin 10) :
    pairing219 (dualVector219 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) j)
      (x : Fin 10 → ℤ) = (c.repr x j : ℚ) := by
  let W : Matrix (Fin 10) (Fin 10) ℚ := fun j i => ((c j : Fin 10 → ℤ) i : ℚ)
  have hW : IsUnit W := Matrix.linearIndependent_rows_iff_isUnit.mp hc
  have he : (fun i => ((x : Fin 10 → ℤ) i : ℚ)) =
      fun i => ∑ k, (c.repr x k : ℚ)*W k i := by
    ext i
    have h0 := congrArg G.subtype (c.sum_repr x)
    simp only [map_sum,map_zsmul] at h0
    have h := congrArg (fun y : Fin 10 → ℤ => (y i : ℚ)) h0
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Int.cast_sum,Int.cast_mul] using h.symm
  calc
    pairing219 (dualVector219 W j) (x : Fin 10 → ℤ) =
        ∑ i, (∑ k, (c.repr x k : ℚ)*W k i)*dualVector219 W j i :=
      congrArg (fun v : Fin 10 → ℚ => ∑ i, v i*dualVector219 W j i) he
    _ = _ := dual_row_sum220 W hW (fun k => (c.repr x k : ℚ)) j


theorem pairing_zero220 (x : Fin 10 → ℤ) : pairing219 0 x = 0 := by
  simp only [pairing219,Pi.zero_apply,mul_zero,Finset.sum_const_zero]

theorem pairing_add220 (v w : Fin 10 → ℚ) (x : Fin 10 → ℤ) :
    pairing219 (v+w) x = pairing219 v x+pairing219 w x := by
  simp only [pairing219,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem pairing_zsmul220 (a : ℤ) (v : Fin 10 → ℚ) (x : Fin 10 → ℤ) :
    pairing219 (a • v) x = (a : ℚ)*pairing219 v x := by
  have he : a • v = (a : ℚ) • v := by ext i; simp
  rw [he,pairing_smul219]

theorem basisDual_subset_scaled219
    (G : AddSubgroup (Fin 10 → ℤ)) (hD : G.index ≠ 0) (c : Basis (Fin 10) ℤ G)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)))
    (z : Fin 10 → ℚ) (hz : z ∈ basisDualSpan219 G c) : z ∈ scaledDual219 G := by
  rw [scaledDual_pairing219 G hD]
  intro x
  induction hz using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j,rfl⟩ := hv
    refine ⟨c.repr x j,?_⟩
    rw [pairing_smul219,basis_dual_pairing220 G c hc x j]
  | zero => exact ⟨0,by rw [pairing_zero220,Int.cast_zero,mul_zero]⟩
  | add v w hv hw ihv ihw =>
    obtain ⟨a,ha⟩ := ihv
    obtain ⟨b,hb⟩ := ihw
    refine ⟨a+b,?_⟩
    rw [pairing_add220,ha,hb,Int.cast_add,mul_add]
  | smul a v hv ih =>
    obtain ⟨b,hb⟩ := ih
    refine ⟨a*b,?_⟩
    rw [pairing_zsmul220,hb,Int.cast_mul]
    ring

theorem scaledDual_eq_basis219
    (G : AddSubgroup (Fin 10 → ℤ)) (hD : G.index ≠ 0) (c : Basis (Fin 10) ℤ G)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))) :
    scaledDual219 G = (basisDualSpan219 G c : Set (Fin 10 → ℚ)) := by
  ext z
  exact ⟨scaledDual_subset_basis219 G c hc z,basisDual_subset_scaled219 G hD c hc z⟩

end CompoundFeasibility.SourceDualGeometry219
