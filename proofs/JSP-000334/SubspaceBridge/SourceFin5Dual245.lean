import SubspaceBridge.OriginalDual10
import SubspaceBridge.SourceExceptionalPair241
import SubspaceBridge.OriginalSource5
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceRank4_245
open OriginalDual10 SourceFlag241

theorem last_dual_pairing245 (u : Fin 5 → Fin 5 → ℚ) (hu : LinearIndependent ℚ u)
    (j : Fin 5) :
    (∑ i, u j i * lastDual10 (n := 4) u hu i) = if j = 4 then 1 else 0 := by
  exact (functional_coordinates_dual10 (rationalFrameDual42 u hu 4) (u j)).symm.trans
    (rationalFrameDual42_pairing u hu 4 j)

theorem last_dual_nonzero245 (u : Fin 5 → Fin 5 → ℚ) (hu : LinearIndependent ℚ u) :
    lastDual10 (n := 4) u hu ≠ 0 := by
  intro hz
  have h := last_dual_pairing245 u hu 4
  rw [hz] at h
  norm_num at h

theorem last_dual_kernel245 (u : Fin 5 → Fin 5 → ℚ) (hu : LinearIndependent ℚ u) :
    LinearMap.ker (rationalFrameDual42 u hu 4) =
      Submodule.span ℚ (Set.range (fun j : Fin 4 => u j.castSucc)) := by
  apply le_antisymm
  · intro x hx
    have hz : (rationalFrameBasis42 u hu).repr x 4 = 0 := by
      rw [← Basis.dualBasis_apply]
      exact (show rationalFrameDual42 u hu 4 x = 0 from hx)
    have he := (rationalFrameBasis42 u hu).sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 4 = (4 : Fin 5) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [rationalFrameBasis42_apply]
    exact Submodule.subset_span ⟨j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change rationalFrameDual42 u hu 4 (u j.castSucc) = 0
    rw [rationalFrameDual42_pairing,if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

theorem lattice5_eq_generic245 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (e : Fin 5 → ℕ) :
    lattice5 p A e = lattice10 p A e := rfl

theorem exists_attaining_family245 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (Omega : Set ℝ) (hq : ∀ Q ∈ Omega, 1 < Q) :
    ∃ u : (q : Omega) → Fin 5 → originalSourceGroup5 A2 A3 q.val c2 c3,
      ∀ q : Omega, LinearIndependent ℝ (fun j => integerReal (u q j : Fin 5 → ℤ)) ∧
        (∀ j, coordinateGauge5 (originalCoordinates5 L hL q.val (hq q.val q.property) c0)
          (integerReal (u q j : Fin 5 → ℤ)) =
            sourceMinima5 A2 A3 L hL q.val (hq q.val q.property) c0 c2 c3 j) ∧
        integerLastDual10 (n := 4) (fun j => (u q j : Fin 5 → ℤ)) ≠ 0 := by
  classical
  have hex (q : Omega) := exists_sourceMinima5_attaining A2 A3 L hL q.val
    (hq q.val q.property) c0 c2 c3
  choose u hu hpos hmono hatt hpoint using hex
  exact ⟨u,fun q => ⟨hu q,hatt q,integerLastDual10_nonzero _
    (original_rational_independent241 _ (hu q))⟩⟩

end CompoundFeasibility.SourceRank4_245
