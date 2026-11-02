import SubspaceBridge.SourceCompoundGap54_246F
import Mathlib.LinearAlgebra.Dual.Lemmas
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag247
open Exterior54_246

def dotDual247 : (Fin 5 → ℚ) ≃ₗ[ℚ] Module.Dual ℚ (Fin 5 → ℚ) :=
  (Pi.basisFun ℚ (Fin 5)).toDualEquiv

theorem dotDual_apply247 (x y : Fin 5 → ℚ) :
    dotDual247 x y = ∑ i, x i * y i := by
  rw [OriginalDual10.functional_coordinates_dual10]
  apply Finset.sum_congr rfl
  intro i _
  have hi : dotDual247 x (Pi.single i 1) = x i := by
    simpa only [dotDual247, Basis.toDualEquiv_apply, Pi.basisFun_apply, Pi.basisFun_repr] using
      (Pi.basisFun ℚ (Fin 5)).toDual_apply_left x i
  rw [hi,mul_comm]

def annihilator247 (H : Submodule ℚ (Fin 5 → ℚ)) : Submodule ℚ (Fin 5 → ℚ) :=
  H.dualAnnihilator.comap dotDual247.toLinearMap

theorem annihilator_rank247 (H : Submodule ℚ (Fin 5 → ℚ))
    (hH : Module.finrank ℚ H = 4) : Module.finrank ℚ (annihilator247 H) = 1 := by
  have he := Submodule.comap_equiv_self_of_inj_of_le (f := dotDual247.toLinearMap)
    (p := H.dualAnnihilator) dotDual247.injective (by
      intro f _
      obtain ⟨x,hx⟩ := dotDual247.surjective f
      exact ⟨x,hx⟩)
  change Module.finrank ℚ (H.dualAnnihilator.comap dotDual247.toLinearMap) = 1
  rw [he.finrank_eq]
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq H
  rw [hH] at hd
  have hn : Module.finrank ℚ (Fin 5 → ℚ) = 5 := by simp
  rw [hn] at hd
  omega

theorem signedQuad_pairing247 (u : Matrix (Fin 5) (Fin 5) ℚ) (r k : Fin 5) :
    (∑ i, u r i * signedQuad246 u k i) = if r = k then u.det else 0 := by
  simp_rw [signedQuad_adjugate246]
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℚ => M r k) (Matrix.mul_adjugate u)
  simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using h

theorem first_four_pairing247 (u : Matrix (Fin 5) (Fin 5) ℚ) (j : Fin 4) :
    dotDual247 (u 0) (signedQuad246 u j.castSucc.rev) = 0 := by
  rw [dotDual_apply247,signedQuad_pairing247]
  have hj : ∀ j : Fin 4, (0 : Fin 5) ≠ j.castSucc.rev := by decide
  exact if_neg (hj j)

theorem signedQuad_rat_independent247 (u : Matrix (Fin 5) (Fin 5) ℚ)
    (hu : LinearIndependent ℚ u) : LinearIndependent ℚ (signedQuad246 u) := by
  have he : signedQuad246 u = (compound4246 u : Matrix (Fin 5) (Fin 5) ℚ) := by
    funext j i
    exact signedQuad_adjugate246 u j i
  rw [he]
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr
    (compound_unit4246 u (Matrix.linearIndependent_rows_iff_isUnit.mp hu))

theorem four_wedge_annihilator247 (u : Matrix (Fin 5) (Fin 5) ℚ)
    (hu : LinearIndependent ℚ u) :
    let H := Submodule.span ℚ (Set.range (fun j : Fin 4 => signedQuad246 u j.castSucc.rev))
    annihilator247 H = Submodule.span ℚ {u 0} ∧ Module.finrank ℚ (annihilator247 H) = 1 := by
  let H := Submodule.span ℚ (Set.range (fun j : Fin 4 => signedQuad246 u j.castSucc.rev))
  have hi : LinearIndependent ℚ (fun j : Fin 4 => signedQuad246 u j.castSucc.rev) :=
    (signedQuad_rat_independent247 u hu).comp (fun j : Fin 4 => j.castSucc.rev)
      (Fin.rev_injective.comp (Fin.castSucc_injective 4))
  have hH : Module.finrank ℚ H = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hi
  have hr := annihilator_rank247 H hH
  have hm : u 0 ∈ annihilator247 H := by
    change dotDual247 (u 0) ∈ H.dualAnnihilator
    apply (Submodule.mem_dualAnnihilator (dotDual247 (u 0))).mpr
    have hh : H ≤ LinearMap.ker (dotDual247 (u 0)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact first_four_pairing247 u j
    intro x hx
    exact hh hx
  have hle : Submodule.span ℚ {u 0} ≤ annihilator247 H :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hm
  have hs : Module.finrank ℚ (Submodule.span ℚ {u 0}) = 1 := finrank_span_singleton (hu.ne_zero 0)
  exact ⟨(Submodule.eq_of_le_of_finrank_eq hle (hs.trans hr.symm)).symm,hr⟩

theorem signedQuad_rat_cast247 (u : Fin 5 → Fin 5 → ℤ) (j : Fin 5) :
    (fun i => ((signedQuad246 u j i : ℤ) : ℚ)) = signedQuad246 (fun k i => (u k i : ℚ)) j := by
  funext i
  rw [signedQuad_adjugate246, signedQuad_adjugate246]
  have h := (Int.castRingHom ℚ).map_adjugate (u : Matrix (Fin 5) (Fin 5) ℤ)
  exact congrArg (fun M : Matrix (Fin 5) (Fin 5) ℚ => M i j) h

end CompoundFeasibility.SourceFlag247
