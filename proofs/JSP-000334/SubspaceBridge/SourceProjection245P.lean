import SubspaceBridge.SourceFin5Dual245
import SubspaceBridge.SourceShortSpan241
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245P

theorem spanning_five245P (v : Fin 10 → Fin 5 → ℝ)
    (hs : Submodule.span ℝ (Set.range v) = ⊤) :
    ∃ a : Fin 5 → Fin 10, LinearIndependent ℝ (fun i => v (a i)) := by
  classical
  obtain ⟨t,ht,hspan,hli⟩ := exists_linearIndependent ℝ (Set.range v)
  have hfinite : t.Finite := (Set.finite_range v).subset ht
  letI : Fintype t := hfinite.fintype
  let b : Basis t ℝ (Fin 5 → ℝ) := Basis.mk hli (by rw [Subtype.range_val,hspan,hs])
  have hc : Fintype.card t = 5 := by
    have h := Module.finrank_eq_card_basis b
    simpa using h.symm
  let e : t ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  have hex (x : t) : ∃ j, v j = (x : Fin 5 → ℝ) := ht x.property
  choose a ha using hex
  refine ⟨fun i => a (e.symm i),?_⟩
  have hind := hli.comp e.symm e.symm.injective
  convert hind using 1
  funext i
  exact ha (e.symm i)

theorem projected_frame245P (p : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ))
    (hp : Function.Surjective p) (w : Fin 10 → Fin 10 → ℝ)
    (hw : LinearIndependent ℝ w) :
    ∃ a : Fin 5 → Fin 10, LinearIndependent ℝ (fun i => p (w (a i))) := by
  have hs : Submodule.span ℝ (Set.range w) = ⊤ := by
    simpa only [coe_basisOfPiSpaceOfLinearIndependent] using
      (basisOfPiSpaceOfLinearIndependent hw).span_eq
  apply spanning_five245P (fun j => p (w j))
  rw [show Set.range (fun j => p (w j)) = p '' Set.range w from Set.range_comp p w,
    ← Submodule.map_span,hs,Submodule.map_top,LinearMap.range_eq_top.mpr hp]

end CompoundFeasibility.BlockReduction245P
