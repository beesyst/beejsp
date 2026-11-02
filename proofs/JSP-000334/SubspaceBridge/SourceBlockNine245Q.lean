import SubspaceBridge.SourceBlockGauge245Q
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245Q

def joinLinear245Q : ((Fin 5 → ℝ) × (Fin 5 → ℝ)) →ₗ[ℝ] (Fin 10 → ℝ) where
  toFun x := join245Q x.1 x.2
  map_add' x y := by
    ext j
    cases h : BlockReduction245P.blockIndex245P.symm j <;> simp [join245Q,h]
  map_smul' a x := by
    ext j
    cases h : BlockReduction245P.blockIndex245P.symm j <;> simp [join245Q,h]

theorem joinLinear_injective245Q : Function.Injective joinLinear245Q := by
  intro x y h
  apply Prod.ext
  · simpa only [joinLinear245Q,LinearMap.coe_mk,AddHom.coe_mk,first_join245Q] using congrArg first245Q h
  · simpa only [joinLinear245Q,LinearMap.coe_mk,AddHom.coe_mk,second_join245Q] using congrArg second245Q h

def nineFrame245Q (u : Fin 5 → Fin 5 → ℝ) (j : Fin 9) : Fin 10 → ℝ :=
  Sum.elim (fun i : Fin 4 => join245Q (u i.castSucc) 0)
    (fun i : Fin 5 => join245Q 0 (Pi.single i 1))
    ((finSumFinEquiv : Fin 4 ⊕ Fin 5 ≃ Fin 9).symm j)

theorem nine_independent245Q (u : Fin 5 → Fin 5 → ℝ) (hu : LinearIndependent ℝ u) :
    LinearIndependent ℝ (nineFrame245Q u) := by
  have h4 := hu.comp (fun j : Fin 4 => j.castSucc) (Fin.castSucc_injective _)
  have h5 := (Pi.basisFun ℝ (Fin 5)).linearIndependent
  have hp := linearIndependent_inl_union_inr' h4 h5
  have hm := hp.map' joinLinear245Q (LinearMap.ker_eq_bot.mpr joinLinear_injective245Q)
  have hr := hm.comp (finSumFinEquiv : Fin 4 ⊕ Fin 5 ≃ Fin 9).symm
    (finSumFinEquiv : Fin 4 ⊕ Fin 5 ≃ Fin 9).symm.injective
  convert hr using 1
  funext j
  obtain ⟨s,rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 5 ≃ Fin 9).surjective j
  cases s <;> simp [nineFrame245Q,joinLinear245Q]

end CompoundFeasibility.BlockReduction245Q
