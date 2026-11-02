import SubspaceBridge.FiveTermSource4
import SubspaceBridge.FiveTermProjection4
namespace JSP000334
open scoped BigOperators Matrix

noncomputable def fiveTermUnit4 (x : Fin 5 → ℚ) (i : Fin 5) : fixedSUnitGroup := by
  classical
  exact if h : x∈normalizedRelations fixedSUnitGroup 4 then (h.2.1 i).choose else 1

theorem five_term_unit_value4 {x : Fin 5 → ℚ} (hx : x∈normalizedRelations fixedSUnitGroup 4) (i : Fin 5) :
    ((fiveTermUnit4 x i : ℚˣ) : ℚ)=x i := by
  simp only [fiveTermUnit4,dif_pos hx]
  exact (hx.2.1 i).choose_spec

theorem five_term_pair_fiber_values4 (S : Set (Fin 5 → ℚ))
    (hs : S⊆normalizedRelations fixedSUnitGroup 4) (i j : Fin 5)
    (p : fixedSUnitGroup × fixedSUnitGroup) (x : Fin 5 → ℚ)
    (hx : x∈{x∈S | (fiveTermUnit4 x i,fiveTermUnit4 x j)=p}) :
    x i=((p.1 : ℚˣ) : ℚ) ∧ x j=((p.2 : ℚˣ) : ℚ) := by
  have he1 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.1 : ℚˣ) : ℚ)) hx.2
  have he2 := congrArg (fun q : fixedSUnitGroup × fixedSUnitGroup => ((q.2 : ℚˣ) : ℚ)) hx.2
  simpa only [five_term_unit_value4 (hs hx.1)] using And.intro he1 he2

end JSP000334
