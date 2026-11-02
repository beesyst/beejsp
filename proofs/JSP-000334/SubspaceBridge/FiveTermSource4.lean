import SubspaceBridge.FiveTermDegeneracy4
import SubspaceBridge.AllPointFiniteCover4
namespace JSP000334
open scoped BigOperators Matrix

theorem five_term_proper_annihilator4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P≠⊤) :
    ∃ a0 a1 a2 a3 : ℚ,(a0≠0 ∨ a1≠0 ∨ a2≠0 ∨ a3≠0) ∧
      ∀ y∈P,a0*y 0+a1*y 1+a2*y 2+a3*y 3=0 := by
  obtain ⟨f,hf,hker⟩ := P.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hP)
  have heval (y : Fin 4 → ℚ) : f y=f ![1,0,0,0]*y 0+f ![0,1,0,0]*y 1+f ![0,0,1,0]*y 2+f ![0,0,0,1]*y 3 := by
    have hy : y=y 0 • ![(1 : ℚ),0,0,0]+y 1 • ![0,1,0,0]+y 2 • ![0,0,1,0]+y 3 • ![0,0,0,1] := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hy]
    simp only [map_add,map_smul,smul_eq_mul]
    ring
  refine ⟨f ![1,0,0,0],f ![0,1,0,0],f ![0,0,1,0],f ![0,0,0,1],?_,?_⟩
  · by_contra hn
    push_neg at hn
    apply hf
    apply LinearMap.ext
    intro y
    simpa [hn.1,hn.2.1,hn.2.2.1,hn.2.2.2] using heval y
  · intro y hy
    have hk : f y=0 := hker hy
    rw [heval] at hk
    exact hk

theorem five_term_relation_facts4 {x : Fin 5 → ℚ}
    (hx : x∈normalizedRelations fixedSUnitGroup 4) :
    x 0=1 ∧ x 0+x 1+x 2+x 3+x 4=0 ∧ (∀ i,x i≠0) ∧
      x 4=-(x 0+x 1+x 2+x 3) := by
  have hs : x 0+x 1+x 2+x 3+x 4=0 := by simpa [Fin.sum_univ_succ,add_assoc] using hx.2.2.1
  refine ⟨hx.1,hs,?_,by linarith⟩
  intro i
  obtain ⟨u,hu⟩ := hx.2.1 i
  rw [← hu]
  exact Units.ne_zero _

end JSP000334
