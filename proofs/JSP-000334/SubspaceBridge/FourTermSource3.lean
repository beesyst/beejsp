import SubspaceBridge.AllPointFiniteCover3
namespace JSP000334

theorem four_term_relation_facts {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    x 0=1 ∧ x 0+x 1+x 2+x 3=0 ∧
      x 0+x 1≠0 ∧ x 0+x 2≠0 ∧ x 1+x 2≠0 ∧ ∀ i,x i≠0 := by
  refine ⟨hx.1,?_,?_,?_,?_,?_⟩
  · simpa [Fin.sum_univ_succ,add_assoc] using hx.2.2.1
  · simpa using hx.2.2.2 ({0,1} : Finset (Fin 4)) (by decide) (by decide)
  · simpa using hx.2.2.2 ({0,2} : Finset (Fin 4)) (by decide) (by decide)
  · simpa using hx.2.2.2 ({1,2} : Finset (Fin 4)) (by decide) (by decide)
  · intro i
    obtain ⟨u,hu⟩ := hx.2.1 i
    rw [← hu]
    exact Units.ne_zero _

theorem four_term_original_mem {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3)
    (P : Submodule ℚ (Fin 3 → ℚ)) (w : Fin 4 → ℤ) (s : fixedSUnitGroup)
    (hscale : ∀ i,(w i : ℚ)=((s : ℚˣ) : ℚ)*x i)
    (hw : (fun i : Fin 3 => (w i.castSucc : ℚ)) ∈ P) : ![1,x 1,x 2] ∈ P := by
  have hs : ((s : ℚˣ) : ℚ)≠0 := Units.ne_zero _
  have hm := P.smul_mem (((s : ℚˣ) : ℚ)⁻¹) hw
  have he : (((s : ℚˣ) : ℚ)⁻¹) • (fun i : Fin 3 => (w i.castSucc : ℚ)) =
      (fun i : Fin 3 => x i.castSucc) := by
    ext i
    change ((s : ℚˣ) : ℚ)⁻¹*(w i.castSucc : ℚ)=x i.castSucc
    rw [hscale,inv_mul_cancel_left₀ hs]
  rw [he] at hm
  have hv : (fun i : Fin 3 => x i.castSucc) = ![1,x 1,x 2] := by
    ext i
    fin_cases i
    · exact hx.1
    · rfl
    · rfl
  rw [hv] at hm
  exact hm

theorem four_term_proper_annihilator (P : Submodule ℚ (Fin 3 → ℚ)) (hP : P≠⊤) :
    ∃ a0 a1 a2 : ℚ,(a0≠0 ∨ a1≠0 ∨ a2≠0) ∧
      ∀ y∈P,a0*y 0+a1*y 1+a2*y 2=0 := by
  obtain ⟨f,hf,hker⟩ := P.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hP)
  have heval (y : Fin 3 → ℚ) : f y=f ![1,0,0]*y 0+f ![0,1,0]*y 1+f ![0,0,1]*y 2 := by
    have hy : y=y 0 • ![(1 : ℚ),0,0]+y 1 • ![0,1,0]+y 2 • ![0,0,1] := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hy]
    simp only [map_add,map_smul,smul_eq_mul]
    ring
  refine ⟨f ![1,0,0],f ![0,1,0],f ![0,0,1],?_,?_⟩
  · by_contra hn
    push_neg at hn
    apply hf
    apply LinearMap.ext
    intro y
    simpa [hn.1,hn.2.1,hn.2.2] using heval y
  · intro y hy
    have hk : f y=0 := hker hy
    rw [heval] at hk
    exact hk

end JSP000334
