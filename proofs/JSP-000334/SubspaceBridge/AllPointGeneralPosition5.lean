import SubspaceBridge.AllPointFiniteGeometry5
import SubspaceBridge.AllPointSourceExtraction5
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

def allpoint_no_finite_cover5 (E : (Fin 5 → ℤ) → Prop) : Prop :=
  ¬ ∃ F : Set (Submodule ℚ (Fin 5 → ℚ)), F.Finite ∧ (∀ P ∈ F, P ≠ ⊤) ∧
    ∀ z, E z → ∃ P ∈ F, (fun i => (z i : ℚ)) ∈ P

theorem allpoint_avoid_finite5 (E : (Fin 5 → ℤ) → Prop) (hno : allpoint_no_finite_cover5 E)
    (F : Finset (Submodule ℚ (Fin 5 → ℚ))) (hF : ∀ P ∈ F, P ≠ ⊤) :
    ∃ z, E z ∧ ∀ P ∈ F, (fun i => (z i : ℚ)) ∉ P := by
  classical
  by_contra h
  push_neg at h
  exact hno ⟨(F : Set (Submodule ℚ (Fin 5 → ℚ))),F.finite_toSet,hF,h⟩

theorem allpoint_general_position_step5 (E : (Fin 5 → ℤ) → Prop) (hno : allpoint_no_finite_cover5 E)
    (n : ℕ) (v : Fin n → (Fin 5 → ℤ)) :
    ∃ z, E z ∧ max 5 (max (n : ℝ) ((∑ i, (archFiveHeight (v i) : ℝ))+1)) < (archFiveHeight z : ℝ) ∧
      ∀ i j k l : Fin n, (fun l => (z l : ℚ)) ∉ Submodule.span ℚ
        {fun a => (v i a : ℚ),fun a => (v j a : ℚ),fun a => (v k a : ℚ),fun a => (v l a : ℚ)} := by
  classical
  let M := max 5 (max (n : ℝ) ((∑ i, (archFiveHeight (v i) : ℝ))+1))
  let pairs : Finset (Submodule ℚ (Fin 5 → ℚ)) := Finset.univ.image
    (fun ij : Fin n × Fin n × Fin n × Fin n => Submodule.span ℚ {fun k => (v ij.1 k : ℚ),fun k => (v ij.2.1 k : ℚ),fun k => (v ij.2.2.1 k : ℚ),fun k => (v ij.2.2.2 k : ℚ)})
  let low := (allpoint_bounded_height_finite5 M).toFinset.image
    (fun z => Submodule.span ℚ {fun k => (z k : ℚ),fun k => (z k : ℚ),fun k => (z k : ℚ),fun k => (z k : ℚ)})
  have hproper : ∀ P ∈ pairs ∪ low, P ≠ ⊤ := by
    intro P hP
    rcases Finset.mem_union.mp hP with hp | hp
    · obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp hp
      exact allpoint_quad_proper5 _ _ _ _
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hp
      exact allpoint_quad_proper5 _ _ _ _
  obtain ⟨z,hz,havoid⟩ := allpoint_avoid_finite5 E hno (pairs ∪ low) hproper
  refine ⟨z,hz,?_,?_⟩
  · by_contra h
    have hb : (archFiveHeight z : ℝ) ≤ M := le_of_not_gt h
    have hlow : Submodule.span ℚ {fun k => (z k : ℚ),fun k => (z k : ℚ),fun k => (z k : ℚ),fun k => (z k : ℚ)} ∈ low := by
      apply Finset.mem_image.mpr
      exact ⟨z,by simpa using hb,rfl⟩
    apply havoid _ (Finset.mem_union_right _ hlow)
    exact Submodule.subset_span (by simp)
  · intro i j k l
    apply havoid
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(i,j,k,l),Finset.mem_univ _,rfl⟩

theorem allpoint_general_position_sequence5 (E : (Fin 5 → ℤ) → Prop) (hno : allpoint_no_finite_cover5 E) :
    ∃ z : ℕ → (Fin 5 → ℤ), (∀ n, E (z n)) ∧
      (∀ n, 5 < (archFiveHeight (z n) : ℝ) ∧ (n : ℝ) < (archFiveHeight (z n) : ℝ)) ∧
      StrictMono (fun n => (archFiveHeight (z n) : ℝ)) ∧
      ∀ n, ∀ i j k l : Fin n, (fun k => (z n k : ℚ)) ∉ Submodule.span ℚ
        {fun a => (z i.val a : ℚ),fun a => (z j.val a : ℚ),fun a => (z k.val a : ℚ),fun a => (z l.val a : ℚ)} := by
  classical
  choose next hE hheight havoid using allpoint_general_position_step5 E hno
  let step (n : ℕ) (prev : ∀ m, m < n → (Fin 5 → ℤ)) : (Fin 5 → ℤ) := next n (fun i => prev i.val i.isLt)
  let z (n : ℕ) : (Fin 5 → ℤ) := Nat.strongRecOn n step
  have hrec (n : ℕ) : z n = next n (fun i => z i.val) := by
    change Nat.lt_wfRel.wf.fix step n = _
    rw [WellFounded.fix_eq]
    rfl
  have hspec (n : ℕ) : E (z n) ∧
      max 5 (max (n : ℝ) ((∑ i : Fin n, (archFiveHeight (z i.val) : ℝ))+1)) < (archFiveHeight (z n) : ℝ) ∧
      ∀ i j k l : Fin n, (fun k => (z n k : ℚ)) ∉ Submodule.span ℚ
        {fun a => (z i.val a : ℚ),fun a => (z j.val a : ℚ),fun a => (z k.val a : ℚ),fun a => (z l.val a : ℚ)} := by
    have h := And.intro (hE n (fun i => z i.val))
      (And.intro (hheight n (fun i => z i.val)) (havoid n (fun i => z i.val)))
    rw [← hrec n] at h
    exact h
  refine ⟨z,fun n => (hspec n).1,?_,?_,fun n => (hspec n).2.2⟩
  · intro n
    exact ⟨lt_of_le_of_lt (le_max_left _ _) (hspec n).2.1,
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (hspec n).2.1⟩
  · intro i j hij
    have hnon (l : Fin j) : 0 ≤ (archFiveHeight (z l.val) : ℝ) := by
      unfold archFiveHeight
      positivity
    have hh := Finset.single_le_sum (fun l _ => hnon l) (Finset.mem_univ (⟨i,hij⟩ : Fin j))
    have hb : (archFiveHeight (z i) : ℝ) < (∑ l : Fin j, (archFiveHeight (z l.val) : ℝ))+1 := by linarith
    exact hb.trans (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) (hspec j).2.1)



theorem allpoint_general_position_intersection5 (z : ℕ → Fin 5 → ℤ)
    (hH : ∀ n,5<(archFiveHeight (z n) : ℝ))
    (havoid : ∀ n,∀ i j k l : Fin n,(fun a => (z n a : ℚ))∉Submodule.span ℚ
      {fun a => (z i.val a : ℚ),fun a => (z j.val a : ℚ),fun a => (z k.val a : ℚ),fun a => (z l.val a : ℚ)})
    (P : Submodule ℚ (Fin 5 → ℚ)) (hP : P≠⊤) :
    {n | (fun i => (z n i : ℚ))∈P}.Finite := by
  classical
  let v (n : ℕ) : Fin 5 → ℚ := fun i => (z n i : ℚ)
  have hn (n : ℕ) : v n≠0 := by
    intro h
    have hh := hH n
    have hc (i : Fin 5) : (z n i : ℚ)=0 := by simpa only [v,Pi.zero_apply] using congrFun h i
    norm_num [archFiveHeight,hc] at hh
  have hbad (i j k l m : ℕ) (hij : i<j) (hjk : j<k) (hkl : k<l) (hlm : l<m)
      (hi : v i∈P) (hj : v j∈P) (hk : v k∈P) (hl : v l∈P) (hm : v m∈P) : False := by
    have hnotj : v j∉Submodule.span ℚ {v i} := by
      simpa only [v,Set.insert_eq_of_mem (Set.mem_singleton _)] using
        havoid j ⟨i,hij⟩ ⟨i,hij⟩ ⟨i,hij⟩ ⟨i,hij⟩
    have hpair : LinearIndependent ℚ (![v j,v i] : Fin 2 → Fin 5 → ℚ) := by
      apply linearIndependent_fin2.mpr
      refine ⟨hn i,?_⟩
      intro a ha
      exact hnotj (Submodule.mem_span_singleton.mpr ⟨a,ha⟩)
    have hr2 : Set.range (![v j,v i] : Fin 2 → Fin 5 → ℚ)={v j,v i} := by
      ext x
      simp [Fin.exists_fin_two,or_comm,eq_comm]
    have hnotk : v k∉Submodule.span ℚ (Set.range (![v j,v i] : Fin 2 → Fin 5 → ℚ)) := by
      rw [hr2]
      simpa only [v,Set.insert_idem] using havoid k ⟨j,hjk⟩ ⟨j,hjk⟩ ⟨j,hjk⟩ ⟨i,lt_trans hij hjk⟩
    have hthree : LinearIndependent ℚ (![v k,v j,v i] : Fin 3 → Fin 5 → ℚ) :=
      linearIndependent_fin_cons.mpr ⟨hpair,hnotk⟩
    have hr3 : Set.range (![v k,v j,v i] : Fin 3 → Fin 5 → ℚ)={v k,v j,v i} := by
      ext x
      simp [Fin.exists_fin_succ,or_comm,or_left_comm,or_assoc,eq_comm]
    have hnotl : v l∉Submodule.span ℚ (Set.range (![v k,v j,v i] : Fin 3 → Fin 5 → ℚ)) := by
      rw [hr3]
      simpa only [v,Set.insert_idem] using havoid l ⟨k,hkl⟩ ⟨k,hkl⟩ ⟨j,lt_trans hjk hkl⟩ ⟨i,lt_trans hij (lt_trans hjk hkl)⟩
    have hfour : LinearIndependent ℚ (![v l,v k,v j,v i] : Fin 4 → Fin 5 → ℚ) :=
      linearIndependent_fin_cons.mpr ⟨hthree,hnotl⟩
    have hr4 : Set.range (![v l,v k,v j,v i] : Fin 4 → Fin 5 → ℚ)={v l,v k,v j,v i} := by
      ext x
      simp [Fin.exists_fin_succ,or_comm,or_left_comm,or_assoc,eq_comm]
    have hnotm : v m∉Submodule.span ℚ (Set.range (![v l,v k,v j,v i] : Fin 4 → Fin 5 → ℚ)) := by
      rw [hr4]
      exact havoid m ⟨l,hlm⟩ ⟨k,lt_trans hkl hlm⟩ ⟨j,lt_trans hjk (lt_trans hkl hlm)⟩ ⟨i,lt_trans hij (lt_trans hjk (lt_trans hkl hlm))⟩
    have hfive : LinearIndependent ℚ (![v m,v l,v k,v j,v i] : Fin 5 → Fin 5 → ℚ) :=
      linearIndependent_fin_cons.mpr ⟨hfour,hnotm⟩
    have htop := hfive.span_eq_top_of_card_eq_finrank (by simp)
    have hle : Submodule.span ℚ (Set.range (![v m,v l,v k,v j,v i] : Fin 5 → Fin 5 → ℚ))≤P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      fin_cases a
      · exact hm
      · exact hl
      · exact hk
      · exact hj
      · exact hi
    rw [htop] at hle
    exact hP (top_unique hle)
  let S : Set ℕ := {n | v n∈P}
  have hbound : BddAbove S := by
    apply Classical.byContradiction
    intro h
    obtain ⟨i,hi,_⟩ := not_bddAbove_iff.mp h 0
    obtain ⟨j,hj,hij⟩ := not_bddAbove_iff.mp h i
    obtain ⟨k,hk,hjk⟩ := not_bddAbove_iff.mp h j
    obtain ⟨l,hl,hkl⟩ := not_bddAbove_iff.mp h k
    obtain ⟨m,hm,hlm⟩ := not_bddAbove_iff.mp h l
    exact hbad i j k l m hij hjk hkl hlm hi hj hk hl hm
  obtain ⟨N,hN⟩ := hbound
  exact (Set.finite_Iic N).subset (fun n hn => hN hn)

end
end JSP000334
