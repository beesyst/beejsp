import SubspaceBridge.AllPointFiniteGeometry3
import SubspaceBridge.AllPointSourceFamily3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

def allpoint_no_finite_cover3 (E : IntegerTriple → Prop) : Prop :=
  ¬ ∃ F : Set (Submodule ℚ (Fin 3 → ℚ)), F.Finite ∧ (∀ P ∈ F, P ≠ ⊤) ∧
    ∀ z, E z → ∃ P ∈ F, (fun i => (z i : ℚ)) ∈ P

theorem allpoint_avoid_finite3 (E : IntegerTriple → Prop) (hno : allpoint_no_finite_cover3 E)
    (F : Finset (Submodule ℚ (Fin 3 → ℚ))) (hF : ∀ P ∈ F, P ≠ ⊤) :
    ∃ z, E z ∧ ∀ P ∈ F, (fun i => (z i : ℚ)) ∉ P := by
  classical
  by_contra h
  push_neg at h
  exact hno ⟨(F : Set (Submodule ℚ (Fin 3 → ℚ))),F.finite_toSet,hF,h⟩

theorem allpoint_general_position_step3 (E : IntegerTriple → Prop) (hno : allpoint_no_finite_cover3 E)
    (n : ℕ) (v : Fin n → IntegerTriple) :
    ∃ z, E z ∧ max 3 (max (n : ℝ) ((∑ i, (archTripleHeight (v i) : ℝ))+1)) < (archTripleHeight z : ℝ) ∧
      ∀ i j : Fin n, (fun k => (z k : ℚ)) ∉ Submodule.span ℚ
        {fun k => (v i k : ℚ),fun k => (v j k : ℚ)} := by
  classical
  let M := max 3 (max (n : ℝ) ((∑ i, (archTripleHeight (v i) : ℝ))+1))
  let pairs : Finset (Submodule ℚ (Fin 3 → ℚ)) := Finset.univ.image
    (fun ij : Fin n × Fin n => Submodule.span ℚ {fun k => (v ij.1 k : ℚ),fun k => (v ij.2 k : ℚ)})
  let low := (allpoint_bounded_height_finite3 M).toFinset.image
    (fun z => Submodule.span ℚ {fun k => (z k : ℚ),fun k => (z k : ℚ)})
  have hproper : ∀ P ∈ pairs ∪ low, P ≠ ⊤ := by
    intro P hP
    rcases Finset.mem_union.mp hP with hp | hp
    · obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp hp
      exact allpoint_pair_proper3 _ _
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hp
      exact allpoint_pair_proper3 _ _
  obtain ⟨z,hz,havoid⟩ := allpoint_avoid_finite3 E hno (pairs ∪ low) hproper
  refine ⟨z,hz,?_,?_⟩
  · by_contra h
    have hb : (archTripleHeight z : ℝ) ≤ M := le_of_not_gt h
    have hlow : Submodule.span ℚ {fun k => (z k : ℚ),fun k => (z k : ℚ)} ∈ low := by
      apply Finset.mem_image.mpr
      exact ⟨z,by simpa using hb,rfl⟩
    apply havoid _ (Finset.mem_union_right _ hlow)
    exact Submodule.subset_span (by simp)
  · intro i j
    apply havoid
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩

theorem allpoint_general_position_sequence3 (E : IntegerTriple → Prop) (hno : allpoint_no_finite_cover3 E) :
    ∃ z : ℕ → IntegerTriple, (∀ n, E (z n)) ∧
      (∀ n, 3 < (archTripleHeight (z n) : ℝ) ∧ (n : ℝ) < (archTripleHeight (z n) : ℝ)) ∧
      StrictMono (fun n => (archTripleHeight (z n) : ℝ)) ∧
      ∀ n, ∀ i j : Fin n, (fun k => (z n k : ℚ)) ∉ Submodule.span ℚ
        {fun k => (z i.val k : ℚ),fun k => (z j.val k : ℚ)} := by
  classical
  choose next hE hheight havoid using allpoint_general_position_step3 E hno
  let step (n : ℕ) (prev : ∀ m, m < n → IntegerTriple) : IntegerTriple := next n (fun i => prev i.val i.isLt)
  let z (n : ℕ) : IntegerTriple := Nat.strongRecOn n step
  have hrec (n : ℕ) : z n = next n (fun i => z i.val) := by
    change Nat.lt_wfRel.wf.fix step n = _
    rw [WellFounded.fix_eq]
    rfl
  have hspec (n : ℕ) : E (z n) ∧
      max 3 (max (n : ℝ) ((∑ i : Fin n, (archTripleHeight (z i.val) : ℝ))+1)) < (archTripleHeight (z n) : ℝ) ∧
      ∀ i j : Fin n, (fun k => (z n k : ℚ)) ∉ Submodule.span ℚ
        {fun k => (z i.val k : ℚ),fun k => (z j.val k : ℚ)} := by
    have h := And.intro (hE n (fun i => z i.val))
      (And.intro (hheight n (fun i => z i.val)) (havoid n (fun i => z i.val)))
    rw [← hrec n] at h
    exact h
  refine ⟨z,fun n => (hspec n).1,?_,?_,fun n => (hspec n).2.2⟩
  · intro n
    exact ⟨lt_of_le_of_lt (le_max_left _ _) (hspec n).2.1,
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (hspec n).2.1⟩
  · intro i j hij
    have hnon (l : Fin j) : 0 ≤ (archTripleHeight (z l.val) : ℝ) := by
      change 0 ≤ ((max |(z l.val 0 : ℚ)| (max |(z l.val 1 : ℚ)| |(z l.val 2 : ℚ)|) : ℚ) : ℝ)
      positivity
    have hh := Finset.single_le_sum (fun l _ => hnon l) (Finset.mem_univ (⟨i,hij⟩ : Fin j))
    have hb : (archTripleHeight (z i) : ℝ) < (∑ l : Fin j, (archTripleHeight (z l.val) : ℝ))+1 := by linarith
    exact hb.trans (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) (hspec j).2.1)


theorem allpoint_general_position_intersection3 (z : ℕ → IntegerTriple)
    (hH : ∀ n, 3 < (archTripleHeight (z n) : ℝ))
    (havoid : ∀ n, ∀ i j : Fin n, (fun k => (z n k : ℚ)) ∉ Submodule.span ℚ
      {fun k => (z i.val k : ℚ),fun k => (z j.val k : ℚ)})
    (P : Submodule ℚ (Fin 3 → ℚ)) (hP : P ≠ ⊤) :
    {n | (fun i => (z n i : ℚ)) ∈ P}.Finite ∧ {n | (fun i => (z n i : ℚ)) ∈ P}.ncard ≤ 2 := by
  classical
  let v (n : ℕ) : Fin 3 → ℚ := fun i => (z n i : ℚ)
  have hn (n : ℕ) : v n ≠ 0 := by
    intro h
    have hh := hH n
    have hc (i : Fin 3) : (z n i : ℚ) = 0 := by simpa only [v,Pi.zero_apply] using congrFun h i
    norm_num [archTripleHeight,hc] at hh
  have hbad (i j k : ℕ) (hij : i < j) (hjk : j < k)
      (hi : v i ∈ P) (hj : v j ∈ P) (hk : v k ∈ P) : False := by
    have hnotj : v j ∉ Submodule.span ℚ {v i} := by
      simpa only [v,Set.pair_eq_singleton] using havoid j ⟨i,hij⟩ ⟨i,hij⟩
    have hpair : LinearIndependent ℚ (![v j,v i] : Fin 2 → Fin 3 → ℚ) := by
      apply linearIndependent_fin2.mpr
      refine ⟨hn i,?_⟩
      intro a ha
      exact hnotj (Submodule.mem_span_singleton.mpr ⟨a,ha⟩)
    have hrange : Set.range (![v j,v i] : Fin 2 → Fin 3 → ℚ) = {v j,v i} := by
      ext x
      simp [Fin.exists_fin_two,eq_comm,or_comm]
    have hnotk : v k ∉ Submodule.span ℚ (Set.range (![v j,v i] : Fin 2 → Fin 3 → ℚ)) := by
      rw [hrange]
      exact havoid k ⟨j,hjk⟩ ⟨i,lt_trans hij hjk⟩
    have htriple : LinearIndependent ℚ (![v k,v j,v i] : Fin 3 → Fin 3 → ℚ) :=
      linearIndependent_fin_cons.mpr ⟨hpair,hnotk⟩
    have htop := htriple.span_eq_top_of_card_eq_finrank (by simp)
    have hle : Submodule.span ℚ (Set.range (![v k,v j,v i] : Fin 3 → Fin 3 → ℚ)) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      fin_cases a
      · exact hk
      · exact hj
      · exact hi
    rw [htop] at hle
    exact hP (top_unique hle)
  let S : Set ℕ := {n | v n ∈ P}
  have hbound : BddAbove S := by
    apply Classical.byContradiction
    intro h
    obtain ⟨i,hi,_⟩ := not_bddAbove_iff.mp h 0
    obtain ⟨j,hj,hij⟩ := not_bddAbove_iff.mp h i
    obtain ⟨k,hk,hjk⟩ := not_bddAbove_iff.mp h j
    exact hbad i j k hij hjk hi hj hk
  obtain ⟨N,hN⟩ := hbound
  have hfinite : S.Finite := (Set.finite_Iic N).subset (fun n hn => hN hn)
  refine ⟨hfinite,?_⟩
  apply Nat.le_of_not_gt
  intro hcard
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := (Set.two_lt_ncard_iff hfinite).mp hcard
  have hord : (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨ (b < a ∧ a < c) ∨
      (b < c ∧ c < a) ∨ (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by omega
  rcases hord with h | h | h | h | h | h
  · exact hbad a b c h.1 h.2 ha hb hc
  · exact hbad a c b h.1 h.2 ha hc hb
  · exact hbad b a c h.1 h.2 hb ha hc
  · exact hbad b c a h.1 h.2 hb hc ha
  · exact hbad c a b h.1 h.2 hc ha hb
  · exact hbad c b a h.1 h.2 hc hb ha

end
end JSP000334
