import Spike
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FieldSimp

namespace JSP000334

open scoped BigOperators

def twoUnit : ℚˣ := Units.mk0 2 (by norm_num)

def threeUnit : ℚˣ := Units.mk0 3 (by norm_num)

def fixedSUnitGroup : Subgroup ℚˣ :=
  Subgroup.closure ({-1, twoUnit, threeUnit} : Set ℚˣ)

def FixedSUnitFiniteness : Prop :=
  ∀ m : Fin 5, (normalizedRelations fixedSUnitGroup (m.val + 1)).Finite

def fixedRelationRatios : Set ℚ :=
  ⋃ m : Fin 5, ⋃ x ∈ normalizedRelations fixedSUnitGroup (m.val + 1),
    Set.range (fun p : Fin (m.val + 2) × Fin (m.val + 2) => -(x p.1 / x p.2))

theorem fixed_relation_ratios_finite (hfin : FixedSUnitFiniteness) :
    fixedRelationRatios.Finite := by
  apply Set.finite_iUnion
  intro m
  exact (hfin m).biUnion (fun x _ => Set.finite_range _)

abbrev ComparisonIndex := Fin 3 ⊕ Fin 3

def summandVector (r : Exponents) : Fin 3 → ℚ :=
  ![(2 : ℚ) ^ r.a, (3 : ℚ) ^ r.b, (2 : ℚ) ^ r.c * (3 : ℚ) ^ r.d]

theorem summandVector_injective : Function.Injective summandVector := by
  intro r s h
  apply summandList_injective
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [summandVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have ha : 2 ^ r.a = 2 ^ s.a := by exact_mod_cast h0
  have hb : 3 ^ r.b = 3 ^ s.b := by exact_mod_cast h1
  have hc : 2 ^ r.c * 3 ^ r.d = 2 ^ s.c * 3 ^ s.d := by exact_mod_cast h2
  simp only [summandList, ha, hb, hc]

theorem summandVector_pos (r : Exponents) (i : Fin 3) : 0 < summandVector r i := by
  fin_cases i <;> simp [summandVector]

private theorem summandVector_mem_group (r : Exponents) (i : Fin 3) :
    ∃ u : fixedSUnitGroup, ((u : ℚˣ) : ℚ) = summandVector r i := by
  have htwo : twoUnit ∈ fixedSUnitGroup := Subgroup.subset_closure (by simp)
  have hthree : threeUnit ∈ fixedSUnitGroup := Subgroup.subset_closure (by simp)
  fin_cases i
  · exact ⟨⟨twoUnit ^ r.a, fixedSUnitGroup.pow_mem htwo _⟩, by simp [summandVector, twoUnit]⟩
  · exact ⟨⟨threeUnit ^ r.b, fixedSUnitGroup.pow_mem hthree _⟩, by simp [summandVector, threeUnit]⟩
  · exact ⟨⟨twoUnit ^ r.c * threeUnit ^ r.d,
      fixedSUnitGroup.mul_mem (fixedSUnitGroup.pow_mem htwo _) (fixedSUnitGroup.pow_mem hthree _)⟩,
      by simp [summandVector, twoUnit, threeUnit]⟩

def comparisonVector (r s : Exponents) : ComparisonIndex → ℚ
  | Sum.inl i => summandVector r i
  | Sum.inr i => -summandVector s i

def MinimalZeroBlock (x : ComparisonIndex → ℚ) (I : Finset ComparisonIndex) : Prop :=
  I.Nonempty ∧ (∑ i ∈ I, x i) = 0 ∧
    ∀ J : Finset ComparisonIndex, J.Nonempty → J ⊆ I → J ≠ I → (∑ i ∈ J, x i) ≠ 0

theorem exists_minimal_zero_block_containing (x : ComparisonIndex → ℚ)
    (a : ComparisonIndex) (hsum : ∑ i, x i = 0) :
    ∃ I : Finset ComparisonIndex, a ∈ I ∧ MinimalZeroBlock x I := by
  classical
  let P : ℕ → Prop := fun k => ∃ I : Finset ComparisonIndex,
    a ∈ I ∧ (∑ i ∈ I, x i) = 0 ∧ I.card = k
  have hex : ∃ k, P k := ⟨Finset.univ.card, Finset.univ, Finset.mem_univ _, hsum, rfl⟩
  obtain ⟨I, ha, hzero, hcard⟩ := Nat.find_spec hex
  have hminimal (J : Finset ComparisonIndex) (haJ : a ∈ J)
      (hzJ : ∑ i ∈ J, x i = 0) : I.card ≤ J.card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨J, haJ, hzJ, rfl⟩
  refine ⟨I, ha, ⟨⟨a, ha⟩, hzero, ?_⟩⟩
  intro J hJ hJI hne hzJ
  by_cases haJ : a ∈ J
  · exact (not_lt_of_ge (hminimal J haJ hzJ))
      (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hJI, hne⟩))
  · have haK : a ∈ I \ J := by simp [ha, haJ]
    have hzK : ∑ i ∈ I \ J, x i = 0 := by
      have h := Finset.sum_sdiff hJI (f := x)
      rw [hzJ, hzero, add_zero] at h
      exact h
    have hlt : (I \ J).card < I.card := by
      have h := Finset.card_sdiff_add_card_eq_card hJI
      have hjpos := Finset.card_pos.mpr hJ
      omega
    exact (not_lt_of_ge (hminimal (I \ J) haK hzK)) hlt

theorem minimal_comparison_block_has_right (r s : Exponents)
    {I : Finset ComparisonIndex} (hI : MinimalZeroBlock (comparisonVector r s) I) :
    ∃ j : Fin 3, Sum.inr j ∈ I := by
  classical
  by_contra h
  push_neg at h
  have hpos : 0 < ∑ i ∈ I, comparisonVector r s i := by
    apply Finset.sum_pos _ hI.1
    intro i hi
    cases i with
    | inl i => exact summandVector_pos r i
    | inr i => exact False.elim (h i hi)
  rw [hI.2.1] at hpos
  exact (lt_irrefl 0 hpos)


theorem minimal_block_ratio_mem (x : ComparisonIndex → ℚ)
    (hunits : ∀ i, ∃ u : fixedSUnitGroup, ((u : ℚˣ) : ℚ) = x i)
    {I : Finset ComparisonIndex} (hI : MinimalZeroBlock x I)
    {a b : ComparisonIndex} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    -(x a / x b) ∈ fixedRelationRatios := by
  classical
  have hlow : 2 ≤ I.card := by
    have hsub : {a, b} ⊆ I := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    simpa [hab] using Finset.card_le_card hsub
  have hhigh : I.card ≤ 6 := by
    simpa using Finset.card_le_univ I
  let m : Fin 5 := ⟨I.card - 2, by omega⟩
  let e : Fin (m.val + 2) ≃ I :=
    (I.equivFinOfCardEq (by dsimp [m]; omega)).symm
  let z : Fin (m.val + 2) → fixedSUnitGroup := fun i => (hunits (e i).val).choose
  have hz (i : Fin (m.val + 2)) : ((z i : ℚˣ) : ℚ) = x (e i).val :=
    (hunits (e i).val).choose_spec
  have hsum : ∑ i, ((z i : ℚˣ) : ℚ) = 0 := by
    simp only [hz]
    rw [e.sum_comp (fun i : I => x i.val)]
    have h := Finset.sum_attach I x
    simpa using h.trans hI.2.1
  have hnd : Nondegenerate (fun i => ((z i : ℚˣ) : ℚ)) := by
    intro J hJ hproper
    let K := J.image (fun i => (e i).val)
    have hKI : K ⊆ I := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact (e j).property
    have hKne : K.Nonempty := hJ.image _
    have hKproper : K ≠ I := by
      intro heq
      apply hproper
      apply Finset.eq_univ_of_forall
      intro i
      have hi : (e i).val ∈ K := by simpa only [heq] using (e i).property
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
      have hji : j = i := e.injective (Subtype.ext he)
      simpa [hji] using hj
    have hsumK : ∑ i ∈ K, x i = ∑ j ∈ J, ((z j : ℚˣ) : ℚ) := by
      rw [Finset.sum_image]
      · simp only [hz]
      · intro i _ j _ he
        exact e.injective (Subtype.ext he)
    rw [← hsumK]
    exact hI.2.2 K hKne hKI hKproper
  let y := normalize (fun i => ((z i : ℚˣ) : ℚ)) 0
  have hy : y ∈ normalizedRelations fixedSUnitGroup (m.val + 1) :=
    normalize_mem_relations fixedSUnitGroup z hsum hnd
  have hza : ((z (e.symm ⟨a, ha⟩) : ℚˣ) : ℚ) = x a := by simp [hz]
  have hzb : ((z (e.symm ⟨b, hb⟩) : ℚˣ) : ℚ) = x b := by simp [hz]
  have hratio : y (e.symm ⟨a, ha⟩) / y (e.symm ⟨b, hb⟩) = x a / x b := by
    dsimp [y, normalize]
    rw [hza, hzb]
    have hb0 : x b ≠ 0 := by
      obtain ⟨u, hu⟩ := hunits b
      rw [← hu]
      exact Units.ne_zero _
    have hz0 : ((z 0 : ℚˣ) : ℚ) ≠ 0 := Units.ne_zero _
    field_simp
  simp only [fixedRelationRatios, Set.mem_iUnion, Set.mem_range]
  exact ⟨m, y, hy, (e.symm ⟨a, ha⟩, e.symm ⟨b, hb⟩), congrArg Neg.neg hratio⟩


private theorem comparisonVector_units (r s : Exponents) (i : ComparisonIndex) :
    ∃ u : fixedSUnitGroup, ((u : ℚˣ) : ℚ) = comparisonVector r s i := by
  cases i with
  | inl i => exact summandVector_mem_group r i
  | inr i =>
      obtain ⟨u, hu⟩ := summandVector_mem_group s i
      have hm : (-1 : ℚˣ) ∈ fixedSUnitGroup := Subgroup.subset_closure (by simp)
      exact ⟨⟨-1, hm⟩ * u, by simp [comparisonVector, hu]⟩

private theorem comparisonVector_sum {r s : Exponents} {n : ℕ}
    (hr : r ∈ solutions n) (hs : s ∈ solutions n) :
    ∑ i, comparisonVector r s i = 0 := by
  have hsum (t : Exponents) : ∑ i, summandVector t i = (value t : ℚ) := by
    simp [summandVector, value, Fin.sum_univ_succ, add_assoc]
  have hrval : value r = n := hr
  have hsval : value s = n := hs
  simp [Fintype.sum_sum_type, comparisonVector, Finset.sum_neg_distrib, hsum, hrval, hsval]

theorem exists_fixed_reference_ratio {r s : Exponents} {n : ℕ}
    (hr : r ∈ solutions n) (hs : s ∈ solutions n) (i : Fin 3) :
    ∃ j : Fin 3, ∃ q : fixedRelationRatios,
      summandVector r i = q.val * summandVector s j := by
  classical
  obtain ⟨I, hi, hI⟩ := exists_minimal_zero_block_containing
    (comparisonVector r s) (Sum.inl i) (comparisonVector_sum hr hs)
  obtain ⟨j, hj⟩ := minimal_comparison_block_has_right r s hI
  have hmem : summandVector r i / summandVector s j ∈ fixedRelationRatios := by
    have h := minimal_block_ratio_mem (comparisonVector r s)
      (comparisonVector_units r s) hI hi hj (by simp)
    simpa only [comparisonVector, div_neg, neg_neg] using h
  refine ⟨j, ⟨_, hmem⟩, ?_⟩
  exact (div_mul_cancel₀ _ (ne_of_gt (summandVector_pos s j))).symm

def referenceValues (s : Exponents) : Set ℚ :=
  ⋃ j : Fin 3, (fun q : ℚ => q * summandVector s j) '' fixedRelationRatios

theorem referenceValues_finite (hfin : FixedSUnitFiniteness) (s : Exponents) :
    (referenceValues s).Finite := by
  exact Set.finite_iUnion (fun j => (fixed_relation_ratios_finite hfin).image _)

theorem summandVector_mem_referenceValues {r s : Exponents} {n : ℕ}
    (hr : r ∈ solutions n) (hs : s ∈ solutions n) (i : Fin 3) :
    summandVector r i ∈ referenceValues s := by
  obtain ⟨j, q, hq⟩ := exists_fixed_reference_ratio hr hs i
  exact Set.mem_iUnion.mpr ⟨j, q.val, q.property, hq.symm⟩

theorem newman_of_fixed_sunit_finiteness (hfin : FixedSUnitFiniteness) :
    NewmanConjecture := by
  classical
  letI : Fintype fixedRelationRatios := (fixed_relation_ratios_finite hfin).fintype
  let Code := Fin 3 → Fin 3 × fixedRelationRatios
  refine ⟨Fintype.card Code, ?_⟩
  intro n _hn
  by_cases hne : (solutions n).Nonempty
  · let s : {r // r ∈ solutions n} := ⟨hne.choose, hne.choose_spec⟩
    have hrel : ∀ (r : {r // r ∈ solutions n}) (i : Fin 3),
        ∃ j : Fin 3, ∃ q : fixedRelationRatios,
          summandVector r.val i = q.val * summandVector s.val j := by
      intro r i
      exact exists_fixed_reference_ratio r.property s.property i
    choose j q hq using hrel
    let code : {r // r ∈ solutions n} → Code := fun r i => (j r i, q r i)
    have hcode : Function.Injective code := by
      intro r t hrt
      apply Subtype.ext
      apply summandVector_injective
      funext i
      have hi := congrFun hrt i
      have hj : j r i = j t i := congrArg Prod.fst hi
      have hqi : q r i = q t i := congrArg Prod.snd hi
      have hrq := hq r i
      rw [hj, hqi] at hrq
      exact hrq.trans (hq t i).symm
    letI : Fintype {r // r ∈ solutions n} := (solutions_finite n).fintype
    unfold tupleCount
    rw [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective code hcode
  · have hempty : solutions n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [tupleCount, hempty]

end JSP000334
