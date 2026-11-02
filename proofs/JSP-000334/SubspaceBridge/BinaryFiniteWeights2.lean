import SubspaceBridge.BinarySourceWeights2
open scoped BigOperators Classical
namespace JSP000334

noncomputable def binaryWeightIndex (c : Fin 3 → Fin 2 → ℝ) (tau : Fin 3) (i : Fin 2) : ℤ :=
  ⌈1152*c tau i⌉
noncomputable def binaryWeightRaw (z : Fin 3 → Fin 2 → ℤ) (tau : Fin 3) (i : Fin 2) : ℝ :=
  (z tau i : ℝ)/1152
noncomputable def binaryWeightCandidate (z : Fin 3 → Fin 2 → ℤ) (tau : Fin 3) (i : Fin 2) : ℝ :=
  if tau=0 then binaryWeightRaw z tau i-(∑ t : Fin 3,∑ j : Fin 2,binaryWeightRaw z t j)/2
  else binaryWeightRaw z tau i
noncomputable def binaryWeightApprox (c : Fin 3 → Fin 2 → ℝ) : Fin 3 → Fin 2 → ℝ :=
  binaryWeightCandidate (binaryWeightIndex c)

theorem binary_weight_raw_error (c : Fin 3 → Fin 2 → ℝ) (tau : Fin 3) (i : Fin 2) :
    c tau i≤binaryWeightRaw (binaryWeightIndex c) tau i ∧
      binaryWeightRaw (binaryWeightIndex c) tau i≤c tau i+1/1152 := by
  unfold binaryWeightRaw binaryWeightIndex
  have hl := Int.le_ceil (1152*c tau i)
  have hu := Int.ceil_lt_add_one (1152*c tau i)
  constructor <;> linarith

theorem binary_weight_candidate_balance (z : Fin 3 → Fin 2 → ℤ) :
    (∑ tau : Fin 3,∑ i : Fin 2,binaryWeightCandidate z tau i)=0 := by
  simp only [binaryWeightCandidate,Fin.sum_univ_three,Fin.sum_univ_two,Fin.isValue,
    Fin.reduceEq,ite_true,ite_false]
  ring

theorem binary_weight_round_bounds (c : Fin 3 → Fin 2 → ℝ)
    (hb : (∑ tau : Fin 3,∑ i : Fin 2,c tau i)=0) (hc : ∀ tau i,|c tau i|≤15/32) :
    (∀ tau i,|binaryWeightApprox c tau i|≤1) ∧
    (∀ i,c 0 i-1/384≤binaryWeightApprox c 0 i) ∧
    (∀ tau : Fin 3,tau ≠ 0 → ∀ i,c tau i≤binaryWeightApprox c tau i) := by
  let s := ∑ tau : Fin 3,∑ i : Fin 2,binaryWeightRaw (binaryWeightIndex c) tau i
  have h0 := binary_weight_raw_error c 0
  have h1 := binary_weight_raw_error c 1
  have h2 := binary_weight_raw_error c 2
  have hs : 0≤s ∧ s≤1/192 := by
    dsimp [s]
    simp only [Fin.sum_univ_three,Fin.sum_univ_two] at hb ⊢
    constructor <;> linarith [(h0 0).1,(h0 0).2,(h0 1).1,(h0 1).2,
      (h1 0).1,(h1 0).2,(h1 1).1,(h1 1).2,(h2 0).1,(h2 0).2,(h2 1).1,(h2 1).2]
  have he (tau i) := binary_weight_raw_error c tau i
  have hre (i : Fin 2) : binaryWeightApprox c 0 i=binaryWeightRaw (binaryWeightIndex c) 0 i-s/2 := by
    rfl
  have hfi (tau : Fin 3) (ht : tau ≠ 0) (i : Fin 2) :
      binaryWeightApprox c tau i=binaryWeightRaw (binaryWeightIndex c) tau i := by
    simp [binaryWeightApprox,binaryWeightCandidate,ht]
  refine ⟨?_,?_,?_⟩
  · intro tau i
    have hh := abs_le.mp (hc tau i)
    apply abs_le.mpr
    by_cases ht : tau=0
    · subst tau
      rw [hre]
      constructor <;> linarith [(he 0 i).1,(he 0 i).2]
    · rw [hfi tau ht]
      constructor <;> linarith [(he tau i).1,(he tau i).2]
  · intro i
    rw [hre]
    linarith [(he 0 i).1]
  · intro tau ht i
    rw [hfi tau ht]
    exact (he tau i).1

noncomputable def binaryWeightCandidates : Set (Fin 3 → Fin 2 → ℝ) :=
  (binaryWeightCandidate '' {z : Fin 3 → Fin 2 → ℤ | ∀ tau i,-1152≤z tau i ∧ z tau i≤1152}) ∩
    {c | (∑ tau : Fin 3,∑ i : Fin 2,c tau i)=0 ∧ ∀ tau i,|c tau i|≤1}

theorem binary_weight_candidates_finite : binaryWeightCandidates.Finite := by
  have hh : {z : Fin 3 → Fin 2 → ℤ | ∀ tau i,-1152≤z tau i ∧ z tau i≤1152}.Finite :=
    Set.Finite.pi' (fun _ => Set.Finite.pi' (fun _ => Set.finite_Icc _ _))
  exact (hh.image binaryWeightCandidate).subset Set.inter_subset_left

theorem binary_weight_approx_mem (c : Fin 3 → Fin 2 → ℝ)
    (hb : (∑ tau : Fin 3,∑ i : Fin 2,c tau i)=0) (hc : ∀ tau i,|c tau i|≤15/32) :
    binaryWeightApprox c ∈ binaryWeightCandidates := by
  have hz (tau i) : -(1152 : ℤ)≤binaryWeightIndex c tau i ∧ binaryWeightIndex c tau i≤1152 := by
    have hh := abs_le.mp (hc tau i)
    unfold binaryWeightIndex
    constructor
    · exact_mod_cast (show -(1152 : ℝ)≤(⌈1152*c tau i⌉ : ℝ) by linarith [Int.le_ceil (1152*c tau i)])
    · exact Int.ceil_le.mpr (by norm_num;linarith)
  exact ⟨⟨binaryWeightIndex c,hz,rfl⟩,binary_weight_candidate_balance _,(binary_weight_round_bounds c hb hc).1⟩

end JSP000334
