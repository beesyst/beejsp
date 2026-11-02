import SubspaceBridge.ParameterSelection3
open scoped BigOperators
namespace JSP000334

def sourceWeightConditions3 (c : Fin 3 → Fin 3 → ℝ) : Prop :=
  (∀ i, |c 0 i| ≤ 1) ∧ (∀ tau, tau ≠ 0 → ∀ i, -1 ≤ c tau i ∧ c tau i ≤ 0) ∧
    (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0

noncomputable def finiteWeightIndex3 (n : ℕ) (c : Fin 3 → Fin 3 → ℝ) (tau i : Fin 3) : ℤ :=
  if tau = 0 then ⌊(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌋
  else ⌈(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌉

noncomputable def finiteWeightRaw3 (n : ℕ) (z : Fin 3 → Fin 3 → ℤ) (tau i : Fin 3) : ℝ :=
  (z tau i : ℝ)/(n : ℝ)

noncomputable def finiteWeightCandidate3 (n : ℕ) (z : Fin 3 → Fin 3 → ℤ) (tau i : Fin 3) : ℝ :=
  if tau = 0 then finiteWeightRaw3 n z tau i - (∑ t : Fin 3, ∑ j : Fin 3, finiteWeightRaw3 n z t j)/3
  else finiteWeightRaw3 n z tau i

noncomputable def finiteWeightApprox3 (n : ℕ) (c : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  finiteWeightCandidate3 n (finiteWeightIndex3 n c)

theorem finiteWeight_floor_bounds3 (n : ℕ) (hn : 0 < n) (x : ℝ) :
    x-1/(n : ℝ) ≤ (⌊(n : ℝ)*x⌋ : ℝ)/(n : ℝ) ∧
      (⌊(n : ℝ)*x⌋ : ℝ)/(n : ℝ) ≤ x := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (1/(n : ℝ))*(n : ℝ) = 1 := one_div_mul_cancel hp.ne'
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [Int.lt_floor_add_one ((n : ℝ)*x)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Int.floor_le ((n : ℝ)*x)]

theorem finiteWeight_ceil_bounds3 (n : ℕ) (hn : 0 < n) (x : ℝ) :
    x ≤ (⌈(n : ℝ)*x⌉ : ℝ)/(n : ℝ) ∧
      (⌈(n : ℝ)*x⌉ : ℝ)/(n : ℝ) ≤ x+1/(n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (1/(n : ℝ))*(n : ℝ) = 1 := one_div_mul_cancel hp.ne'
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [Int.le_ceil ((n : ℝ)*x)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Int.ceil_lt_add_one ((n : ℝ)*x)]

theorem finiteWeightCandidate3_balance (n : ℕ) (z : Fin 3 → Fin 3 → ℤ) :
    (∑ tau : Fin 3, ∑ i : Fin 3, finiteWeightCandidate3 n z tau i) = 0 := by
  simp only [finiteWeightCandidate3, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  ring

theorem finiteWeight_raw_errors3 (n : ℕ) (hn : 0 < n) (c : Fin 3 → Fin 3 → ℝ) :
    (∀ i, (1-4/(n : ℝ))*c 0 i-1/(n : ℝ) ≤ finiteWeightRaw3 n (finiteWeightIndex3 n c) 0 i ∧
      finiteWeightRaw3 n (finiteWeightIndex3 n c) 0 i ≤ (1-4/(n : ℝ))*c 0 i) ∧
    (∀ tau, tau ≠ 0 → ∀ i,
      (1-4/(n : ℝ))*c tau i ≤ finiteWeightRaw3 n (finiteWeightIndex3 n c) tau i ∧
      finiteWeightRaw3 n (finiteWeightIndex3 n c) tau i ≤ (1-4/(n : ℝ))*c tau i+1/(n : ℝ)) := by
  constructor
  · intro i
    simpa only [finiteWeightRaw3, finiteWeightIndex3, if_pos rfl] using
      finiteWeight_floor_bounds3 n hn ((1-4/(n : ℝ))*c 0 i)
  · intro tau ht i
    simpa only [finiteWeightRaw3, finiteWeightIndex3, if_neg ht] using
      finiteWeight_ceil_bounds3 n hn ((1-4/(n : ℝ))*c tau i)

theorem finiteWeight_raw_sum3 (n : ℕ) (hn : 0 < n) (c : Fin 3 → Fin 3 → ℝ)
    (hb : (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0) :
    -3/(n : ℝ) ≤ (∑ tau : Fin 3, ∑ i : Fin 3, finiteWeightRaw3 n (finiteWeightIndex3 n c) tau i) ∧
    (∑ tau : Fin 3, ∑ i : Fin 3, finiteWeightRaw3 n (finiteWeightIndex3 n c) tau i) ≤ 6/(n : ℝ) := by
  obtain ⟨h0,hp⟩ := finiteWeight_raw_errors3 n hn c
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have hscaled : (1-4/(n : ℝ))*(∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0 := by rw [hb, mul_zero]
  simp only [Fin.sum_univ_three] at hb hscaled ⊢
  simp only [div_eq_mul_inv, one_mul] at *
  constructor <;> nlinarith [(h0 0).1,(h0 0).2,(h0 1).1,(h0 1).2,(h0 2).1,(h0 2).2,
    (h1 0).1,(h1 0).2,(h1 1).1,(h1 1).2,(h1 2).1,(h1 2).2,
    (h2 0).1,(h2 0).2,(h2 1).1,(h2 1).2,(h2 2).1,(h2 2).2]

theorem finiteWeightApprox3_bounds (n : ℕ) (hn : 16 ≤ n)
    (c : Fin 3 → Fin 3 → ℝ) (hc : sourceWeightConditions3 c) :
    sourceWeightConditions3 (finiteWeightApprox3 n c) ∧
      (∀ i, c 0 i-7/(n : ℝ) ≤ finiteWeightApprox3 n c 0 i) ∧
      (∀ tau, tau ≠ 0 → ∀ i, c tau i ≤ finiteWeightApprox3 n c tau i) := by
  have hnp : 0 < n := by omega
  have hp : (0 : ℝ) < n := by exact_mod_cast hnp
  have he : 0 < 1/(n : ℝ) := by positivity
  have he' : 1/(n : ℝ) ≤ 1/16 := (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 16)).mpr (by simpa only [one_mul] using (show (16 : ℝ) ≤ n by exact_mod_cast hn))
  have h4 : 4/(n : ℝ) ≤ 1/4 := by
    calc
      _ = 4*(1/(n : ℝ)) := by ring
      _ ≤ 4*(1/16) := mul_le_mul_of_nonneg_left he' (by norm_num)
      _ = _ := by norm_num
  obtain ⟨h0,hf,hb⟩ := hc
  obtain ⟨ha0,haf⟩ := finiteWeight_raw_errors3 n hnp c
  obtain ⟨hBl,hBu⟩ := finiteWeight_raw_sum3 n hnp c hb
  have hreal (i : Fin 3) : |finiteWeightApprox3 n c 0 i| ≤ 1 ∧
      c 0 i-7/(n : ℝ) ≤ finiteWeightApprox3 n c 0 i := by
    have hc0 := abs_le.mp (h0 i)
    have hscaled := mul_le_mul_of_nonneg_left hc0.1 (by linarith : 0 ≤ 1-4/(n : ℝ))
    have hscaled' := mul_le_mul_of_nonneg_left hc0.2 (by linarith : 0 ≤ 1-4/(n : ℝ))
    change |finiteWeightRaw3 n (finiteWeightIndex3 n c) 0 i -
      (∑ t : Fin 3, ∑ j : Fin 3, finiteWeightRaw3 n (finiteWeightIndex3 n c) t j)/3| ≤ 1 ∧ _
    change _ ∧ c 0 i-7/(n : ℝ) ≤ finiteWeightRaw3 n (finiteWeightIndex3 n c) 0 i -
      (∑ t : Fin 3, ∑ j : Fin 3, finiteWeightRaw3 n (finiteWeightIndex3 n c) t j)/3
    have hsmall := mul_le_mul_of_nonneg_left hc0.2 (by positivity : 0 ≤ 4/(n : ℝ))
    simp only [div_eq_mul_inv, one_mul] at *
    refine ⟨abs_le.mpr ⟨?_,?_⟩,?_⟩ <;> nlinarith [(ha0 i).1,(ha0 i).2]
  have hfinite (tau : Fin 3) (ht : tau ≠ 0) (i : Fin 3) :
      -1 ≤ finiteWeightApprox3 n c tau i ∧ finiteWeightApprox3 n c tau i ≤ 0 ∧
      c tau i ≤ finiteWeightApprox3 n c tau i := by
    have hci := hf tau ht i
    have hscaled := mul_le_mul_of_nonneg_left hci.1 (by linarith : 0 ≤ 1-4/(n : ℝ))
    have hscaled' : (1-4/(n : ℝ))*c tau i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hci.2
    have hceil : ⌈(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌉ ≤ (0 : ℤ) :=
      Int.ceil_le.mpr (by simpa using mul_nonpos_of_nonneg_of_nonpos hp.le hscaled')
    have hceilR : (⌈(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌉ : ℝ) ≤ 0 := by exact_mod_cast hceil
    have hnonpos : finiteWeightApprox3 n c tau i ≤ 0 := by
      simp only [finiteWeightApprox3, finiteWeightCandidate3, finiteWeightRaw3, finiteWeightIndex3, if_neg ht]
      exact div_nonpos_of_nonpos_of_nonneg hceilR hp.le
    have heq : finiteWeightApprox3 n c tau i = finiteWeightRaw3 n (finiteWeightIndex3 n c) tau i := by
      simp only [finiteWeightApprox3, finiteWeightCandidate3, if_neg ht]
    rw [heq] at hnonpos ⊢
    have hsmall := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4/(n : ℝ)) hci.2
    simp only [div_eq_mul_inv, one_mul] at *
    refine ⟨?_,hnonpos,?_⟩ <;> nlinarith [(haf tau ht i).1]
  refine ⟨⟨fun i => (hreal i).1,fun tau ht i => ⟨(hfinite tau ht i).1,(hfinite tau ht i).2.1⟩,
    finiteWeightCandidate3_balance n _⟩,fun i => (hreal i).2,fun tau ht i => (hfinite tau ht i).2.2⟩

noncomputable def finiteWeightCandidates3 (n : ℕ) : Set (Fin 3 → Fin 3 → ℝ) :=
  (finiteWeightCandidate3 n '' {z : Fin 3 → Fin 3 → ℤ | ∀ tau i, -(n : ℤ) ≤ z tau i ∧ z tau i ≤ n}) ∩
    {d | sourceWeightConditions3 d}

theorem finiteWeightCandidates3_finite (n : ℕ) : (finiteWeightCandidates3 n).Finite := by
  have hbox : {z : Fin 3 → Fin 3 → ℤ | ∀ tau i, -(n : ℤ) ≤ z tau i ∧ z tau i ≤ n}.Finite :=
    Set.Finite.pi' (fun _ => Set.Finite.pi' (fun _ => Set.finite_Icc _ _))
  exact (hbox.image (finiteWeightCandidate3 n)).subset Set.inter_subset_left

theorem finiteWeightIndex3_bounded (n : ℕ) (hn : 16 ≤ n) (c : Fin 3 → Fin 3 → ℝ)
    (hc : sourceWeightConditions3 c) :
    ∀ tau i, -(n : ℤ) ≤ finiteWeightIndex3 n c tau i ∧ finiteWeightIndex3 n c tau i ≤ n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor : 0 ≤ 1-4/(n : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hp).mpr (by linarith)
  have hfactor' : 1-4/(n : ℝ) ≤ 1 := by
    have : 0 < 4/(n : ℝ) := by positivity
    linarith
  intro tau i
  have hci : -1 ≤ c tau i ∧ c tau i ≤ 1 := by
    by_cases ht : tau = 0
    · subst tau; exact abs_le.mp (hc.1 i)
    · exact ⟨(hc.2.1 tau ht i).1, (hc.2.1 tau ht i).2.trans (by norm_num)⟩
  have hscaled : -(n : ℝ) ≤ (n : ℝ)*((1-4/(n : ℝ))*c tau i) ∧
      (n : ℝ)*((1-4/(n : ℝ))*c tau i) ≤ n := by
    have h1 := mul_le_mul_of_nonneg_left hci.1 hfactor
    have h2 := mul_le_mul_of_nonneg_left hci.2 hfactor
    constructor
    · have h : -1 ≤ (1-4/(n : ℝ))*c tau i := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h hp.le]
    · have h : (1-4/(n : ℝ))*c tau i ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h hp.le]
  unfold finiteWeightIndex3
  split_ifs with ht
  · constructor
    · exact Int.le_floor.mpr (by simpa using hscaled.1)
    · exact_mod_cast ((Int.floor_le _).trans hscaled.2)
  · constructor
    · exact_mod_cast (hscaled.1.trans (Int.le_ceil _))
    · exact Int.ceil_le.mpr (by simpa using hscaled.2)

theorem finiteWeightApprox3_mem (n : ℕ) (hn : 16 ≤ n) (c : Fin 3 → Fin 3 → ℝ)
    (hc : sourceWeightConditions3 c) : finiteWeightApprox3 n c ∈ finiteWeightCandidates3 n := by
  exact ⟨⟨finiteWeightIndex3 n c,finiteWeightIndex3_bounded n hn c hc,rfl⟩,
    (finiteWeightApprox3_bounds n hn c hc).1⟩

theorem finiteWeight_unbounded_fiber3 (F : Set (Fin 3 → Fin 3 → ℝ)) (hF : F.Finite)
    (U : Set ℝ) (hU : ¬ BddAbove U) (a : ℝ → Fin 3 → Fin 3 → ℝ)
    (ha : ∀ Q ∈ U, a Q ∈ F) :
    ∃ d ∈ F, ¬ BddAbove {Q | Q ∈ U ∧ a Q = d} := by
  classical
  by_contra hnone
  have hb (d : F) : BddAbove {Q | Q ∈ U ∧ a Q = d.val} := by
    by_contra h
    exact hnone ⟨d.val,d.property,h⟩
  choose b hb using hb
  letI := hF.fintype
  obtain ⟨B,hB⟩ := (Set.finite_range b).bddAbove
  apply hU
  refine ⟨B,?_⟩
  intro Q hQ
  let d : F := ⟨a Q,ha Q hQ⟩
  exact (hb d (show Q ∈ {Q | Q ∈ U ∧ a Q = d.val} from ⟨hQ,rfl⟩)).trans (hB (Set.mem_range_self d))

theorem finiteWeight_select3 (n : ℕ) (hn : 16 ≤ n) (U : Set ℝ) (hU : ¬ BddAbove U)
    (c : ℝ → Fin 3 → Fin 3 → ℝ) (hc : ∀ Q ∈ U, sourceWeightConditions3 (c Q)) :
    ∃ d ∈ finiteWeightCandidates3 n, ∃ U' : Set ℝ, U' ⊆ U ∧ ¬ BddAbove U' ∧
      ∀ Q ∈ U', finiteWeightApprox3 n (c Q) = d := by
  obtain ⟨d,hd,hu⟩ := finiteWeight_unbounded_fiber3 _ (finiteWeightCandidates3_finite n) U hU
    (fun Q => finiteWeightApprox3 n (c Q)) (fun Q hQ => finiteWeightApprox3_mem n hn (c Q) (hc Q hQ))
  exact ⟨d,hd,{Q | Q ∈ U ∧ finiteWeightApprox3 n (c Q) = d},fun _ h => h.1,hu,fun _ h => h.2⟩

theorem finiteWeight_resolution3 (delta : ℝ) (hd : 0 < delta) :
    ∃ n : ℕ, 16 ≤ n ∧ 7/(n : ℝ) ≤ delta/4 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 16 (200/delta))
  have hnR : (16 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnp : (0 : ℝ) < n := by linarith
  have hprod : 200 < (n : ℝ)*delta := (div_lt_iff₀ hd).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  refine ⟨n,by exact_mod_cast hnR.le,?_⟩
  apply (div_le_iff₀ hnp).mpr
  nlinarith

theorem finiteWeight_tuple3 (n : ℕ) (hn : 16 ≤ n) (delta : ℝ) (hd : 0 < delta)
    (he : 7/(n : ℝ) ≤ delta/4) (c : Fin 3 → Fin 3 → ℝ)
    (hc : sourceWeightConditions3 c) (s : Fin 3 → Fin 3)
    (hs : -delta/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2)) :
    -(3*delta)/4 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2) ∧
    -(3*delta)/4 ≤ finiteWeightApprox3 n c 0 (s 0)+finiteWeightApprox3 n c 1 (s 1)+
      finiteWeightApprox3 n c 2 (s 2) := by
  obtain ⟨_,h0,hf⟩ := finiteWeightApprox3_bounds n hn c hc
  constructor <;> linarith [h0 (s 0),hf 1 (by decide) (s 1),hf 2 (by decide) (s 2)]

theorem finiteWeight_delta3 (delta : ℝ) (hd : 0 < delta) :
    0 < min (delta/2) (1/2) ∧ min (delta/2) (1/2) < 1 ∧
    min (delta/2) (1/2) ≤ delta/2 ∧
    432*(min (delta/2) (1/2)/1000) < min (delta/2) (1/2) := by
  have hp : 0 < min (delta/2) (1/2) := lt_min (by linarith) (by norm_num)
  exact ⟨hp,lt_of_le_of_lt (min_le_right _ _) (by norm_num),min_le_left _ _,by linarith⟩


noncomputable def sourceLogWeights3 (Q : ℝ) (W : Fin 3 → Fin 3 → ℝ) (tau i : Fin 3) : ℝ :=
  Real.log (W tau i)/Real.log Q

theorem sourceLogWeights3_rpow (Q : ℝ) (hQ : 1 < Q) (W : Fin 3 → Fin 3 → ℝ)
    (hW : ∀ tau i, 0 < W tau i) (tau i : Fin 3) :
    Q^(sourceLogWeights3 Q W tau i) = W tau i := by
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hQ)]
  unfold sourceLogWeights3
  rw [mul_div_cancel₀ _ (Real.log_pos hQ).ne', Real.exp_log (hW tau i)]

theorem sourceLogWeights3_conditions (Q : ℝ) (hQ : 1 < Q) (W : Fin 3 → Fin 3 → ℝ)
    (hW : ∀ tau i, 0 < W tau i)
    (hcut : ∀ tau i, (W tau i)⁻¹ < Q)
    (hcut0 : ∀ i, W 0 i < Q)
    (hfinite : ∀ tau, tau ≠ 0 → ∀ i, W tau i ≤ 1)
    (hprod : (∏ tau : Fin 3, ∏ i : Fin 3, W tau i) = 1) :
    sourceWeightConditions3 (sourceLogWeights3 Q W) := by
  have hl := Real.log_pos hQ
  have hlo (tau i : Fin 3) : -1 ≤ sourceLogWeights3 Q W tau i := by
    have hh := Real.log_lt_log (inv_pos.mpr (hW tau i)) (hcut tau i)
    rw [Real.log_inv] at hh
    apply (le_div_iff₀ hl).mpr
    linarith
  refine ⟨?_,?_,?_⟩
  · intro i
    refine abs_le.mpr ⟨hlo 0 i,?_⟩
    apply (div_le_iff₀ hl).mpr
    have hh := Real.log_lt_log (hW 0 i) (hcut0 i)
    linarith
  · intro tau ht i
    refine ⟨hlo tau i,?_⟩
    apply div_nonpos_of_nonpos_of_nonneg _ hl.le
    exact Real.log_nonpos (hW tau i).le (hfinite tau ht i)
  · have hlogs : (∑ tau : Fin 3, ∑ i : Fin 3, Real.log (W tau i)) = 0 := by
      have heq : Real.log (∏ tau : Fin 3, ∏ i : Fin 3, W tau i) =
          (∑ tau : Fin 3, ∑ i : Fin 3, Real.log (W tau i)) := by
        rw [Real.log_prod Finset.univ (fun tau => ∏ i : Fin 3, W tau i) (fun tau _ => (Finset.prod_pos (fun i _ => hW tau i)).ne')]
        apply Finset.sum_congr rfl
        intro tau _
        exact Real.log_prod Finset.univ (W tau) (fun i _ => (hW tau i).ne')
      rw [hprod,Real.log_one] at heq
      exact heq.symm
    unfold sourceLogWeights3
    simp only [← Finset.sum_div]
    rw [hlogs,zero_div]

theorem sourceWeight48_log3 (Q delta : ℝ) (hQ : 1 < Q)
    (W : Fin 3 → Fin 3 → ℝ) (hW : ∀ tau i, 0 < W tau i)
    (s : Fin 3 → Fin 3)
    (h48 : 1 ≤ W 0 (s 0)*W 1 (s 1)*W 2 (s 2)*Q^(delta/2)) :
    -delta/2 ≤ sourceLogWeights3 Q W 0 (s 0)+sourceLogWeights3 Q W 1 (s 1)+
      sourceLogWeights3 Q W 2 (s 2) := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1) h48
  rw [Real.log_one,Real.log_mul (mul_pos (mul_pos (hW 0 _) (hW 1 _)) (hW 2 _)).ne'
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).ne',
    Real.log_mul (mul_pos (hW 0 _) (hW 1 _)).ne' (hW 2 _).ne',
    Real.log_mul (hW 0 _).ne' (hW 1 _).ne',
    Real.log_rpow (lt_trans zero_lt_one hQ)] at hh
  unfold sourceLogWeights3
  rw [← add_div,← add_div]
  apply (le_div_iff₀ (Real.log_pos hQ)).mpr
  linarith

theorem finiteWeight_real_local_value3 (k : Fin 3) (w : IntegerTriple) (i : Fin 3) :
    rothLocalAbs 0 (rothNormalLocalValue (retainedIntegerMatrix3 k) w i) =
      |retainedRealCoordinates3 k (integerTripleReal3 w) i| := by
  change |((rothNormalLocalValue (retainedIntegerMatrix3 k) w i : ℚ) : ℝ)| =
    |∑ l : Fin 3, (retainedRealMatrix3 k) i l * (w l : ℝ)|
  simp [rothNormalLocalValue, retainedRealMatrix3]

theorem finiteWeight_rational_local_value3 (k : Fin 3) (w : IntegerTriple) (i : Fin 3) :
    rothNormalLocalValue (retainedIntegerMatrix3 k) w i =
      threeCoordinateSumForms k i (fun l => (w l : ℚ)) := by
  rw [← retainedIntegerMatrix3_apply]
  simp [rothNormalLocalValue,Matrix.mulVec,dotProduct]

theorem finiteWeight_same_frame3 (n : ℕ) (hn : 16 ≤ n)
    (deltaSource deltaAux Q : ℝ) (hQ : 1 < Q) (he : 7/(n : ℝ) ≤ deltaSource-deltaAux)
    (c : Fin 3 → Fin 3 → ℝ) (hc : sourceWeightConditions3 c) (k₀ k₂ k₃ : Fin 3)
    (B : Basis (Fin 3) ℝ RealTriple)
    (u : Fin 3 → qSourceLattice3 k₂ k₃ Q (c 1) (c 2))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q (c 0) hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
        successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) j)
    (hsmall : successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) 1 < Q^(-deltaSource)) :
    (∀ j : Fin 2, ∀ i, rothLocalAbs 0
      (rothNormalLocalValue (retainedIntegerMatrix3 k₀) (u j.castSucc : IntegerTriple) i) ≤
        Q^(finiteWeightApprox3 n c 0 i-deltaAux)) ∧
    (∀ j : Fin 2, ∀ i, rothLocalAbs 1
      (rothNormalLocalValue (retainedIntegerMatrix3 k₂) (u j.castSucc : IntegerTriple) i) ≤
        Q^(finiteWeightApprox3 n c 1 i)) ∧
    (∀ j : Fin 2, ∀ i, rothLocalAbs 2
      (rothNormalLocalValue (retainedIntegerMatrix3 k₃) (u j.castSucc : IntegerTriple) i) ≤
        Q^(finiteWeightApprox3 n c 2 i)) := by
  obtain ⟨_,h0,hf⟩ := finiteWeightApprox3_bounds n hn c hc
  have hp := lt_trans zero_lt_one hQ
  obtain ⟨_,_,_,_,horder,_⟩ := exists_successive_minima3 B (qSourceCoordinates3 k₀ Q (c 0) hQ)
  have hrad (j : Fin 2) : successiveRadius3 B (qSourceCoordinates3 k₀ Q (c 0) hQ) j.castSucc ≤
      Q^(-deltaSource) := by
    fin_cases j
    · exact horder.1.trans hsmall.le
    · exact hsmall.le
  have hpoint (j : Fin 2) := (qSourceLattice3_spec k₂ k₃ Q (c 1) (c 2) hQ
    (fun i => (hc.2.1 1 (by decide) i).2) (fun i => (hc.2.1 2 (by decide) i).2)).1
      (u j.castSucc) |>.mp (u j.castSucc).property
  refine ⟨?_,?_,?_⟩
  · intro j i
    rw [finiteWeight_real_local_value3]
    have hb := qSource_arch_bound k₀ Q (c 0) hQ (integerTripleReal3 (u j.castSucc : IntegerTriple)) i
    rw [hatt] at hb
    calc
      _ ≤ Q^(-deltaSource)*Q^(c 0 i) := hb.trans
        (mul_le_mul_of_nonneg_right (hrad j) (Real.rpow_nonneg hp.le _))
      _ = Q^(c 0 i-deltaSource) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith [h0 i])
  · intro j i
    simp only [rothLocalAbs,Fin.reduceEq,ite_false,ite_true,finiteWeight_rational_local_value3]
    exact ((hpoint j).1 i).trans (Real.rpow_le_rpow_of_exponent_le hQ.le (hf 1 (by decide) i))
  · intro j i
    simp only [rothLocalAbs,Fin.reduceEq,ite_false,ite_true,finiteWeight_rational_local_value3]
    exact ((hpoint j).2 i).trans (Real.rpow_le_rpow_of_exponent_le hQ.le (hf 2 (by decide) i))

theorem finiteWeightReduction3 (deltaSource : ℝ) (hd : 0 < deltaSource) :
    ∃ (n : ℕ) (deltaAux eta : ℝ), 16 ≤ n ∧ 7/(n : ℝ) ≤ deltaSource/4 ∧
      deltaAux = min (deltaSource/2) (1/2) ∧ eta = deltaAux/1000 ∧
      0 < deltaAux ∧ deltaAux < 1 ∧ 0 < eta ∧ 432*eta < deltaAux ∧
      (finiteWeightCandidates3 n).Finite ∧
      ∀ (U : Set ℝ), ¬ BddAbove U → ∀ c : ℝ → Fin 3 → Fin 3 → ℝ,
        (∀ Q ∈ U, sourceWeightConditions3 (c Q)) →
        ∃ d ∈ finiteWeightCandidates3 n, ∃ U' : Set ℝ,
          U' ⊆ U ∧ ¬ BddAbove U' ∧ sourceWeightConditions3 d ∧
          ∀ Q ∈ U', finiteWeightApprox3 n (c Q) = d ∧
            (∀ i, c Q 0 i-deltaSource ≤ d 0 i-deltaAux) ∧
            (∀ tau, tau ≠ 0 → ∀ i, c Q tau i ≤ d tau i) ∧
            (∀ s : Fin 3 → Fin 3, -deltaSource/2 ≤ c Q 0 (s 0)+c Q 1 (s 1)+c Q 2 (s 2) →
              -(3*deltaSource)/4 ≤ c Q 0 (s 0)+c Q 1 (s 1)+c Q 2 (s 2) ∧
              -(3*deltaSource)/4 ≤ d 0 (s 0)+d 1 (s 1)+d 2 (s 2)) := by
  obtain ⟨n,hn,he⟩ := finiteWeight_resolution3 deltaSource hd
  obtain ⟨ha,ha',ha2,hsmall⟩ := finiteWeight_delta3 deltaSource hd
  refine ⟨n,min (deltaSource/2) (1/2),min (deltaSource/2) (1/2)/1000,hn,he,rfl,rfl,
    ha,ha',by positivity,hsmall,finiteWeightCandidates3_finite n,?_⟩
  intro U hU c hc
  obtain ⟨d,hdmem,U',hsub,hu,heq⟩ := finiteWeight_select3 n hn U hU c hc
  refine ⟨d,hdmem,U',hsub,hu,hdmem.2,?_⟩
  intro Q hQ
  have hconditions := hc Q (hsub hQ)
  obtain ⟨_,h0,hf⟩ := finiteWeightApprox3_bounds n hn (c Q) hconditions
  have hident := heq Q hQ
  refine ⟨hident,?_,?_,?_⟩
  · intro i
    have hh := h0 i
    rw [hident] at hh
    linarith
  · simpa only [hident] using hf
  · intro tuple htuple
    have hh := finiteWeight_tuple3 n hn deltaSource hd he (c Q) hconditions tuple htuple
    simpa only [hident] using hh

end JSP000334
