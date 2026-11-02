import SubspaceBridge.AllPointFixedSourceFamily5
open scoped BigOperators
namespace JSP000334
def sourceWeightConditions5 (c : Fin 3 → Fin 5 → ℝ) : Prop :=
  (∀ i, |c 0 i| ≤ 1) ∧ (∀ tau, tau ≠ 0 → ∀ i, -1 ≤ c tau i ∧ c tau i ≤ 0) ∧
    (∑ tau : Fin 3, ∑ i : Fin 5, c tau i) = 0

noncomputable def finiteWeightIndex5 (n : ℕ) (c : Fin 3 → Fin 5 → ℝ) (tau : Fin 3) (i : Fin 5) : ℤ :=
  if tau = 0 then ⌊(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌋
  else ⌈(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌉

noncomputable def finiteWeightRaw5 (n : ℕ) (z : Fin 3 → Fin 5 → ℤ) (tau : Fin 3) (i : Fin 5) : ℝ :=
  (z tau i : ℝ)/(n : ℝ)

noncomputable def finiteWeightCandidate5 (n : ℕ) (z : Fin 3 → Fin 5 → ℤ) (tau : Fin 3) (i : Fin 5) : ℝ :=
  if tau = 0 then finiteWeightRaw5 n z tau i - (∑ t : Fin 3, ∑ j : Fin 5, finiteWeightRaw5 n z t j)/5
  else finiteWeightRaw5 n z tau i

noncomputable def finiteWeightApprox5 (n : ℕ) (c : Fin 3 → Fin 5 → ℝ) : Fin 3 → Fin 5 → ℝ :=
  finiteWeightCandidate5 n (finiteWeightIndex5 n c)

theorem finiteWeight_floor_bounds5 (n : ℕ) (hn : 0 < n) (x : ℝ) :
    x-1/(n : ℝ) ≤ (⌊(n : ℝ)*x⌋ : ℝ)/(n : ℝ) ∧
      (⌊(n : ℝ)*x⌋ : ℝ)/(n : ℝ) ≤ x := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (1/(n : ℝ))*(n : ℝ) = 1 := one_div_mul_cancel hp.ne'
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [Int.lt_floor_add_one ((n : ℝ)*x)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Int.floor_le ((n : ℝ)*x)]

theorem finiteWeight_ceil_bounds5 (n : ℕ) (hn : 0 < n) (x : ℝ) :
    x ≤ (⌈(n : ℝ)*x⌉ : ℝ)/(n : ℝ) ∧
      (⌈(n : ℝ)*x⌉ : ℝ)/(n : ℝ) ≤ x+1/(n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (1/(n : ℝ))*(n : ℝ) = 1 := one_div_mul_cancel hp.ne'
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [Int.le_ceil ((n : ℝ)*x)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Int.ceil_lt_add_one ((n : ℝ)*x)]

theorem finiteWeightCandidate5_balance (n : ℕ) (z : Fin 3 → Fin 5 → ℤ) :
    (∑ tau : Fin 3, ∑ i : Fin 5, finiteWeightCandidate5 n z tau i) = 0 := by
  simp [finiteWeightCandidate5, Fin.sum_univ_succ]
  ring

theorem finiteWeight_raw_errors5 (n : ℕ) (hn : 0 < n) (c : Fin 3 → Fin 5 → ℝ) :
    (∀ i, (1-4/(n : ℝ))*c 0 i-1/(n : ℝ) ≤ finiteWeightRaw5 n (finiteWeightIndex5 n c) 0 i ∧
      finiteWeightRaw5 n (finiteWeightIndex5 n c) 0 i ≤ (1-4/(n : ℝ))*c 0 i) ∧
    (∀ tau, tau ≠ 0 → ∀ i,
      (1-4/(n : ℝ))*c tau i ≤ finiteWeightRaw5 n (finiteWeightIndex5 n c) tau i ∧
      finiteWeightRaw5 n (finiteWeightIndex5 n c) tau i ≤ (1-4/(n : ℝ))*c tau i+1/(n : ℝ)) := by
  constructor
  · intro i
    simpa only [finiteWeightRaw5, finiteWeightIndex5, if_pos rfl] using
      finiteWeight_floor_bounds5 n hn ((1-4/(n : ℝ))*c 0 i)
  · intro tau ht i
    simpa only [finiteWeightRaw5, finiteWeightIndex5, if_neg ht] using
      finiteWeight_ceil_bounds5 n hn ((1-4/(n : ℝ))*c tau i)

theorem finiteWeight_raw_sum5 (n : ℕ) (hn : 0 < n) (c : Fin 3 → Fin 5 → ℝ)
    (hb : (∑ tau : Fin 3, ∑ i : Fin 5, c tau i) = 0) :
    -5/(n : ℝ) ≤ (∑ tau : Fin 3, ∑ i : Fin 5, finiteWeightRaw5 n (finiteWeightIndex5 n c) tau i) ∧
    (∑ tau : Fin 3, ∑ i : Fin 5, finiteWeightRaw5 n (finiteWeightIndex5 n c) tau i) ≤ 10/(n : ℝ) := by
  obtain ⟨h0,hp⟩ := finiteWeight_raw_errors5 n hn c
  let R := finiteWeightRaw5 n (finiteWeightIndex5 n c)
  let a : ℝ := 1-4/(n : ℝ)
  have hlo : (∑ i : Fin 5,a*c 0 i)-5/(n : ℝ)≤∑ i : Fin 5,R 0 i := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 5))) => (h0 i).1)
    simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_assoc,mul_one, Nat.cast_ofNat, mul_one_div] using hh
  have hhi : (∑ i : Fin 5,R 0 i)≤∑ i : Fin 5,a*c 0 i :=
    Finset.sum_le_sum (fun i _ => (h0 i).2)
  have hfl (tau : Fin 3) (ht : tau≠0) : (∑ i : Fin 5,a*c tau i)≤∑ i : Fin 5,R tau i :=
    Finset.sum_le_sum (fun i _ => (hp tau ht i).1)
  have hfu (tau : Fin 3) (ht : tau≠0) : (∑ i : Fin 5,R tau i)≤(∑ i : Fin 5,a*c tau i)+5/(n : ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 5))) => (hp tau ht i).2)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_assoc,mul_one, Nat.cast_ofNat, mul_one_div] using hh
  have hz : (∑ i : Fin 5,a*c 0 i)+(∑ i : Fin 5,a*c 1 i)+(∑ i : Fin 5,a*c 2 i)=0 := by
    have hh : a*(∑ tau : Fin 3,∑ i : Fin 5,c tau i)=0 := by rw [hb,mul_zero]
    simpa only [Fin.sum_univ_three,Finset.mul_sum,mul_add] using hh
  change -5/(n : ℝ)≤(∑ tau : Fin 3,∑ i : Fin 5,R tau i) ∧ (∑ tau : Fin 3,∑ i : Fin 5,R tau i)≤10/(n : ℝ)
  simp only [Fin.sum_univ_three]
  constructor
  · calc
      -5/(n : ℝ)=(∑ i : Fin 5,a*c 0 i)-5/(n : ℝ)+(∑ i : Fin 5,a*c 1 i)+(∑ i : Fin 5,a*c 2 i)  := by
        calc
          _=(∑ i : Fin 5,a*c 0 i)+(∑ i : Fin 5,a*c 1 i)+(∑ i : Fin 5,a*c 2 i)-5/(n : ℝ) := by rw [hz]; ring
          _=_ := by ring
      _≤_ := add_le_add (add_le_add hlo (hfl 1 (by decide))) (hfl 2 (by decide))
  · calc
      _≤(∑ i : Fin 5,a*c 0 i)+((∑ i : Fin 5,a*c 1 i)+5/(n : ℝ))+((∑ i : Fin 5,a*c 2 i)+5/(n : ℝ)) :=
        add_le_add (add_le_add hhi (hfu 1 (by decide))) (hfu 2 (by decide))
      _=10/(n : ℝ) := by
        calc
          _=((∑ i : Fin 5,a*c 0 i)+(∑ i : Fin 5,a*c 1 i)+(∑ i : Fin 5,a*c 2 i))+10/(n : ℝ) := by ring
          _=_ := by rw [hz]; ring

theorem finiteWeightApprox5_bounds (n : ℕ) (hn : 16 ≤ n)
    (c : Fin 3 → Fin 5 → ℝ) (hc : sourceWeightConditions5 c) :
    sourceWeightConditions5 (finiteWeightApprox5 n c) ∧
      (∀ i, c 0 i-7/(n : ℝ) ≤ finiteWeightApprox5 n c 0 i) ∧
      (∀ tau, tau ≠ 0 → ∀ i, c tau i ≤ finiteWeightApprox5 n c tau i) := by
  have hnp : 0 < n := by omega
  have hp : (0 : ℝ) < n := by exact_mod_cast hnp
  have he : 0 < 1/(n : ℝ) := by positivity
  have he' : 1/(n : ℝ) ≤ 1/16 := (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 16)).mpr (by simpa only [one_mul] using (show (16 : ℝ) ≤ n by exact_mod_cast hn))
  have h5 : 4/(n : ℝ) ≤ 1/4 := by
    calc
      _ = 4*(1/(n : ℝ)) := by ring
      _ ≤ 4*(1/16) := mul_le_mul_of_nonneg_left he' (by norm_num)
      _ = _ := by norm_num
  obtain ⟨h0,hf,hb⟩ := hc
  obtain ⟨ha0,haf⟩ := finiteWeight_raw_errors5 n hnp c
  obtain ⟨hBl,hBu⟩ := finiteWeight_raw_sum5 n hnp c hb
  have hreal (i : Fin 5) : |finiteWeightApprox5 n c 0 i| ≤ 1 ∧
      c 0 i-7/(n : ℝ) ≤ finiteWeightApprox5 n c 0 i := by
    have hc0 := abs_le.mp (h0 i)
    have hscaled := mul_le_mul_of_nonneg_left hc0.1 (by linarith : 0 ≤ 1-4/(n : ℝ))
    have hscaled' := mul_le_mul_of_nonneg_left hc0.2 (by linarith : 0 ≤ 1-4/(n : ℝ))
    change |finiteWeightRaw5 n (finiteWeightIndex5 n c) 0 i -
      (∑ t : Fin 3, ∑ j : Fin 5, finiteWeightRaw5 n (finiteWeightIndex5 n c) t j)/5| ≤ 1 ∧ _
    change _ ∧ c 0 i-7/(n : ℝ) ≤ finiteWeightRaw5 n (finiteWeightIndex5 n c) 0 i -
      (∑ t : Fin 3, ∑ j : Fin 5, finiteWeightRaw5 n (finiteWeightIndex5 n c) t j)/5
    have hsmall := mul_le_mul_of_nonneg_left hc0.2 (by positivity : 0 ≤ 4/(n : ℝ))
    simp only [div_eq_mul_inv, one_mul] at *
    refine ⟨abs_le.mpr ⟨?_,?_⟩,?_⟩ <;> nlinarith [(ha0 i).1,(ha0 i).2]
  have hfinite (tau : Fin 3) (ht : tau ≠ 0) (i : Fin 5) :
      -1 ≤ finiteWeightApprox5 n c tau i ∧ finiteWeightApprox5 n c tau i ≤ 0 ∧
      c tau i ≤ finiteWeightApprox5 n c tau i := by
    have hci := hf tau ht i
    have hscaled := mul_le_mul_of_nonneg_left hci.1 (by linarith : 0 ≤ 1-4/(n : ℝ))
    have hscaled' : (1-4/(n : ℝ))*c tau i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hci.2
    have hceil : ⌈(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌉ ≤ (0 : ℤ) :=
      Int.ceil_le.mpr (by simpa using mul_nonpos_of_nonneg_of_nonpos hp.le hscaled')
    have hceilR : (⌈(n : ℝ)*((1-4/(n : ℝ))*c tau i)⌉ : ℝ) ≤ 0 := by exact_mod_cast hceil
    have hnonpos : finiteWeightApprox5 n c tau i ≤ 0 := by
      simp only [finiteWeightApprox5, finiteWeightCandidate5, finiteWeightRaw5, finiteWeightIndex5, if_neg ht]
      exact div_nonpos_of_nonpos_of_nonneg hceilR hp.le
    have heq : finiteWeightApprox5 n c tau i = finiteWeightRaw5 n (finiteWeightIndex5 n c) tau i := by
      simp only [finiteWeightApprox5, finiteWeightCandidate5, if_neg ht]
    rw [heq] at hnonpos ⊢
    have hsmall := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4/(n : ℝ)) hci.2
    simp only [div_eq_mul_inv, one_mul] at *
    refine ⟨?_,hnonpos,?_⟩ <;> nlinarith [(haf tau ht i).1]
  refine ⟨⟨fun i => (hreal i).1,fun tau ht i => ⟨(hfinite tau ht i).1,(hfinite tau ht i).2.1⟩,
    finiteWeightCandidate5_balance n _⟩,fun i => (hreal i).2,fun tau ht i => (hfinite tau ht i).2.2⟩

noncomputable def finiteWeightCandidates5 (n : ℕ) : Set (Fin 3 → Fin 5 → ℝ) :=
  (finiteWeightCandidate5 n '' {z : Fin 3 → Fin 5 → ℤ | ∀ tau i, -(n : ℤ) ≤ z tau i ∧ z tau i ≤ n}) ∩
    {d | sourceWeightConditions5 d}

theorem finiteWeightCandidates5_finite (n : ℕ) : (finiteWeightCandidates5 n).Finite := by
  have hbox : {z : Fin 3 → Fin 5 → ℤ | ∀ tau i, -(n : ℤ) ≤ z tau i ∧ z tau i ≤ n}.Finite :=
    Set.Finite.pi' (fun _ => Set.Finite.pi' (fun _ => Set.finite_Icc _ _))
  exact (hbox.image (finiteWeightCandidate5 n)).subset Set.inter_subset_left

theorem finiteWeightIndex5_bounded (n : ℕ) (hn : 16 ≤ n) (c : Fin 3 → Fin 5 → ℝ)
    (hc : sourceWeightConditions5 c) :
    ∀ tau i, -(n : ℤ) ≤ finiteWeightIndex5 n c tau i ∧ finiteWeightIndex5 n c tau i ≤ n := by
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
  unfold finiteWeightIndex5
  split_ifs with ht
  · constructor
    · exact Int.le_floor.mpr (by simpa using hscaled.1)
    · exact_mod_cast ((Int.floor_le _).trans hscaled.2)
  · constructor
    · exact_mod_cast (hscaled.1.trans (Int.le_ceil _))
    · exact Int.ceil_le.mpr (by simpa using hscaled.2)

theorem finiteWeightApprox5_mem (n : ℕ) (hn : 16 ≤ n) (c : Fin 3 → Fin 5 → ℝ)
    (hc : sourceWeightConditions5 c) : finiteWeightApprox5 n c ∈ finiteWeightCandidates5 n := by
  exact ⟨⟨finiteWeightIndex5 n c,finiteWeightIndex5_bounded n hn c hc,rfl⟩,
    (finiteWeightApprox5_bounds n hn c hc).1⟩

noncomputable def sourceLogWeights5 (Q : ℝ) (W : Fin 3 → Fin 5 → ℝ) (tau : Fin 3) (i : Fin 5) : ℝ :=
  Real.log (W tau i)/Real.log Q

theorem sourceLogWeights5_rpow (Q : ℝ) (hQ : 1 < Q) (W : Fin 3 → Fin 5 → ℝ)
    (hW : ∀ tau i, 0 < W tau i) (tau : Fin 3) (i : Fin 5) :
    Q^(sourceLogWeights5 Q W tau i) = W tau i := by
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hQ)]
  unfold sourceLogWeights5
  rw [mul_div_cancel₀ _ (Real.log_pos hQ).ne', Real.exp_log (hW tau i)]

theorem sourceLogWeights5_conditions (Q : ℝ) (hQ : 1 < Q) (W : Fin 3 → Fin 5 → ℝ)
    (hW : ∀ tau i, 0 < W tau i)
    (hcut : ∀ tau i, (W tau i)⁻¹ < Q)
    (hcut0 : ∀ i, W 0 i < Q)
    (hfinite : ∀ tau, tau ≠ 0 → ∀ i, W tau i ≤ 1)
    (hprod : (∏ tau : Fin 3, ∏ i : Fin 5, W tau i) = 1) :
    sourceWeightConditions5 (sourceLogWeights5 Q W) := by
  have hl := Real.log_pos hQ
  have hlo (tau : Fin 3) (i : Fin 5) : -1 ≤ sourceLogWeights5 Q W tau i := by
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
  · have hlogs : (∑ tau : Fin 3, ∑ i : Fin 5, Real.log (W tau i)) = 0 := by
      have heq : Real.log (∏ tau : Fin 3, ∏ i : Fin 5, W tau i) =
          (∑ tau : Fin 3, ∑ i : Fin 5, Real.log (W tau i)) := by
        rw [Real.log_prod Finset.univ (fun tau => ∏ i : Fin 5, W tau i) (fun tau _ => (Finset.prod_pos (fun i _ => hW tau i)).ne')]
        apply Finset.sum_congr rfl
        intro tau _
        exact Real.log_prod Finset.univ (W tau) (fun i _ => (hW tau i).ne')
      rw [hprod,Real.log_one] at heq
      exact heq.symm
    unfold sourceLogWeights5
    simp only [← Finset.sum_div]
    rw [hlogs,zero_div]

end JSP000334
