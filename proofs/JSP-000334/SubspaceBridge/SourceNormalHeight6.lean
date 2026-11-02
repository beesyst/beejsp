import SubspaceBridge.SourceMultiblock6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalHeight
open SourceNormalIndex Auxiliary6 SourceMultiblock

def normalHeight6 (M : Fin 6 → ℤ) : ℕ := Finset.univ.sup (fun i => (M i).natAbs)

theorem normalHeight6_coord (M : Fin 6 → ℤ) (i : Fin 6) :
    |(M i : ℝ)| ≤ (normalHeight6 M : ℝ) := by
  have hi := Finset.le_sup (f := fun i => (M i).natAbs) (Finset.mem_univ i)
  have he : ((M i).natAbs : ℝ) = |(M i : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [← he]
  exact_mod_cast hi

theorem normalHeight6_pos (M : Fin 6 → ℤ) (hM : M ≠ 0) : 0 < normalHeight6 M := by
  by_contra hn
  have hz : normalHeight6 M = 0 := by omega
  apply hM
  funext i
  have hi : (M i).natAbs ≤ normalHeight6 M := Finset.le_sup (f := fun j => (M j).natAbs) (Finset.mem_univ i)
  rw [hz] at hi
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)

theorem normalHeight6_neg (M : Fin 6 → ℤ) : normalHeight6 (-M) = normalHeight6 M := by
  simp [normalHeight6]

theorem normalHeight6_le_iff (M : Fin 6 → ℤ) (H : ℕ) :
    normalHeight6 M ≤ H ↔ ∀ i, (M i).natAbs ≤ H := by
  simp [normalHeight6,Finset.sup_le_iff]

theorem normalHeight6_normalization_bound (z M : Fin 6 → ℤ) (g : ℤ)
    (hg : g ≠ 0) (hz : ∀ i, z i = g*M i) : normalHeight6 M ≤ normalHeight6 z := by
  apply (normalHeight6_le_iff _ _).mpr
  intro i
  have hg1 : 1 ≤ g.natAbs := Int.natAbs_pos.mpr hg
  have hi := (normalHeight6_le_iff z _).mp le_rfl i
  rw [hz i,Int.natAbs_mul] at hi
  exact (show (M i).natAbs ≤ g.natAbs*(M i).natAbs by
    simpa only [one_mul] using Nat.mul_le_mul_right (M i).natAbs hg1).trans hi

theorem actual_normal_last_dual6 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M : Fin 6 → ℤ)
    (hM : M ≠ 0) (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i) = 0) :
    ∃ q : ℚ, q ≠ 0 ∧ normalForm6 M =
      q • rationalFrameDual42 (fun j i => (v j i : ℚ)) hv 5 := by
  let u := fun j i => (v j i : ℚ)
  have hf := functional_lastDual42 u hv (normalForm6 M) (by
    intro j
    rw [normalForm6_apply]
    change (∑ i, (M i : ℚ)*(v j.castSucc i : ℚ)) = 0
    exact_mod_cast hann j)
  refine ⟨normalForm6 M (u 5),?_,hf⟩
  intro hzero
  have hz : normalForm6 M = 0 := by simpa [hzero] using hf
  apply hM
  funext i
  have he := congrArg (fun f : Module.Dual ℚ (Fin 6 → ℚ) => f (Pi.single i 1)) hz
  simpa [normalForm6,Pi.single_apply] using he

theorem standard_frame_normal_height6 (M a : Fin 6 → ℤ)
    (ha : (∑ i, a i*M i) = 1)
    (hann : ∀ j : Fin 5, (∑ i, M i*(Pi.single j.castSucc (1 : ℤ) : Fin 6 → ℤ) i) = 0) :
    normalHeight6 M = 1 := by
  have hz (j : Fin 5) : M j.castSucc = 0 := by
    simpa [Pi.single_apply,mul_ite,Finset.sum_ite_eq,Finset.sum_ite_eq',eq_comm] using hann j
  have hp : a 5*M 5 = 1 := by
    simpa [Fin.sum_univ_castSucc,hz] using ha
  have hab : (M 5).natAbs = 1 := by
    have he := congrArg Int.natAbs hp
    rw [Int.natAbs_mul,Int.natAbs_one] at he
    exact Nat.eq_one_of_dvd_one ⟨(a 5).natAbs,by simpa [mul_comm] using he.symm⟩
  apply le_antisymm
  · apply (normalHeight6_le_iff _ _).mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hab.le
    · simp [hz]
  · have hi : (M 5).natAbs ≤ normalHeight6 M := Finset.le_sup (f := fun j => (M j).natAbs) (Finset.mem_univ 5)
    simpa [hab] using hi

theorem standard_frame_lower_gate6 (M a : Fin 6 → ℤ)
    (ha : (∑ i, a i*M i) = 1)
    (hann : ∀ j : Fin 5, (∑ i, M i*(Pi.single j.castSucc (1 : ℤ) : Fin 6 → ℤ) i) = 0)
    (Q C : ℝ) (hQ : 1 < Q) (hC : 0 < C) :
    ¬ Q^C ≤ (normalHeight6 M : ℝ) := by
  rw [standard_frame_normal_height6 M a ha hann]
  simpa using (not_le_of_gt (Real.one_lt_rpow hQ hC))

theorem standard_frame_actual_normal_gate6 :
    ∃ M a : Fin 6 → ℤ, M ≠ 0 ∧ (∑ i, a i*M i) = 1 ∧
      Ideal.span (Set.range M) = ⊤ ∧
      (∀ j : Fin 5, (∑ i, M i*(Pi.single j.castSucc (1 : ℤ) : Fin 6 → ℤ) i) = 0) ∧
      LinearMap.ker (normalForm6 M) =
        firstFiveSpan42 (fun j i => ((Pi.single j (1 : ℤ) : Fin 6 → ℤ) i : ℚ)) ∧
      normalHeight6 M = 1 ∧
      (∀ Q C : ℝ, 1 < Q → 0 < C → ¬ Q^C ≤ (normalHeight6 M : ℝ)) := by
  let v : Fin 6 → Fin 6 → ℤ := fun j => Pi.single j 1
  have hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)) := by
    have he : (fun j i => (v j i : ℚ)) = fun j => (Pi.basisFun ℚ (Fin 6)) j := by
      funext j i
      simp [v,Pi.single_apply]
    rw [he]
    exact (Pi.basisFun ℚ (Fin 6)).linearIndependent
  obtain ⟨M,a,hM,ha,hprim,hann,hker⟩ := primitive_normal6 v hv
  exact ⟨M,a,hM,ha,hprim,hann,hker,standard_frame_normal_height6 M a ha hann,
    fun Q C hQ hC => standard_frame_lower_gate6 M a ha hann Q C hQ hC⟩

theorem active_row_nonzero6 {K : Type*} [Field K] [Algebra ℚ K]
    (A : Fin 6 → K) (M : Fin 6 → ℤ) (k : Fin 6)
    (hA : LinearIndependent ℚ (fun j : {i : Fin 6 // A i ≠ 0} => A j.val))
    (hk : A k ≠ 0) (hM : M k ≠ 0) :
    (∑ i, (M i : K)*A i) ≠ 0 := by
  classical
  intro hz
  have he : (∑ j : {i : Fin 6 // A i ≠ 0}, (M j.val : ℚ) • A j.val) =
      ∑ i : Fin 6, (M i : K)*A i := by
    simp only [Algebra.smul_def,map_intCast]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin 6 => A i ≠ 0))
      (by intro i; simp) (fun i => (M i : K)*A i)]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hi0 : A i = 0 := by simpa using hnot
    simp [hi0]
  have hc := (Fintype.linearIndependent_iff.mp hA) (fun j => (M j.val : ℚ))
    (he.trans hz) ⟨k,hk⟩
  exact hM (by exact_mod_cast hc)

theorem proper_cofactor_selection6 {K : Fin 3 → Type*}
    [∀ tau, Field (K tau)] [∀ tau, Algebra ℚ (K tau)]
    (A : (tau : Fin 3) → Fin 6 → Fin 6 → K tau) (S : Finset (Fin 6))
    (hli : ∀ tau i, i ∈ S →
      LinearIndependent ℚ (fun j : {k : Fin 6 // A tau i k ≠ 0} => A tau i j.val))
    (hcover : ∀ k : Fin 6, ∃ i ∈ S, ∀ tau, A tau i k ≠ 0)
    (M : Fin 6 → ℤ) (hM : M ≠ 0) :
    ∃ i ∈ S, ∀ tau, (∑ k, (M k : K tau)*A tau i k) ≠ 0 := by
  have hex : ∃ k, M k ≠ 0 := by
    by_contra! hz
    exact hM (funext hz)
  obtain ⟨k,hk⟩ := hex
  obtain ⟨i,hi,hA⟩ := hcover k
  exact ⟨i,hi,fun tau => active_row_nonzero6 (A tau i) M k (hli tau i hi) (hA tau) hk⟩

end CompoundFeasibility.SourceNormalHeight
