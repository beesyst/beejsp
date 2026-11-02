import SubspaceBridge.SourceNormalHeight6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceProper6
open SourceNormalHeight Auxiliary6.SourceExpansion

def standardArchWeight6 (i : Fin 6) : ℝ := if i.val = 5 then -1 else 1/5

theorem standardArchWeight6_bounds :
    (∀ i, |standardArchWeight6 i| ≤ 1) ∧ (∑ i, standardArchWeight6 i) = 0 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [standardArchWeight6,Fin.ext_iff,abs_div]
  · norm_num [standardArchWeight6,Fin.sum_univ_succ,Fin.ext_iff]

theorem standard_frame_arch_bounds6 (Q : ℝ) (hQ : 1 < Q) (j : Fin 5) (i : Fin 6) :
    |((Pi.single j.castSucc (1 : ℤ) : Fin 6 → ℤ) i : ℝ)| ≤
      Q^(standardArchWeight6 i-1/10) := by
  have hj : j.castSucc.val ≠ 5 := by
    change j.val ≠ 5
    omega
  by_cases hi : j.castSucc = i
  · subst i
    simp only [Pi.single_eq_same,Int.cast_one,abs_one,standardArchWeight6,if_neg hj]
    exact Real.one_le_rpow hQ.le (by norm_num)
  · simpa [Pi.single_apply,hi,Ne.symm hi] using
      Real.rpow_nonneg (zero_le_one.trans hQ.le) (standardArchWeight6 i-1/10)

theorem standard_frame_finite_bounds6 (p : ℕ) [Fact p.Prime] (j : Fin 5) (i : Fin 6) :
    (padicNorm p (((Pi.single j.castSucc (1 : ℤ) : Fin 6 → ℤ) i : ℤ) : ℚ) : ℝ) ≤ 1 := by
  by_cases hi : j.castSucc = i <;> simp [Pi.single_apply,hi]

theorem standard_frame_admissible_vanishing6 (M : Fin 6 → ℤ)
    (hann : ∀ j : Fin 5, (∑ i, M i*(Pi.single j.castSucc (1 : ℤ) : Fin 6 → ℤ) i) = 0) :
    ∀ j : Fin 5, -(1/10 : ℝ)/2 ≤ standardArchWeight6 j.castSucc ∧
      |(M j.castSucc : ℝ)| * (padicNorm 2 (M j.castSucc : ℚ) : ℝ)*
        (padicNorm 3 (M j.castSucc : ℚ) : ℝ) = 0 := by
  intro j
  have hz : M j.castSucc = 0 := by
    simpa [Pi.single_apply,mul_ite,Finset.sum_ite_eq,Finset.sum_ite_eq',eq_comm] using hann j
  have hj : j.castSucc.val ≠ 5 := by
    change j.val ≠ 5
    omega
  have hjv : j.val ≠ 5 := by omega
  norm_num [standardArchWeight6,hjv,hz]



def cofactor6 {F : Type*} [CommRing F] (B : Matrix (Fin 6) (Fin 6) F) :
    Matrix (Fin 6) (Fin 6) F := B.adjugate.transpose

def cofactorValue6 {F : Type*} [CommRing F] (B : Matrix (Fin 6) (Fin 6) F)
    (M : Fin 6 → ℤ) (i : Fin 6) : F := ∑ k, (M k : F)*cofactor6 B i k

theorem cofactor6_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (B : Matrix (Fin 6) (Fin 6) F) (i k : Fin 6) :
    cofactor6 (B.map f) i k = f (cofactor6 B i k) := by
  have he := f.map_adjugate B
  change B.adjugate.map f = (B.map f).adjugate at he
  exact (congrFun (congrFun he k) i).symm

theorem cofactorValue6_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (B : Matrix (Fin 6) (Fin 6) F) (M : Fin 6 → ℤ) (i : Fin 6) :
    cofactorValue6 (B.map f) M i = f (cofactorValue6 B M i) := by
  simp only [cofactorValue6,cofactor6_map,map_sum,map_mul,map_intCast]

theorem finite_cofactor6_rational (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (i k : Fin 6) :
    cofactor6 (finiteMatrix p A) i k =
      algebraMap ℚ ℚ_[p] (cofactor6 (compound A) i k) :=
  cofactor6_map _ _ i k

theorem rational_active_independence6 {F : Type*} [Field F] [Algebra ℚ F]
    (r : Fin 6 → ℚ)
    (hli : LinearIndependent ℚ (fun k : {i : Fin 6 // algebraMap ℚ F (r i) ≠ 0} =>
      algebraMap ℚ F (r k.val))) (i j : Fin 6)
    (hi : r i ≠ 0) (hj : r j ≠ 0) : i = j := by
  have hiF : algebraMap ℚ F (r i) ≠ 0 := (map_ne_zero (algebraMap ℚ F)).mpr hi
  have hjF : algebraMap ℚ F (r j) ≠ 0 := (map_ne_zero (algebraMap ℚ F)).mpr hj
  have he := hli.eq_of_smul_apply_eq_smul_apply (r j) (r i) ⟨i,hiF⟩ ⟨j,hjF⟩ hj (by
    simp only [Algebra.smul_def]
    exact mul_comm _ _)
  exact congrArg Subtype.val he

theorem finite_cofactor_active_support6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (i : Fin 6)
    (hli : LinearIndependent ℚ (fun k : {j : Fin 6 // cofactor6 (finiteMatrix p A) i j ≠ 0} =>
      cofactor6 (finiteMatrix p A) i k.val)) (j k : Fin 6)
    (hj : cofactor6 (compound A) i j ≠ 0) (hk : cofactor6 (compound A) i k ≠ 0) : j = k := by
  apply rational_active_independence6 (F := ℚ_[p]) (cofactor6 (compound A) i) _ j k hj hk
  have he : cofactor6 (finiteMatrix p A) i =
      fun k => algebraMap ℚ ℚ_[p] (cofactor6 (compound A) i k) :=
    funext (finite_cofactor6_rational p A i)
  rw [he] at hli
  exact hli

end CompoundFeasibility.SourceProper6
