import SubspaceBridge.SourceFixedReference234
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedGeometry235
open SourceFixedArithmetic234

theorem positive_scale235 (C : ℤ) (hC : 0 < C) (n m : ℕ) : 0 < C*2^n*3^m := by
  positivity

theorem real_coordinate_scale235 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (v : Fin 10 → ℤ) (t : ℤ) (i : Fin 10) :
    (L⁻¹.transpose *ᵥ integerReal (t • v)) i =
      (t : ℝ)*(L⁻¹.transpose *ᵥ integerReal v) i := by
  have he : integerReal (t • v) = (t : ℝ) • integerReal v := by
    funext j
    change (((t • v) j : ℤ) : ℝ) = (t : ℝ)*(v j : ℝ)
    simp only [Pi.smul_apply,smul_eq_mul,Int.cast_mul]
  rw [he,Matrix.mulVec_smul]
  rfl

theorem floor_real_bound235 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (b : ℝ) (hb : b ≤ 0) :
    (p : ℝ)^((9-Int.floor ((Real.log Q/Real.log p)*b)).toNat) ≤ (p : ℝ)^10*Q^(-b) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hpp : (0 : ℝ) < p := by linarith
  have hqp : 0 < Q := by linarith
  have hlp : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp').ne'
  have hL : 0 ≤ Real.log Q/Real.log p := (div_pos (Real.log_pos hQ) (Real.log_pos hp')).le
  have hg : Int.floor ((Real.log Q/Real.log p)*b) ≤ 0 :=
    Int.floor_nonpos (mul_nonpos_of_nonneg_of_nonpos hL hb)
  have hn : 0 ≤ 9-Int.floor ((Real.log Q/Real.log p)*b) := by omega
  have he : (((9-Int.floor ((Real.log Q/Real.log p)*b)).toNat : ℕ) : ℝ) =
      9-(Int.floor ((Real.log Q/Real.log p)*b) : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hn]
    push_cast
    rfl
  have hpow : (p : ℝ)^(-(Real.log Q/Real.log p)*b) = Q^(-b) := by
    rw [Real.rpow_def_of_pos hpp,Real.rpow_def_of_pos hqp]
    congr 1
    field_simp
    ring
  calc
    _ = (p : ℝ)^((((9-Int.floor ((Real.log Q/Real.log p)*b)).toNat : ℕ) : ℝ)) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ (p : ℝ)^(10+(-(Real.log Q/Real.log p)*b)) := by
      apply Real.rpow_le_rpow_of_exponent_le hp'.le
      rw [he]
      linarith [Int.sub_one_lt_floor ((Real.log Q/Real.log p)*b)]
    _ = (p : ℝ)^10*Q^(-b) := by
      rw [Real.rpow_add hpp,hpow]
      congr 1
      exact Real.rpow_natCast _ 10


theorem supported_floor_upper235 (p : ℕ) (hp : 1 < p)
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A) (q : ℝ) (hq : 1 < q)
    (c : Fin 10 → ℝ) (hc : ∀ i, c i ≤ 0) (v : Fin 10 → ℤ) (hv : v ≠ 0) :
    ∃ j ∈ dualSupport234 A v,
      (p : ℝ)^((9-floorMin234 p A hA q c v hv).toNat) ≤
        (p : ℝ)^10*q^(-(∑ k : Fin 9, c (j.succAbove k))) := by
  obtain ⟨j,hj,hg⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((dualSupport234 A v).image (complementaryFloor234 p q c))
      ((dualSupport_nonempty234 A hA v hv).image _))
  refine ⟨j,hj,?_⟩
  have hh := floor_real_bound235 p hp q hq (∑ k : Fin 9, c (j.succAbove k))
    (Finset.sum_nonpos (fun k _ => hc (j.succAbove k)))
  change complementaryFloor234 p q c j = floorMin234 p A hA q c v hv at hg
  change (p : ℝ)^((9-complementaryFloor234 p q c j).toNat) ≤ _ at hh
  rwa [hg] at hh

theorem complement_exponent235 (c2 c3 : Fin 10 → ℝ) (j2 j3 : Fin 10) :
    -(∑ k : Fin 9, c2 (j2.succAbove k))-(∑ k : Fin 9, c3 (j3.succAbove k)) =
      -(∑ k, c2 k)-(∑ k, c3 k)+c2 j2+c3 j3 := by
  have h2 := Fin.sum_univ_succAbove c2 j2
  have h3 := Fin.sum_univ_succAbove c3 j3
  linarith

theorem rescale_real_bound235
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (h2 : IsUnit A2) (h3 : IsUnit A3)
    (q : ℝ) (hq : 1 < q) (c2 c3 : Fin 10 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (v : Fin 10 → ℤ) (hv : v ≠ 0) (C : ℤ) (hC : 0 < C)
    (t : ℤ) (ht : t = C*2^((9-floorMin234 2 A2 h2 q c2 v hv).toNat)*
      3^((9-floorMin234 3 A3 h3 q c3 v hv).toNat)) :
    ∃ j2 ∈ dualSupport234 A2 v, ∃ j3 ∈ dualSupport234 A3 v,
      (t : ℝ) ≤ (C : ℝ)*2^10*3^10*
        q^(-(∑ k, c2 k)-(∑ k, c3 k)+c2 j2+c3 j3) := by
  obtain ⟨j2,hj2,hb2⟩ := supported_floor_upper235 2 (by decide) A2 h2 q hq c2 hc2 v hv
  obtain ⟨j3,hj3,hb3⟩ := supported_floor_upper235 3 (by decide) A3 h3 q hq c3 hc3 v hv
  refine ⟨j2,hj2,j3,hj3,?_⟩
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul hb2 hb3 (by positivity) (by positivity)) (show (0 : ℝ) ≤ C by exact_mod_cast hC.le)
  have he : q^(-(∑ k, c2 k)-(∑ k, c3 k)+c2 j2+c3 j3) =
      q^(-(∑ k : Fin 9, c2 (j2.succAbove k)))*
        q^(-(∑ k : Fin 9, c3 (j3.succAbove k))) := by
    rw [← complement_exponent235 c2 c3 j2 j3,sub_eq_add_neg,
      Real.rpow_add (zero_lt_one.trans hq)]
  rw [ht,he]
  push_cast
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1 <;> ring


end CompoundFeasibility.SourceFixedGeometry235
