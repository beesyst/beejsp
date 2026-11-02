import SubspaceBridge.SourceFixedFloors234
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedArithmetic234
theorem clear_positive234 (A : Matrix (Fin 10) (Fin 10) ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∃ M : Matrix (Fin 10) (Fin 10) ℤ,
      M.map (Int.castRingHom ℚ) = (d : ℚ) • A := by
  obtain ⟨d,hd,h⟩ := clear_matrix_denominators A
  choose M hM using h
  by_cases hp : 0 < d
  · refine ⟨d,hp,M,?_⟩
    ext i j
    exact hM i j
  · refine ⟨-d,by omega,-M,?_⟩
    ext i j
    simp only [Matrix.map_apply,Matrix.neg_apply,Int.cast_neg,Matrix.smul_apply,smul_eq_mul,neg_mul]
    exact congrArg Neg.neg (hM i j)

theorem rational_pairing234 (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A)
    (x v : Fin 10 → ℚ) :
    (A *ᵥ x) ⬝ᵥ (A⁻¹.transpose *ᵥ v) = x ⬝ᵥ v := by
  rw [dotProduct_comm,Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec,← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA),
    Matrix.transpose_one,Matrix.one_mulVec,dotProduct_comm]

theorem cleared_pairing234 (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A)
    (d f : ℤ) (M N : Matrix (Fin 10) (Fin 10) ℤ)
    (hM : M.map (Int.castRingHom ℚ) = (d : ℚ) • A)
    (hN : N.map (Int.castRingHom ℚ) = (f : ℚ) • A⁻¹.transpose)
    (x v : Fin 10 → ℤ) :
    (∑ i, (M *ᵥ x) i * (N *ᵥ v) i) = d*f*(∑ i, x i*v i) := by
  have h := rational_pairing234 A hA (fun i => (x i : ℚ)) (fun i => (v i : ℚ))
  have hx : (fun i => ((M *ᵥ x) i : ℚ)) = (d : ℚ) • (A *ᵥ (fun i => (x i : ℚ))) := by
    ext i
    simpa only [hM,Matrix.smul_mulVec_assoc,Pi.smul_apply,smul_eq_mul] using
      (Int.castRingHom ℚ).map_mulVec M x i
  have hv : (fun i => ((N *ᵥ v) i : ℚ)) = (f : ℚ) • (A⁻¹.transpose *ᵥ (fun i => (v i : ℚ))) := by
    ext i
    simpa only [hN,Matrix.smul_mulVec_assoc,Pi.smul_apply,smul_eq_mul] using
      (Int.castRingHom ℚ).map_mulVec N v i
  have hh : (fun i => ((M *ᵥ x) i : ℚ)) ⬝ᵥ (fun i => ((N *ᵥ v) i : ℚ)) =
      (d : ℚ)*(f : ℚ)*((fun i => (x i : ℚ)) ⬝ᵥ (fun i => (v i : ℚ))) := by
    rw [hx,hv,smul_dotProduct,dotProduct_smul,h]
    simp only [smul_eq_mul]
    ring
  simp only [dotProduct] at hh
  exact_mod_cast hh

theorem local_rows_dvd234 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (d : ℤ) (M : Matrix (Fin 10) (Fin 10) ℤ)
    (hM : M.map (Int.castRingHom ℚ) = (d : ℚ) • A)
    (e : Fin 10 → ℕ) (x : Fin 10 → ℤ) (hx : x ∈ lattice10 p A e) :
    ∀ i, (p : ℤ)^(e i) ∣ (M *ᵥ x) i := by
  intro i
  have he : ((M *ᵥ x) i : ℚ) = (d : ℚ)*(A *ᵥ (fun j => (x j : ℚ))) i := by
    have hh := (Int.castRingHom ℚ).map_mulVec M x i
    rw [hM,Matrix.smul_mulVec_assoc] at hh
    exact hh
  suffices hn : padicNorm p ((M *ᵥ x) i : ℚ) ≤ (p : ℚ)^(-(e i : ℤ)) by
    simpa only [Nat.cast_pow] using (padicNorm.dvd_iff_norm_le (p := p)).mpr hn
  rw [he,padicNorm.mul]
  have hb := (lattice10_spec p A e x).mp hx i
  exact (mul_le_mul_of_nonneg_right (padicNorm.of_int d) (padicNorm.nonneg _)).trans (by simpa using hb)

theorem rational_padic_coordinates234 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A)
    (v : Fin 10 → ℤ) (i : Fin 10) :
    ((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ (fun j => (v j : ℚ_[p]))) i =
      algebraMap ℚ ℚ_[p] ((A⁻¹.transpose *ᵥ (fun j => (v j : ℚ))) i) := by
  have hi : (A.map (algebraMap ℚ ℚ_[p]))⁻¹ = A⁻¹.map (algebraMap ℚ ℚ_[p]) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul,Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    ext i j
    simp [Matrix.map_apply,Matrix.one_apply]
  rw [hi]
  simpa only [Matrix.transpose_map,Function.comp_apply,map_intCast] using
    ((algebraMap ℚ ℚ_[p]).map_mulVec A⁻¹.transpose (fun j => (v j : ℚ)) i).symm

theorem local_rescale_dvd234 (p : ℕ) [Fact p.Prime] (hp : 1 < p)
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : IsUnit A)
    (d f : ℤ) (M N : Matrix (Fin 10) (Fin 10) ℤ)
    (hM : M.map (Int.castRingHom ℚ) = (d : ℚ) • A)
    (hN : N.map (Int.castRingHom ℚ) = (f : ℚ) • A⁻¹.transpose)
    (q : ℝ) (hq : 1 < q) (c : Fin 10 → ℝ) (hc : ∀ i, c i ≤ 0)
    (v : Fin 10 → ℤ) (hv : v ≠ 0) (x : Fin 10 → ℤ)
    (hx : x ∈ lattice10 p A (fun i => Nat.ceil (JSP000334.qThreshold p q (c i)))) :
    (p : ℤ)^(∑ i, Nat.ceil (JSP000334.qThreshold p q (c i))) ∣
      d*f*(p : ℤ)^((9-floorMin234 p A hA q c v hv).toNat)*(∑ i, x i*v i) := by
  let e := fun i => Nat.ceil (JSP000334.qThreshold p q (c i))
  let n := (9-floorMin234 p A hA q c v hv).toNat
  have hrow := local_rows_dvd234 p A d M hM e x hx
  have hcomp (i : Fin 10) : (p : ℤ)^((∑ j, e j)-e i) ∣ (p : ℤ)^n*(N *ᵥ v) i := by
    have he : ((N *ᵥ v) i : ℚ) = (f : ℚ)*(A⁻¹.transpose *ᵥ (fun j => (v j : ℚ))) i := by
      have hh := (Int.castRingHom ℚ).map_mulVec N v i
      rw [hN,Matrix.smul_mulVec_assoc] at hh
      exact hh
    by_cases hi : (A⁻¹.transpose *ᵥ (fun j => (v j : ℚ))) i = 0
    · have hz : (N *ᵥ v) i = 0 := by
        have hh : ((N *ᵥ v) i : ℚ) = 0 := by rw [he,hi,mul_zero]
        exact_mod_cast hh
      rw [hz,mul_zero]
      exact dvd_zero _
    · have hm := floorMin_le234 p A hA q c v hv i (by simp [dualSupport234,hi])
      have hb := floor_bound234 p hp q hq c hc i
      have hn := Int.toNat_le_toNat (sub_le_sub_left hm 9)
      exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (hb.trans hn)) _
  have hd : (p : ℤ)^(∑ i, e i) ∣ ∑ i, (M *ᵥ x) i*((p : ℤ)^n*(N *ᵥ v) i) := by
    apply Finset.dvd_sum
    intro i _
    have he : e i ≤ ∑ j, e j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hh := mul_dvd_mul (hrow i) (hcomp i)
    rwa [← pow_add,Nat.add_sub_of_le he] at hh
  have he : (∑ i, (M *ᵥ x) i*((p : ℤ)^n*(N *ᵥ v) i)) =
      d*f*(p : ℤ)^n*(∑ i, x i*v i) := by
    calc
      _ = (p : ℤ)^n*(∑ i, (M *ᵥ x) i*(N *ᵥ v) i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [cleared_pairing234 A hA d f M N hM hN x v]; ring
  exact he ▸ hd

end CompoundFeasibility.SourceFixedArithmetic234
