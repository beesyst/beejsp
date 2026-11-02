import SubspaceBridge.CofactorDualMinima3
open scoped BigOperators Matrix
open MeasureTheory
namespace JSP000334
noncomputable section

theorem cofactor_sourceDual_integer_pairing3 (k : Fin 3) (x v : IntegerTriple) :
    (∑ j : Fin 3, x j * v j) =
      ∑ i : Fin 3, (cofactorIntegerMatrix3 k *ᵥ x) i * cofactorDualInt3 k v i := by
  fin_cases k <;>
    norm_num [cofactorIntegerMatrix3_table,cofactorOriginalMatrix3_table,cofactorDualInt3,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> ring

theorem cofactor_sourceDual_complementary_divisibility3 (p : ℕ) (k : Fin 3) (a : Fin 3 → ℕ)
    (x v : IntegerTriple)
    (hx : ∀ i, (p : ℤ) ^ a i ∣ (cofactorIntegerMatrix3 k *ᵥ x) i)
    (hv : ∀ i, (p : ℤ) ^ (∑ j, a j - a i) ∣ cofactorDualInt3 k v i) :
    (p : ℤ) ^ (∑ j, a j) ∣ ∑ j : Fin 3, x j * v j := by
  rw [cofactor_sourceDual_integer_pairing3 k x v]
  apply Finset.dvd_sum
  intro i _
  have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h := mul_dvd_mul (hx i) (hv i)
  rwa [← pow_add, Nat.add_sub_of_le hi] at h

theorem cofactor_sourceDual_complementary_mem3 (k₂ k₃ : Fin 3) (a b : Fin 3 → ℕ)
    (c : Basis (Fin 3) ℤ (mixedCongruence3 (cofactorIntegerMatrix3 k₂)
      (cofactorIntegerMatrix3 k₃) a b))
    (hc : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((c j : IntegerTriple) i : ℚ)))
    (v : IntegerTriple)
    (h₂ : ∀ i, (2 : ℤ) ^ (∑ j, a j - a i) ∣ cofactorDualInt3 k₂ v i)
    (h₃ : ∀ i, (3 : ℤ) ^ (∑ j, b j - b i) ∣ cofactorDualInt3 k₃ v i) :
    (fun i => (v i : ℚ)) ∈ dualFrameSourceBasisLattice3
      (mixedCongruence3 (cofactorIntegerMatrix3 k₂) (cofactorIntegerMatrix3 k₃) a b) c := by
  let G := mixedCongruence3 (cofactorIntegerMatrix3 k₂) (cofactorIntegerMatrix3 k₃) a b
  have hD : G.index = 2 ^ (∑ i, a i) * 3 ^ (∑ i, b i) :=
    mixedCongruence3_index _ _ (cofactorIntegerMatrix3_isUnit _) (cofactorIntegerMatrix3_isUnit _) a b
  have hDnz : (G.index : ℚ) ≠ 0 := by rw [hD]; positivity
  apply dualFrameSourceLattice3_subset_basis G c hc
  refine ⟨fun i => (v i : ℚ) / G.index, ?_, ?_⟩
  · intro x
    have hx := (mem_mixedCongruence3 _ _ a b (x : IntegerTriple)).mp x.property
    have hd₂ := cofactor_sourceDual_complementary_divisibility3 2 k₂ a x v hx.1 h₂
    have hd₃ := cofactor_sourceDual_complementary_divisibility3 3 k₃ b x v hx.2 h₃
    have hcop : IsCoprime ((2 : ℤ) ^ (∑ i, a i)) ((3 : ℤ) ^ (∑ i, b i)) :=
      IsCoprime.pow (show IsCoprime (2 : ℤ) 3 from ⟨-1,1,by norm_num⟩)
    obtain ⟨z,hz⟩ := hcop.mul_dvd hd₂ hd₃
    refine ⟨z, ?_⟩
    have hcast : (∑ i : Fin 3, ((x : IntegerTriple) i : ℚ) * (v i : ℚ)) =
        (G.index : ℚ) * (z : ℚ) := by
      rw [hD]
      exact_mod_cast hz
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, hcast]
    field_simp [hDnz]
  · ext i
    exact mul_div_cancel₀ (v i : ℚ) hDnz

def cofactor_sourceDualSupport3 (k : Fin 3) (v : IntegerTriple) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => cofactorDualInt3 k v i ≠ 0)

theorem cofactor_sourceDualSupport3_nonempty (k : Fin 3) (v : IntegerTriple) (hv : v ≠ 0) :
    (cofactor_sourceDualSupport3 k v).Nonempty := by
  by_contra hh
  have hz (i : Fin 3) : cofactorDualInt3 k v i = 0 := by
    by_contra hi
    exact hh ⟨i,by simp [cofactor_sourceDualSupport3,hi]⟩
  apply hv
  ext l
  have h := cofactorDualInt3_reconstruct k v l
  simp_rw [hz,Int.cast_zero,mul_zero,Finset.sum_const_zero] at h
  exact_mod_cast h

noncomputable def cofactor_sourceDualFloorMin3 (p : ℕ) (k : Fin 3) (Q : ℝ) (c : Fin 3 → ℝ)
    (v : IntegerTriple) (hv : v ≠ 0) : ℤ :=
  ((cofactor_sourceDualSupport3 k v).image (fun i => Int.floor ((Real.log Q/Real.log p)*
    (c (i.succAbove 0)+c (i.succAbove 1))))).min' ((cofactor_sourceDualSupport3_nonempty k v hv).image _)

theorem cofactor_sourceDualFloorMin3_le (p : ℕ) (k : Fin 3) (Q : ℝ) (c : Fin 3 → ℝ)
    (v : IntegerTriple) (hv : v ≠ 0) (i : Fin 3) (hi : cofactorDualInt3 k v i ≠ 0) :
    cofactor_sourceDualFloorMin3 p k Q c v hv ≤ Int.floor ((Real.log Q/Real.log p)*
      (c (i.succAbove 0)+c (i.succAbove 1))) := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,by simp [cofactor_sourceDualSupport3,hi],rfl⟩)

theorem cofactor_sourceDualInt_smul3 (k : Fin 3) (t : ℤ) (v : IntegerTriple) (i : Fin 3) :
    cofactorDualInt3 k (t • v) i = t * cofactorDualInt3 k v i := by
  simp only [cofactorDualInt3]
  split_ifs <;> rw [Matrix.mulVec_smul] <;> simp [Pi.smul_apply,smul_eq_mul]

theorem cofactor_sourceDual_rescale_mem3 (k₂ k₃ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (v : IntegerTriple) (hv : v ≠ 0)
    (c : Basis (Fin 3) ℤ (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃))
    (hc : LinearIndependent ℚ (fun j : Fin 3 => fun i : Fin 3 => ((c j : IntegerTriple) i : ℚ))) :
    let t : ℤ := 2 ^ (2-cofactor_sourceDualFloorMin3 2 k₂ Q c₂ v hv).toNat *
      3 ^ (2-cofactor_sourceDualFloorMin3 3 k₃ Q c₃ v hv).toNat
    t ≠ 0 ∧ (fun i => ((t • v) i : ℚ)) ∈
      dualFrameSourceBasisLattice3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) c := by
  intro t
  have ht : t ≠ 0 := by dsimp [t]; positivity
  refine ⟨ht,?_⟩
  apply cofactor_sourceDual_complementary_mem3 k₂ k₃
    (fun i => Nat.ceil (-c₂ i*Real.log Q/Real.log 2))
    (fun i => Nat.ceil (-c₃ i*Real.log Q/Real.log 3)) c hc (t • v)
  · intro i
    rw [cofactor_sourceDualInt_smul3]
    by_cases hi : cofactorDualInt3 k₂ v i = 0
    · rw [hi,mul_zero]; exact dvd_zero _
    · have hb := sourceDual_floor_bound3 2 (by decide) Q hQ c₂ hc₂ i
      have hm := Int.toNat_le_toNat (sub_le_sub_left (cofactor_sourceDualFloorMin3_le 2 k₂ Q c₂ v hv i hi) 2)
      have hd : (2 : ℤ) ^ ((∑ j, Nat.ceil (-c₂ j*Real.log Q/Real.log 2))-
          Nat.ceil (-c₂ i*Real.log Q/Real.log 2)) ∣ t := by
        exact dvd_mul_of_dvd_left (pow_dvd_pow _ (hb.trans hm)) _
      exact dvd_mul_of_dvd_left hd _
  · intro i
    rw [cofactor_sourceDualInt_smul3]
    by_cases hi : cofactorDualInt3 k₃ v i = 0
    · rw [hi,mul_zero]; exact dvd_zero _
    · have hb := sourceDual_floor_bound3 3 (by decide) Q hQ c₃ hc₃ i
      have hm := Int.toNat_le_toNat (sub_le_sub_left (cofactor_sourceDualFloorMin3_le 3 k₃ Q c₃ v hv i hi) 2)
      have hd : (3 : ℤ) ^ ((∑ j, Nat.ceil (-c₃ j*Real.log Q/Real.log 3))-
          Nat.ceil (-c₃ i*Real.log Q/Real.log 3)) ∣ t := by
        exact dvd_mul_of_dvd_right (pow_dvd_pow _ (hb.trans hm)) _
      exact dvd_mul_of_dvd_left hd _

theorem cofactor_sourceRealLogWeights3_coordinates (k : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (A c₂ c₃ : Fin 3 → ℝ) (hA : ∀ i, 0 < A i) :
    cofactorSourceCoordinates3 k Q (sourceRealLogWeights3 Q A c₂ c₃ 0) hQ =
      archCoordinates3 (cofactorRealCoordinates3 k) A hA := by
  ext x i
  change cofactorRealCoordinates3 k x i/Q^(Real.log (A i)/Real.log Q) = _
  have he : Q^(Real.log (A i)/Real.log Q) = A i := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < Q),mul_div_cancel₀ _ (Real.log_pos hQ).ne',
      Real.exp_log (hA i)]
  rw [he]
  rfl

theorem cofactor_sourceReal_uniform_selected_vanishing3 (k₀ k₂ k₃ : Fin 3)
    (S : Set (Fin 3 → Fin 3)) (hS : S.Nonempty) (delta : ℝ) (hd : 0 < delta) :
    ∃ Q0 : ℝ, 1 ≤ Q0 ∧ ∀ Q : ℝ, Q0 < Q → ∀ hQ : 1 < Q,
      ∀ (A c₂ c₃ : Fin 3 → ℝ) (hA : ∀ i, 0 < A i),
      (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) → (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) →
      (∀ i, A i < Q ∧ (A i)⁻¹ < Q) →
      (∏ i, A i*Q^(c₂ i)*Q^(c₃ i)) = 1 →
      S ⊆ sourceTupleSet3 Q delta A c₂ c₃ →
      ∀ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃),
      lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 →
      LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) →
      (∀ j, coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA)
        (integerTripleReal3 (u j : IntegerTriple)) =
        successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) j) →
      successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) 1 < Q^(-delta) →
      ∀ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s
        (fun i => (((dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u *
          (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
          dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i)) = 0 := by
  obtain ⟨Q0,hQ0,hzero⟩ := cofactor_uniform_selected_vanishing3 k₀ k₂ k₃ S hS delta hd
  refine ⟨Q0,hQ0,?_⟩
  intro Q hcutQ hQ A c₂ c₃ hA hc₂ hc₃ hcut hnorm hSsub
  let c := sourceRealLogWeights3 Q A c₂ c₃
  have hc := sourceRealLogWeights3_conditions Q hQ A c₂ c₃ hA hc₂ hc₃ hcut hnorm
  have ht (s : Fin 3 → Fin 3) (hs : s ∈ S) : -delta/2 ≤ c 0 (s 0)+c 1 (s 1)+c 2 (s 2) := by
    let W : Fin 3 → Fin 3 → ℝ := ![A,fun i => Q^(c₂ i),fun i => Q^(c₃ i)]
    have hW : ∀ tau i, 0 < W tau i := by
      intro tau i
      fin_cases tau
      · exact hA i
      · exact Real.rpow_pos_of_pos (by linarith) _
      · exact Real.rpow_pos_of_pos (by linarith) _
    have h := sourceWeight48_log3 Q delta hQ W hW s (hSsub hs)
    have he : sourceLogWeights3 Q W = c := by
      ext tau i
      fin_cases tau
      · rfl
      · change Real.log (Q^(c₂ i))/Real.log Q = c₂ i
        rw [Real.log_rpow (by linarith : 0 < Q),mul_div_cancel_right₀ _ (Real.log_pos hQ).ne']
      · change Real.log (Q^(c₃ i))/Real.log Q = c₃ i
        rw [Real.log_rpow (by linarith : 0 < Q),mul_div_cancel_right₀ _ (Real.log_pos hQ).ne']
    rwa [he] at h
  have hz := hzero Q hcutQ hQ c hc ht
  rw [cofactor_sourceRealLogWeights3_coordinates k₀ Q hQ A c₂ c₃ hA] at hz
  intro B u hB hu hatt hsmall s hs
  have h := hz B u hB hu hatt hsmall s hs
  rw [cofactorSelectedProduct3_scale,h,mul_zero]

theorem cofactor_sourceDual_rescale_real_bound3 (k₂ k₃ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (v : IntegerTriple) (hv : v ≠ 0) :
    ∃ i₂ ∈ cofactor_sourceDualSupport3 k₂ v, ∃ i₃ ∈ cofactor_sourceDualSupport3 k₃ v,
      let t : ℤ := 2 ^ (2-cofactor_sourceDualFloorMin3 2 k₂ Q c₂ v hv).toNat *
        3 ^ (2-cofactor_sourceDualFloorMin3 3 k₃ Q c₃ v hv).toNat
      (t : ℝ) ≤ 216*Q^(-(c₂ (i₂.succAbove 0)+c₂ (i₂.succAbove 1)+
        c₃ (i₃.succAbove 0)+c₃ (i₃.succAbove 1))) := by
  obtain ⟨i₂,hi₂,hg₂⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((cofactor_sourceDualSupport3 k₂ v).image (fun i => Int.floor
      ((Real.log Q/Real.log 2)*(c₂ (i.succAbove 0)+c₂ (i.succAbove 1)))))
      ((cofactor_sourceDualSupport3_nonempty k₂ v hv).image _))
  obtain ⟨i₃,hi₃,hg₃⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((cofactor_sourceDualSupport3 k₃ v).image (fun i => Int.floor
      ((Real.log Q/Real.log 3)*(c₃ (i.succAbove 0)+c₃ (i.succAbove 1)))))
      ((cofactor_sourceDualSupport3_nonempty k₃ v hv).image _))
  refine ⟨i₂,hi₂,i₃,hi₃,?_⟩
  intro t
  have h2 := sourceDual_floor_real_bound3 2 (by decide) Q hQ
    (c₂ (i₂.succAbove 0)+c₂ (i₂.succAbove 1)) (by linarith [hc₂ (i₂.succAbove 0),hc₂ (i₂.succAbove 1)])
  have h3 := sourceDual_floor_real_bound3 3 (by decide) Q hQ
    (c₃ (i₃.succAbove 0)+c₃ (i₃.succAbove 1)) (by linarith [hc₃ (i₃.succAbove 0),hc₃ (i₃.succAbove 1)])
  change Int.floor _ = cofactor_sourceDualFloorMin3 2 k₂ Q c₂ v hv at hg₂
  change Int.floor _ = cofactor_sourceDualFloorMin3 3 k₃ Q c₃ v hv at hg₃
  norm_num only [Nat.cast_ofNat] at h2 h3
  rw [hg₂] at h2
  rw [hg₃] at h3
  have h := mul_le_mul h2 h3 (by positivity) (by positivity)
  push_cast [t]
  convert h using 1
  rw [show -(c₂ (i₂.succAbove 0)+c₂ (i₂.succAbove 1)+c₃ (i₃.succAbove 0)+c₃ (i₃.succAbove 1)) =
      -(c₂ (i₂.succAbove 0)+c₂ (i₂.succAbove 1)) + -(c₃ (i₃.succAbove 0)+c₃ (i₃.succAbove 1)) by ring,
    Real.rpow_add (by linarith : 0 < Q)]
  ring

theorem cofactor_sourceReal_width_geometry3 (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (A : Fin 3 → ℝ) (hA : ∀ i, 0 < A i)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hatt : ∀ j, coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) j) :
    let e := archCoordinates3 (cofactorRealCoordinates3 k₀) A hA
    ZLattice.covolume (lattice3 B) = ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) ∧
    volume.real (parallelepipedBody3 e) = 8*∏ i, A i ∧
    (∀ j i, |∑ l : Fin 3, cofactorRealMatrix3 k₀ i l*((u j : IntegerTriple) l : ℝ)| ≤
      successiveRadius3 B e j*A i) ∧
    (∏ j, successiveRadius3 B e j)*(∏ i, A i) ≤
      ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) := by
  intro e
  have hcov : ZLattice.covolume (lattice3 B) =
      ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) := by
    rw [hB,(cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    exact (cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  have hvol : volume.real (parallelepipedBody3 e) = 8*∏ i, A i := by
    rw [← archBody3_eq_parallelepiped _ _ hA,archBody3_volume _ _ hA,cofactorRealCoordinates3_abs_det,div_one]
  refine ⟨hcov,hvol,?_,?_⟩
  · intro j i
    have hh : |e (integerTripleReal3 (u j : IntegerTriple)) i| ≤
        coordinateGauge3 e (integerTripleReal3 (u j : IntegerTriple)) := by
      simpa only [coordinateGauge3,Real.norm_eq_abs] using
        norm_le_pi_norm (e (integerTripleReal3 (u j : IntegerTriple))) i
    change |(∑ l : Fin 3, cofactorRealMatrix3 k₀ i l*((u j : IntegerTriple) l : ℝ))/A i| ≤ _ at hh
    rw [abs_div,abs_of_pos (hA i),div_le_iff₀ (hA i),hatt] at hh
    exact hh
  · have h := successive_minima3_parallelepiped_volume_upper B e
    rw [hvol,hcov] at h
    nlinarith

theorem cofactor_sourceReal_dual_second_gt_one3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (A : Fin 3 → ℝ) (hA : ∀ i, 0 < A i)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) j)
    (hsmall : successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) 1 < Q^(-delta))
    (hlarge : 1296 < Q^delta)
    (c : Basis (Fin 3) ℤ (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃))
    (hc : LinearIndependent ℝ (fun j => integerTripleReal3 (c j : IntegerTriple)))
    (hD : (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index ≠ 0) :
    1 < successiveRadius3 (sourceDualBasis3 _ c hc hD)
      (cofactor_sourceDualCoordinates3 k₀ (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index A
        (by exact_mod_cast Nat.pos_of_ne_zero hD) hA) 1 := by
  obtain ⟨hcov,hvol,hpoint,hprod⟩ := cofactor_sourceReal_width_geometry3 k₀ k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃ A hA B u hB hatt
  have h := (cofactor_sourceDual_minima_transference3 _ c hc hD u hu B _ hcov k₀ A hA hvol hpoint hprod 1).1
  have hr : (1 : Fin 3).rev = 1 := rfl
  rw [hr] at h
  obtain ⟨_,_,_,hpos,_,_⟩ := exists_successive_minima3 B
    (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA)
  exact sourceDual_second_minimum_gt_one3 Q delta _ _ hQ (hpos 1) hsmall hlarge h

theorem cofactor_sourceReal_index_lower3 (k₂ k₃ : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    Q^(-(∑ i, (c₂ i+c₃ i))) ≤ ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) := by
  rw [(cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1,
    qCongruenceIndex3_factorization Q c₂ c₃ hQ]
  have he : (∏ i, Q^(-c₂ i)*Q^(-c₃ i)) = Q^(-(∑ i, (c₂ i+c₃ i))) := by
    simp_rw [← Real.rpow_add (by linarith : 0 < Q)]
    rw [← Real.rpow_sum_of_pos (by linarith : 0 < Q) _ Finset.univ]
    congr 1
    simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib]
    ring
  rw [he]
  exact le_mul_of_one_le_right (Real.rpow_pos_of_pos (by linarith) _).le
    (qRoundingFactor3_bounds Q c₂ c₃ hQ hc₂ hc₃).1

theorem cofactor_sourceDual_two_case_body3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (hQ : 1 < Q)
    (A c₂ c₃ : Fin 3 → ℝ) (hA : ∀ i, 0 < A i)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (S : Set (Fin 3 → Fin 3)) (hS : S = sourceTupleSet3 Q delta A c₂ c₃)
    (v : IntegerTriple) (hv : v ≠ 0)
    (hzero : ∀ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s (fun i => (v i : ℚ)) = 0)
    (hlarge : ∀ i, 216*|(cofactorDualInt3 k₀ v i : ℝ)| ≤ Q^(delta/2)) :
    let t : ℤ := 2 ^ (2-cofactor_sourceDualFloorMin3 2 k₂ Q c₂ v hv).toNat *
      3 ^ (2-cofactor_sourceDualFloorMin3 3 k₃ Q c₃ v hv).toNat
    integerTripleReal3 (t • v) ∈ cofactor_sourceDualBody3 k₀ (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index A := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro t i
  have ht : (0 : ℝ) < t := by dsimp [t]; positivity
  change |cofactorDualRealCoordinates3 k₀ (integerTripleReal3 (t • v)) i| ≤ _
  rw [cofactorDualInt3_real_value,cofactor_sourceDualInt_smul3,Int.cast_mul]
  by_cases hcase : ∃ s ∈ S, s 0 = i ∧ s 1 ∈ cofactor_sourceDualSupport3 k₂ v ∧ s 2 ∈ cofactor_sourceDualSupport3 k₃ v
  · obtain ⟨s,hs,hs0,hs2,hs3⟩ := hcase
    have h2 : (padicNorm 2 (cofactorDualInt3 k₂ v (s 1) : ℚ) : ℝ) ≠ 0 := by
      have hh : (cofactorDualInt3 k₂ v (s 1) : ℚ) ≠ 0 := by
        exact_mod_cast (Finset.mem_filter.mp hs2).2
      exact_mod_cast padicNorm.nonzero hh
    have h3 : (padicNorm 3 (cofactorDualInt3 k₃ v (s 2) : ℚ) : ℝ) ≠ 0 := by
      have hh : (cofactorDualInt3 k₃ v (s 2) : ℚ) ≠ 0 := by
        exact_mod_cast (Finset.mem_filter.mp hs3).2
      exact_mod_cast padicNorm.nonzero hh
    have hz := hzero s hs
    simp only [cofactorSelectedProduct3,cofactorDualInt3_value,Rat.cast_intCast,hs0] at hz
    have hf := (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right h3)).resolve_right h2
    rw [abs_eq_zero.mp hf,mul_zero,abs_zero]
    exact div_nonneg (Nat.cast_nonneg _) (hA i).le
  · obtain ⟨i₂,hi₂,i₃,hi₃,hbound⟩ := cofactor_sourceDual_rescale_real_bound3 k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃ v hv
    have hnot : ![i,i₂,i₃] ∉ S := by
      intro hs
      exact hcase ⟨![i,i₂,i₃],hs,rfl,hi₂,hi₃⟩
    have hlt : A i*Q^(c₂ i₂)*Q^(c₃ i₃)*Q^(delta/2) < 1 := by
      apply lt_of_not_ge
      intro hh
      apply hnot
      rw [hS]
      exact hh
    have hp : 0 < Q := by linarith
    let R := Q^(-(∑ j, (c₂ j+c₃ j)))
    have hR : 0 < R := Real.rpow_pos_of_pos hp _
    have hD := cofactor_sourceReal_index_lower3 k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃
    have he : Q^(-(c₂ (i₂.succAbove 0)+c₂ (i₂.succAbove 1)+
        c₃ (i₃.succAbove 0)+c₃ (i₃.succAbove 1))) = R*Q^(c₂ i₂)*Q^(c₃ i₃) := by
      rw [sourceDual_complement_exponent3,Real.rpow_add hp,Real.rpow_add hp]
    rw [he] at hbound
    change (t : ℝ) ≤ 216*(R*Q^(c₂ i₂)*Q^(c₃ i₃)) at hbound
    have hAi := hA i
    have hp2 := Real.rpow_pos_of_pos hp (c₂ i₂)
    have hp3 := Real.rpow_pos_of_pos hp (c₃ i₃)
    have hscale : A i*|(t : ℝ)*(cofactorDualInt3 k₀ v i : ℝ)| ≤
        (216*|(cofactorDualInt3 k₀ v i : ℝ)|)*R*(A i*Q^(c₂ i₂)*Q^(c₃ i₃)) := by
      rw [abs_mul,abs_of_pos ht]
      calc
        _ ≤ A i*(216*(R*Q^(c₂ i₂)*Q^(c₃ i₃)))*|(cofactorDualInt3 k₀ v i : ℝ)| := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hbound (hA i).le) (abs_nonneg (cofactorDualInt3 k₀ v i : ℝ))
        _ = _ := by ring
    have hlarge' := mul_le_mul_of_nonneg_right (hlarge i)
      (show 0 ≤ R*(A i*Q^(c₂ i₂)*Q^(c₃ i₃)) by positivity)
    have hmul : A i*|(t : ℝ)*(cofactorDualInt3 k₀ v i : ℝ)| ≤
        ((cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℝ) := by
      have hh := mul_lt_mul_of_pos_left hlt hR
      nlinarith [hscale,hlarge']
    exact (le_div_iff₀ (hA i)).mpr (by nlinarith [hmul])

theorem cofactor_sourceReal_last_dual_body3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (A : Fin 3 → ℝ) (hA : ∀ i, 0 < A i)
    (hnorm : (∏ i, A i*Q^(c₂ i)*Q^(c₃ i)) = 1)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) j)
    (hsmall : successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) 1 < Q^(-delta))
    (hlarge : 1296 < Q^delta)
    (c : Basis (Fin 3) ℤ (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)) :
    rationalTripleReal3 (fun i => (((dualFrameRelativeIndex3 (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃) u *
      (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index : ℕ) : ℚ) *
        dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i)) ∈
      cofactor_sourceDualBody3 k₀ (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).index A := by
  let G := cofactorSourceLattice3 k₂ k₃ Q c₂ c₃
  let e := archCoordinates3 (cofactorRealCoordinates3 k₀) A hA
  let s := successiveRadius3 B e
  have hp : 0 < Q := by linarith
  have hD : (0 : ℝ) < G.index := by
    rw [(cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    unfold qCongruenceIndex3
    positivity
  obtain ⟨hcov,hvol,hpoint,hprod⟩ := cofactor_sourceReal_width_geometry3 k₀ k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃ A hA B u hB hatt
  obtain ⟨_,_,_,hs,hmon,_⟩ := exists_successive_minima3 B e
  have hP : 0 < ∏ i, A i := Finset.prod_pos (fun i _ => hA i)
  have hPD : (∏ i, A i) ≤ (G.index : ℝ) := by
    rw [sourceReal_width_product3 Q hQ A c₂ c₃ hnorm]
    exact cofactor_sourceReal_index_lower3 k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃
  have hlower := source_minima_product_lower3 B e G.index (∏ i, A i) hP hvol hcov
  have hlower' : (1 : ℝ)/6 ≤ ∏ i, s i := by
    have hh := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 6) hP)).mp hlower
    dsimp [s]
    nlinarith
  have hexp : Q^(-delta)*Q^delta = 1 := by rw [← Real.rpow_add hp,neg_add_cancel,Real.rpow_zero]
  have hsm : s 1 < 1/1296 := by
    have hh := mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hp delta)
    rw [hexp] at hh
    have hs1 : 0 < s 1 := hs 1
    nlinarith
  have hlast : 6 < s 2 := by
    by_contra h
    have hh : s 2 ≤ 6 := le_of_not_gt h
    have h01 : s 0*s 1 ≤ (s 1)^2 := by nlinarith [hmon.1,hs 1]
    have h012 := mul_le_mul h01 hh (hs 2).le (sq_nonneg (s 1))
    rw [Fin.prod_univ_three] at hlower'
    have hsq := mul_nonneg (hs 1).le (sub_nonneg.mpr hsm.le)
    nlinarith [hs 1]
  have hr := dualFrame3_source_real_bound G c u hu (cofactorRealMatrix3 k₀)
    (by rw [cofactorRealMatrix3_det]; norm_num) s A hs hA hpoint hprod
  have hg := cofactor_sourceDual_frame_gauge_bound3 k₀ G.index
    (((dualFrameRelativeIndex3 G u*G.index : ℕ) : ℝ)) (s 2) A hD hA
    (fun j => (u j : IntegerTriple)) 2 (fun i => hr i 2)
  rw [cofactor_sourceDualBody3_eq_parallelepiped k₀ G.index A hD hA,mem_parallelepipedBody3_iff]
  have he : rationalTripleReal3 (fun i => (((dualFrameRelativeIndex3 G u*G.index : ℕ) : ℚ)*
      dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i)) =
      fun i => (((dualFrameRelativeIndex3 G u*G.index : ℕ) : ℝ))*
        (dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i : ℝ) := by
    ext i
    simp [rationalTripleReal3]
  rw [he]
  apply hg.trans
  rw [← div_eq_mul_inv]
  exact (div_le_one (hs 2)).mpr hlast.le

theorem cofactor_sourceDual_power_cutoff3 (delta : ℝ) (hd : 0 < delta)
    (k : Fin 3) (v : IntegerTriple) :
    ∃ B : ℝ, ∀ Q : ℝ, B < Q → 1 < Q →
      1296 < Q^delta ∧ ∀ i, 216*|(cofactorDualInt3 k v i : ℝ)| ≤ Q^(delta/2) := by
  let C := 1296 + ∑ i : Fin 3, 216*|(cofactorDualInt3 k v i : ℝ)|
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < delta/2 by linarith)).eventually
      (Filter.eventually_gt_atTop C))
  refine ⟨B,?_⟩
  intro Q hBQ hQ
  have hc := hB Q hBQ.le
  have hsum : 0 ≤ ∑ i : Fin 3, 216*|(cofactorDualInt3 k v i : ℝ)| := by positivity
  have hmono : Q^(delta/2) ≤ Q^delta :=
    Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
  refine ⟨by dsimp [C] at hc; linarith,?_⟩
  intro i
  have hi : 216*|(cofactorDualInt3 k v i : ℝ)| ≤
      ∑ j : Fin 3, 216*|(cofactorDualInt3 k v j : ℝ)| :=
    Finset.single_le_sum (f := fun j => (216 : ℝ)*|(cofactorDualInt3 k v j : ℝ)|) (fun _ _ => by positivity) (Finset.mem_univ i)
  dsimp [C] at hc
  linarith

theorem cofactor_sourceReal_fixed_reference_line3 (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ) (hQ : 1 < Q)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (A : Fin 3 → ℝ) (hA : ∀ i, 0 < A i)
    (hnorm : (∏ i, A i*Q^(c₂ i)*Q^(c₃ i)) = 1)
    (S : Set (Fin 3 → Fin 3)) (hS : S = sourceTupleSet3 Q delta A c₂ c₃)
    (v : IntegerTriple) (hv : v ≠ 0)
    (hzero : ∀ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s (fun i => (v i : ℚ)) = 0)
    (hlarge : 1296 < Q^delta)
    (hcoeff : ∀ i, 216*|(cofactorDualInt3 k₀ v i : ℝ)| ≤ Q^(delta/2))
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → cofactorSourceLattice3 k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (cofactorSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA)
      (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) j)
    (hsmall : successiveRadius3 B (archCoordinates3 (cofactorRealCoordinates3 k₀) A hA) 1 < Q^(-delta)) :
    Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} =
      Submodule.span ℚ {fun i => (v i : ℚ)} := by
  classical
  let G := cofactorSourceLattice3 k₂ k₃ Q c₂ c₃
  obtain ⟨c⟩ : Nonempty (Basis (Fin 3) ℤ G) := mixedCongruence3_has_basis _ _ _ _
  have hc := mixedCongruence3_basis_real_independent _ _ (cofactorIntegerMatrix3_isUnit k₂)
    (cofactorIntegerMatrix3_isUnit k₃) _ _ c
  have hcQ := dualFrameMatrix3_rational_independent (fun j => (c j : IntegerTriple)) hc
  have huQ := dualFrameMatrix3_rational_independent (fun j => (u j : IntegerTriple)) hu
  have hD : G.index ≠ 0 := by
    rw [(cofactorSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.1]
    unfold qCongruenceIndex3
    positivity
  have hpD : (0 : ℝ) < G.index := by exact_mod_cast Nat.pos_of_ne_zero hD
  let q : ℚ := ((dualFrameRelativeIndex3 G u*G.index : ℕ) : ℚ)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast mul_ne_zero (Nat.ne_of_gt (dualFrameRelativeIndex3_pos G c u hu)) hD
  let x : Fin 3 → ℚ := fun i => q*dualFrameVector3 (fun j => (u j : IntegerTriple)) 2 i
  obtain ⟨z,hz,hxz⟩ := source_scaled_last_dual_nonzero3 G c u hu
  have hx : x ≠ 0 := by
    rw [show x = fun i => (z i : ℚ) from hxz]
    intro h
    apply hz
    ext i
    have hh := congrFun h i
    change (z i : ℚ) = 0 at hh
    exact_mod_cast hh
  let t : ℤ := 2 ^ (2-cofactor_sourceDualFloorMin3 2 k₂ Q c₂ v hv).toNat *
    3 ^ (2-cofactor_sourceDualFloorMin3 3 k₃ Q c₃ v hv).toNat
  let y : Fin 3 → ℚ := fun i => ((t • v) i : ℚ)
  obtain ⟨ht,hyL⟩ := cofactor_sourceDual_rescale_mem3 k₂ k₃ Q hQ c₂ c₃ hc₂ hc₃ v hv c hcQ
  have hy : y ≠ 0 := by
    intro h
    apply hv
    ext i
    have hh := congrFun h i
    have hmul : (t : ℚ)*(v i : ℚ) = 0 := by
      simpa only [y,Pi.smul_apply,smul_eq_mul,Int.cast_mul,Pi.zero_apply] using hh
    have htQ : (t : ℚ) ≠ 0 := by dsimp [t]; exact_mod_cast ht
    exact_mod_cast (mul_eq_zero.mp hmul).resolve_left htQ
  have hxL := dualFrameVector3_source_basis_mem G c hcQ u huQ 2
  have hxB := cofactor_sourceReal_last_dual_body3 k₀ k₂ k₃ Q delta hQ c₂ c₃ hc₂ hc₃ A hA hnorm B u hB hu hatt hsmall hlarge c
  have hyB := cofactor_sourceDual_two_case_body3 k₀ k₂ k₃ Q delta hQ A c₂ c₃ hA hc₂ hc₃ S hS v hv hzero hcoeff
  have hsep := cofactor_sourceReal_dual_second_gt_one3 k₀ k₂ k₃ Q delta hQ c₂ c₃ hc₂ hc₃ A hA B u hB hu hatt hsmall hlarge c hc hD
  let Bs := sourceDualBasis3 G c hc hD
  let es := cofactor_sourceDualCoordinates3 k₀ G.index A hpD hA
  have hxL' : rationalTripleReal3 x ∈ lattice3 Bs := by
    rw [sourceDualBasis3_lattice]
    exact ⟨x,hxL,rfl⟩
  have hyL' : rationalTripleReal3 y ∈ lattice3 Bs := by
    rw [sourceDualBasis3_lattice]
    exact ⟨y,hyL,rfl⟩
  have hxB' : rationalTripleReal3 x ∈ parallelepipedBody3 es := by
    rw [← cofactor_sourceDualBody3_eq_parallelepiped]
    exact hxB
  have hyB' : rationalTripleReal3 y ∈ parallelepipedBody3 es := by
    rw [← cofactor_sourceDualBody3_eq_parallelepiped]
    exact hyB
  obtain ⟨r,hr⟩ := sourceDual_body_proportional3 Bs es hsep x y hy hxL' hyL' hxB' hyB'
  have hrnz : r ≠ 0 := by intro h; apply hx; rw [hr,h,zero_smul]
  have htQ : (t : ℚ) ≠ 0 := by dsimp [t]; exact_mod_cast ht
  have hyEq : y = (t : ℚ) • (fun i => (v i : ℚ)) := by ext i; simp [y,Pi.smul_apply,smul_eq_mul]
  change Submodule.span ℚ {dualFrameVector3 (fun j => (u j : IntegerTriple)) 2} = _
  calc
    _ = Submodule.span ℚ {x} := (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hq) _).symm
    _ = Submodule.span ℚ {y} := by rw [hr,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hrnz)]
    _ = _ := by rw [hyEq,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr htQ)]

theorem cofactor_source_fixed_dual_direction3 (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₂ c₃ : Fin 3 → ℝ) (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0)
    (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega)
    (A : ℝ → Fin 3 → ℝ) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (hA : ∀ Q ∈ Omega, ∀ i, 0 < A Q i)
    (hcut : ∀ Q ∈ Omega, ∀ i, A Q i < Q ∧ (A Q i)⁻¹ < Q)
    (hnorm : ∀ Q ∈ Omega, (∏ i, A Q i*Q^(c₂ i)*Q^(c₃ i)) = 1)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (cofactorSourceLattice3 k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j,
      coordinateGauge3 (archCoordinates3 (cofactorRealCoordinates3 k₀) (A Q.val) (hA Q.val Q.property))
        (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q)
        (archCoordinates3 (cofactorRealCoordinates3 k₀) (A Q.val) (hA Q.val Q.property)) j)
    (hsmall : ∀ Q : Omega, successiveRadius3 (B Q)
      (archCoordinates3 (cofactorRealCoordinates3 k₀) (A Q.val) (hA Q.val Q.property)) 1 < Q.val^(-delta)) :
    ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ U : Set ℝ, U ⊆ Omega ∧ ¬ BddAbove U ∧
      ∀ Q : Omega, Q.val ∈ U →
        Submodule.span ℚ {dualFrameVector3 (fun j => (u Q j : IntegerTriple)) 2} =
          Submodule.span ℚ {fun i => (v i : ℚ)} := by
  classical
  obtain ⟨S,hS,U,hUOmega,hU,hpattern⟩ := sourceTupleSet3_unbounded_selection Omega hOmega delta A c₂ c₃
    (fun Q hm => sourceTupleSet3_nonempty Q delta (hQ Q hm) hd (A Q) c₂ c₃ (hA Q hm) (hnorm Q hm))
  obtain ⟨Q0,hQ0,hzero⟩ := cofactor_sourceReal_uniform_selected_vanishing3 k₀ k₂ k₃ S hS delta hd
  obtain ⟨Q1,hQ1,hQ1cut⟩ := not_bddAbove_iff'.mp hU Q0
  let q1 : Omega := ⟨Q1,hUOmega hQ1⟩
  let G1 := cofactorSourceLattice3 k₂ k₃ Q1 c₂ c₃
  obtain ⟨c1⟩ : Nonempty (Basis (Fin 3) ℤ G1) := mixedCongruence3_has_basis _ _ _ _
  obtain ⟨v,hv,hveq⟩ := source_scaled_last_dual_nonzero3 G1 c1 (u q1) (hu q1)
  have hvzero : ∀ s ∈ S, cofactorSelectedProduct3 k₀ k₂ k₃ s (fun i => (v i : ℚ)) = 0 := by
    intro s hs
    rw [← hveq]
    exact hzero Q1 (lt_of_not_ge hQ1cut) (hQ Q1 q1.property) (A Q1) c₂ c₃ (hA Q1 q1.property)
      hc₂ hc₃ (hcut Q1 q1.property) (hnorm Q1 q1.property)
      (by rw [hpattern Q1 hQ1]) (B q1) (u q1) (hB q1) (hu q1) (hatt q1) (hsmall q1) s hs
  obtain ⟨C,hC⟩ := cofactor_sourceDual_power_cutoff3 delta hd k₀ v
  refine ⟨v,hv,{Q | Q ∈ U ∧ C < Q},fun _ h => hUOmega h.1,sourceDual_unbounded_tail3 U hU C,?_⟩
  intro Q hQU
  obtain ⟨hlarge,hcoeff⟩ := hC Q.val hQU.2 (hQ Q.val Q.property)
  exact cofactor_sourceReal_fixed_reference_line3 k₀ k₂ k₃ Q.val delta (hQ Q.val Q.property) c₂ c₃
    (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) (A Q.val) (hA Q.val Q.property)
    (hnorm Q.val Q.property) S (hpattern Q.val hQU.1).symm v hv hvzero hlarge hcoeff
    (B Q) (u Q) (hB Q) (hu Q) (hatt Q) (hsmall Q)

end
end JSP000334
