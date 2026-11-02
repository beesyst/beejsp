import SubspaceBridge.SchlickeweiEquation4106
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiEquation4116
open SourceLocalUpper6 SourceHeightBounds6 Auxiliary6.SourceExpansion SourceWeights
open SchlickeweiDualVanishing6 SourceProper6 SchlickeweiEquation4106

theorem padic_minor_bound6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ_[p]) (f : Fin 5 → ℤ)
    (hA : ∀ j k, ‖A j k‖ ≤ (p : ℝ) ^ f k) :
    ‖A.det‖ ≤ (p : ℝ) ^ (∑ k, f k) := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hprod (s : Finset (Fin 5)) : (∏ k ∈ s, (p : ℝ) ^ f k) =
      (p : ℝ) ^ (∑ k ∈ s, f k) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.prod_insert, Finset.sum_insert, ha, ih, zpow_add₀ hp]
  calc
    _ ≤ ∏ k, (p : ℝ) ^ f k := padic_det5_le p A _ (fun k => zpow_nonneg (by positivity) _) hA
    _ = _ := hprod Finset.univ

def sourceExponent6 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 6) : ℤ :=
  -(Nat.ceil (JSP000334.qThreshold p q (pairWeights42 c i)) : ℤ)

theorem local_integer_exponent6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (q : ℝ) (c : Fin 4 → ℝ) (z : Fin 6 → ℤ) :
    z ∈ directLocal42 p A (fun j => JSP000334.qThreshold p q (c j)) ↔
      ∀ i, ‖(finiteMatrix p A *ᵥ (fun k => (z k : ℚ_[p]))) i‖ ≤
        (p : ℝ) ^ sourceExponent6 p q c i := by
  rw [directLocal42_spec]
  apply forall_congr'
  intro i
  rw [finite_form_norm, ← qThreshold_add42]
  simp only [sourceExponent6, pairWeights42, zpow_neg, zpow_natCast]
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rfl

open SourceReadiness6
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_first_five_integer_bounds6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    (∀ (j : Fin 5) i, ‖(finiteMatrix 2 A2 *ᵥ
      (fun k => ((R.w q j.castSucc : Fin 6 → ℤ) k : ℚ_[2]))) i‖ ≤
        (2 : ℝ) ^ sourceExponent6 2 q.val c2 i) ∧
    (∀ (j : Fin 5) i, ‖(finiteMatrix 3 A3 *ᵥ
      (fun k => ((R.w q j.castSucc : Fin 6 → ℤ) k : ℚ_[3]))) i‖ ≤
        (3 : ℝ) ^ sourceExponent6 3 q.val c3 i) := by
  constructor
  · intro j
    exact (local_integer_exponent6 2 A2 q.val c2 _).mp (R.w q j.castSucc).property.1
  · intro j
    exact (local_integer_exponent6 3 A3 q.val c3 _).mp (R.w q j.castSucc).property.2

theorem source_exponent_rescaling6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (i : Fin 6) :
    sourceExponent6 2 q.val c2 i =
      -(Nat.ceil (JSP000334.qThreshold 2 (q.val ^ (11 : ℕ)) (R.c 1 i)) : ℤ) ∧
    sourceExponent6 3 q.val c3 i =
      -(Nat.ceil (JSP000334.qThreshold 3 (q.val ^ (11 : ℕ)) (R.c 2 i)) : ℤ) := by
  rw [(R.finite_weights i).1, (R.finite_weights i).2]
  simp only [sourceExponent6, finiteWeight, davenport_rescaled_threshold42]
  trivial

theorem source_exponent_nonpos6 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 6) :
    sourceExponent6 p q c i ≤ 0 := neg_nonpos.mpr (Int.natCast_nonneg _)

theorem mapped_det_one6 {K : Type*} [CommRing K]
    (B : Matrix (Fin 6) (Fin 6) ℚ) (f : ℚ →+* K) (hB : B.det = 1) :
    (B.map f).det = 1 := by
  have hm : f.mapMatrix B = B.map f := by
    ext i j
    rfl
  have hd : f B.det = (B.map f).det :=
    (f.map_det B).trans (congrArg Matrix.det hm)
  rw [hB, map_one] at hd
  exact hd.symm

open Auxiliary6.SourceExpansion

theorem finite_matrix_det_one6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
    (finiteMatrix p A).det = 1 := by
  have hc := compound42_det_one A hA
  unfold finiteMatrix
  with_reducible exact mapped_det_one6 (compound A) (algebraMap ℚ ℚ_[p]) hc


theorem padic_frame_minor6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (f : Fin 6 → ℤ)
    (hv : ∀ (j : Fin 5) k, ‖(B *ᵥ (fun a => (v j.castSucc a : ℚ_[p]))) k‖ ≤
      (p : ℝ) ^ f k) (i : Fin 6) :
    ‖((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k)) := by
  apply padic_minor_bound6 p _ (fun k => f (i.succAbove k))
  intro j k
  change ‖transformedFrame6 B v j.castSucc (i.succAbove k)‖ ≤ _
  rw [transformedFrame6_apply]
  exact hv j _

theorem source_finite_minors6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (i : Fin 6) :
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    (‖((transformedFrame6 (finiteMatrix 2 A2) v).submatrix Fin.castSucc i.succAbove).det‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 2 q.val c2 (i.succAbove k))) ∧
    (‖((transformedFrame6 (finiteMatrix 3 A3) v).submatrix Fin.castSucc i.succAbove).det‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 3 q.val c3 (i.succAbove k))) := by
  dsimp only
  have hf := source_first_five_integer_bounds6 R q
  let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
  have h2 := padic_frame_minor6 2 (finiteMatrix 2 A2) v (sourceExponent6 2 q.val c2) hf.1 i
  have h3 := padic_frame_minor6 3 (finiteMatrix 3 A3) v (sourceExponent6 3 q.val c3) hf.2 i
  simp only [Nat.cast_ofNat] at h2 h3
  constructor
  · with_reducible exact h2
  · with_reducible exact h3

theorem last_dual_finite_minor6 {K : Type*} [NormedField K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (hB : B.det = 1)
    (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (i : Fin 6) :
    ‖(v.det : K)‖ * ‖dualFormValue6 B (dualVector6 v hv) i‖ =
      ‖((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det‖ := by
  have hc (k : Fin 6) : (rawNormal6 v k : K) =
      (v.det : K) * algebraMap ℚ K (dualVector6 v hv k) := by
    have h := congrArg (algebraMap ℚ K) (last_dual_adjugate6 v hv k)
    simpa only [map_mul, map_intCast] using h
  have hs := transformed_minor_cofactor6 B v (rawNormal6 v) 1
    (fun k => by simp) i
  have hvv : cofactorValue6 B (rawNormal6 v) i =
      (v.det : K) * rationalValue6 B (dualVector6 v hv) i := by
    simp only [cofactorValue6, rationalValue6, hc, Finset.mul_sum, mul_assoc]
  let D : Fin 6 → ℚ := dualVector6 v hv
  have he : rationalValue6 B (dualVector6 v hv) i = dualFormValue6 B (dualVector6 v hv) i := by
    with_reducible exact cofactor_dualForm6 B hB D i
  rw [Int.cast_one, one_mul, hvv, he] at hs
  have hn := congrArg (fun x : K => ‖x‖) hs
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using hn.symm

theorem norm_natAbs_cast6 {K : Type*} [NormedField K] (z : ℤ) :
    ‖(z.natAbs : K)‖ = ‖(z : K)‖ := by
  rcases Int.natAbs_eq z with h | h
  · simpa only [Int.cast_natCast] using (congrArg (fun a : ℤ => ‖(a : K)‖) h).symm
  · simpa only [Int.cast_neg, Int.cast_natCast, norm_neg] using
      (congrArg (fun a : ℤ => ‖(a : K)‖) h).symm

theorem scaled_last_dual_minor6 {K : Type*} [NormedField K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (hB : B.det = 1)
    (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (N : ℕ) (hN : N = v.det.natAbs) (i : Fin 6) :
    ‖∑ k, ((N : K) * algebraMap ℚ K (dualVector6 v hv k)) * B⁻¹.transpose i k‖ =
      ‖((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det‖ := by
  have he : (∑ k, ((N : K) * algebraMap ℚ K (dualVector6 v hv k)) * B⁻¹.transpose i k) =
      (N : K) * dualFormValue6 B (dualVector6 v hv) i := by
    simp only [dualFormValue6, Finset.mul_sum, mul_assoc]
  rw [he, norm_mul, hN, norm_natAbs_cast6]
  exact last_dual_finite_minor6 B hB v hv i

theorem source_integer_scale6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let J := SourceRelativeIndex6.frameRelativeIndex G (R.w q)
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    ZLattice.covolume (integerRealImage G) = (G.index : ℝ) ∧
      J * G.index = v.det.natAbs ∧
      ((J * G.index : ℕ) : ℝ) = (J : ℝ) * ZLattice.covolume (integerRealImage G) := by
  dsimp only
  obtain ⟨b⟩ := directCompoundGroup42_has_basis A2 A3 q.val c2 c3
  have hd := integerRealImage_covolume_index _ b
  have hn := SourceRelativeIndex6.source_frame_normalization6 R q
  refine ⟨hd, ?_, ?_⟩
  · with_reducible exact hn.2.2.1
  · rw [hd, Nat.cast_mul]
end CompoundFeasibility.SchlickeweiEquation4116

#check CompoundFeasibility.SchlickeweiEquation4116.padic_minor_bound6
#print CompoundFeasibility.SchlickeweiEquation4116.padic_minor_bound6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.padic_minor_bound6

#check CompoundFeasibility.SchlickeweiEquation4116.local_integer_exponent6
#print CompoundFeasibility.SchlickeweiEquation4116.local_integer_exponent6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.local_integer_exponent6

#check CompoundFeasibility.SchlickeweiEquation4116.source_first_five_integer_bounds6
#print CompoundFeasibility.SchlickeweiEquation4116.source_first_five_integer_bounds6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_first_five_integer_bounds6

#check CompoundFeasibility.SchlickeweiEquation4116.source_exponent_rescaling6
#print CompoundFeasibility.SchlickeweiEquation4116.source_exponent_rescaling6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_exponent_rescaling6

#check CompoundFeasibility.SchlickeweiEquation4116.source_exponent_nonpos6
#print CompoundFeasibility.SchlickeweiEquation4116.source_exponent_nonpos6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_exponent_nonpos6

#check CompoundFeasibility.SchlickeweiEquation4116.mapped_det_one6
#print CompoundFeasibility.SchlickeweiEquation4116.mapped_det_one6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.mapped_det_one6

#check CompoundFeasibility.SchlickeweiEquation4116.finite_matrix_det_one6
#print CompoundFeasibility.SchlickeweiEquation4116.finite_matrix_det_one6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.finite_matrix_det_one6

#check CompoundFeasibility.SchlickeweiEquation4116.padic_frame_minor6
#print CompoundFeasibility.SchlickeweiEquation4116.padic_frame_minor6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.padic_frame_minor6

#check CompoundFeasibility.SchlickeweiEquation4116.source_finite_minors6
#print CompoundFeasibility.SchlickeweiEquation4116.source_finite_minors6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_finite_minors6

#check CompoundFeasibility.SchlickeweiEquation4116.last_dual_finite_minor6
#print CompoundFeasibility.SchlickeweiEquation4116.last_dual_finite_minor6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.last_dual_finite_minor6

#check CompoundFeasibility.SchlickeweiEquation4116.norm_natAbs_cast6
#print CompoundFeasibility.SchlickeweiEquation4116.norm_natAbs_cast6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.norm_natAbs_cast6

#check CompoundFeasibility.SchlickeweiEquation4116.scaled_last_dual_minor6
#print CompoundFeasibility.SchlickeweiEquation4116.scaled_last_dual_minor6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.scaled_last_dual_minor6

#check CompoundFeasibility.SchlickeweiEquation4116.source_integer_scale6
#print CompoundFeasibility.SchlickeweiEquation4116.source_integer_scale6
#print axioms CompoundFeasibility.SchlickeweiEquation4116.source_integer_scale6
