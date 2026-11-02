import SubspaceBridge.AlgebraicLiouville6
import SubspaceBridge.OriginalDeformation4
import SubspaceBridge.OriginalAuxiliaryDual4
import SubspaceBridge.SourceRelativeIndex6

open scoped BigOperators Matrix
noncomputable section
namespace CompoundFeasibility

theorem liouville4_literal174_common_field (a : Fin 4 → Fin 4 → ℝ)
    (ha : ∀ s i, IsAlgebraic ℚ (a s i)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∀ s i, a s i ∈ K := by
  let S : Set ℝ := Set.range (fun p : Fin 4 × Fin 4 => a p.1 p.2)
  let K := IntermediateField.adjoin ℚ S
  haveI : Finite S := Set.finite_range _
  have hfin : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨⟨s,i⟩,rfl⟩
    exact (ha s i).isIntegral)
  exact ⟨K,hfin,fun s i => IntermediateField.subset_adjoin ℚ S ⟨(s,i),rfl⟩⟩

theorem liouville4_literal174_common_denominator (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (b : Fin 4 → Fin 4 → K) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ s i, IsIntegral ℤ ((M : K) * b s i) := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  haveI : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).mpr inferInstance
  obtain ⟨M,hM,hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun p : Fin 4 × Fin 4 => b p.1 p.2))
  refine ⟨M,hM,fun s i => ?_⟩
  simpa only [Algebra.smul_def,eq_intCast] using hi (b s i) (Finset.mem_image.mpr ⟨(s,i),Finset.mem_univ _,rfl⟩)

theorem liouville4_literal174_conjugate_height (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (b : Fin 4 → Fin 4 → K) :
    ∃ B : ℝ, 0 < B ∧ ∀ (sigma : K →ₐ[ℚ] ℂ) s (z : Fin 4 → ℤ),
      ‖sigma (∑ i, b s i * (z i : K))‖ ≤
        B * max 1 ‖(fun i => (z i : ℝ))‖ := by
  classical
  let B := max 1 (∑ sigma : K →ₐ[ℚ] ℂ, ∑ s : Fin 4, ∑ i : Fin 4, ‖sigma (b s i)‖)
  refine ⟨B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro sigma s z
  have hrow : (∑ i : Fin 4, ‖sigma (b s i)‖) ≤ B := by
    apply le_trans _ (le_max_right _ _)
    have hs : (∑ i : Fin 4, ‖sigma (b s i)‖) ≤ ∑ t : Fin 4, ∑ i : Fin 4, ‖sigma (b t i)‖ :=
      Finset.single_le_sum (s := Finset.univ) (f := fun t : Fin 4 => ∑ i : Fin 4, ‖sigma (b t i)‖) (fun t _ => Finset.sum_nonneg (fun i _ => norm_nonneg _)) (Finset.mem_univ s)
    have ht : (∑ t : Fin 4, ∑ i : Fin 4, ‖sigma (b t i)‖) ≤ ∑ tau : K →ₐ[ℚ] ℂ, ∑ t : Fin 4, ∑ i : Fin 4, ‖tau (b t i)‖ :=
      Finset.single_le_sum (s := Finset.univ) (f := fun tau : K →ₐ[ℚ] ℂ => ∑ t : Fin 4, ∑ i : Fin 4, ‖tau (b t i)‖) (fun t _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => norm_nonneg _))) (Finset.mem_univ sigma)
    exact hs.trans ht
  have hi (i : Fin 4) : |(z i : ℝ)| ≤ max 1 ‖(fun i => (z i : ℝ))‖ := by
    have hh : |(z i : ℝ)| ≤ ‖(fun i => (z i : ℝ))‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (z i : ℝ)) i
    exact hh.trans (le_max_right _ _)
  calc
    ‖sigma (∑ i, b s i * (z i : K))‖ = ‖∑ i, sigma (b s i) * (z i : ℂ)‖ := by simp only [map_sum,map_mul,map_intCast]
    _ ≤ ∑ i : Fin 4, ‖sigma (b s i)‖ * |(z i : ℝ)| := by simpa only [norm_mul,Complex.norm_intCast] using norm_sum_le (s := Finset.univ) (f := fun i => sigma (b s i) * (z i : ℂ))
    _ ≤ ∑ i : Fin 4, ‖sigma (b s i)‖ * max 1 ‖(fun i => (z i : ℝ))‖ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (norm_nonneg _)
    _ = (∑ i : Fin 4, ‖sigma (b s i)‖) * max 1 ‖(fun i => (z i : ℝ))‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ B * max 1 ‖(fun i => (z i : ℝ))‖ := mul_le_mul_of_nonneg_right hrow (le_trans zero_le_one (le_max_left _ _))

theorem liouville4_literal174_field_liouville (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (b : Fin 4 → Fin 4 → K) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ s (z : Fin 4 → ℤ),
      (∑ i, (b s i : ℝ) * (z i : ℝ)) ≠ 0 →
      C ≤ |∑ i, (b s i : ℝ) * (z i : ℝ)| * (max 1 ‖(fun i => (z i : ℝ))‖)^D := by
  classical
  obtain ⟨M,hM,hint⟩ := liouville4_literal174_common_denominator K b
  let c : Fin 4 → Fin 4 → K := fun s i => (M : K) * b s i
  obtain ⟨B,hB,hheight⟩ := liouville4_literal174_conjugate_height K c
  let sigma0 : K →ₐ[ℚ] ℂ := (IsScalarTower.toAlgHom ℚ ℝ ℂ).comp K.val
  let D := Fintype.card (K →ₐ[ℚ] ℂ) - 1
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hden : 0 < |(M : ℝ)| * B^D := mul_pos (abs_pos.mpr hMr) (pow_pos hB _)
  refine ⟨(|(M : ℝ)| * B^D)⁻¹,inv_pos.mpr hden,D,?_⟩
  intro s z hz
  let beta : K := ∑ i, c s i * (z i : K)
  have hb : IsIntegral ℤ beta := IsIntegral.sum _ (fun i _ =>
    (hint s i).mul (isIntegral_algebraMap : IsIntegral ℤ ((algebraMap ℤ K) (z i))))
  have he : sigma0 beta = ((M : ℝ) * (∑ i, (b s i : ℝ) * (z i : ℝ)) : ℝ) := by
    simp [beta,c,sigma0,Finset.mul_sum,mul_assoc]
  have hb0 : beta ≠ 0 := by
    intro h
    have hh := he
    rw [h,map_zero] at hh
    have hh' : (M : ℝ) * (∑ i, (b s i : ℝ) * (z i : ℝ)) = 0 := by
      exact_mod_cast hh.symm
    exact (mul_ne_zero hMr hz) hh'
  have hp := liouville6_integral_norm_lower K beta hb hb0
  rw [liouville6_norm_product] at hp
  rw [← Finset.mul_prod_erase Finset.univ (fun sigma : K →ₐ[ℚ] ℂ => ‖sigma beta‖)
    (Finset.mem_univ sigma0)] at hp
  have hrest : (∏ sigma ∈ Finset.univ.erase sigma0, ‖sigma beta‖) ≤
      (B * max 1 ‖(fun i => (z i : ℝ))‖)^D := by
    calc
      _ ≤ ∏ _sigma ∈ Finset.univ.erase sigma0, B * max 1 ‖(fun i => (z i : ℝ))‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun sigma _ => hheight sigma s z)
      _ = _ := by rw [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ sigma0)]; rfl
  have htotal : 1 ≤ (|(M : ℝ)| * B^D) *
      (|∑ i, (b s i : ℝ) * (z i : ℝ)| * (max 1 ‖(fun i => (z i : ℝ))‖)^D) := by
    calc
      1 ≤ ‖sigma0 beta‖ * (∏ sigma ∈ Finset.univ.erase sigma0, ‖sigma beta‖) := hp
      _ ≤ ‖sigma0 beta‖ * (B * max 1 ‖(fun i => (z i : ℝ))‖)^D :=
        mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
      _ = _ := by rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul,mul_pow]; ring
  rw [← one_div]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)

theorem algebraic_fin4_literal174_liouville_lower
    (a : Fin 4 → Fin 4 → ℝ) (ha : ∀ s i, IsAlgebraic ℚ (a s i)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ s : Fin 4, ∀ z : Fin 4 → ℤ,
      (∑ i, a s i * (z i : ℝ)) ≠ 0 →
      C ≤ |∑ i, a s i * (z i : ℝ)| * (max 1 ‖integerReal z‖)^D := by
  obtain ⟨K,hK,hmem⟩ := liouville4_literal174_common_field a ha
  letI : FiniteDimensional ℚ K := hK
  let b : Fin 4 → Fin 4 → K := fun s i => ⟨a s i,hmem s i⟩
  exact liouville4_literal174_field_liouville K b

end CompoundFeasibility

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalDeformedFrame4Literal174
open OriginalDeformation4 OriginalLastDual4 OriginalAuxiliaryDual4

theorem exists_deformed_attaining4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) :
    ∃ w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ)) ∧
      ∃ hw : LinearIndependent ℚ (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)),
      (∀ j, 0 < originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) ∧
      Monotone (originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd) ∧
      (∀ j, coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
        (integerReal (w j : Fin 4 → ℤ)) =
        originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) ∧
      lastDual4 (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)) hw ≠ 0 := by
  let b := sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd
  obtain ⟨v,hv,hmem,hpos,hmono,hatt⟩ := exists_successive_minima4 b e
  have hlift (j : Fin 4) : ∃ z : originalSourceGroup4 A2 A3 Q c2 c3,
      integerReal (z : Fin 4 → ℤ) = v j := by
    have hj := hmem j
    rw [sourceRealBasis4_span] at hj
    obtain ⟨z,hz,he⟩ := hj
    exact ⟨⟨z,hz⟩,he⟩
  choose w hw using hlift
  have hreal : LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ)) := by
    simpa only [hw] using hv
  have hrat := integral_frame_rational_independent (fun j => (w j : Fin 4 → ℤ)) hreal
  refine ⟨w,hreal,hrat,hpos,hmono,?_,lastDual4_nonzero _ hrat⟩
  intro j
  change coordinateGauge4 e (integerReal (w j : Fin 4 → ℤ)) = successiveRadius4 b e j
  rw [hw j]
  exact hatt j

theorem deformed_gauge_bounds4
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i)
    (x : Fin 4 → ℝ) (r : ℝ) :
    coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) x ≤ r ↔
      ∀ i, |(L *ᵥ x) i| ≤ r*deformedWidths4 Q c0 d sigma i := by
  rw [coordinateGauge4,pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro i
  rw [originalDeformedCoordinates4_apply,Real.norm_eq_abs,abs_div,abs_mul,
    abs_of_pos (hd _),abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _),
    div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)]
  dsimp [deformedWidths4]
  rw [← mul_div_assoc,le_div_iff₀ (hd _)]
  constructor <;> intro h <;> nlinarith

theorem frame_normalization4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c2 c3 : Fin 4 → ℝ)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ))) :
    let G := originalSourceGroup4 A2 A3 Q c2 c3
    let J := SourceRelativeIndex6.frameRelativeIndex G w
    let v : Matrix (Fin 4) (Fin 4) ℤ := fun j => (w j : Fin 4 → ℤ)
    Finite (G ⧸ Submodule.span ℤ (Set.range w)) ∧ 0 < J ∧
      J*G.index = v.det.natAbs ∧
      |(v.det : ℝ)| = (J : ℝ)*ZLattice.covolume (integerRealImage G) ∧
      v.det ≠ 0 ∧ 0 < ZLattice.covolume (integerRealImage G) := by
  obtain ⟨b⟩ := sourceLattice4_has_basis A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  have hwZ : LinearIndependent ℤ w := LinearIndependent.of_comp
    (integerReal.comp (originalSourceGroup4 A2 A3 Q c2 c3).subtype.toIntLinearMap)
    (hw.restrict_scalars' ℤ)
  letI : IsZLattice ℝ (integerRealImage (originalSourceGroup4 A2 A3 Q c2 c3)) := by
    dsimp [originalSourceGroup4]
    infer_instance
  exact ⟨(SourceRelativeIndex6.integer_span_index_det b w hwZ).1,
    SourceRelativeIndex6.frameRelativeIndex_pos _ b w hwZ,
    SourceRelativeIndex6.frameRelativeIndex_mul_index _ b w hwZ,
    SourceRelativeIndex6.frame_abs_det_covolume _ b w hwZ,
    integerFrame4_det_ne_zero _ (integral_frame_rational_independent _ hw),
    ZLattice.covolume_pos _ MeasureTheory.volume⟩


theorem deformed_frame_real_cofactor4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
      (integerReal (w j : Fin 4 → ℤ)) =
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j) (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℝ))) i‖ ≤
      6 * (∏ j : Fin 3, originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j.castSucc) *
        (∏ k : Fin 3, deformedWidths4 Q c0 d sigma (i.succAbove k)) := by
  apply real_cofactor_bound4 L hLdet _ _ _ _ i
  intro j k
  exact (deformed_gauge_bounds4 L hL Q hQ c0 d sigma hd _ _).mp (hatt j.castSucc).le k

theorem first_three_deformed_product4
    (mu : Fin 4 → ℝ) (hp : ∀ i, 0 < mu i) (hm : Monotone mu)
    (Q delta : ℝ) (hQ : 0 < Q) (hsmall : mu 2 < Q^(-delta)) :
    (∏ j : Fin 3, mu j.castSucc) < Q^(-3*delta) := by
  have hle : (∏ j : Fin 3, mu j.castSucc) ≤ (mu 2)^3 := by
    calc
      _ ≤ ∏ _j : Fin 3, mu 2 := Finset.prod_le_prod
        (fun j _ => (hp _).le) (fun j _ => hm (by change j.val ≤ 2; omega))
      _ = _ := by simp
  apply hle.trans_lt
  calc
    (mu 2)^3 < (Q^(-delta))^3 := pow_lt_pow_left₀ hsmall (hp 2).le (by decide)
    _ = Q^(-3*delta) := by rw [← Real.rpow_mul_natCast hQ.le]; congr 1; ring

theorem omitted_positive_widths4 (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i) (i : Fin 4) :
    (∏ k : Fin 3, A (i.succAbove k)) = (∏ k : Fin 4, A k)/A i := by
  rw [Fin.prod_univ_succAbove (fun k => A k) i]
  apply (eq_div_iff (hA i).ne').mpr
  ring

theorem deformed_cofactor_decay4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
      (integerReal (w j : Fin 4 → ℤ)) =
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j)
    (delta : ℝ)
    (hsmall : originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 <
      (Q^(5 : ℕ))^(-delta)) (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℝ))) i‖ <
      6 * ((∏ k : Fin 4, deformedWidths4 Q c0 d sigma k)/deformedWidths4 Q c0 d sigma i) *
        (Q^(5 : ℕ))^(-3*delta) := by
  obtain ⟨_,_,_,hp,hm,_⟩ := exists_successive_minima4
    (sourceRealBasis4 A2 A3 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))))
    (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
  have hprod := first_three_deformed_product4 _ hp hm _ delta (by positivity) hsmall
  change (∏ j : Fin 3, originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j.castSucc) <
    (Q^(5 : ℕ))^(-3*delta) at hprod
  have hbound := deformed_frame_real_cofactor4 A2 A3 L hL hLdet Q hQ c0 c2 c3 d sigma hd w hatt i
  rw [omitted_positive_widths4 _ (deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 d hd sigma) i] at hbound
  apply hbound.trans_lt
  have hW : 0 < (∏ k : Fin 4, deformedWidths4 Q c0 d sigma k)/deformedWidths4 Q c0 d sigma i :=
    div_pos (Finset.prod_pos (fun k _ => deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 d hd sigma k))
      (deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 d hd sigma i)
  nlinarith

theorem deformed_frame_finite_cofactor4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (Q : ℝ) (c2 c3 : Fin 4 → ℝ)
    (w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3) (i : Fin 4) :
    (‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℚ_[2]))) i‖ ≤
      (2 : ℝ)^(∑ k : Fin 3, -(Nat.ceil (JSP000334.qThreshold 2 Q (c2 (i.succAbove k))) : ℤ))) ∧
    (‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual4 (fun j => (w j : Fin 4 → ℤ)) k : ℚ_[3]))) i‖ ≤
      (3 : ℝ)^(∑ k : Fin 3, -(Nat.ceil (JSP000334.qThreshold 3 Q (c3 (i.succAbove k))) : ℤ))) := by
  exact ⟨finite_cofactor_bound4 2 A2 h2 _ _ (fun j => (w j).property.1) i,
    finite_cofactor_bound4 3 A3 h3 _ _ (fun j => (w j).property.2) i⟩

end CompoundFeasibility.OriginalDeformedFrame4Literal174

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174
open OriginalLastDual4 OriginalAuxiliaryDual4 OriginalDeformedFrame4Literal174 OriginalDeformation4

def primeProduct4 (e2 e3 : Fin 4 → ℕ) : ℕ := 2^(∑ i, e2 i)*3^(∑ i, e3 i)

def auxiliaryInteger4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ)
    (y : Fin 4 → ℤ) : Prop :=
  (∀ i, ‖(L⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i‖ ≤
    ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3))/A i) ∧
  (∀ i, ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[2]))) i‖ ≤
    (2 : ℝ)^(∑ k : Fin 3, -(e2 (i.succAbove k) : ℤ))) ∧
  (∀ i, ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[3]))) i‖ ≤
    (3 : ℝ)^(∑ k : Fin 3, -(e3 (i.succAbove k) : ℤ)))

theorem auxiliary_pairing_dvd4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (e : Fin 4 → ℕ) (x y : Fin 4 → ℤ) (hx : x ∈ lattice4 p A e)
    (hy : ∀ i, ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ)^(∑ k : Fin 3, -(e (i.succAbove k) : ℤ))) :
    (p : ℤ)^(∑ i, e i) ∣ integerPairing4 x y := by
  have hB : (A.map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
    rw [mapped_det_one4 A hA]
    exact one_ne_zero
  have h := native_ultrametric_pairing4 p _ hB (fun i => -(e i : ℤ)) x y
    (original_lattice_finite_bound4 p A e x hx) hy
  apply (SchlickeweiIntegerPairing6.integer_norm_dvd6 p _ (∑ i, e i)).mp
  simpa only [Finset.sum_neg_distrib,← Nat.cast_sum] using h

theorem auxiliary_pairing_primeProduct4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ)
    (x : sourceLattice4 A2 A3 e2 e3) (y : Fin 4 → ℤ)
    (hy : auxiliaryInteger4 A2 A3 L e2 e3 A y) :
    (primeProduct4 e2 e3 : ℤ) ∣ integerPairing4 (x : Fin 4 → ℤ) y := by
  have hcop : IsCoprime ((2 : ℤ)^(∑ i, e2 i)) ((3 : ℤ)^(∑ i, e3 i)) :=
    IsCoprime.pow (show IsCoprime (2 : ℤ) 3 from ⟨-1,1,by norm_num⟩)
  simpa only [primeProduct4,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    hcop.mul_dvd (auxiliary_pairing_dvd4 2 A2 h2 e2 _ y x.property.1 hy.2.1)
      (auxiliary_pairing_dvd4 3 A3 h3 e3 _ y x.property.2 hy.2.2)

theorem auxiliary_pairing_real4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det ≠ 0) (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (x y : Fin 4 → ℤ)
    (hx : ∀ i, |(L *ᵥ (fun k => (x k : ℝ))) i| ≤ epsilon*A i)
    (hy : auxiliaryInteger4 A2 A3 L e2 e3 A y) :
    ‖(integerPairing4 x y : ℝ)‖ ≤
      4*epsilon*ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) := by
  have hb := real_pairing_bound4 L hL x y (fun i => epsilon*A i)
    (fun i => ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3))/A i)
    (fun i => mul_nonneg he (hA i).le) (by simpa only [Real.norm_eq_abs] using hx) hy.1
  apply hb.trans_eq
  calc
    _ = ∑ _i : Fin 4, epsilon*ZLattice.covolume
        (integerRealImage (sourceLattice4 A2 A3 e2 e3)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hA i).ne']
      ring
    _ = _ := by simp; ring

theorem auxiliary_pairing_zero4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det ≠ 0)
    (e2 e3 : Fin 4 → ℕ) (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (K epsilon : ℝ) (he : 0 ≤ epsilon)
    (hcov : ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) ≤
      K*(primeProduct4 e2 e3 : ℝ)) (hsmall : 4*epsilon*K < 1)
    (x : sourceLattice4 A2 A3 e2 e3) (y : Fin 4 → ℤ)
    (hx : ∀ i, |(L *ᵥ (fun k => ((x : Fin 4 → ℤ) k : ℝ))) i| ≤ epsilon*A i)
    (hy : auxiliaryInteger4 A2 A3 L e2 e3 A y) :
    integerPairing4 (x : Fin 4 → ℤ) y = 0 := by
  have hP : 0 < primeProduct4 e2 e3 := by unfold primeProduct4; positivity
  have hPR : (0 : ℝ) < primeProduct4 e2 e3 := by exact_mod_cast hP
  have hbound := auxiliary_pairing_real4 A2 A3 L hL e2 e3 A hA epsilon he _ y hx hy
  have hle := mul_le_mul_of_nonneg_left hcov (show 0 ≤ 4*epsilon by positivity)
  have hlt := mul_lt_mul_of_pos_right hsmall hPR
  have hsmallreal : ‖(integerPairing4 (x : Fin 4 → ℤ) y : ℝ)‖ < (primeProduct4 e2 e3 : ℝ) := by
    nlinarith
  by_contra hz
  have hab := Int.natAbs_le_of_dvd_ne_zero
    (auxiliary_pairing_primeProduct4 A2 A3 L h2 h3 e2 e3 A x y hy) hz
  have habR : (primeProduct4 e2 e3 : ℝ) ≤ ‖(integerPairing4 (x : Fin 4 → ℤ) y : ℝ)‖ := by
    simpa only [Int.natAbs_natCast,Int.cast_natAbs,Int.cast_abs,Real.norm_eq_abs] using
      (show ((primeProduct4 e2 e3 : ℤ).natAbs : ℝ) ≤
        ((integerPairing4 (x : Fin 4 → ℤ) y).natAbs : ℝ) by exact_mod_cast hab)
  exact (not_lt_of_ge habR) hsmallreal

theorem rational_annihilator_line4 (w : Fin 4 → Fin 4 → ℚ)
    (hw : LinearIndependent ℚ w) (y : Fin 4 → ℚ)
    (hann : ∀ j : Fin 3, (∑ i, w j.castSucc i*y i) = 0) :
    y ∈ Submodule.span ℚ {lastDual4 w hw} := by
  let f : Module.Dual ℚ (Fin 4 → ℚ) := ∑ i, y i • LinearMap.proj i
  have hf : ∀ j : Fin 3, f (w j.castSucc) = 0 := by
    intro j
    simpa only [f,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,
      smul_eq_mul,mul_comm] using hann j
  have he := functional_lastDual4 w hw f hf
  have hy : y = f (w 3) • lastDual4 w hw := by
    funext i
    have hi := congrArg (fun g : Module.Dual ℚ (Fin 4 → ℚ) => g (Pi.single i 1)) he
    simpa [f,lastDual4,Pi.single_apply] using hi
  rw [hy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))


theorem source_auxiliary_line4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det ≠ 0)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ), T < Q → ∀ (hQ : 1 < Q) (c2 c3 A : Fin 4 → ℝ),
      (∀ i, 0 < A i) →
      ∀ w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3,
      ∀ hw : LinearIndependent ℚ (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)),
      (∀ (j : Fin 3) i, |(L *ᵥ (fun k => ((w j.castSucc : Fin 4 → ℤ) k : ℝ))) i| ≤
        (Q^(5 : ℕ))^(-delta)*A i) →
      ∀ y : Fin 4 → ℤ,
      auxiliaryInteger4 A2 A3 L
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))) A y →
      (∀ j : Fin 3, integerPairing4 (w j.castSucc : Fin 4 → ℤ) y = 0) ∧
      (fun i => (y i : ℚ)) ∈ Submodule.span ℚ {lastDual4 (fun j i => ((w j : Fin 4 → ℤ) i : ℚ)) hw} := by
  obtain ⟨K,hK,hindex⟩ := sourceLattice4_uniform_index_upper A2 A3 (sourceUnit42 A2 h2) (sourceUnit42 A3 h3)
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (4*(K : ℝ)) (2*delta) (by positivity)
  refine ⟨T,hT,?_⟩
  intro Q hTQ hQ c2 c3 A hA w hw hx y hy
  let e2 := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i))
  let e3 := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))
  have hcov : ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) ≤
      (K : ℝ)*(primeProduct4 e2 e3 : ℝ) := by
    rw [sourceLattice4_covolume_index]
    have h := hindex e2 e3
    have hn : (sourceLattice4 A2 A3 e2 e3).index ≤ K*primeProduct4 e2 e3 := by
      simpa only [primeProduct4,Nat.mul_assoc] using h
    exact_mod_cast hn
  have hQ5 : 1 < Q^(5 : ℕ) := one_lt_pow₀ hQ (by decide)
  have hQQ5 : Q ≤ Q^(5 : ℕ) := le_self_pow₀ hQ.le (by decide)
  have hsmall : 4*(Q^(5 : ℕ))^(-delta)*(K : ℝ) < 1 := by
    have hb : 4*(K : ℝ) < (Q^(5 : ℕ))^delta := by
      convert hcut (Q^(5 : ℕ)) (hTQ.trans_le hQQ5) using 1 <;> congr 1 <;> ring
    rw [Real.rpow_neg (zero_lt_one.trans hQ5).le]
    have he := (div_lt_one (Real.rpow_pos_of_pos (zero_lt_one.trans hQ5) delta)).mpr hb
    convert he using 1 <;> ring
  have hz (j : Fin 3) : integerPairing4 (w j.castSucc : Fin 4 → ℤ) y = 0 :=
    auxiliary_pairing_zero4 A2 A3 L h2 h3 hL e2 e3 A hA K _ (by positivity)
      hcov hsmall (w j.castSucc) y (hx j) hy
  refine ⟨hz,rational_annihilator_line4 _ hw _ ?_⟩
  intro j
  exact_mod_cast hz j

theorem source_prime_product_covolume4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (e2 e3 : Fin 4 → ℕ) :
    (primeProduct4 e2 e3 : ℝ) ≤ ZLattice.covolume (integerRealImage (sourceLattice4 A2 A3 e2 e3)) := by
  obtain ⟨b⟩ := sourceLattice4_has_basis A2 A3 e2 e3
  have h := integerRealImage_padic_covolume_lower (sourceLattice4 A2 A3 e2 e3) b A2 A3 e2 e3
    (fun x hx i => (lattice4_spec 2 A2 e2 x).mp hx.1 i)
    (fun x hx i => (lattice4_spec 3 A3 e3 x).mp hx.2 i)
  simpa only [primeProduct4,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,h2,h3,padicNorm.one,
    Rat.cast_one,one_mul] using h

theorem balanced_width_product_covolume4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (Q : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 4 → ℝ)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (∏ i, A i) ≤ ZLattice.covolume (integerRealImage (originalSourceGroup4 A2 A3 Q c2 c3)) := by
  have hQp := zero_lt_one.trans hQ
  have hp : 0 < ∏ i, Q^(c2 i+c3 i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos hQp _)
  have heq : (∏ i, A i) = (∏ i, Q^(-c2 i))*(∏ i, Q^(-c3 i)) := by
    have hinv : (∏ i, A i) = (∏ i, Q^(c2 i+c3 i))⁻¹ := by
      rw [← one_div]
      apply (eq_div_iff hp.ne').mpr
      simpa using hb
    rw [hinv]
    simp_rw [Real.rpow_add hQp,Real.rpow_neg hQp.le]
    rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,Finset.prod_inv_distrib]
    ring
  have hbound (p : ℕ) (hp : 1 < p) (c : ℝ) :
      Q^(-c) ≤ (p : ℝ)^Nat.ceil (JSP000334.qThreshold p Q c) := by
    rw [← JSP000334.qThreshold_rpow p hp Q c hQ,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
  rw [heq]
  apply le_trans _ (source_prime_product_covolume4 A2 A3 h2 h3 _ _)
  unfold primeProduct4
  push_cast
  rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul (Finset.prod_le_prod (fun i _ => (Real.rpow_pos_of_pos hQp _).le)
      (fun i _ => hbound 2 (by decide) (c2 i)))
    (Finset.prod_le_prod (fun i _ => (Real.rpow_pos_of_pos hQp _).le)
      (fun i _ => hbound 3 (by decide) (c3 i)))
    (Finset.prod_nonneg (fun i _ => (Real.rpow_pos_of_pos hQp _).le)) (by positivity)

end CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalDeformedSource4Literal174
open OriginalDeformation4 OriginalLastDual4 OriginalAuxiliaryDual4 OriginalDeformedFrame4Literal174 OriginalAuxiliaryGeometry4Literal174

structure DeformedAttaining4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3) where
  deformation_pos : ∀ i, 0 < gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) i
  sigma : Equiv.Perm (Fin 4)
  w : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3
  real_independent : LinearIndependent ℝ (fun j => integerReal (w j : Fin 4 → ℤ))
  rational_independent : LinearIndependent ℚ (fun j i => ((w j : Fin 4 → ℤ) i : ℚ))
  attaining : ∀ j, coordinateGauge4
    (originalDeformedCoordinates4 L hL Q hQ c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)
    (integerReal (w j : Fin 4 → ℤ)) = originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j
  minima_pos : ∀ j, 0 < originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j
  minima_mono : Monotone (originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)
  small : originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos 2 < (Q^(5 : ℕ))^(-(delta/24))
  widths_pos : ∀ i, 0 < deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i
  balance : (∏ i, deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i)*
    (∏ i, Q^(c2 i+c3 i)) = 1
  sizes : ∀ i, deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i < Q^(5 : ℕ) ∧
    (deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i)⁻¹ < Q^(5 : ℕ) ∧
    Q^(-c2 i) < Q^(5 : ℕ) ∧ Q^(-c3 i) < Q^(5 : ℕ)
  body : ∀ x, x ∈ parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos) ↔
    ∀ i, |(L *ᵥ x) i| ≤ deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma i
  volume : MeasureTheory.volume.real (parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0
    (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos)) =
    MeasureTheory.volume.real (originalBody4 L Q c0)
  comparison : ∀ j, gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) j*
    sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j/16 ≤
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
        (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos j ≤
      16*(gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) j*sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j)
  separation : ∀ j : Fin 4, ∀ z : originalSourceGroup4 A2 A3 Q c2 c3,
    integerReal (z : Fin 4 → ℤ) ∉ minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) j →
    gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3) j*sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j/16 ≤
      coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0
        (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) sigma deformation_pos) (integerReal (z : Fin 4 → ℤ))

theorem attaining_of_ready4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hready : deformationReady4 A2 A3 L hL Q hQ c0 c2 c3 delta u) :
    Nonempty (DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u) := by
  rcases hready with ⟨_,_,hd,hprod,hanti,hscaled,sigma,hpos,hbal,hcmp,hvol,hsep,_,_,hsmall,hsizes,hbody,_,_⟩
  obtain ⟨w,hreal,hrat,hp,hm,ha,_⟩ := exists_deformed_attaining4 A2 A3 L hL Q hQ c0 c2 c3 _ sigma hd
  exact ⟨⟨hd,sigma,w,hreal,hrat,ha,hp,hm,hsmall,hpos,hbal,hsizes,hbody,hvol,hcmp,hsep⟩⟩

theorem attaining_first_three4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u) (j : Fin 3) (i : Fin 4) :
    |(L *ᵥ integerReal (F.w j.castSucc : Fin 4 → ℤ)) i| ≤
      (Q^(5 : ℕ))^(-(delta/24))*deformedWidths4 Q c0
        (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma i := by
  have hb := (deformed_gauge_bounds4 L hL Q hQ c0 _ F.sigma F.deformation_pos _ _).mp (F.attaining j.castSucc).le i
  have hsmall := (F.minima_mono (show j.castSucc ≤ (2 : Fin 4) by change j.val ≤ 2; omega)).trans_lt F.small
  exact hb.trans (mul_le_mul_of_nonneg_right hsmall.le (F.widths_pos i).le)

end CompoundFeasibility.OriginalDeformedSource4Literal174

#check CompoundFeasibility.liouville4_literal174_common_field
#print CompoundFeasibility.liouville4_literal174_common_field
#print axioms CompoundFeasibility.liouville4_literal174_common_field
#check CompoundFeasibility.liouville4_literal174_common_denominator
#print CompoundFeasibility.liouville4_literal174_common_denominator
#print axioms CompoundFeasibility.liouville4_literal174_common_denominator
#check CompoundFeasibility.liouville4_literal174_conjugate_height
#print CompoundFeasibility.liouville4_literal174_conjugate_height
#print axioms CompoundFeasibility.liouville4_literal174_conjugate_height
#check CompoundFeasibility.liouville4_literal174_field_liouville
#print CompoundFeasibility.liouville4_literal174_field_liouville
#print axioms CompoundFeasibility.liouville4_literal174_field_liouville
#check CompoundFeasibility.algebraic_fin4_literal174_liouville_lower
#print CompoundFeasibility.algebraic_fin4_literal174_liouville_lower
#print axioms CompoundFeasibility.algebraic_fin4_literal174_liouville_lower
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.exists_deformed_attaining4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.exists_deformed_attaining4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.exists_deformed_attaining4
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_gauge_bounds4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_gauge_bounds4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_gauge_bounds4
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.frame_normalization4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.frame_normalization4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.frame_normalization4
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_frame_real_cofactor4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_frame_real_cofactor4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_frame_real_cofactor4
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.first_three_deformed_product4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.first_three_deformed_product4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.first_three_deformed_product4
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.omitted_positive_widths4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.omitted_positive_widths4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.omitted_positive_widths4
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_cofactor_decay4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_cofactor_decay4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_cofactor_decay4
#check CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_frame_finite_cofactor4
#print CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_frame_finite_cofactor4
#print axioms CompoundFeasibility.OriginalDeformedFrame4Literal174.deformed_frame_finite_cofactor4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.primeProduct4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.primeProduct4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.primeProduct4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliaryInteger4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliaryInteger4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliaryInteger4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_dvd4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_dvd4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_dvd4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_primeProduct4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_primeProduct4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_primeProduct4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_real4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_real4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_real4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_zero4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_zero4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.auxiliary_pairing_zero4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.rational_annihilator_line4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.rational_annihilator_line4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.rational_annihilator_line4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.source_auxiliary_line4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.source_auxiliary_line4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.source_auxiliary_line4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.source_prime_product_covolume4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.source_prime_product_covolume4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.source_prime_product_covolume4
#check CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.balanced_width_product_covolume4
#print CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.balanced_width_product_covolume4
#print axioms CompoundFeasibility.OriginalAuxiliaryGeometry4Literal174.balanced_width_product_covolume4
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4
#check CompoundFeasibility.OriginalDeformedSource4Literal174.attaining_of_ready4
#print CompoundFeasibility.OriginalDeformedSource4Literal174.attaining_of_ready4
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.attaining_of_ready4
#check CompoundFeasibility.OriginalDeformedSource4Literal174.attaining_first_three4
#print CompoundFeasibility.OriginalDeformedSource4Literal174.attaining_first_three4
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.attaining_first_three4
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.mk
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.mk
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.mk
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.deformation_pos
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.deformation_pos
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.deformation_pos
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.sigma
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.sigma
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.sigma
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.w
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.w
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.w
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.real_independent
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.real_independent
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.real_independent
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.rational_independent
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.rational_independent
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.rational_independent
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.attaining
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.attaining
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.attaining
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.minima_pos
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.minima_pos
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.minima_pos
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.minima_mono
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.minima_mono
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.minima_mono
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.small
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.small
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.small
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.widths_pos
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.widths_pos
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.widths_pos
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.balance
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.balance
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.balance
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.sizes
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.sizes
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.sizes
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.body
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.body
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.body
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.volume
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.volume
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.volume
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.comparison
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.comparison
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.comparison
#check CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.separation
#print CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.separation
#print axioms CompoundFeasibility.OriginalDeformedSource4Literal174.DeformedAttaining4.separation
