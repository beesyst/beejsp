import SubspaceBridge.SourceLocalUpperIntegration6
import SubspaceBridge.ConditionalNormalHeight3
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFieldLower6
open SourceNormalHeight SourceProper6 SourceMixed6 Auxiliary6 Auxiliary6.SourceExpansion

theorem cofactor_coefficients_in_field6 (K : IntermediateField ℚ ℝ)
    (B : Matrix (Fin 6) (Fin 6) ℝ) (hB : ∀ i j, B i j ∈ K) :
    ∃ b : Matrix (Fin 6) (Fin 6) K, ∀ i j, (b i j : ℝ) = cofactor6 B i j := by
  let T : Matrix (Fin 6) (Fin 6) K := fun i j => ⟨B i j,hB i j⟩
  refine ⟨cofactor6 T,fun i j => ?_⟩
  exact (cofactor6_map K.val.toRingHom T i j).symm

theorem actual_cofactor_field6 (K : IntermediateField ℚ ℝ)
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hmem : ∀ tau i j, forms A2 A3 L tau i j ∈ K) :
    ∃ b : Matrix (Fin 6) (Fin 6) K,
      ∀ i j, (b i j : ℝ) = cofactor6 (compound L) i j := by
  exact cofactor_coefficients_in_field6 K (compound L) (fun i j => hmem 0 i j)

theorem cofactor_field_evaluation6 (K : IntermediateField ℚ ℝ)
    (B : Matrix (Fin 6) (Fin 6) ℝ) (b : Matrix (Fin 6) (Fin 6) K)
    (hb : ∀ i j, (b i j : ℝ) = cofactor6 B i j) (M : Fin 6 → ℤ) (s : Fin 6) :
    (∑ i, (b s i : ℝ)*(M i : ℝ)) = cofactorValue6 B M s := by
  simp only [hb,cofactorValue6,mul_comm]


theorem liouville6_explicit_degree (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (b : Fin 6 → Fin 6 → K) :
    ∃ C : ℝ, 0 < C ∧ ∀ s (z : Fin 6 → ℤ),
      (∑ i, (b s i : ℝ) * (z i : ℝ)) ≠ 0 →
      C ≤ |∑ i, (b s i : ℝ) * (z i : ℝ)| * (max 1 ‖(fun i => (z i : ℝ))‖)^(Module.finrank ℚ K-1) := by
  classical
  obtain ⟨M,hM,hint⟩ := liouville6_common_denominator K b
  let c : Fin 6 → Fin 6 → K := fun s i => (M : K) * b s i
  obtain ⟨B,hB,hheight⟩ := liouville6_conjugate_height K c
  let sigma0 : K →ₐ[ℚ] ℂ := (IsScalarTower.toAlgHom ℚ ℝ ℂ).comp K.val
  let D := Fintype.card (K →ₐ[ℚ] ℂ) - 1
  have hD : D = Module.finrank ℚ K-1 := by dsimp only [D]; rw [AlgHom.card ℚ K ℂ]
  rw [← hD]
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hden : 0 < |(M : ℝ)| * B^D := mul_pos (abs_pos.mpr hMr) (pow_pos hB _)
  refine ⟨(|(M : ℝ)| * B^D)⁻¹,inv_pos.mpr hden,?_⟩
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


theorem normal_pi_norm_le_height6 (M : Fin 6 → ℤ) :
    ‖(fun i => (M i : ℝ))‖ ≤ (normalHeight6 M : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using normalHeight6_coord M i

theorem real_cofactor_liouville6 (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (B : Matrix (Fin 6) (Fin 6) ℝ) (b : Matrix (Fin 6) (Fin 6) K)
    (hb : ∀ i j, (b i j : ℝ) = cofactor6 B i j) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (M : Fin 6 → ℤ) s,
      cofactorValue6 B M s ≠ 0 →
      C ≤ ‖cofactorValue6 B M s‖*(max 1 (normalHeight6 M : ℝ))^D := by
  obtain ⟨C,hC,D,h⟩ := liouville6_field_liouville K b
  refine ⟨C,hC,D,?_⟩
  intro M s hn
  have hv := cofactor_field_evaluation6 K B b hb M s
  have hl := h s M (hv ▸ hn)
  rw [hv,← Real.norm_eq_abs] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (le_trans zero_le_one (le_max_left _ _))
    (max_le_max_left 1 (normal_pi_norm_le_height6 M)) D) (norm_nonneg _))

theorem real_cofactor_degree_lower6 (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (B : Matrix (Fin 6) (Fin 6) ℝ) (b : Matrix (Fin 6) (Fin 6) K)
    (hb : ∀ i j, (b i j : ℝ) = cofactor6 B i j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 6 → ℤ) s,
      cofactorValue6 B M s ≠ 0 →
      C ≤ ‖cofactorValue6 B M s‖*(max 1 (normalHeight6 M : ℝ))^(Module.finrank ℚ K-1) := by
  obtain ⟨C,hC,h⟩ := liouville6_explicit_degree K b
  refine ⟨C,hC,?_⟩
  intro M s hn
  have hv := cofactor_field_evaluation6 K B b hb M s
  have hl := h s M (hv ▸ hn)
  rw [hv,← Real.norm_eq_abs] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (le_trans zero_le_one (le_max_left _ _))
    (max_le_max_left 1 (normal_pi_norm_le_height6 M)) (Module.finrank ℚ K-1)) (norm_nonneg _))



theorem fixed_rational_denominator6 (A : Matrix (Fin 4) (Fin 4) ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ N : Matrix (Fin 6) (Fin 6) ℤ,
      ∀ i j, (N i j : ℚ) = (d : ℚ)*cofactor6 (compound A) i j := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun ij : Fin 6 × Fin 6 => cofactor6 (compound A) ij.1 ij.2)
  choose N hN using hd
  refine ⟨d.val,mem_nonZeroDivisors_iff_ne_zero.mp d.property,fun i j => N (i,j),?_⟩
  intro i j
  simpa only [Algebra.smul_def,eq_intCast] using hN (i,j)

theorem finite_denominator_identity6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (d : ℤ) (hd : d ≠ 0)
    (N : Matrix (Fin 6) (Fin 6) ℤ)
    (hN : ∀ i j, (N i j : ℚ) = (d : ℚ)*cofactor6 (compound A) i j)
    (M : Fin 6 → ℤ) (s : Fin 6) :
    cofactorValue6 (finiteMatrix p A) M s =
      ((∑ i, M i*N s i : ℤ) : ℚ_[p])/(d : ℚ_[p]) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hr : cofactorValue6 (compound A) M s = ((∑ i, M i*N s i : ℤ) : ℚ)/(d : ℚ) := by
    apply (eq_div_iff hdQ).mpr
    simp only [cofactorValue6,Int.cast_sum,Int.cast_mul,Finset.sum_mul,hN]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = algebraMap ℚ ℚ_[p] (cofactorValue6 (compound A) M s) := by
      simp only [cofactorValue6,finite_cofactor6_rational,map_sum,map_mul,map_intCast]
    _ = _ := by rw [hr,map_div₀,map_intCast,map_intCast]

theorem finite_numerator_nonzero6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (d : ℤ) (hd : d ≠ 0)
    (N : Matrix (Fin 6) (Fin 6) ℤ)
    (hN : ∀ i j, (N i j : ℚ) = (d : ℚ)*cofactor6 (compound A) i j)
    (M : Fin 6 → ℤ) (s : Fin 6)
    (hne : cofactorValue6 (finiteMatrix p A) M s ≠ 0) :
    (∑ i, M i*N s i : ℤ) ≠ 0 := by
  intro hz
  apply hne
  rw [finite_denominator_identity6 p A d hd N hN M s,hz,Int.cast_zero,zero_div]


theorem integer_numerator_height6 (N : Matrix (Fin 6) (Fin 6) ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 6 → ℤ) s,
      |((∑ i, M i*N s i : ℤ) : ℝ)| ≤ C*max 1 (normalHeight6 M : ℝ) := by
  let C : ℝ := 1+∑ s, ∑ i, |(N s i : ℝ)|
  have hsum : 0 ≤ ∑ s, ∑ i, |(N s i : ℝ)| :=
    Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro M s
  have hrow : (∑ i, |(N s i : ℝ)|) ≤ C := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun s : Fin 6 => ∑ i, |(N s i : ℝ)|)
      (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  calc
    _ = ‖∑ i, (M i : ℝ)*(N s i : ℝ)‖ := by simp only [Int.cast_sum,Int.cast_mul,Real.norm_eq_abs]
    _ ≤ ∑ i, |(M i : ℝ)| *|(N s i : ℝ)| := by
      simpa only [norm_mul,Real.norm_eq_abs] using
        norm_sum_le (s := Finset.univ) (f := fun i => (M i : ℝ)*(N s i : ℝ))
    _ ≤ ∑ i, max 1 (normalHeight6 M : ℝ)*|(N s i : ℝ)| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        ((normalHeight6_coord M i).trans (le_max_right _ _)) (abs_nonneg _)
    _ = (∑ i, |(N s i : ℝ)|)*max 1 (normalHeight6 M : ℝ) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow (zero_le_one.trans (le_max_left _ _))

theorem integer_padic2_lower6 (z : ℤ) (hz : z ≠ 0) :
    1 / |(z : ℝ)| ≤ ‖(z : ℚ_[2])‖ := by
  have h := (JSP000334.conditional_integer_local_lower3 z hz).1
  have h' : 1 ≤ |(z : ℝ)| *‖(z : ℚ_[2])‖ := by
    simpa [← finite_norm 2] using h
  have ha : 0 < |(z : ℝ)| := abs_pos.mpr (by exact_mod_cast hz)
  exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using h')

theorem integer_padic3_lower6 (z : ℤ) (hz : z ≠ 0) :
    1 / |(z : ℝ)| ≤ ‖(z : ℚ_[3])‖ := by
  have h := (JSP000334.conditional_integer_local_lower3 z hz).2
  have h' : 1 ≤ |(z : ℝ)| *‖(z : ℚ_[3])‖ := by
    simpa [← finite_norm 3] using h
  have ha : 0 < |(z : ℝ)| := abs_pos.mpr (by exact_mod_cast hz)
  exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using h')

theorem finite_cofactor_lower6 (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : Fin 6 → ℤ) s,
      cofactorValue6 (finiteMatrix p A) M s ≠ 0 →
      c ≤ ‖cofactorValue6 (finiteMatrix p A) M s‖*max 1 (normalHeight6 M : ℝ) ∧
      c/max 1 (normalHeight6 M : ℝ) ≤ ‖cofactorValue6 (finiteMatrix p A) M s‖ := by
  obtain ⟨d,hd,N,hN⟩ := fixed_rational_denominator6 A
  obtain ⟨C,hC,hheight⟩ := integer_numerator_height6 N
  have hdp : (d : ℚ_[p]) ≠ 0 := by exact_mod_cast hd
  have hdn : 0 < ‖(d : ℚ_[p])‖ := norm_pos_iff.mpr hdp
  have hden : 0 < C*‖(d : ℚ_[p])‖ := mul_pos hC hdn
  refine ⟨1/(C*‖(d : ℚ_[p])‖),one_div_pos.mpr hden,?_⟩
  intro M s hne
  let z : ℤ := ∑ i, M i*N s i
  have hz : z ≠ 0 := finite_numerator_nonzero6 p A d hd N hN M s hne
  have ha : 0 < |(z : ℝ)| := abs_pos.mpr (by exact_mod_cast hz)
  have hzlower : 1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := by
    rcases hp with rfl | rfl
    · exact (div_le_iff₀ ha).mp (integer_padic2_lower6 z hz) |>.trans_eq (mul_comm _ _)
    · exact (div_le_iff₀ ha).mp (integer_padic3_lower6 z hz) |>.trans_eq (mul_comm _ _)
  have hnorm : ‖(z : ℚ_[p])‖ = ‖cofactorValue6 (finiteMatrix p A) M s‖*‖(d : ℚ_[p])‖ := by
    rw [finite_denominator_identity6 p A d hd N hN M s,norm_div,div_mul_cancel₀ _ hdn.ne']
  have htotal : 1 ≤ (C*‖(d : ℚ_[p])‖)*
      (‖cofactorValue6 (finiteMatrix p A) M s‖*max 1 (normalHeight6 M : ℝ)) := by
    calc
      1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := hzlower
      _ ≤ (C*max 1 (normalHeight6 M : ℝ))*‖(z : ℚ_[p])‖ :=
        mul_le_mul_of_nonneg_right (hheight M s) (norm_nonneg _)
      _ = _ := by rw [hnorm]; ring
  have hl : 1/(C*‖(d : ℚ_[p])‖) ≤
      ‖cofactorValue6 (finiteMatrix p A) M s‖*max 1 (normalHeight6 M : ℝ) :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)
  exact ⟨hl,(div_le_iff₀ (zero_lt_one.trans_le (le_max_left _ _))).mpr hl⟩



theorem actual_cofactor_mem6 (K : IntermediateField ℚ ℝ)
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hmem : ∀ tau i j, forms A2 A3 L tau i j ∈ K) :
    ∀ i j, cofactor6 (compound L) i j ∈ K := by
  obtain ⟨b,hb⟩ := actual_cofactor_field6 K A2 A3 L hmem
  intro i j
  rw [← hb i j]
  exact (b i j).property

theorem field_degree_exponents6 (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] :
    Module.finrank ℚ K-1+2 = Module.finrank ℚ K+1 ∧
      Module.finrank ℚ K+1 ≤ 3*Module.finrank ℚ K-1 := by
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

theorem actual_mixed_field_lower6 (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hmem : ∀ tau i j, forms A2 A3 L tau i j ∈ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 6 → ℤ) (s : MixedIndex6),
      actualNonzero6 A2 A3 L M s →
      C ≤ actualNormProduct6 A2 A3 L M s*(max 1 (normalHeight6 M : ℝ))^(Module.finrank ℚ K+1) ∧
      C ≤ actualNormProduct6 A2 A3 L M s*(max 1 (normalHeight6 M : ℝ))^(3*Module.finrank ℚ K-1) := by
  obtain ⟨b,hb⟩ := actual_cofactor_field6 K A2 A3 L hmem
  obtain ⟨C0,hC0,h0⟩ := real_cofactor_degree_lower6 K (compound L) b hb
  obtain ⟨C2,hC2,h2⟩ := finite_cofactor_lower6 2 (Or.inl rfl) A2
  obtain ⟨C3,hC3,h3⟩ := finite_cofactor_lower6 3 (Or.inr rfl) A3
  refine ⟨C0*C2*C3,mul_pos (mul_pos hC0 hC2) hC3,?_⟩
  intro M s hn
  let H : ℝ := max 1 (normalHeight6 M : ℝ)
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH : 0 ≤ H := zero_le_one.trans hH1
  have hr := h0 M (s 0) hn.1
  have hp2 := (h2 M (s 1) hn.2.1).1
  have hp3 := (h3 M (s 2) hn.2.2).1
  have hs : C0*C2*C3 ≤ actualNormProduct6 A2 A3 L M s*H^(Module.finrank ℚ K+1) := by
    calc
      _ ≤ (‖cofactorValue6 (compound L) M (s 0)‖*H^(Module.finrank ℚ K-1))*
          (‖cofactorValue6 (finiteMatrix 2 A2) M (s 1)‖*H)*
          (‖cofactorValue6 (finiteMatrix 3 A3) M (s 2)‖*H) := by
        exact mul_le_mul (mul_le_mul hr hp2 hC2.le
          (mul_nonneg (norm_nonneg _) (pow_nonneg hH _))) hp3 hC3.le
          (mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hH _))
            (mul_nonneg (norm_nonneg _) hH))
      _ = _ := by
        rw [← (field_degree_exponents6 K).1,pow_add,pow_two]
        unfold actualNormProduct6
        ring
  refine ⟨hs,hs.trans ?_⟩
  have hP : 0 ≤ actualNormProduct6 A2 A3 L M s :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH1 (field_degree_exponents6 K).2) hP

end CompoundFeasibility.SourceFieldLower6
