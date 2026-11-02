import SubspaceBridge.SourceSelectedDual4
import SubspaceBridge.SourceFieldLower6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalHeight4
open SourceSelectedDual4 SchmidtNormalCoordinates4 OriginalSelectedInputs4

theorem normal_pi_norm_le_height4 (M : Fin 4 → ℤ) :
    ‖(fun i => (M i : ℝ))‖ ≤ (normalHeight4 M : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using normalHeight4_coord M i

theorem real_dual_lower4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (M : Fin 4 → ℤ) i,
      dualValue4 L M i ≠ 0 →
      C ≤ ‖dualValue4 L M i‖*(max 1 (normalHeight4 M : ℝ))^D := by
  obtain ⟨C,hC,D,h⟩ := fixed_dual_liouville4 L hL hAlg
  refine ⟨C,hC,D,?_⟩
  intro M i hn
  have hl := h i M hn
  rw [← Real.norm_eq_abs] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (le_trans zero_le_one (le_max_left _ _))
    (max_le_max_left 1 (normal_pi_norm_le_height4 M)) D) (norm_nonneg _))

def finiteValue4 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 4) (Fin 4) ℚ) (M : Fin 4 → ℤ) (i : Fin 4) : ℚ_[p] :=
  ∑ k, (B i k : ℚ_[p])*(M k : ℚ_[p])

theorem fixed_rational_denominator4 (B : Matrix (Fin 4) (Fin 4) ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ N : Matrix (Fin 4) (Fin 4) ℤ,
      ∀ i j, (N i j : ℚ) = (d : ℚ)*B i j := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun ij : Fin 4 × Fin 4 => B ij.1 ij.2)
  choose N hN using hd
  refine ⟨d.val,mem_nonZeroDivisors_iff_ne_zero.mp d.property,fun i j => N (i,j),?_⟩
  intro i j
  simpa only [Algebra.smul_def,eq_intCast] using hN (i,j)

theorem finite_denominator_identity4 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 4) (Fin 4) ℚ) (d : ℤ) (hd : d ≠ 0)
    (N : Matrix (Fin 4) (Fin 4) ℤ)
    (hN : ∀ i j, (N i j : ℚ) = (d : ℚ)*B i j)
    (M : Fin 4 → ℤ) (s : Fin 4) :
    finiteValue4 p B M s = ((∑ i, M i*N s i : ℤ) : ℚ_[p])/(d : ℚ_[p]) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hr : (∑ i, B s i*(M i : ℚ)) = ((∑ i, M i*N s i : ℤ) : ℚ)/(d : ℚ) := by
    apply (eq_div_iff hdQ).mpr
    simp only [Int.cast_sum,Int.cast_mul,Finset.sum_mul,hN]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = algebraMap ℚ ℚ_[p] (∑ i, B s i*(M i : ℚ)) := by
      simp [finiteValue4]
    _ = _ := by rw [hr,map_div₀,map_intCast,map_intCast]

theorem integer_numerator_height4 (N : Matrix (Fin 4) (Fin 4) ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 4 → ℤ) s,
      |((∑ i, M i*N s i : ℤ) : ℝ)| ≤ C*max 1 (normalHeight4 M : ℝ) := by
  let C : ℝ := 1+∑ s, ∑ i, |(N s i : ℝ)|
  have hsum : 0 ≤ ∑ s, ∑ i, |(N s i : ℝ)| :=
    Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro M s
  have hrow : (∑ i, |(N s i : ℝ)|) ≤ C := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun s : Fin 4 => ∑ i, |(N s i : ℝ)|)
      (fun s _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  calc
    _ = ‖∑ i, (M i : ℝ)*(N s i : ℝ)‖ := by simp only [Int.cast_sum,Int.cast_mul,Real.norm_eq_abs]
    _ ≤ ∑ i, |(M i : ℝ)| *|(N s i : ℝ)| := by
      simpa only [norm_mul,Real.norm_eq_abs] using
        norm_sum_le (s := Finset.univ) (f := fun i => (M i : ℝ)*(N s i : ℝ))
    _ ≤ ∑ i, max 1 (normalHeight4 M : ℝ)*|(N s i : ℝ)| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        ((normalHeight4_coord M i).trans (le_max_right _ _)) (abs_nonneg _)
    _ = (∑ i, |(N s i : ℝ)|)*max 1 (normalHeight4 M : ℝ) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow (zero_le_one.trans (le_max_left _ _))

theorem finite_form_lower4 (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : Fin 4 → ℤ) s,
      finiteValue4 p A M s ≠ 0 →
      c ≤ ‖finiteValue4 p A M s‖*max 1 (normalHeight4 M : ℝ) ∧
      c/max 1 (normalHeight4 M : ℝ) ≤ ‖finiteValue4 p A M s‖ := by
  obtain ⟨d,hd,N,hN⟩ := fixed_rational_denominator4 A
  obtain ⟨C,hC,hheight⟩ := integer_numerator_height4 N
  have hdp : (d : ℚ_[p]) ≠ 0 := by exact_mod_cast hd
  have hdn : 0 < ‖(d : ℚ_[p])‖ := norm_pos_iff.mpr hdp
  have hden : 0 < C*‖(d : ℚ_[p])‖ := mul_pos hC hdn
  refine ⟨1/(C*‖(d : ℚ_[p])‖),one_div_pos.mpr hden,?_⟩
  intro M s hne
  let z : ℤ := ∑ i, M i*N s i
  have hz : z ≠ 0 := by
    intro hz
    apply hne
    rw [finite_denominator_identity4 p A d hd N hN M s]
    change (z : ℚ_[p])/(d : ℚ_[p]) = 0
    rw [hz,Int.cast_zero,zero_div]
  have ha : 0 < |(z : ℝ)| := abs_pos.mpr (by exact_mod_cast hz)
  have hzlower : 1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := by
    rcases hp with rfl | rfl
    · exact (div_le_iff₀ ha).mp (SourceFieldLower6.integer_padic2_lower6 z hz) |>.trans_eq (mul_comm _ _)
    · exact (div_le_iff₀ ha).mp (SourceFieldLower6.integer_padic3_lower6 z hz) |>.trans_eq (mul_comm _ _)
  have hnorm : ‖(z : ℚ_[p])‖ = ‖finiteValue4 p A M s‖*‖(d : ℚ_[p])‖ := by
    rw [finite_denominator_identity4 p A d hd N hN M s,norm_div,div_mul_cancel₀ _ hdn.ne']
  have htotal : 1 ≤ (C*‖(d : ℚ_[p])‖)*
      (‖finiteValue4 p A M s‖*max 1 (normalHeight4 M : ℝ)) := by
    calc
      1 ≤ |(z : ℝ)| *‖(z : ℚ_[p])‖ := hzlower
      _ ≤ (C*max 1 (normalHeight4 M : ℝ))*‖(z : ℚ_[p])‖ :=
        mul_le_mul_of_nonneg_right (hheight M s) (norm_nonneg _)
      _ = _ := by rw [hnorm]; ring
  have hl : 1/(C*‖(d : ℚ_[p])‖) ≤
      ‖finiteValue4 p A M s‖*max 1 (normalHeight4 M : ℝ) :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using htotal)
  exact ⟨hl,(div_le_iff₀ (zero_lt_one.trans_le (le_max_left _ _))).mpr hl⟩




theorem finite_dualValue4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (M : Fin 4 → ℤ) (s : Fin 4) :
    dualValue4 (A.map (algebraMap ℚ ℚ_[p])) M s = finiteValue4 p A⁻¹.transpose M s := by
  have hd : A.det ≠ 0 := by rw [hA]; exact one_ne_zero
  have hi := (Auxiliary6.SourceBalance.mapped_inverse (algebraMap ℚ ℚ_[p]) A hd).1
  have he : (A.map (algebraMap ℚ ℚ_[p]))⁻¹ = A⁻¹.map (algebraMap ℚ ℚ_[p]) :=
    Matrix.inv_eq_left_inv hi
  simp [dualValue4,finiteValue4,he,Matrix.mulVec,dotProduct]

theorem finite_dual_lower4 (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Fin 4 → ℤ) s,
      dualValue4 (A.map (algebraMap ℚ ℚ_[p])) M s ≠ 0 →
      C ≤ ‖dualValue4 (A.map (algebraMap ℚ ℚ_[p])) M s‖*max 1 (normalHeight4 M : ℝ) := by
  obtain ⟨C,hC,h⟩ := finite_form_lower4 p hp A⁻¹.transpose
  refine ⟨C,hC,?_⟩
  intro M s hn
  rw [finite_dualValue4 p A hA M s] at hn ⊢
  exact (h M s hn).1

theorem mixed_dual_lower4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ (M : Fin 4 → ℤ) (s : OriginalSelectedSystem4.MixedIndex4),
      mixedNonzero4 A2 A3 L M s →
      C ≤ mixedProduct4 A2 A3 L M s*(max 1 (normalHeight4 M : ℝ))^(D+2) := by
  obtain ⟨C0,hC0,D,h0⟩ := real_dual_lower4 L hL hAlg
  obtain ⟨C2,hC2,hp2⟩ := finite_dual_lower4 2 (Or.inl rfl) A2 h2
  obtain ⟨C3,hC3,hp3⟩ := finite_dual_lower4 3 (Or.inr rfl) A3 h3
  refine ⟨C0*C2*C3,mul_pos (mul_pos hC0 hC2) hC3,D,?_⟩
  intro M s hn
  let H : ℝ := max 1 (normalHeight4 M : ℝ)
  have hH : 0 ≤ H := zero_le_one.trans (le_max_left _ _)
  have hr := h0 M (s 0) hn.1
  have h2' := hp2 M (s 1) hn.2.1
  have h3' := hp3 M (s 2) hn.2.2
  calc
    _ ≤ (‖dualValue4 L M (s 0)‖*H^D)*
        (‖dualValue4 (A2.map (algebraMap ℚ ℚ_[2])) M (s 1)‖*H)*
        (‖dualValue4 (A3.map (algebraMap ℚ ℚ_[3])) M (s 2)‖*H) :=
      mul_le_mul (mul_le_mul hr h2' hC2.le
        (mul_nonneg (norm_nonneg _) (pow_nonneg hH _))) h3' hC3.le
        (mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hH _))
          (mul_nonneg (norm_nonneg _) hH))
    _ = _ := by rw [pow_add,pow_two]; unfold mixedProduct4; ring


open SourceSelectedDual4 SchmidtNormalCoordinates4 OriginalSelectedSystem4
open OriginalAuxiliaryDual4 OriginalLastDual4 OriginalDeformedSource4 OriginalDeformation4

theorem primitive_mixed_le_cofactor4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Fin 4 → Fin 4 → ℤ) (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hs : ∀ i, integerLastDual4 v i = g*M i) (s : MixedIndex4) :
    mixedProduct4 A2 A3 L M s ≤ mixedProduct4 A2 A3 L (integerLastDual4 v) s := by
  have hP : 0 ≤ mixedProduct4 A2 A3 L M s := by
    unfold mixedProduct4
    positivity
  calc
    _ = 1*mixedProduct4 A2 A3 L M s := by ring
    _ ≤ (‖(g : ℝ)‖*‖(g : ℚ_[2])‖*‖(g : ℚ_[3])‖)*mixedProduct4 A2 A3 L M s :=
      mul_le_mul_of_nonneg_right (SourceLocalUpper6.integer_g_three_place6 g hg) hP
    _ = _ := by
      simp only [mixedProduct4,dualValue4_scaling _ _ _ g hs,norm_mul]
      ring

theorem padic_cofactor_bound4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (v : Fin 4 → Fin 4 → ℤ) (b : Fin 4 → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hv : ∀ (j : Fin 3) i,
      ‖(A.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun k => (v j.castSucc k : ℚ_[p]))) i‖ ≤ b i)
    (i : Fin 4) :
    ‖dualValue4 (A.map (algebraMap ℚ ℚ_[p])) (integerLastDual4 v) i‖ ≤
      ∏ k : Fin 3, b (i.succAbove k) := by
  rw [dualValue4,cofactor_minor_norm4 _ (mapped_det_one4 A hA)]
  apply padic_det3_bound4 p _ _ (fun k => hb _) (fun j k => ?_)
  simpa [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using
    hv j (i.succAbove k)

theorem mixed_cofactor_decay4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (v : Fin 4 → Fin 4 → ℤ) (Q d : ℝ) (hQ : 0 < Q)
    (A b2 b3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hb2 : ∀ i, 0 < b2 i) (hb3 : ∀ i, 0 < b3 i)
    (hbal : (∏ i, A i)*(∏ i, b2 i)*(∏ i, b3 i) = 1)
    (hr : ∀ (j : Fin 3) i, |(L *ᵥ (fun k => (v j.castSucc k : ℝ))) i| ≤ Q^(-d)*A i)
    (hp2 : ∀ (j : Fin 3) i,
      ‖(A2.map (algebraMap ℚ ℚ_[2]) *ᵥ (fun k => (v j.castSucc k : ℚ_[2]))) i‖ ≤ b2 i)
    (hp3 : ∀ (j : Fin 3) i,
      ‖(A3.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun k => (v j.castSucc k : ℚ_[3]))) i‖ ≤ b3 i)
    (s : MixedIndex4) (hs : 1 ≤ A (s 0)*b2 (s 1)*b3 (s 2)*Q^(d/2)) :
    mixedProduct4 A2 A3 L (integerLastDual4 v) s ≤ 6*Q^(-5*d/2) := by
  let R := ∏ k : Fin 3, A ((s 0).succAbove k)
  let B2 := ∏ k : Fin 3, b2 ((s 1).succAbove k)
  let B3 := ∏ k : Fin 3, b3 ((s 2).succAbove k)
  let D := A (s 0)*b2 (s 1)*b3 (s 2)
  let P := mixedProduct4 A2 A3 L (integerLastDual4 v) s
  have hn : 0 ≤ P := by dsimp [P,mixedProduct4]; positivity
  have hcancel : R*B2*B3*D = 1 := by
    have ha := Fin.prod_univ_succAbove A (s 0)
    have h2' := Fin.prod_univ_succAbove b2 (s 1)
    have h3' := Fin.prod_univ_succAbove b3 (s 2)
    rw [ha,h2',h3'] at hbal
    dsimp [R,B2,B3,D]
    nlinarith only [hbal]
  have hr' := real_cofactor_bound4 L hL v (fun _ : Fin 3 => Q^(-d)) A hr (s 0)
  have h2' := padic_cofactor_bound4 2 A2 h2 v b2 (fun i => (hb2 i).le) hp2 (s 1)
  have h3' := padic_cofactor_bound4 3 A3 h3 v b3 (fun i => (hb3 i).le) hp3 (s 2)
  have hR : 0 ≤ R := Finset.prod_nonneg (fun k _ => (hA _).le)
  have hB2 : 0 ≤ B2 := Finset.prod_nonneg (fun k _ => (hb2 _).le)
  have hB3 : 0 ≤ B3 := Finset.prod_nonneg (fun k _ => (hb3 _).le)
  have hbound : P ≤ (6*(Q^(-d))^3*R)*B2*B3 := by
    dsimp only [P,mixedProduct4,R,B2,B3]
    apply mul_le_mul (mul_le_mul (by simpa using hr') h2' (norm_nonneg _) (by dsimp only [R] at hR; positivity))
      h3' (norm_nonneg _) (by dsimp only [R,B2] at hR hB2; positivity)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (hA _).le (hb2 _).le) (hb3 _).le
  have hPD : P*D ≤ 6*Q^(-3*d) := by
    calc
      _ ≤ ((6*(Q^(-d))^3*R)*B2*B3)*D := mul_le_mul_of_nonneg_right hbound hD
      _ = 6*(Q^(-d))^3*(R*B2*B3*D) := by ring
      _ = 6*Q^(-3*d) := by
        rw [hcancel,mul_one,← Real.rpow_natCast,← Real.rpow_mul hQ.le]
        congr 2
        ring
  calc
    P ≤ P*(D*Q^(d/2)) := by simpa using mul_le_mul_of_nonneg_left hs hn
    _ = (P*D)*Q^(d/2) := by ring
    _ ≤ (6*Q^(-3*d))*Q^(d/2) := mul_le_mul_of_nonneg_right hPD (by positivity)
    _ = 6*Q^(-5*d/2) := by rw [mul_assoc,← Real.rpow_add hQ]; congr 2; ring


theorem rescaled_balance4 (Q : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 4 → ℝ)
    (hbal : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (∏ i, A i)*(∏ i, (Q^(5 : ℕ))^(c2 i/5))*(∏ i, (Q^(5 : ℕ))^(c3 i/5)) = 1 := by
  rw [mul_assoc,← Finset.prod_mul_distrib]
  convert hbal using 2
  apply Finset.prod_congr rfl
  intro i _
  rw [rescaled_power4 Q _ (zero_lt_one.trans hQ),rescaled_power4 Q _ (zero_lt_one.trans hQ),
    ← Real.rpow_add (zero_lt_one.trans hQ)]

theorem source_selected_mixed_decay4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hscale : ∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i)
    (s : MixedIndex4)
    (hs : s ∈ publishedIndexSet4 (Q^(5 : ℕ)) (delta/24)
      (deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma)
      (fun i => c2 i/5) (fun i => c3 i/5)) :
    mixedProduct4 A2 A3 L M s ≤ 6*(Q^(5 : ℕ))^(-5*(delta/24)/2) := by
  let A := deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma
  let b2 : Fin 4 → ℝ := fun i => (Q^(5 : ℕ))^(c2 i/5)
  let b3 : Fin 4 → ℝ := fun i => (Q^(5 : ℕ))^(c3 i/5)
  have hbal := rescaled_balance4 Q hQ A c2 c3 F.balance
  let v : Fin 4 → Fin 4 → ℤ := fun j => (F.w j : Fin 4 → ℤ)
  have hp2 : ∀ (j : Fin 3) i,
      ‖(A2.map (algebraMap ℚ ℚ_[2]) *ᵥ (fun k => (v j.castSucc k : ℚ_[2]))) i‖ ≤ b2 i := by
    intro j i
    exact (SourceWeights4.finite_form_bounds A2 A3 Q hQ c2 c3 hc2 hc3 (F.w j.castSucc)).1 i
  have hp3 : ∀ (j : Fin 3) i,
      ‖(A3.map (algebraMap ℚ ℚ_[3]) *ᵥ (fun k => (v j.castSucc k : ℚ_[3]))) i‖ ≤ b3 i := by
    intro j i
    exact (SourceWeights4.finite_form_bounds A2 A3 Q hQ c2 c3 hc2 hc3 (F.w j.castSucc)).2 i
  have hr : ∀ (j : Fin 3) i, |(L *ᵥ (fun k => (v j.castSucc k : ℝ))) i| ≤
      (Q^(5 : ℕ))^(-(delta/24))*A i := fun j i => attaining_first_three4 F j i
  have hs' : 1 ≤ A (s 0)*b2 (s 1)*b3 (s 2)*(Q^(5 : ℕ))^((delta/24)/2) :=
    (Finset.mem_filter.mp hs).2
  have hcof := mixed_cofactor_decay4 A2 A3 L h2 h3 hLdet v (Q^(5 : ℕ)) (delta/24)
    (pow_pos (zero_lt_one.trans hQ) _) A b2 b3 F.widths_pos
    (fun i => Real.rpow_pos_of_pos (pow_pos (zero_lt_one.trans hQ) _) _)
    (fun i => Real.rpow_pos_of_pos (pow_pos (zero_lt_one.trans hQ) _) _) hbal hr hp2 hp3 s hs'
  exact (primitive_mixed_le_cofactor4 A2 A3 L v M g hg hscale s).trans hcof


def inverseConstant4 (B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  1+∑ i, ∑ k, |B⁻¹ i k|

theorem inverseConstant4_pos (B : Matrix (Fin 4) (Fin 4) ℝ) : 0 < inverseConstant4 B := by
  have h : 0 ≤ ∑ i, ∑ k, |B⁻¹ i k| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
  unfold inverseConstant4
  linarith

theorem inverse_coordinate4 (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : IsUnit B)
    (x : Fin 4 → ℝ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hx : ∀ k, ‖(B *ᵥ x) k‖ ≤ Q) (i : Fin 4) :
    |x i| ≤ inverseConstant4 B*Q := by
  have hid : B⁻¹ *ᵥ (B *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB),Matrix.one_mulVec]
  have hrow : (∑ k, |B⁻¹ i k|) ≤ inverseConstant4 B := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 4 => ∑ k, |B⁻¹ i k|)
      (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ i)
    unfold inverseConstant4
    linarith
  calc
    |x i| = ‖∑ k, B⁻¹ i k*(B *ᵥ x) k‖ := by
      change |x i| = ‖(B⁻¹ *ᵥ (B *ᵥ x)) i‖
      rw [hid,Real.norm_eq_abs]
    _ ≤ ∑ k, ‖B⁻¹ i k*(B *ᵥ x) k‖ := norm_sum_le _ _
    _ ≤ ∑ k, |B⁻¹ i k| *Q := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
    _ = (∑ k, |B⁻¹ i k|)*Q := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hQ

theorem normalHeight4_real_le (M : Fin 4 → ℤ) (B : ℝ)
    (h : ∀ i, |(M i : ℝ)| ≤ B) : (normalHeight4 M : ℝ) ≤ B := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4))
    Finset.univ_nonempty (fun i => (M i).natAbs)
  change ((Finset.univ.sup (fun i => (M i).natAbs) : ℕ) : ℝ) ≤ B
  rw [hi]
  have he : ((M i).natAbs : ℝ) = |(M i : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [he]
  exact h i


theorem cofactor_coordinate_upper4 (v : Fin 4 → Fin 4 → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ (j : Fin 3) i, |(v j.castSucc i : ℝ)| ≤ B) (i : Fin 4) :
    |(integerLastDual4 v i : ℝ)| ≤ 6*B^3 := by
  have h := real_cofactor_bound4 (1 : Matrix (Fin 4) (Fin 4) ℝ) (by simp) v
    (fun _ : Fin 3 => B) (fun _ : Fin 4 => 1) (fun j k => by simpa using hv j k) i
  simpa using h

theorem source_normal_height_upper4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (hd : 0 < delta)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hscale : ∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i) :
    (normalHeight4 M : ℝ) ≤ (6*(inverseConstant4 L)^3)*(Q^(5 : ℕ))^3 := by
  let V := Q^(5 : ℕ)
  have hV : 1 < V := one_lt_pow₀ hQ (by decide)
  have hsmall : V^(-(delta/24)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hV.le (by linarith)
  have hform (j : Fin 3) (i : Fin 4) :
      ‖(L *ᵥ integerReal (F.w j.castSucc : Fin 4 → ℤ)) i‖ ≤ V := by
    rw [Real.norm_eq_abs]
    exact (attaining_first_three4 F j i).trans
      ((mul_le_mul_of_nonneg_right hsmall (F.widths_pos i).le).trans
        (by simpa using (F.sizes i).1.le))
  have hcoord (j : Fin 3) (i : Fin 4) :
      |((F.w j.castSucc : Fin 4 → ℤ) i : ℝ)| ≤ inverseConstant4 L*V :=
    inverse_coordinate4 L hL _ V (zero_lt_one.trans hV).le (hform j) i
  have hMbound := normalHeight4_normalization_bound _ M g hg hscale
  have hcof : (normalHeight4 (integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ))) : ℝ) ≤
      6*(inverseConstant4 L*V)^3 :=
    normalHeight4_real_le _ _ (cofactor_coordinate_upper4 _ _
      (mul_nonneg (inverseConstant4_pos L).le (zero_lt_one.trans hV).le) hcoord)
  calc
    _ ≤ (normalHeight4 (integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ))) : ℝ) := by exact_mod_cast hMbound
    _ ≤ 6*(inverseConstant4 L*V)^3 := hcof
    _ = _ := by dsimp [V]; ring

theorem source_normal_height_upper_envelope4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (hd : 0 < delta)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u)
    (M : Fin 4 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hscale : ∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i)
    (hcut : 6*(inverseConstant4 L)^3 ≤ Q^(5 : ℕ)) :
    max 1 (normalHeight4 M : ℝ) ≤ (Q^(5 : ℕ))^(4 : ℝ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl,Real.rpow_natCast]
  apply max_le
  · exact one_le_pow₀ (one_lt_pow₀ hQ (by decide)).le
  · exact (source_normal_height_upper4 hd F M g hg hscale).trans
      ((mul_le_mul_of_nonneg_right hcut (by positivity)).trans_eq (by ring))
theorem combined_product4 (C Q eps H P : ℝ) (n : ℕ)
    (hQ : 0 < Q) (hH : 0 ≤ H)
    (hl : C ≤ P*H^n) (hu : P ≤ 6*Q^(-eps)) :
    (C/6)*Q^eps ≤ H^n := by
  have h := hl.trans (mul_le_mul_of_nonneg_right hu (pow_nonneg hH n))
  have hp : 0 < Q^eps := Real.rpow_pos_of_pos hQ _
  have he : Q^(-eps)*Q^eps = 1 := by
    rw [← Real.rpow_add hQ]
    convert Real.rpow_zero Q using 1 <;> ring
  have ht := mul_le_mul_of_nonneg_right h hp.le
  have hr : (6*Q^(-eps)*H^n)*Q^eps = 6*H^n := by
    calc
      _ = 6*H^n*(Q^(-eps)*Q^eps) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hr] at ht
  linarith

def lowerThreshold4 (C eps : ℝ) : ℝ := max 2 ((6/C)^((eps/2)⁻¹))

def heightAlpha4 (eps : ℝ) (n : ℕ) : ℝ := eps/(2*(n : ℝ))

theorem lower_absorption4 (C eps Q H : ℝ) (n : ℕ) (hn0 : 0 < n) (hC : 0 < C)
    (hd : 0 < eps) (hQ : lowerThreshold4 C eps ≤ Q) (hH : 1 ≤ H)
    (hl : (C/6)*Q^(eps) ≤ H^n) :
    Q^(heightAlpha4 eps n) ≤ H := by
  have hQ2 : 2 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := by linarith
  have he : 0 < eps/2 := by positivity
  have hc : 0 < 6/C := by positivity
  have ht : (6/C)^((eps/2)⁻¹) ≤ Q := (le_max_right _ _).trans hQ
  have hb := Real.rpow_le_rpow (Real.rpow_nonneg hc.le _) ht he.le
  rw [Real.rpow_inv_rpow hc.le he.ne'] at hb
  have hconst : 1 ≤ (C/6)*Q^(eps/2) := by
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ C/6 by positivity)
    have hh0 : (C/6)*(6/C) = 1 := by field_simp
    rwa [hh0] at hh
  have hn : 0 < (n : ℝ) := by positivity
  have hpow : (Q^(heightAlpha4 eps n))^n = Q^(eps/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ0.le]
    congr 1
    simp only [heightAlpha4,Nat.cast_add,Nat.cast_one]
    field_simp
    <;> ring
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hQ0.le _) (zero_le_one.trans hH) hn).mp
  simp only [Real.rpow_natCast]
  rw [hpow]
  calc
    Q^(eps/2) ≤ ((C/6)*Q^(eps/2))*Q^(eps/2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hQ0.le _)
    _ = (C/6)*Q^(eps) := by
      rw [mul_assoc,← Real.rpow_add hQ0]
      congr 2
      ring
    _ ≤ _ := hl



theorem selected_lower_height4 (C eps Q H P : ℝ) (n : ℕ)
    (hn : 0 < n) (hC : 0 < C) (he : 0 < eps) (hQ : lowerThreshold4 C eps ≤ Q)
    (hH : 1 ≤ H) (hl : C ≤ P*H^n) (hu : P ≤ 6*Q^(-eps)) :
    Q^(heightAlpha4 eps n) ≤ H := by
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((le_max_left _ _).trans hQ)
  exact lower_absorption4 C eps Q H n hn hC he hQ hH
    (combined_product4 C Q eps H P n hQ0 (zero_le_one.trans hH) hl hu)


theorem source_uniform_height_envelopes4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∃ T : ℝ, 1 < T ∧
      ∀ (Q : ℝ), T < Q → ∀ (hQ : 1 < Q) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
      ∀ (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3),
      ∀ F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u,
      ∀ (M : Fin 4 → ℤ) (g : ℤ), g ≠ 0 →
      (∀ i, integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) i = g*M i) →
      ∀ s ∈ publishedIndexSet4 (Q^(5 : ℕ)) (delta/24)
        (deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma)
        (fun i => c2 i/5) (fun i => c3 i/5),
      mixedNonzero4 A2 A3 L M s →
      (Q^(5 : ℕ))^alpha ≤ max 1 (normalHeight4 M : ℝ) ∧
        max 1 (normalHeight4 M : ℝ) ≤ (Q^(5 : ℕ))^(4 : ℝ) := by
  obtain ⟨C,hC,D,hlower⟩ := mixed_dual_lower4 A2 A3 L h2 h3 hLdet hAlg
  let eps := 5*(delta/24)/2
  let alpha := heightAlpha4 eps (D+2)
  let T := max (lowerThreshold4 C eps) (6*(inverseConstant4 L)^3)
  have he : 0 < eps := by dsimp [eps]; positivity
  have ha : 0 < alpha := by dsimp [alpha,heightAlpha4]; positivity
  have hT : 1 < T := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨alpha,ha,T,hT,?_⟩
  intro Q hTQ hQ hL c0 c2 c3 hc2 hc3 u F M g hg hscale s hs hn
  have hQQ : Q ≤ Q^(5 : ℕ) := le_self_pow₀ hQ.le (by decide)
  have hcut : lowerThreshold4 C eps ≤ Q^(5 : ℕ) :=
    ((le_max_left _ _).trans hTQ.le).trans hQQ
  constructor
  · exact selected_lower_height4 C eps (Q^(5 : ℕ)) (max 1 (normalHeight4 M : ℝ))
      (mixedProduct4 A2 A3 L M s) (D+2) (by omega) hC he hcut (le_max_left _ _)
      (hlower M s hn) (by
        convert source_selected_mixed_decay4 h2 h3 hLdet hc2 hc3 F M g hg hscale s hs using 1 <;>
          dsimp [eps] <;> ring)
  · exact source_normal_height_upper_envelope4 hd F M g hg hscale
      (((le_max_right _ _).trans hTQ.le).trans hQQ)

end CompoundFeasibility.SourceNormalHeight4
