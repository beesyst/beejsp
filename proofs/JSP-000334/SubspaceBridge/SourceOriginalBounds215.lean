import SubspaceBridge.SourceOriginalNormalization213
import SubspaceBridge.SourceVolume10
import SubspaceBridge.SourceOriginalNorms214
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceOriginalBounds215
open SourceOriginalVariable10 SourceOriginalSatz212 OriginalDual10 SourceOriginalDual10 SourceOriginalNorm214
variable {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
  {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {delta : ℝ} {S0 : Finset SourceSelectedSet10.MixedIndex10}

theorem original_width_covolume215 (h2 : A2.det = 1) (h3 : A3.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    (∏ i, D.A i) ≤ originalCovolume212 D := by
  have hf : sourceLocalDetFactor10 A2 A3 = 1 := by
    simp only [sourceLocalDetFactor10,h2,h3,padicNorm.one,Rat.cast_one,one_mul]
  have h := sourceLattice10_covolume_width_lower A2 A3 Q hQ
    (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
    (fun i => normalizedFinite10 3 Q (D.f3 i))
    (normalized_balance10 Q D.A D.positive D.f2 D.f3 D.balance)
  simp_rw [hf,one_mul,normalized_width_exact10 Q _ hQ (D.positive _),original_lattice_eq212 D] at h
  exact h
theorem original_first_nine_minima215
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) :
    (∏ j : Fin 9, sourceMinima10 A2 A3 L hL Q hQ
      (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
      (fun i => normalizedFinite10 3 Q (D.f3 i)) j.castSucc) ≤ Q^(-9*delta) := by
  have hp := sourceMinima10_pos_mono A2 A3 L hL Q hQ
    (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
    (fun i => normalizedFinite10 3 Q (D.f3 i))
  calc
    _ ≤ ∏ _j : Fin 9, Q^(-delta) := Finset.prod_le_prod
      (fun j _ => (hp.1 _).le) (fun j _ => (hp.2 (by change j.val ≤ 8; omega)).trans D.small.le)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans hQ).le]
      congr 1
      ring

theorem original_real_cofactor215 (hLd : L.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℝ))) i‖ ≤
      362880 * (∏ j : Fin 9, sourceMinima10 A2 A3 L hL Q hQ
        (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
        (fun i => normalizedFinite10 3 Q (D.f3 i)) j.castSucc) *
        (∏ k : Fin 9, D.A (i.succAbove k)) := by
  let u' : Fin 10 → originalSourceGroup10 A2 A3 Q
      (fun i => normalizedFinite10 2 Q (D.f2 i)) (fun i => normalizedFinite10 3 Q (D.f3 i)) :=
    fun j => ⟨D.u j,(normalized_source_group_exact10 A2 A3 Q hQ D.f2 D.f3 D.nonpos2 D.nonpos3
      (D.u j)).mpr ⟨D.member2 j,D.member3 j⟩⟩
  have hpoint := source_original_coordinate_bounds10 A2 A3 L hL Q hQ
    (fun i => normalizedWidth10 Q (D.A i)) (fun i => normalizedFinite10 2 Q (D.f2 i))
    (fun i => normalizedFinite10 3 Q (D.f3 i)) u' D.attaining
  simp_rw [normalized_width_exact10 Q _ hQ (D.positive _)] at hpoint
  exact real_cofactor_fin10 L hLd D.u _ D.A hpoint i

theorem original_real_integer_bound215 (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 D.u k : ℝ))) i‖ ≤
      362880 * (D.A i)⁻¹ * originalCovolume212 D * Q^(-9*delta) := by
  have hA := D.positive i
  have hw := original_width_covolume215 h2 h3 D
  have hn := original_first_nine_minima215 D
  have ho : (∏ k : Fin 9, D.A (i.succAbove k)) = (D.A i)⁻¹ * (∏ k, D.A k) := by
    rw [Fin.prod_univ_succAbove D.A i,← mul_assoc,inv_mul_cancel₀ hA.ne',one_mul]
  have hp : 0 ≤ ∏ k : Fin 9, D.A (i.succAbove k) :=
    (Finset.prod_pos (fun k _ => D.positive _)).le
  calc
    _ ≤ _ := original_real_cofactor215 hLd D i
    _ ≤ 362880 * Q^(-9*delta) * (∏ k : Fin 9, D.A (i.succAbove k)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hp
    _ = 362880 * (D.A i)⁻¹ * (∏ k, D.A k) * Q^(-9*delta) := by rw [ho]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num) (inv_nonneg.mpr hA.le)))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le

theorem original_real_bound215 (h2 : A2.det = 1) (h3 : A3.det = 1) (hLd : L.det = 1)
    (D : OriginalData10 A2 A3 L hL Q hQ delta S0) (i : Fin 10) :
    ‖∑ k, (((originalIndex212 D : ℝ)*originalCovolume212 D)*
      (lastDual10 (fun j i => (D.u j i : ℚ))
        (integer_frame_rational_independent10 D.u D.independent) k : ℝ))*L⁻¹.transpose i k‖ ≤
      362880 * (D.A i)⁻¹ * originalCovolume212 D * Q^(-9*delta) := by
  rw [← original_real_sum_norm214 D i]
  exact original_real_integer_bound215 h2 h3 hLd D i

end CompoundFeasibility.SourceOriginalBounds215
