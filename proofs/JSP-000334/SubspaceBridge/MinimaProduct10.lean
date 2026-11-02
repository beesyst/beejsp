import SubspaceBridge.MinimaUpper10
import SubspaceBridge.SourceVolume10
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section

instance originalSourceGroup10_isZLattice (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 10 → ℝ) :
    IsZLattice ℝ (integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) := by
  change IsZLattice ℝ (integerRealImage (sourceLattice10 A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))))
  infer_instance


theorem scalar_product_comparison10 (W D A d l u : ℝ)
    (hW : 0 < W) (hD : 0 < D) (hd : 0 < d)
    (hl : l*W ≤ D) (hu : D ≤ u*W)
    (hdet : d*D ≤ 3628800*A*W) (hm : A*(1024*W/d)/D ≤ 1048576) :
    d*l/3628800 ≤ A ∧ A ≤ 1024*d*u := by
  have hlo : (d*l)*W ≤ (3628800*A)*W := by
    calc
      (d*l)*W = d*(l*W) := by ring
      _ ≤ d*D := mul_le_mul_of_nonneg_left hl hd.le
      _ ≤ (3628800*A)*W := hdet
  have hlc := (mul_le_mul_right hW).mp hlo
  have hm' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hD).mp hm) hd.le
  have he : A*(1024*W/d)*d = (A*1024)*W := by field_simp; ring
  rw [he] at hm'
  have hhi : (A*1024)*W ≤ (1048576*d*u)*W := hm'.trans (by
    convert mul_le_mul_of_nonneg_left hu (show 0 ≤ 1048576*d by positivity) using 1 <;> ring)
  have hhc := (mul_le_mul_right hW).mp hhi
  constructor <;> nlinarith

theorem scalar_volume_ratio10 (W D d l u : ℝ) (hW : 0 < W) (hD : 0 < D)
    (hd : 0 < d) (hl : 0 < l) (hu : 0 < u) (hlo : l*W ≤ D) (hhi : D ≤ u*W) :
    1024/(d*u) ≤ (1024*W/d)/D ∧ (1024*W/d)/D ≤ 1024/(d*l) := by
  have hv : 0 ≤ 1024*W/d := by positivity
  constructor
  · calc
      _ = (1024*W/d)/(u*W) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left hv hD hhi
  · calc
      _ ≤ (1024*W/d)/(l*W) := div_le_div_of_nonneg_left hv (mul_pos hl hW) hlo
      _ = _ := by field_simp; ring

theorem sourceMinima10_product_volume_upper (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ) :
    (∏ i, sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) * volume.real (originalBody10 L Q c₀) /
      ZLattice.covolume (integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ≤ (4 : ℝ)^10 := by
  let b := sourceRealBasis10 A₂ A₃ (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hu := successive_minima10_product_volume_upper b (originalCoordinates10 L hL Q hQ c₀)
  have hbody : {x | coordinateGauge10 (originalCoordinates10 L hL Q hQ c₀) x ≤ 1} = originalBody10 L Q c₀ := by
    ext x
    exact (originalBody10_mem_iff L hL Q hQ c₀ x).symm
  have heq : sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = successiveRadius10 b (originalCoordinates10 L hL Q hQ c₀) :=
    funext (sourceMinima10_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  rw [← heq,hbody,sourceRealBasis10_span] at hu
  exact hu

theorem source_original_uniform_minima_two_sided10
    (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c10 C10 : ℝ, 0 < c10 ∧ 0 < C10 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        c10 ≤ (∏ i, sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
          (∏ i, sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤ C10 := by
  obtain ⟨K,hK,hupper⟩ := sourceLattice10_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  have hd : 0 < |L.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL))
  have hl := sourceLocalDetFactor10_pos A₂ A₃ h₂ h₃
  refine ⟨|L.det| * sourceLocalDetFactor10 A₂ A₃/3628800,1024*|L.det| * ((K : ℝ)*60466176),by positivity,by positivity,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let G := originalSourceGroup10 A₂ A₃ Q c₂ c₃
  let W := ∏ i, Q^c₀ i
  have hW : 0 < W := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  have hD : 0 < ZLattice.covolume (integerRealImage G) := ZLattice.covolume_pos _ volume
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima10_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  obtain ⟨c⟩ := sourceLattice10_has_basis A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hdet := integerRealImage_frame_product_lower G c L u hu (fun i => Q^c₀ i)
    (sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃) hpoint
  have hcovlo := sourceLattice10_covolume_width_lower A₂ A₃ Q hQ c₀ c₂ c₃ hb
  have hcovhi := (div_le_iff₀ hW).mp (hupper Q hQ c₀ c₂ c₃ hc₂ hc₃ hb)
  have hm := sourceMinima10_product_volume_upper A₂ A₃ L hL Q hQ c₀ c₂ c₃
  rw [originalBody10_volume L hL Q hQ] at hm
  exact scalar_product_comparison10 W _ _ |L.det| (sourceLocalDetFactor10 A₂ A₃) ((K : ℝ)*60466176)
    hW hD hd hcovlo hcovhi (by simpa using hdet) (by norm_num only [show (4 : ℝ)^10 = 1048576 by norm_num] at hm; exact hm)

theorem sourceLattice10_full_rank (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) : Module.finrank ℤ (sourceLattice10 A₂ A₃ e₂ e₃) = 10 := by
  obtain ⟨c⟩ := sourceLattice10_has_basis A₂ A₃ e₂ e₃
  simpa using Module.finrank_eq_card_basis c

theorem sourceLattice10_index_pos (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) : 0 < (sourceLattice10 A₂ A₃ e₂ e₃).index := by
  have h := ZLattice.covolume_pos (integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃)) volume
  rw [sourceLattice10_covolume_index] at h
  exact_mod_cast h

theorem source_original_uniform_volume_ratio10
    (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        a ≤ volume.real (originalBody10 L Q c₀) /
          ZLattice.covolume (integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ∧
        volume.real (originalBody10 L Q c₀) /
          ZLattice.covolume (integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ≤ b := by
  obtain ⟨K,hK,hupper⟩ := sourceLattice10_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  have hd : 0 < |L.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL))
  have hl := sourceLocalDetFactor10_pos A₂ A₃ h₂ h₃
  refine ⟨1024/(|L.det| * ((K : ℝ)*60466176)),1024/(|L.det| * sourceLocalDetFactor10 A₂ A₃),
    by positivity,by positivity,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let W := ∏ i, Q^c₀ i
  have hW : 0 < W := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  have hD := ZLattice.covolume_pos (integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) volume
  rw [originalBody10_volume L hL Q hQ]
  exact scalar_volume_ratio10 W _ |L.det| (sourceLocalDetFactor10 A₂ A₃) ((K : ℝ)*60466176)
    hW hD hd hl (by positivity)
    (sourceLattice10_covolume_width_lower A₂ A₃ Q hQ c₀ c₂ c₃ hb)
    ((div_le_iff₀ hW).mp (hupper Q hQ c₀ c₂ c₃ hc₂ hc₃ hb))

end
end CompoundFeasibility
