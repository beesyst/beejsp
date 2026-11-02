import SubspaceBridge.MinimaUpper5
import SubspaceBridge.SourceVolume5
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section

instance originalSourceGroup5_isZLattice (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    IsZLattice ℝ (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) := by
  change IsZLattice ℝ (integerRealImage (sourceLattice5 A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))))
  infer_instance


theorem scalar_product_comparison5 (W D A d l u : ℝ)
    (hW : 0 < W) (hD : 0 < D) (hd : 0 < d)
    (hl : l*W ≤ D) (hu : D ≤ u*W)
    (hdet : d*D ≤ 120*A*W) (hm : A*(32*W/d)/D ≤ 1024) :
    d*l/120 ≤ A ∧ A ≤ 32*d*u := by
  have hlo : (d*l)*W ≤ (120*A)*W := by
    calc
      (d*l)*W = d*(l*W) := by ring
      _ ≤ d*D := mul_le_mul_of_nonneg_left hl hd.le
      _ ≤ (120*A)*W := hdet
  have hlc := (mul_le_mul_right hW).mp hlo
  have hm' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hD).mp hm) hd.le
  have he : A*(32*W/d)*d = (A*32)*W := by field_simp; ring
  rw [he] at hm'
  have hhi : (A*32)*W ≤ (1024*d*u)*W := hm'.trans (by
    convert mul_le_mul_of_nonneg_left hu (show 0 ≤ 1024*d by positivity) using 1 <;> ring)
  have hhc := (mul_le_mul_right hW).mp hhi
  constructor <;> nlinarith

theorem scalar_volume_ratio5 (W D d l u : ℝ) (hW : 0 < W) (hD : 0 < D)
    (hd : 0 < d) (hl : 0 < l) (hu : 0 < u) (hlo : l*W ≤ D) (hhi : D ≤ u*W) :
    32/(d*u) ≤ (32*W/d)/D ∧ (32*W/d)/D ≤ 32/(d*l) := by
  have hv : 0 ≤ 32*W/d := by positivity
  constructor
  · calc
      _ = (32*W/d)/(u*W) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left hv hD hhi
  · calc
      _ ≤ (32*W/d)/(l*W) := div_le_div_of_nonneg_left hv (mul_pos hl hW) hlo
      _ = _ := by field_simp; ring

theorem sourceMinima5_product_volume_upper (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) :
    (∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) * volume.real (originalBody5 L Q c₀) /
      ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ≤ (4 : ℝ)^5 := by
  let b := sourceRealBasis5 A₂ A₃ (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hu := successive_minima5_product_volume_upper b (originalCoordinates5 L hL Q hQ c₀)
  have hbody : {x | coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) x ≤ 1} = originalBody5 L Q c₀ := by
    ext x
    exact (originalBody5_mem_iff L hL Q hQ c₀ x).symm
  have heq : sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = successiveRadius5 b (originalCoordinates5 L hL Q hQ c₀) :=
    funext (sourceMinima5_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  rw [← heq,hbody,sourceRealBasis5_span] at hu
  exact hu

theorem source_original_uniform_minima_two_sided5
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c5 C5 : ℝ, 0 < c5 ∧ 0 < C5 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        c5 ≤ (∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
          (∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤ C5 := by
  obtain ⟨K,hK,hupper⟩ := sourceLattice5_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  have hd : 0 < |L.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL))
  have hl := sourceLocalDetFactor5_pos A₂ A₃ h₂ h₃
  refine ⟨|L.det| * sourceLocalDetFactor5 A₂ A₃/120,32*|L.det| * ((K : ℝ)*7776),by positivity,by positivity,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let G := originalSourceGroup5 A₂ A₃ Q c₂ c₃
  let W := ∏ i, Q^c₀ i
  have hW : 0 < W := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  have hD : 0 < ZLattice.covolume (integerRealImage G) := ZLattice.covolume_pos _ volume
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima5_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  obtain ⟨c⟩ := sourceLattice5_has_basis A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hdet := integerRealImage_frame_product_lower G c L u hu (fun i => Q^c₀ i)
    (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃) hpoint
  have hcovlo := sourceLattice5_covolume_width_lower A₂ A₃ Q hQ c₀ c₂ c₃ hb
  have hcovhi := (div_le_iff₀ hW).mp (hupper Q hQ c₀ c₂ c₃ hc₂ hc₃ hb)
  have hm := sourceMinima5_product_volume_upper A₂ A₃ L hL Q hQ c₀ c₂ c₃
  rw [originalBody5_volume L hL Q hQ] at hm
  exact scalar_product_comparison5 W _ _ |L.det| (sourceLocalDetFactor5 A₂ A₃) ((K : ℝ)*7776)
    hW hD hd hcovlo hcovhi (by simpa using hdet) (by norm_num only [show (4 : ℝ)^5 = 1024 by norm_num] at hm; exact hm)

theorem sourceLattice5_full_rank (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : Module.finrank ℤ (sourceLattice5 A₂ A₃ e₂ e₃) = 5 := by
  obtain ⟨c⟩ := sourceLattice5_has_basis A₂ A₃ e₂ e₃
  simpa using Module.finrank_eq_card_basis c

theorem sourceLattice5_index_pos (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : 0 < (sourceLattice5 A₂ A₃ e₂ e₃).index := by
  have h := ZLattice.covolume_pos (integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃)) volume
  rw [sourceLattice5_covolume_index] at h
  exact_mod_cast h

theorem source_original_uniform_volume_ratio5
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        a ≤ volume.real (originalBody5 L Q c₀) /
          ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ∧
        volume.real (originalBody5 L Q c₀) /
          ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ≤ b := by
  obtain ⟨K,hK,hupper⟩ := sourceLattice5_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  have hd : 0 < |L.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL))
  have hl := sourceLocalDetFactor5_pos A₂ A₃ h₂ h₃
  refine ⟨32/(|L.det| * ((K : ℝ)*7776)),32/(|L.det| * sourceLocalDetFactor5 A₂ A₃),
    by positivity,by positivity,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let W := ∏ i, Q^c₀ i
  have hW : 0 < W := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  have hD := ZLattice.covolume_pos (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) volume
  rw [originalBody5_volume L hL Q hQ]
  exact scalar_volume_ratio5 W _ |L.det| (sourceLocalDetFactor5 A₂ A₃) ((K : ℝ)*7776)
    hW hD hd hl (by positivity)
    (sourceLattice5_covolume_width_lower A₂ A₃ Q hQ c₀ c₂ c₃ hb)
    ((div_le_iff₀ hW).mp (hupper Q hQ c₀ c₂ c₃ hc₂ hc₃ hb))

end
end CompoundFeasibility
