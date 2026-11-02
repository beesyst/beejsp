import SubspaceBridge.SourceLattice10
import SubspaceBridge.Minima10
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section
noncomputable def weightedCoordinates10 {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := e x i / w i
  invFun y := e.symm (fun i => y i * w i)
  map_add' x y := by ext i; simp [add_div]
  map_smul' r x := by ext i; simp [smul_eq_mul,mul_div_assoc]
  left_inv x := by
    change e.symm (fun i => (e x i / w i) * w i) = x
    have h : (fun i => (e x i / w i) * w i) = e x :=
      funext (fun i => div_mul_cancel₀ _ (hw i).ne')
    rw [h,e.symm_apply_apply]
  right_inv y := by
    change (fun i => e (e.symm (fun j => y j * w j)) i / w i) = y
    rw [e.apply_symm_apply]
    exact funext (fun i => mul_div_cancel_right₀ _ (hw i).ne')

noncomputable def originalFormEquiv10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' L) (by
    have hu := hL
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem originalFormEquiv10_apply (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (x : Fin 10 → ℝ) : originalFormEquiv10 L hL x = L *ᵥ x := rfl

noncomputable def originalCoordinates10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 10 → ℝ) : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  weightedCoordinates10 (originalFormEquiv10 L hL)
    (fun s => Q ^ c₀ s)
    (fun s => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)

def originalBody10 (L : Matrix (Fin 10) (Fin 10) ℝ) (Q : ℝ) (c₀ : Fin 10 → ℝ) : Set (Fin 10 → ℝ) :=
  {x | ∀ s, |(L *ᵥ x) s| ≤ Q ^ c₀ s}

theorem originalCoordinates10_bounds (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 10 → ℝ) (x : Fin 10 → ℝ) (r : ℝ) :
    ‖originalCoordinates10 L hL Q hQ c₀ x‖ ≤ r ↔
      ∀ s, |(L *ᵥ x) s| ≤ r * (Q ^ c₀ s) := by
  rw [pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro s
  have hw : 0 < Q ^ c₀ s := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  change ‖(L *ᵥ x) s / (Q ^ c₀ s)‖ ≤ r ↔ _
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hw,div_le_iff₀ hw]

theorem originalBody10_mem_iff (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 10 → ℝ) (x : Fin 10 → ℝ) :
    x ∈ originalBody10 L Q c₀ ↔ ‖originalCoordinates10 L hL Q hQ c₀ x‖ ≤ 1 := by
  rw [originalCoordinates10_bounds]
  simp only [one_mul,originalBody10,Set.mem_setOf_eq]


noncomputable def sourceRealBasis10 (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) : Basis (Fin 10) ℝ (Fin 10 → ℝ) :=
  (integerRealImageBasis (sourceLattice10 A₂ A₃ e₂ e₃)
    (sourceLattice10_has_basis A₂ A₃ e₂ e₃).some).ofZLatticeBasis ℝ
      (integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃))

theorem sourceRealBasis10_span (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (e₂ e₃ : Fin 10 → ℕ) :
    lattice10Span (sourceRealBasis10 A₂ A₃ e₂ e₃) = integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃) :=
  Basis.ofZLatticeBasis_span ℝ (integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃))
    (integerRealImageBasis (sourceLattice10 A₂ A₃ e₂ e₃) (sourceLattice10_has_basis A₂ A₃ e₂ e₃).some)

noncomputable def originalSourceGroup10 (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 10 → ℝ) : AddSubgroup (Fin 10 → ℤ) :=
  sourceLattice10 A₂ A₃ (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))

noncomputable def sourceMinima10 (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ) (j : Fin 10) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (j.val+1) → (Fin 10 → ℝ), LinearIndependent ℝ u ∧
    (∀ i, u i ∈ integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ∧
    ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c₀) (u i) ≤ r}

theorem sourceMinima10_eq_radius (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ) (j : Fin 10) :
    sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j =
      successiveRadius10 (sourceRealBasis10 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))
        (originalCoordinates10 L hL Q hQ c₀) j := by
  simp only [sourceMinima10,successiveRadius10,sourceRealBasis10_span,originalSourceGroup10]

theorem exists_sourceMinima10_attaining (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ) :
    ∃ u : Fin 10 → originalSourceGroup10 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 10 → ℤ)) ∧
      (∀ j, 0 < sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ c₀)
        (integerReal (u j : Fin 10 → ℤ)) = sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      ∀ j s, |(L *ᵥ integerReal (u j : Fin 10 → ℤ)) s| ≤
        sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j * (Q ^ c₀ s) := by
  classical
  let e₂ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))
  let e₃ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))
  let b := sourceRealBasis10 A₂ A₃ e₂ e₃
  let e := originalCoordinates10 L hL Q hQ c₀
  obtain ⟨v,hv,hvL,hpos,hmono,hatt,_⟩ := exists_successive_minima10 b e
  have hrad (j : Fin 10) : sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = successiveRadius10 b e j :=
    sourceMinima10_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hvImage (j : Fin 10) : v j ∈ integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃) := by
    change v j ∈ integerRealImage (sourceLattice10 A₂ A₃ e₂ e₃)
    rw [← sourceRealBasis10_span A₂ A₃ e₂ e₃]
    exact hvL j
  have hlift (j : Fin 10) : ∃ x : originalSourceGroup10 A₂ A₃ Q c₂ c₃,
      integerReal (x : Fin 10 → ℤ) = v j := by
    obtain ⟨x,hx,he⟩ := hvImage j
    exact ⟨⟨x,hx⟩,he⟩
  choose u hu using hlift
  have hfun : (fun j => integerReal (u j : Fin 10 → ℤ)) = v := funext hu
  refine ⟨u,?_,?_,?_,?_,?_⟩
  · rw [hfun]
    exact hv
  · intro j
    rw [hrad]
    exact hpos j
  · intro i j hij
    rw [hrad,hrad]
    exact hmono hij
  · intro j
    rw [hu j,hrad]
    exact hatt j
  · intro j
    apply (originalCoordinates10_bounds L hL Q hQ c₀ _ _).mp
    change coordinateGauge10 e (integerReal (u j : Fin 10 → ℤ)) ≤ _
    rw [hu j,hrad,hatt j]


theorem sourceMinima10_admissible (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ) (j : Fin 10) :
    ∃ v : Fin (j.val+1) → (Fin 10 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c₀) (v i) ≤
        sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima10_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let f : Fin (j.val+1) → Fin 10 := Fin.castLE (by omega)
  refine ⟨fun i => integerReal (u (f i) : Fin 10 → ℤ),
    hu.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    exact ⟨(u (f i) : Fin 10 → ℤ),(u (f i)).property,rfl⟩
  · intro i
    rw [hatt]
    exact hmono (show f i ≤ j from (by change i.val ≤ j.val; omega))

theorem sourceMinima10_radius_set_properties (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ) (j : Fin 10) :
    let S := {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 10 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c₀) (v i) ≤ r}
    S.Nonempty ∧ BddBelow S ∧ IsLeast S (sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) := by
  dsimp only
  have hm := sourceMinima10_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hne : ({r : ℝ | ∃ v : Fin (j.val+1) → (Fin 10 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c₀) (v i) ≤ r}).Nonempty := ⟨_,hm⟩
  have hb : BddBelow {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 10 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup10 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge10 (originalCoordinates10 L hL Q hQ c₀) (v i) ≤ r} := by
    refine ⟨0,?_⟩
    rintro r ⟨v,_,_,hv⟩
    exact (norm_nonneg _).trans (hv 0)
  refine ⟨hne,hb,hm,?_⟩
  intro r hr
  exact csInf_le hb hr

theorem sourceMinima10_pos_mono (A₂ A₃ : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 10 → ℝ) :
    (∀ j, 0 < sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima10 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima10_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨hpos,hmono⟩

theorem weightedCoordinates10_det {n : ℕ} (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) :
    LinearMap.det (weightedCoordinates10 A w hw).toLinearMap = LinearMap.det A.toLinearMap / ∏ i, w i := by
  let B := Pi.basisFun ℝ (Fin n)
  have hm : LinearMap.toMatrix B B (weightedCoordinates10 A w hw).toLinearMap =
      Matrix.diagonal (fun i => (w i)⁻¹) * LinearMap.toMatrix B B A.toLinearMap := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, Pi.basisFun_repr, Matrix.diagonal_mul,
      weightedCoordinates10, div_eq_mul_inv, mul_comm]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_mul, Matrix.det_diagonal,
    Finset.prod_inv_distrib, LinearMap.det_toMatrix]
  ring

theorem originalCoordinates10_det (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 10 → ℝ) :
    LinearMap.det (originalCoordinates10 L hL Q hQ c₀).toLinearMap = L.det / ∏ i, Q ^ c₀ i := by
  rw [originalCoordinates10,weightedCoordinates10_det]
  congr 1
  exact LinearMap.det_toLin' L

theorem originalBody10_volume (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 10 → ℝ) :
    volume.real (originalBody10 L Q c₀) = 1024 * (∏ i, Q ^ c₀ i) / |L.det| := by
  have hw : 0 < ∏ i, Q ^ c₀ i := Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  have he : originalBody10 L Q c₀ = (originalCoordinates10 L hL Q hQ c₀) ⁻¹'
      Set.pi Set.univ (fun _ : Fin 10 => Set.Icc (-1 : ℝ) 1) := by
    ext x
    rw [originalBody10_mem_iff L hL Q hQ c₀ x,pi_norm_le_iff_of_nonempty]
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_const,Set.mem_Icc,Real.norm_eq_abs,abs_le]
  have hvol : volume.real (originalBody10 L Q c₀) =
      1024 / |LinearMap.det (originalCoordinates10 L hL Q hQ c₀).toLinearMap| := by
    rw [measureReal_def,he,Measure.addHaar_preimage_linearEquiv,volume_pi,Measure.pi_pi]
    simp only [Real.volume_Icc,LinearEquiv.det_coe_symm,abs_inv,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal,abs_nonneg,div_eq_mul_inv]
    norm_num
    ring
  rw [hvol,originalCoordinates10_det,abs_div,abs_of_pos hw]
  field_simp



end
end CompoundFeasibility
