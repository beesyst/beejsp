import SubspaceBridge.SourceLattice5
import SubspaceBridge.Minima5
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section
noncomputable def weightedCoordinates5 (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ))
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 < w i) : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) where
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

noncomputable def originalFormEquiv5 (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' L) (by
    have hu := hL
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem originalFormEquiv5_apply (L : Matrix (Fin 5) (Fin 5) ℝ)
    (hL : IsUnit L) (x : Fin 5 → ℝ) : originalFormEquiv5 L hL x = L *ᵥ x := rfl

noncomputable def originalCoordinates5 (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) :=
  weightedCoordinates5 (originalFormEquiv5 L hL)
    (fun s => Q ^ c₀ s)
    (fun s => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)

def originalBody5 (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c₀ : Fin 5 → ℝ) : Set (Fin 5 → ℝ) :=
  {x | ∀ s, |(L *ᵥ x) s| ≤ Q ^ c₀ s}

theorem originalCoordinates5_bounds (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) (x : Fin 5 → ℝ) (r : ℝ) :
    ‖originalCoordinates5 L hL Q hQ c₀ x‖ ≤ r ↔
      ∀ s, |(L *ᵥ x) s| ≤ r * (Q ^ c₀ s) := by
  rw [pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro s
  have hw : 0 < Q ^ c₀ s := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  change ‖(L *ᵥ x) s / (Q ^ c₀ s)‖ ≤ r ↔ _
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hw,div_le_iff₀ hw]

theorem originalBody5_mem_iff (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) (x : Fin 5 → ℝ) :
    x ∈ originalBody5 L Q c₀ ↔ ‖originalCoordinates5 L hL Q hQ c₀ x‖ ≤ 1 := by
  rw [originalCoordinates5_bounds]
  simp only [one_mul,originalBody5,Set.mem_setOf_eq]


noncomputable def sourceRealBasis5 (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : Basis (Fin 5) ℝ (Fin 5 → ℝ) :=
  (integerRealImageBasis (sourceLattice5 A₂ A₃ e₂ e₃)
    (sourceLattice5_has_basis A₂ A₃ e₂ e₃).some).ofZLatticeBasis ℝ
      (integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃))

theorem sourceRealBasis5_span (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) :
    lattice5Span (sourceRealBasis5 A₂ A₃ e₂ e₃) = integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃) :=
  Basis.ofZLatticeBasis_span ℝ (integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃))
    (integerRealImageBasis (sourceLattice5 A₂ A₃ e₂ e₃) (sourceLattice5_has_basis A₂ A₃ e₂ e₃).some)

noncomputable def originalSourceGroup5 (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) : AddSubgroup (Fin 5 → ℤ) :=
  sourceLattice5 A₂ A₃ (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))

noncomputable def sourceMinima5 (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (j : Fin 5) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (j.val+1) → (Fin 5 → ℝ), LinearIndependent ℝ u ∧
    (∀ i, u i ∈ integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ∧
    ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) (u i) ≤ r}

theorem sourceMinima5_eq_radius (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (j : Fin 5) :
    sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j =
      successiveRadius5 (sourceRealBasis5 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))
        (originalCoordinates5 L hL Q hQ c₀) j := by
  simp only [sourceMinima5,successiveRadius5,sourceRealBasis5_span,originalSourceGroup5]

theorem exists_sourceMinima5_attaining (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) :
    ∃ u : Fin 5 → originalSourceGroup5 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 5 → ℤ)) ∧
      (∀ j, 0 < sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ j, coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀)
        (integerReal (u j : Fin 5 → ℤ)) = sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      ∀ j s, |(L *ᵥ integerReal (u j : Fin 5 → ℤ)) s| ≤
        sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j * (Q ^ c₀ s) := by
  classical
  let e₂ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))
  let e₃ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))
  let b := sourceRealBasis5 A₂ A₃ e₂ e₃
  let e := originalCoordinates5 L hL Q hQ c₀
  obtain ⟨v,hv,hvL,hpos,hmono,hatt,_⟩ := exists_successive_minima5 b e
  have hrad (j : Fin 5) : sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = successiveRadius5 b e j :=
    sourceMinima5_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hvImage (j : Fin 5) : v j ∈ integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃) := by
    change v j ∈ integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃)
    rw [← sourceRealBasis5_span A₂ A₃ e₂ e₃]
    exact hvL j
  have hlift (j : Fin 5) : ∃ x : originalSourceGroup5 A₂ A₃ Q c₂ c₃,
      integerReal (x : Fin 5 → ℤ) = v j := by
    obtain ⟨x,hx,he⟩ := hvImage j
    exact ⟨⟨x,hx⟩,he⟩
  choose u hu using hlift
  have hfun : (fun j => integerReal (u j : Fin 5 → ℤ)) = v := funext hu
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
    apply (originalCoordinates5_bounds L hL Q hQ c₀ _ _).mp
    change coordinateGauge5 e (integerReal (u j : Fin 5 → ℤ)) ≤ _
    rw [hu j,hrad,hatt j]


theorem sourceMinima5_admissible (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (j : Fin 5) :
    ∃ v : Fin (j.val+1) → (Fin 5 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) (v i) ≤
        sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima5_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let f : Fin (j.val+1) → Fin 5 := Fin.castLE (by omega)
  refine ⟨fun i => integerReal (u (f i) : Fin 5 → ℤ),
    hu.comp f (Fin.castLE_injective _),?_,?_⟩
  · intro i
    exact ⟨(u (f i) : Fin 5 → ℤ),(u (f i)).property,rfl⟩
  · intro i
    rw [hatt]
    exact hmono (show f i ≤ j from (by change i.val ≤ j.val; omega))

theorem sourceMinima5_radius_set_properties (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (j : Fin 5) :
    let S := {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 5 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) (v i) ≤ r}
    S.Nonempty ∧ BddBelow S ∧ IsLeast S (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) := by
  dsimp only
  have hm := sourceMinima5_admissible A₂ A₃ L hL Q hQ c₀ c₂ c₃ j
  have hne : ({r : ℝ | ∃ v : Fin (j.val+1) → (Fin 5 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) (v i) ≤ r}).Nonempty := ⟨_,hm⟩
  have hb : BddBelow {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 5 → ℝ), LinearIndependent ℝ v ∧
      (∀ i, v i ∈ integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ∧
      ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) (v i) ≤ r} := by
    refine ⟨0,?_⟩
    rintro r ⟨v,_,_,hv⟩
    exact (norm_nonneg _).trans (hv 0)
  refine ⟨hne,hb,hm,?_⟩
  intro r hr
  exact csInf_le hb hr

theorem sourceMinima5_pos_mono (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) :
    (∀ j, 0 < sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima5_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨hpos,hmono⟩

theorem weightedCoordinates5_det (A : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (w : Fin 5 → ℝ)
    (hw : ∀ i, 0 < w i) :
    LinearMap.det (weightedCoordinates5 A w hw).toLinearMap = LinearMap.det A.toLinearMap / ∏ i, w i := by
  let B := Pi.basisFun ℝ (Fin 5)
  have hm : LinearMap.toMatrix B B (weightedCoordinates5 A w hw).toLinearMap =
      Matrix.diagonal (fun i => (w i)⁻¹) * LinearMap.toMatrix B B A.toLinearMap := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, Pi.basisFun_repr, Matrix.diagonal_mul,
      weightedCoordinates5, div_eq_mul_inv, mul_comm]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_mul, Matrix.det_diagonal,
    Finset.prod_inv_distrib, LinearMap.det_toMatrix]
  ring

theorem originalCoordinates5_det (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    LinearMap.det (originalCoordinates5 L hL Q hQ c₀).toLinearMap = L.det / ∏ i, Q ^ c₀ i := by
  rw [originalCoordinates5,weightedCoordinates5_det]
  congr 1
  exact LinearMap.det_toLin' L

theorem originalBody5_volume (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    volume.real (originalBody5 L Q c₀) = 32 * (∏ i, Q ^ c₀ i) / |L.det| := by
  have hw : 0 < ∏ i, Q ^ c₀ i := Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  have he : originalBody5 L Q c₀ = (originalCoordinates5 L hL Q hQ c₀) ⁻¹'
      Set.pi Set.univ (fun _ : Fin 5 => Set.Icc (-1 : ℝ) 1) := by
    ext x
    rw [originalBody5_mem_iff L hL Q hQ c₀ x,pi_norm_le_iff_of_nonempty]
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_const,Set.mem_Icc,Real.norm_eq_abs,abs_le]
  have hvol : volume.real (originalBody5 L Q c₀) =
      32 / |LinearMap.det (originalCoordinates5 L hL Q hQ c₀).toLinearMap| := by
    rw [measureReal_def,he,Measure.addHaar_preimage_linearEquiv,volume_pi,Measure.pi_pi]
    simp only [Real.volume_Icc,LinearEquiv.det_coe_symm,abs_inv,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal,abs_nonneg,div_eq_mul_inv]
    norm_num
    ring
  rw [hvol,originalCoordinates5_det,abs_div,abs_of_pos hw]
  field_simp



end
end CompoundFeasibility
