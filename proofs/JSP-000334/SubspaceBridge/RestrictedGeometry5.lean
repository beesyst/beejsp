import SubspaceBridge.OriginalNonRothFlag5
open scoped BigOperators Matrix
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry5

def rationalRealSpan5 (P : Submodule ℚ (Fin 5 → ℚ)) : Submodule ℝ (Fin 5 → ℝ) :=
  Submodule.span ℝ ((fun x : Fin 5 → ℚ => fun i => (x i : ℝ)) '' (P : Set (Fin 5 → ℚ)))

theorem rational_real_independent5 (d : Fin 5) (u : Fin d.val → Fin 5 → ℚ)
    (hu : LinearIndependent ℚ u) : LinearIndependent ℝ (fun j i => (u j i : ℝ)) := by
  classical
  let f := Fintype.linearCombination ℚ u
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hu.fintypeLinearCombination_injective)
  let U : Matrix (Fin 5) (Fin d.val) ℚ := fun i j => u j i
  let G := LinearMap.toMatrix' g
  have hfmat : LinearMap.toMatrix' f = U := by
    ext i j
    simp [f,U,LinearMap.toMatrix'_apply,Fintype.linearCombination_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ite_apply]
  have hGU : G * U = 1 := by
    dsimp only [G]
    rw [← hfmat,← LinearMap.toMatrix'_comp,hg,LinearMap.toMatrix'_id]
  let UR := U.map (algebraMap ℚ ℝ)
  let GR := G.map (algebraMap ℚ ℝ)
  have hGR : GR * UR = 1 := by
    dsimp only [GR,UR]
    rw [← Matrix.map_mul,hGU,Matrix.map_one] <;> simp
  have hinj : Function.Injective (Matrix.toLin' UR) := by
    apply Function.LeftInverse.injective (g := Matrix.toLin' GR)
    intro x
    change GR *ᵥ (UR *ᵥ x) = x
    rw [Matrix.mulVec_mulVec,hGR,Matrix.one_mulVec]
  have hli := (Pi.basisFun ℝ (Fin d.val)).linearIndependent.map'
    (Matrix.toLin' UR) (LinearMap.ker_eq_bot.mpr hinj)
  convert hli using 1
  funext j i
  simp [UR,U,Pi.basisFun_apply,Matrix.toLin'_apply,Matrix.mulVec,Pi.single_apply]


theorem rationalRealSpan5_basis_span (P : Submodule ℚ (Fin 5 → ℚ)) (d : Fin 5)
    (b : Basis (Fin d.val) ℚ P) :
    Submodule.span ℝ (Set.range (fun j i => ((b j : Fin 5 → ℚ) i : ℝ))) = rationalRealSpan5 P := by
  let W := Submodule.span ℝ (Set.range (fun j i => ((b j : Fin 5 → ℚ) i : ℝ)))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    apply Submodule.subset_span
    exact ⟨(b j : Fin 5 → ℚ),(b j).property,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    let y : P := ⟨x,hx⟩
    have heq : (fun i => (x i : ℝ)) =
        ∑ j : Fin d.val, (b.repr y j : ℝ) • (fun i => ((b j : Fin 5 → ℚ) i : ℝ)) := by
      have hQ := congrArg (fun z : P => (z : Fin 5 → ℚ)) (b.sum_repr y)
      ext i
      have hi := congrFun hQ i
      simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
        smul_eq_mul] at hi
      change ∑ j, b.repr y j * (b j : Fin 5 → ℚ) i = x i at hi
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact_mod_cast hi.symm
    change (fun i => (x i : ℝ)) ∈ W
    rw [heq]
    exact Submodule.sum_mem W (fun j _ => W.smul_mem _ (Submodule.subset_span ⟨j,rfl⟩))

theorem rationalRealSpan5_finrank (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) :
    Module.finrank ℝ (rationalRealSpan5 P) = Module.finrank ℚ P := by
  let d : Fin 5 := ⟨Module.finrank ℚ P,by omega⟩
  let b : Basis (Fin d.val) ℚ P := Module.finBasis ℚ P
  have hQ : LinearIndependent ℚ (fun j => (b j : Fin 5 → ℚ)) :=
    b.linearIndependent.map' P.subtype P.ker_subtype
  have hR := rational_real_independent5 d (fun j => (b j : Fin 5 → ℚ)) hQ
  rw [← rationalRealSpan5_basis_span P d b,finrank_span_eq_card hR,Fintype.card_fin]


def restrictedLattice5 (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    Submodule ℤ (rationalRealSpan5 P) :=
  (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)).comap
    ((rationalRealSpan5 P).subtype.restrictScalars ℤ)

theorem rational_source_multiple5 (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (x : Fin 5 → ℚ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ w : Fin 5 → ℤ,
      w ∈ originalSourceGroup5 A₂ A₃ Q c₂ c₃ ∧
      integerReal w = (m : ℝ) • (fun i => (x i : ℝ)) := by
  classical
  obtain ⟨D,hD,hm⟩ := clear_matrix_denominators (fun _ i : Fin 5 => x i)
  choose z hz using hm (0 : Fin 5)
  obtain ⟨E,hE,hEmem⟩ := sourceLattice5_multiple A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  let G := originalSourceGroup5 A₂ A₃ Q c₂ c₃
  have hwm : E • z ∈ G := by
    have hrepr : E • z = ∑ j : Fin 5, z j • Pi.single j E := by
      ext i
      simp [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Pi.single_apply,mul_comm]
    rw [hrepr]
    exact G.sum_mem (fun j _ => G.zsmul_mem (hEmem j) (z j))
  refine ⟨E*D,mul_ne_zero hE hD,E • z,hwm,?_⟩
  ext i
  change ((E * z i : ℤ) : ℝ) = ((E*D : ℤ) : ℝ) * (x i : ℝ)
  have hzr : (z i : ℝ) = (D : ℝ) * (x i : ℝ) := by exact_mod_cast hz i
  push_cast
  rw [hzr]
  ring

instance restrictedLattice5_discrete (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    DiscreteTopology (restrictedLattice5 P A₂ A₃ Q c₂ c₃) := by
  let f : restrictedLattice5 P A₂ A₃ Q c₂ c₃ →
      integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃) :=
    fun x => ⟨x.val.val,x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃) =>
      (z : Fin 5 → ℝ)) h

instance restrictedLattice5_isZLattice (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    IsZLattice ℝ (restrictedLattice5 P A₂ A₃ Q c₂ c₃) where
  span_top := by
    let S := rationalRealSpan5 P
    let K := Submodule.span ℝ (restrictedLattice5 P A₂ A₃ Q c₂ c₃ : Set S)
    have hSK : S ≤ K.map S.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,hx,rfl⟩
      obtain ⟨m,hm,w,hw,heq⟩ := rational_source_multiple5 A₂ A₃ Q c₂ c₃ x
      have hxS : (fun i => (x i : ℝ)) ∈ S := Submodule.subset_span ⟨x,hx,rfl⟩
      let y : S := ⟨integerReal w,heq ▸ S.smul_mem (m : ℝ) hxS⟩
      have hy : y ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃ := by
        change integerReal w ∈ integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)
        exact ⟨w,hw,rfl⟩
      have hmem : (m : ℝ) • (fun i => (x i : ℝ)) ∈ K.map S.subtype := by
        rw [← heq]
        exact ⟨y,Submodule.subset_span hy,rfl⟩
      exact (Submodule.smul_mem_iff (K.map S.subtype) (by exact_mod_cast hm : (m : ℝ) ≠ 0)).mp hmem
    apply Submodule.map_injective_of_injective S.subtype_injective
    apply le_antisymm
    · exact Submodule.map_mono le_top
    · simpa only [Submodule.map_top,Submodule.range_subtype] using hSK


def restrictedBody5 (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c₀ : Fin 5 → ℝ) :
    Set (rationalRealSpan5 P) :=
  (fun x : rationalRealSpan5 P => (x : Fin 5 → ℝ)) ⁻¹' originalBody5 L Q c₀

def restrictedGauge5 (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) (x : rationalRealSpan5 P) : ℝ :=
  coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) (x : Fin 5 → ℝ)

instance rationalRealSpan5_borel (P : Submodule ℚ (Fin 5 → ℚ)) :
    BorelSpace (rationalRealSpan5 P) := Subtype.borelSpace _

def restrictedMeasure5 (P : Submodule ℚ (Fin 5 → ℚ)) : Measure (rationalRealSpan5 P) :=
  (Module.finBasis ℝ (rationalRealSpan5 P)).addHaar

instance restrictedMeasure5_haar (P : Submodule ℚ (Fin 5 → ℚ)) :
    (restrictedMeasure5 P).IsAddHaarMeasure := by
  unfold restrictedMeasure5
  infer_instance

theorem restrictedLattice5_rank (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    Module.finrank ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃) = Module.finrank ℚ P := by
  rw [ZLattice.rank ℝ,rationalRealSpan5_finrank P hP]

theorem restrictedLattice5_covolume_pos (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    0 < ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) :=
  ZLattice.covolume_pos _ _

theorem restrictedBody5_gauge (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    restrictedBody5 P L Q c₀ = {x | restrictedGauge5 P L hL Q hQ c₀ x ≤ 1} := by
  ext x
  exact originalBody5_mem_iff L hL Q hQ c₀ x

theorem restrictedBody5_compact_convex (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    IsCompact (restrictedBody5 P L Q c₀) ∧ Convex ℝ (restrictedBody5 P L Q c₀) := by
  let S := rationalRealSpan5 P
  let e := originalCoordinates5 L hL Q hQ c₀
  have hbody : originalBody5 L Q c₀ = e ⁻¹' Metric.closedBall (0 : Fin 5 → ℝ) 1 := by
    ext x
    rw [originalBody5_mem_iff L hL Q hQ c₀]
    simp only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right]
    rfl
  have hc : IsCompact (originalBody5 L Q c₀) := by
    rw [hbody]
    exact e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hv : Convex ℝ (originalBody5 L Q c₀) := by
    rw [hbody]
    exact (convex_closedBall (0 : Fin 5 → ℝ) 1).linear_preimage e.toLinearMap
  constructor
  · exact S.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hc
  · exact hv.linear_preimage S.subtype


theorem restrictedBody5_symmetric (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    ∀ x ∈ restrictedBody5 P L Q c₀, -x ∈ restrictedBody5 P L Q c₀ := by
  rw [restrictedBody5_gauge P L hL Q hQ c₀]
  intro x hx
  simpa [restrictedGauge5,coordinateGauge5,map_neg] using hx

theorem restrictedBody5_zero_interior (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    (0 : rationalRealSpan5 P) ∈ interior (restrictedBody5 P L Q c₀) := by
  rw [restrictedBody5_gauge P L hL Q hQ c₀]
  let e := originalCoordinates5 L hL Q hQ c₀
  have hg : Continuous (restrictedGauge5 P L hL Q hQ c₀) :=
    (e.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).norm
  apply mem_interior_iff_mem_nhds.mpr
  have hopen := (isOpen_lt hg continuous_const).mem_nhds
    (show restrictedGauge5 P L hL Q hQ c₀ 0 < 1 by simp [restrictedGauge5,coordinateGauge5])
  exact Filter.mem_of_superset hopen (fun x hx =>
    (show restrictedGauge5 P L hL Q hQ c₀ x < 1 from hx).le)

theorem restrictedBody5_volume_pos_finite (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    0 < (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) ∧
      (restrictedMeasure5 P) (restrictedBody5 P L Q c₀) < ⊤ := by
  have hfinite := (restrictedBody5_compact_convex P L hL Q hQ c₀).1.measure_lt_top
    (μ := restrictedMeasure5 P)
  have hpos := Measure.measure_pos_of_nonempty_interior (restrictedMeasure5 P)
    ⟨0,restrictedBody5_zero_interior P L hL Q hQ c₀⟩
  exact ⟨ENNReal.toReal_pos hpos.ne' hfinite.ne,hfinite⟩


def restrictedRadii5 (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (k : Fin (Module.finrank ℚ P)) : Set ℝ :=
  {r | ∃ v : Fin (k.val+1) → rationalRealSpan5 P, LinearIndependent ℝ v ∧
    (∀ i, v i ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃) ∧
    ∀ i, restrictedGauge5 P L hL Q hQ c₀ (v i) ≤ r}

def restrictedMinima5 (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (k : Fin (Module.finrank ℚ P)) : ℝ :=
  sInf (restrictedRadii5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)

theorem restrictedRadii5_bddBelow (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    BddBelow (restrictedRadii5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k) := by
  refine ⟨0,?_⟩
  rintro r ⟨v,_,_,hv⟩
  exact (norm_nonneg _).trans (hv 0)

def ambientPrefixIndex5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    Fin (Module.finrank ℚ P) → Fin 5 := Fin.castLE (by omega)

theorem source_restricted_prefix_eq5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ)
    (u : Fin (Module.finrank ℚ P) → originalSourceGroup5 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 5 → ℤ)))
    (huS : ∀ i, integerReal (u i : Fin 5 → ℤ) ∈ rationalRealSpan5 P)
    (hatt : ∀ i, coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀)
      (integerReal (u i : Fin 5 → ℤ)) =
      sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex5 P hP i)) :
    ∀ k, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k =
      sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex5 P hP k) := by
  let S := rationalRealSpan5 P
  let v : Fin (Module.finrank ℚ P) → S := fun i => ⟨integerReal (u i : Fin 5 → ℤ),huS i⟩
  have hv : LinearIndependent ℝ v := LinearIndependent.of_comp S.subtype hu
  intro k
  let emb : Fin (k.val+1) → Fin (Module.finrank ℚ P) := Fin.castLE (by omega)
  let w := v ∘ emb
  have hw : sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex5 P hP k) ∈
      restrictedRadii5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k := by
    refine ⟨w,hv.comp emb (Fin.castLE_injective _),?_,?_⟩
    · intro i
      change integerReal (u (emb i) : Fin 5 → ℤ) ∈
        integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)
      exact ⟨(u (emb i) : Fin 5 → ℤ),(u (emb i)).property,rfl⟩
    · intro i
      change coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀)
        (integerReal (u (emb i) : Fin 5 → ℤ)) ≤ _
      rw [hatt]
      exact (sourceMinima5_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).2
        (show ambientPrefixIndex5 P hP (emb i) ≤ ambientPrefixIndex5 P hP k by
          change i.val ≤ k.val; omega)
  apply le_antisymm
  · exact csInf_le (restrictedRadii5_bddBelow P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k) hw
  · apply le_csInf ⟨_,hw⟩
    rintro r ⟨a,ha,haL,har⟩
    apply csInf_le (sourceMinima5_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃
      (ambientPrefixIndex5 P hP k)).2.1
    refine ⟨fun i => (a i : Fin 5 → ℝ),ha.map' S.subtype S.ker_subtype,haL,har⟩


def restrictedRealBasis5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan5 P) :=
  (Module.finBasisOfFinrankEq ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃)
    (restrictedLattice5_rank P hP A₂ A₃ Q c₂ c₃)).ofZLatticeBasis ℝ _

theorem restrictedRealBasis5_span (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    Submodule.span ℤ (Set.range (restrictedRealBasis5 P hP A₂ A₃ Q c₂ c₃)) =
      restrictedLattice5 P A₂ A₃ Q c₂ c₃ := Basis.ofZLatticeBasis_span ℝ _ _

theorem restrictedRadii5_nonempty (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    (restrictedRadii5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k).Nonempty := by
  let b := restrictedRealBasis5 P hP A₂ A₃ Q c₂ c₃
  let emb : Fin (k.val+1) → Fin (Module.finrank ℚ P) := Fin.castLE (by omega)
  refine ⟨∑ j, restrictedGauge5 P L hL Q hQ c₀ (b j),fun i => b (emb i),
    b.linearIndependent.comp emb (Fin.castLE_injective _),?_,?_⟩
  · intro i
    rw [← restrictedRealBasis5_span P hP A₂ A₃ Q c₂ c₃]
    exact Submodule.subset_span ⟨emb i,rfl⟩
  · intro i
    have hnonneg (j) : 0 ≤ restrictedGauge5 P L hL Q hQ c₀ (b j) := norm_nonneg _
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ (emb i))

theorem restrictedMinima5_ge_ambient (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex5 P hP k) ≤
      restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k := by
  apply le_csInf (restrictedRadii5_nonempty P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)
  rintro r ⟨a,ha,haL,har⟩
  apply csInf_le (sourceMinima5_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃
    (ambientPrefixIndex5 P hP k)).2.1
  exact ⟨fun i => (a i : Fin 5 → ℝ),ha.map' (rationalRealSpan5 P).subtype
    (rationalRealSpan5 P).ker_subtype,haL,har⟩

theorem restrictedMinima5_pos (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    0 < restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k :=
  ((sourceMinima5_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 _).trans_le
    (restrictedMinima5_ge_ambient P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)

theorem restrictedGauge5_ball_compact (P : Submodule ℚ (Fin 5 → ℚ))
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) (r : ℝ) :
    IsCompact {x | restrictedGauge5 P L hL Q hQ c₀ x ≤ r} := by
  let S := rationalRealSpan5 P
  let e := originalCoordinates5 L hL Q hQ c₀
  have heq : {x | restrictedGauge5 P L hL Q hQ c₀ x ≤ r} =
      S.subtype ⁻¹' (e ⁻¹' Metric.closedBall (0 : Fin 5 → ℝ) r) := by
    ext x
    simp [restrictedGauge5,coordinateGauge5,Metric.mem_closedBall,dist_zero_right,e]
  rw [heq]
  exact S.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage
    (e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _))

theorem restrictedGauge5_ball_finite (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (r : ℝ) :
    ({x | restrictedGauge5 P L hL Q hQ c₀ x ≤ r} ∩
      (restrictedLattice5 P A₂ A₃ Q c₂ c₃ : Set (rationalRealSpan5 P))).Finite := by
  rw [← restrictedRealBasis5_span P hP A₂ A₃ Q c₂ c₃]
  exact ZSpan.setFinite_inter _ (restrictedGauge5_ball_compact P L hL Q hQ c₀ r).isBounded

theorem exists_restricted_shortest_outside5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ)
    (W : Submodule ℝ (rationalRealSpan5 P)) (hW : W ≠ ⊤) :
    ∃ x ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃, x ∉ W ∧
      ∀ y ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃, y ∉ W →
        restrictedGauge5 P L hL Q hQ c₀ x ≤ restrictedGauge5 P L hL Q hQ c₀ y := by
  classical
  let b := restrictedRealBasis5 P hP A₂ A₃ Q c₂ c₃
  have hex : ∃ i, b i ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)
  obtain ⟨i,hi⟩ := hex
  let f := restrictedGauge5 P L hL Q hQ c₀
  let G := restrictedLattice5 P A₂ A₃ Q c₂ c₃
  let T := {x | f x ≤ f (b i)} ∩ (G : Set (rationalRealSpan5 P)) ∩ {x | x ∉ W}
  have hfinite : T.Finite := (restrictedGauge5_ball_finite P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ _).inter_of_left _
  have hbi : b i ∈ G := by
    change b i ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃
    rw [← restrictedRealBasis5_span P hP A₂ A₃ Q c₂ c₃]
    exact Submodule.subset_span ⟨i,rfl⟩
  obtain ⟨x,hx,hmin⟩ := Set.exists_min_image T f hfinite ⟨b i,⟨⟨show f (b i) ≤ f (b i) from le_rfl,hbi⟩,hi⟩⟩
  refine ⟨x,hx.1.2,hx.2,?_⟩
  intro y hy hyW
  by_cases hle : f y ≤ f (b i)
  · exact hmin y ⟨⟨hle,hy⟩,hyW⟩
  · exact hx.1.1.trans (le_of_not_ge hle)

end CompoundFeasibility.RestrictedGeometry5
