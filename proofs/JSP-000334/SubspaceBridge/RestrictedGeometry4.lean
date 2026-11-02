import SubspaceBridge.NonrothFixedFlag4
open scoped BigOperators Matrix
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry4

def rationalRealSpan4 (P : Submodule ℚ (Fin 4 → ℚ)) : Submodule ℝ (Fin 4 → ℝ) :=
  Submodule.span ℝ ((fun x : Fin 4 → ℚ => fun i => (x i : ℝ)) '' (P : Set (Fin 4 → ℚ)))

theorem rational_real_independent4 (d : Fin 4) (u : Fin d.val → Fin 4 → ℚ)
    (hu : LinearIndependent ℚ u) : LinearIndependent ℝ (fun j i => (u j i : ℝ)) := by
  classical
  let f := Fintype.linearCombination ℚ u
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hu.fintypeLinearCombination_injective)
  let U : Matrix (Fin 4) (Fin d.val) ℚ := fun i j => u j i
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


theorem rationalRealSpan4_basis_span (P : Submodule ℚ (Fin 4 → ℚ)) (d : Fin 4)
    (b : Basis (Fin d.val) ℚ P) :
    Submodule.span ℝ (Set.range (fun j i => ((b j : Fin 4 → ℚ) i : ℝ))) = rationalRealSpan4 P := by
  let W := Submodule.span ℝ (Set.range (fun j i => ((b j : Fin 4 → ℚ) i : ℝ)))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    apply Submodule.subset_span
    exact ⟨(b j : Fin 4 → ℚ),(b j).property,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    let y : P := ⟨x,hx⟩
    have heq : (fun i => (x i : ℝ)) =
        ∑ j : Fin d.val, (b.repr y j : ℝ) • (fun i => ((b j : Fin 4 → ℚ) i : ℝ)) := by
      have hQ := congrArg (fun z : P => (z : Fin 4 → ℚ)) (b.sum_repr y)
      ext i
      have hi := congrFun hQ i
      simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
        smul_eq_mul] at hi
      change ∑ j, b.repr y j * (b j : Fin 4 → ℚ) i = x i at hi
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact_mod_cast hi.symm
    change (fun i => (x i : ℝ)) ∈ W
    rw [heq]
    exact Submodule.sum_mem W (fun j _ => W.smul_mem _ (Submodule.subset_span ⟨j,rfl⟩))

theorem rationalRealSpan4_finrank (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) :
    Module.finrank ℝ (rationalRealSpan4 P) = Module.finrank ℚ P := by
  let d : Fin 4 := ⟨Module.finrank ℚ P,by omega⟩
  let b : Basis (Fin d.val) ℚ P := Module.finBasis ℚ P
  have hQ : LinearIndependent ℚ (fun j => (b j : Fin 4 → ℚ)) :=
    b.linearIndependent.map' P.subtype P.ker_subtype
  have hR := rational_real_independent4 d (fun j => (b j : Fin 4 → ℚ)) hQ
  rw [← rationalRealSpan4_basis_span P d b,finrank_span_eq_card hR,Fintype.card_fin]


def restrictedLattice4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    Submodule ℤ (rationalRealSpan4 P) :=
  (integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)).comap
    ((rationalRealSpan4 P).subtype.restrictScalars ℤ)

theorem rational_source_multiple4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (x : Fin 4 → ℚ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ w : Fin 4 → ℤ,
      w ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
      integerReal w = (m : ℝ) • (fun i => (x i : ℝ)) := by
  classical
  obtain ⟨D,hD,hm⟩ := clear_matrix_denominators (fun _ i : Fin 4 => x i)
  choose z hz using hm (0 : Fin 4)
  obtain ⟨E,hE,hEmem⟩ := sourceLattice4_multiple A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  let G := originalSourceGroup4 A₂ A₃ Q c₂ c₃
  have hwm : E • z ∈ G := by
    have hrepr : E • z = ∑ j : Fin 4, z j • Pi.single j E := by
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

instance restrictedLattice4_discrete (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    DiscreteTopology (restrictedLattice4 P A₂ A₃ Q c₂ c₃) := by
  let f : restrictedLattice4 P A₂ A₃ Q c₂ c₃ →
      integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃) :=
    fun x => ⟨x.val.val,x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃) =>
      (z : Fin 4 → ℝ)) h

instance restrictedLattice4_isZLattice (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    IsZLattice ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃) where
  span_top := by
    let S := rationalRealSpan4 P
    let K := Submodule.span ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃ : Set S)
    have hSK : S ≤ K.map S.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,hx,rfl⟩
      obtain ⟨m,hm,w,hw,heq⟩ := rational_source_multiple4 A₂ A₃ Q c₂ c₃ x
      have hxS : (fun i => (x i : ℝ)) ∈ S := Submodule.subset_span ⟨x,hx,rfl⟩
      let y : S := ⟨integerReal w,heq ▸ S.smul_mem (m : ℝ) hxS⟩
      have hy : y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃ := by
        change integerReal w ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)
        exact ⟨w,hw,rfl⟩
      have hmem : (m : ℝ) • (fun i => (x i : ℝ)) ∈ K.map S.subtype := by
        rw [← heq]
        exact ⟨y,Submodule.subset_span hy,rfl⟩
      exact (Submodule.smul_mem_iff (K.map S.subtype) (by exact_mod_cast hm : (m : ℝ) ≠ 0)).mp hmem
    apply Submodule.map_injective_of_injective S.subtype_injective
    apply le_antisymm
    · exact Submodule.map_mono le_top
    · simpa only [Submodule.map_top,Submodule.range_subtype] using hSK


def restrictedBody4 (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ : Fin 4 → ℝ) :
    Set (rationalRealSpan4 P) :=
  (fun x : rationalRealSpan4 P => (x : Fin 4 → ℝ)) ⁻¹' originalBody4 L Q c₀

def restrictedGauge4 (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : rationalRealSpan4 P) : ℝ :=
  coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (x : Fin 4 → ℝ)

instance rationalRealSpan4_borel (P : Submodule ℚ (Fin 4 → ℚ)) :
    BorelSpace (rationalRealSpan4 P) := Subtype.borelSpace _

def restrictedMeasure4 (P : Submodule ℚ (Fin 4 → ℚ)) : Measure (rationalRealSpan4 P) :=
  (Module.finBasis ℝ (rationalRealSpan4 P)).addHaar

instance restrictedMeasure4_haar (P : Submodule ℚ (Fin 4 → ℚ)) :
    (restrictedMeasure4 P).IsAddHaarMeasure := by
  unfold restrictedMeasure4
  infer_instance

theorem restrictedLattice4_rank (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    Module.finrank ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃) = Module.finrank ℚ P := by
  rw [ZLattice.rank ℝ,rationalRealSpan4_finrank P hP]

theorem restrictedLattice4_covolume_pos (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    0 < ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) :=
  ZLattice.covolume_pos _ _

theorem restrictedBody4_gauge (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    restrictedBody4 P L Q c₀ = {x | restrictedGauge4 P L hL Q hQ c₀ x ≤ 1} := by
  ext x
  exact originalBody4_mem_iff L hL Q hQ c₀ x

theorem restrictedBody4_compact_convex (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    IsCompact (restrictedBody4 P L Q c₀) ∧ Convex ℝ (restrictedBody4 P L Q c₀) := by
  let S := rationalRealSpan4 P
  let e := originalCoordinates4 L hL Q hQ c₀
  have hbody : originalBody4 L Q c₀ = parallelepipedBody4 e := by
    ext x
    rw [originalBody4_mem_iff L hL Q hQ c₀,mem_parallelepipedBody4_iff]
    rfl
  have hc := parallelepipedBody4_compact_convex e
  constructor
  · exact S.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage
      (hbody ▸ hc.1)
  · exact (hbody ▸ hc.2).linear_preimage S.subtype

theorem restrictedBody4_symmetric (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    ∀ x ∈ restrictedBody4 P L Q c₀, -x ∈ restrictedBody4 P L Q c₀ := by
  rw [restrictedBody4_gauge P L hL Q hQ c₀]
  intro x hx
  simpa [restrictedGauge4,coordinateGauge4,map_neg] using hx

theorem restrictedBody4_zero_interior (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    (0 : rationalRealSpan4 P) ∈ interior (restrictedBody4 P L Q c₀) := by
  rw [restrictedBody4_gauge P L hL Q hQ c₀]
  let e := originalCoordinates4 L hL Q hQ c₀
  have hg : Continuous (restrictedGauge4 P L hL Q hQ c₀) :=
    (e.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).norm
  apply mem_interior_iff_mem_nhds.mpr
  have hopen := (isOpen_lt hg continuous_const).mem_nhds
    (show restrictedGauge4 P L hL Q hQ c₀ 0 < 1 by simp [restrictedGauge4,coordinateGauge4])
  exact Filter.mem_of_superset hopen (fun x hx =>
    (show restrictedGauge4 P L hL Q hQ c₀ x < 1 from hx).le)

theorem restrictedBody4_volume_pos_finite (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) :
    0 < (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) ∧
      (restrictedMeasure4 P) (restrictedBody4 P L Q c₀) < ⊤ := by
  have hfinite := (restrictedBody4_compact_convex P L hL Q hQ c₀).1.measure_lt_top
    (μ := restrictedMeasure4 P)
  have hpos := Measure.measure_pos_of_nonempty_interior (restrictedMeasure4 P)
    ⟨0,restrictedBody4_zero_interior P L hL Q hQ c₀⟩
  exact ⟨ENNReal.toReal_pos hpos.ne' hfinite.ne,hfinite⟩


def restrictedRadii4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin (Module.finrank ℚ P)) : Set ℝ :=
  {r | ∃ v : Fin (k.val+1) → rationalRealSpan4 P, LinearIndependent ℝ v ∧
    (∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) ∧
    ∀ i, restrictedGauge4 P L hL Q hQ c₀ (v i) ≤ r}

def restrictedMinima4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin (Module.finrank ℚ P)) : ℝ :=
  sInf (restrictedRadii4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)

theorem restrictedRadii4_bddBelow (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    BddBelow (restrictedRadii4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k) := by
  refine ⟨0,?_⟩
  rintro r ⟨v,_,_,hv⟩
  exact (norm_nonneg _).trans (hv 0)

def ambientPrefixIndex4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Fin (Module.finrank ℚ P) → Fin 4 := Fin.castLE (by omega)

theorem source_restricted_prefix_eq4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (u : Fin (Module.finrank ℚ P) → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 4 → ℤ)))
    (huS : ∀ i, integerReal (u i : Fin 4 → ℤ) ∈ rationalRealSpan4 P)
    (hatt : ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀)
      (integerReal (u i : Fin 4 → ℤ)) =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex4 P hP i)) :
    ∀ k, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex4 P hP k) := by
  let S := rationalRealSpan4 P
  let v : Fin (Module.finrank ℚ P) → S := fun i => ⟨integerReal (u i : Fin 4 → ℤ),huS i⟩
  have hv : LinearIndependent ℝ v := LinearIndependent.of_comp S.subtype hu
  intro k
  let emb : Fin (k.val+1) → Fin (Module.finrank ℚ P) := Fin.castLE (by omega)
  let w := v ∘ emb
  have hw : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex4 P hP k) ∈
      restrictedRadii4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k := by
    refine ⟨w,hv.comp emb (Fin.castLE_injective _),?_,?_⟩
    · intro i
      change integerReal (u (emb i) : Fin 4 → ℤ) ∈
        integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃)
      exact ⟨(u (emb i) : Fin 4 → ℤ),(u (emb i)).property,rfl⟩
    · intro i
      change coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀)
        (integerReal (u (emb i) : Fin 4 → ℤ)) ≤ _
      rw [hatt]
      exact (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).2
        (show ambientPrefixIndex4 P hP (emb i) ≤ ambientPrefixIndex4 P hP k by
          change i.val ≤ k.val; omega)
  apply le_antisymm
  · exact csInf_le (restrictedRadii4_bddBelow P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k) hw
  · apply le_csInf ⟨_,hw⟩
    rintro r ⟨a,ha,haL,har⟩
    apply csInf_le (sourceMinima4_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃
      (ambientPrefixIndex4 P hP k)).2.1
    refine ⟨fun i => (a i : Fin 4 → ℝ),ha.map' S.subtype S.ker_subtype,haL,har⟩


def restrictedRealBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan4 P) :=
  (Module.finBasisOfFinrankEq ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
    (restrictedLattice4_rank P hP A₂ A₃ Q c₂ c₃)).ofZLatticeBasis ℝ _

theorem restrictedRealBasis4_span (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    Submodule.span ℤ (Set.range (restrictedRealBasis4 P hP A₂ A₃ Q c₂ c₃)) =
      restrictedLattice4 P A₂ A₃ Q c₂ c₃ := Basis.ofZLatticeBasis_span ℝ _ _

theorem restrictedRadii4_nonempty (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    (restrictedRadii4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k).Nonempty := by
  let b := restrictedRealBasis4 P hP A₂ A₃ Q c₂ c₃
  let emb : Fin (k.val+1) → Fin (Module.finrank ℚ P) := Fin.castLE (by omega)
  refine ⟨∑ j, restrictedGauge4 P L hL Q hQ c₀ (b j),fun i => b (emb i),
    b.linearIndependent.comp emb (Fin.castLE_injective _),?_,?_⟩
  · intro i
    rw [← restrictedRealBasis4_span P hP A₂ A₃ Q c₂ c₃]
    exact Submodule.subset_span ⟨emb i,rfl⟩
  · intro i
    have hnonneg (j) : 0 ≤ restrictedGauge4 P L hL Q hQ c₀ (b j) := norm_nonneg _
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ (emb i))

theorem restrictedMinima4_ge_ambient (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex4 P hP k) ≤
      restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k := by
  apply le_csInf (restrictedRadii4_nonempty P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)
  rintro r ⟨a,ha,haL,har⟩
  apply csInf_le (sourceMinima4_radius_set_properties A₂ A₃ L hL Q hQ c₀ c₂ c₃
    (ambientPrefixIndex4 P hP k)).2.1
  exact ⟨fun i => (a i : Fin 4 → ℝ),ha.map' (rationalRealSpan4 P).subtype
    (rationalRealSpan4 P).ker_subtype,haL,har⟩

theorem restrictedMinima4_pos (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin (Module.finrank ℚ P)) :
    0 < restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k :=
  ((sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 _).trans_le
    (restrictedMinima4_ge_ambient P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)

theorem restrictedGauge4_ball_compact (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (r : ℝ) :
    IsCompact {x | restrictedGauge4 P L hL Q hQ c₀ x ≤ r} := by
  let S := rationalRealSpan4 P
  let e := originalCoordinates4 L hL Q hQ c₀
  have heq : {x | restrictedGauge4 P L hL Q hQ c₀ x ≤ r} =
      S.subtype ⁻¹' (e ⁻¹' Metric.closedBall (0 : Fin 4 → ℝ) r) := by
    ext x
    simp [restrictedGauge4,coordinateGauge4,Metric.mem_closedBall,dist_zero_right,e]
  rw [heq]
  exact S.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage
    (e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _))

theorem restrictedGauge4_ball_finite (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (r : ℝ) :
    ({x | restrictedGauge4 P L hL Q hQ c₀ x ≤ r} ∩
      (restrictedLattice4 P A₂ A₃ Q c₂ c₃ : Set (rationalRealSpan4 P))).Finite := by
  rw [← restrictedRealBasis4_span P hP A₂ A₃ Q c₂ c₃]
  exact ZSpan.setFinite_inter _ (restrictedGauge4_ball_compact P L hL Q hQ c₀ r).isBounded

theorem exists_restricted_shortest_outside4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (W : Submodule ℝ (rationalRealSpan4 P)) (hW : W ≠ ⊤) :
    ∃ x ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, x ∉ W ∧
      ∀ y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, y ∉ W →
        restrictedGauge4 P L hL Q hQ c₀ x ≤ restrictedGauge4 P L hL Q hQ c₀ y := by
  classical
  let b := restrictedRealBasis4 P hP A₂ A₃ Q c₂ c₃
  have hex : ∃ i, b i ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)
  obtain ⟨i,hi⟩ := hex
  let f := restrictedGauge4 P L hL Q hQ c₀
  let G := restrictedLattice4 P A₂ A₃ Q c₂ c₃
  let T := {x | f x ≤ f (b i)} ∩ (G : Set (rationalRealSpan4 P)) ∩ {x | x ∉ W}
  have hfinite : T.Finite := (restrictedGauge4_ball_finite P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ _).inter_of_left _
  have hbi : b i ∈ G := by
    change b i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃
    rw [← restrictedRealBasis4_span P hP A₂ A₃ Q c₂ c₃]
    exact Submodule.subset_span ⟨i,rfl⟩
  obtain ⟨x,hx,hmin⟩ := Set.exists_min_image T f hfinite ⟨b i,⟨⟨show f (b i) ≤ f (b i) from le_rfl,hbi⟩,hi⟩⟩
  refine ⟨x,hx.1.2,hx.2,?_⟩
  intro y hy hyW
  by_cases hle : f y ≤ f (b i)
  · exact hmin y ⟨⟨hle,hy⟩,hyW⟩
  · exact hx.1.1.trans (le_of_not_ge hle)

end CompoundFeasibility.RestrictedGeometry4
