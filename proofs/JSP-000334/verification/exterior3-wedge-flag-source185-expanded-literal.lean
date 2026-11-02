import SubspaceBridge.Exterior3Persistence4
open scoped BigOperators Classical Matrix
open CompoundFeasibility.Exterior3
namespace CompoundFeasibility.Exterior3WedgeFlagLiteral185
open OriginalDeformation4 OriginalDeformedSource4 OriginalLastDual4 OriginalSelectedSystem4 SourceSelectedDual4
noncomputable section

theorem original_deformed_coordinate_mul3 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4))
    (hd : ∀ i, 0 < d i) (x : Fin 4 → ℝ) (i : Fin 4) :
    originalDeformedCoordinates4 L hL Q hQ c₀ d sigma hd x i =
      d (sigma i)*originalCoordinates4 L hL Q hQ c₀ x i := by
  rw [originalDeformedCoordinates4_apply]
  change d (sigma i)*(L *ᵥ x) i/Q^(c₀ i) = d (sigma i)*((L *ᵥ x) i/Q^(c₀ i))
  ring

theorem gap_original_gauge_bound3 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < gapDeformation4 lam i) (x : Fin 4 → ℝ)
    (hb : coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c₀ (gapDeformation4 lam) sigma hd) x ≤
      16*gapRadius4 lam) :
    coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) x ≤ 16*lam 2 := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hi := (norm_le_pi_norm
    (originalDeformedCoordinates4 L hL Q hQ c₀ (gapDeformation4 lam) sigma hd x) i).trans hb
  rw [Real.norm_eq_abs,original_deformed_coordinate_mul3,abs_mul,abs_of_pos (hd _)] at hi
  change (gapRadius4 lam/lam (min (sigma i) 2))*|originalCoordinates4 L hL Q hQ c₀ x i| ≤
    16*gapRadius4 lam at hi
  have ht : gapRadius4 lam*|originalCoordinates4 L hL Q hQ c₀ x i| ≤
      (16*gapRadius4 lam)*lam (min (sigma i) 2) := by
    apply (div_le_iff₀ (hp _)).mp
    simpa only [div_mul_eq_mul_div] using hi
  have hr := gapRadius4_pos lam hp
  have hs := mul_le_mul_of_nonneg_left (hm (min_le_right (sigma i) 2))
    (show 0 ≤ 16*gapRadius4 lam by positivity)
  nlinarith

theorem deformed_first_three_original_gauge3
    {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c₀ c₂ c₃ : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃}
    (F : DeformedAttaining4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ delta u) (j : Fin 3) :
    coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal (F.w j.castSucc : Fin 4 → ℤ)) ≤
      16*sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 := by
  have hp := sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃
  apply gap_original_gauge_bound3 L hL Q hQ c₀ _ hp.1 hp.2 F.sigma F.deformation_pos
  have hb := (F.minima_mono (show j.castSucc ≤ (2 : Fin 4) by change j.val ≤ 2; omega)).trans (F.comparison 2).2
  rw [gapDeformation4_first _ hp.1 2 le_rfl] at hb
  rw [F.attaining]
  exact hb

theorem lattice4_short_span_three3 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 3 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ j, v j ∈ lattice4Span b)
    (hvg : ∀ j, coordinateGauge4 e (v j) < successiveRadius4 b e 3)
    (x : Fin 4 → ℝ) (hx : x ∈ lattice4Span b)
    (hxg : coordinateGauge4 e x < successiveRadius4 b e 3) :
    x ∈ Submodule.span ℝ (Set.range v) := by
  classical
  by_contra hout
  let w : Fin 4 → (Fin 4 → ℝ) := Fin.snoc v x
  have hi : LinearIndependent ℝ w := linearIndependent_fin_snoc.mpr ⟨hv,hout⟩
  have hL : ∀ i, w i ∈ lattice4Span b := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hx
    · simpa [w] using hvL j
  have hg : ∀ i, coordinateGauge4 e (w i) < successiveRadius4 b e 3 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hxg
    · simpa [w] using hvg j
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => coordinateGauge4 e (w i)) Finset.univ_nonempty
  have hle := successiveRadius4_le_family b e 3 w hi hL _
    (fun j => hmax j (Finset.mem_univ j))
  exact (not_lt_of_ge hle) (hg i)

theorem minima_gap_short_bound3 (a b C R delta g : ℝ) (ha : 0 < a) (hR : 1 < R)
    (hgap : a < b*R^(-delta)) (hcut : C < R^delta) (hg : g ≤ C*a) : g < b := by
  have hRp := zero_lt_one.trans hR
  have he : R^(-delta)*R^delta = 1 := by
    rw [← Real.rpow_add hRp,neg_add_cancel,Real.rpow_zero]
  have hmul := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos hRp delta)
  rw [mul_assoc,he,mul_one] at hmul
  exact hg.trans_lt ((mul_lt_mul_of_pos_right hcut ha).trans (by simpa only [mul_comm] using hmul))

theorem deformed_short_span3
    {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c₀ c₂ c₃ : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃}
    (F : DeformedAttaining4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ delta u)
    (hgap : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3*Q^(-delta))
    (hcut : 16 < Q^delta) (z : Fin 4 → ℤ) (hz : z ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hg : coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal z) <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3) :
    integerReal z ∈ Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (F.w j.castSucc : Fin 4 → ℤ))) := by
  let b := sourceRealBasis4 A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hi := F.real_independent.comp (fun j : Fin 3 => j.castSucc) (Fin.castSucc_injective _)
  apply lattice4_short_span_three3 b (originalCoordinates4 L hL Q hQ c₀) _ hi
  · intro j
    rw [sourceRealBasis4_span]
    exact ⟨(F.w j.castSucc : Fin 4 → ℤ),(F.w j.castSucc).property,rfl⟩
  · intro j
    simpa only [sourceMinima4_eq_radius] using minima_gap_short_bound3 _ _ 16 Q delta _
      ((sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 2) hQ hgap hcut
      (deformed_first_three_original_gauge3 F j)
  · rw [sourceRealBasis4_span]
    exact ⟨z,hz,rfl⟩
  · simpa only [sourceMinima4_eq_radius] using hg

theorem retained_wedge_gauge_bound3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (kappa delta : ℝ) (hk : 0 < kappa)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : retainedOriginalWedges3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ kappa delta u) (j : Fin 3) :
    coordinateGauge4 (originalCoordinates4 (compound3Matrix4 L) (compound3_unit L (sourceUnit42 L hL))
      (Q^(3 : ℕ)) (cube_gt_one3 Q hQ) (normalizedWeights3_4 c₀))
      (integerReal (tripleFrame4 (fun i => (u i : Fin 4 → ℤ)) j.castSucc)) ≤
    (216/kappa)*normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 2 := by
  obtain ⟨hc,ht,_,hcompare,_⟩ := hu
  obtain ⟨_,_,_,_,_,_,_,_,hnu⟩ := ht
  rw [normalized_coordinates3_eq]
  have hp := sourceMinima4_pos_mono A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  have hm := (tripleProducts3_pos_mono _ hp.1 hp.2).2
  have hgj := hc.2.2.2.2 j.castSucc
  have hmu := mul_le_mul_of_nonneg_left
    (hm (show j.castSucc ≤ (2 : Fin 4) by change j.val ≤ 2; omega)) (by norm_num : (0 : ℝ) ≤ 6)
  have hbound := hgj.trans hmu
  have hs := mul_le_mul_of_nonneg_left hbound hk.le
  have hlower := (hcompare 2).1
  have hreverse := (hnu 2).2
  rw [div_mul_eq_mul_div,le_div_iff₀ hk]
  nlinarith

theorem wedge_flag_cutoff3 (kappa delta : ℝ) (hd : 0 < delta) :
    ∃ R₀ : ℝ, 1 < R₀ ∧ ∀ R : ℝ, R₀ < R → max 16 (216/kappa) < R^(delta/12) := by
  obtain ⟨R₀,hR₀,hcut⟩ := compound_gap_cutoff42 (max 16 (216/kappa)) (2*(delta/12)) (by positivity)
  refine ⟨R₀,hR₀,?_⟩
  intro R hR
  convert hcut R hR using 1 <;> congr 1 <;> ring

def cubeTail3_4 (Qfixed : Set ℝ) (R₀ : ℝ) : Set ℝ := {Q | Q ∈ Qfixed ∧ R₀ < Q^(3 : ℕ)}

theorem cubeTail3_unbounded (Qfixed : Set ℝ) (hQf : ¬ BddAbove Qfixed) (R₀ : ℝ) :
    ¬ BddAbove (cubeTail3_4 Qfixed R₀) := by
  apply not_bddAbove_iff.mpr
  intro M
  obtain ⟨Q,hQ,hlarge⟩ := not_bddAbove_iff.mp hQf (max M (max R₀ 1))
  have hQ1 : 1 < Q := (le_max_right R₀ 1).trans_lt ((le_max_right M _).trans_lt hlarge)
  have hQR : R₀ < Q := (le_max_left R₀ 1).trans_lt ((le_max_right M _).trans_lt hlarge)
  exact ⟨Q,⟨hQ,hQR.trans_le (le_self_pow₀ hQ1.le (by decide))⟩,(le_max_left M _).trans_lt hlarge⟩

theorem integer_real_span_mem_kernel3 (v : Fin 4 → Fin 4 → ℤ) (n : Fin 4 → ℤ)
    (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P = LinearMap.ker (normalForm4 n))
    (hspan : P = firstThreeSpan4 (fun j i => (v j i : ℚ))) (x : Fin 4 → ℤ)
    (hx : integerReal x ∈ Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (v j.castSucc)))) :
    (fun i => (x i : ℚ)) ∈ P := by
  let f := normalForm4 n
  have hker : Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (v j.castSucc))) ≤
      LinearMap.ker (OriginalShortPlane42.rationalFunctionalReal42 f) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change OriginalShortPlane42.rationalFunctionalReal42 f (integerReal (v j.castSucc)) = 0
    have hmem : (fun i => (v j.castSucc i : ℚ)) ∈ P := by
      rw [hspan]
      exact Submodule.subset_span ⟨j,rfl⟩
    rw [hP] at hmem
    have hz : f (fun i => (v j.castSucc i : ℚ)) = 0 := hmem
    have he := OriginalShortPlane42.rationalFunctionalReal42_cast f (fun i => (v j.castSucc i : ℚ))
    change OriginalShortPlane42.rationalFunctionalReal42 f (integerReal (v j.castSucc)) = _ at he
    rw [he,hz,Rat.cast_zero]
  have hz := hker hx
  change OriginalShortPlane42.rationalFunctionalReal42 f (integerReal x) = 0 at hz
  have he := OriginalShortPlane42.rationalFunctionalReal42_cast f (fun i => (x i : ℚ))
  change OriginalShortPlane42.rationalFunctionalReal42 f (integerReal x) = _ at he
  rw [he] at hz
  rw [hP]
  change f (fun i => (x i : ℚ)) = 0
  exact_mod_cast hz

theorem original_wedge_flag_at3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (kappa delta : ℝ) (hk : 0 < kappa)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : retainedOriginalWedges3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ kappa delta u)
    (uc : Fin 4 → normalizedGroup3_4 A₂ A₃ Q c₂ c₃)
    (F : DeformedAttaining4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L)
      (compound3_unit L (sourceUnit42 L hL)) (Q^(3 : ℕ)) (cube_gt_one3 Q hQ)
      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) (delta/12) uc)
    (n : Fin 4 → ℤ) (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : P = LinearMap.ker (normalForm4 n)) (hPdim : Module.finrank ℚ P = 3)
    (hPF : P = firstThreeSpan4 (fun j i => ((F.w j : Fin 4 → ℤ) i : ℚ)))
    (hcut : max 16 (216/kappa) < (Q^(3 : ℕ))^(delta/12)) :
    let z := tripleFrame4 (fun i => (u i : Fin 4 → ℤ))
    (∀ j : Fin 3, integerReal (z j.castSucc) ∈
      Submodule.span ℝ (Set.range (fun k : Fin 3 => integerReal (F.w k.castSucc : Fin 4 → ℤ)))) ∧
    (∀ j : Fin 3, (fun i => (z j.castSucc i : ℚ)) ∈ P) ∧
    LinearIndependent ℚ (fun j : Fin 3 => fun i => (z j.castSucc i : ℚ)) ∧
    P = firstThreeSpan4 (fun j i => (z j i : ℚ)) := by
  classical
  dsimp only
  let z := tripleFrame4 (fun i => (u i : Fin 4 → ℤ))
  have hgap : sourceMinima4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L)
      (compound3_unit L (sourceUnit42 L hL)) (Q^(3 : ℕ)) (cube_gt_one3 Q hQ)
      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 2 <
    sourceMinima4 (compound3Matrix4 A₂) (compound3Matrix4 A₃) (compound3Matrix4 L)
      (compound3_unit L (sourceUnit42 L hL)) (Q^(3 : ℕ)) (cube_gt_one3 Q hQ)
      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 3*(Q^(3 : ℕ))^(-(delta/12)) := by
    simpa only [normalizedMinima3_4,neg_div] using hu.2.2.2.2
  have hreal (j : Fin 3) : integerReal (z j.castSucc) ∈
      Submodule.span ℝ (Set.range (fun k : Fin 3 => integerReal (F.w k.castSucc : Fin 4 → ℤ))) := by
    apply deformed_short_span3 F hgap ((le_max_left _ _).trans_lt hcut) (z j.castSucc) (hu.2.2.1 j.castSucc)
    exact minima_gap_short_bound3 _ _ (216/kappa) (Q^(3 : ℕ)) (delta/12) _
      ((normalizedMinima3_pos_mono A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃).1 2)
      (cube_gt_one3 Q hQ) hgap ((le_max_right _ _).trans_lt hcut)
      (retained_wedge_gauge_bound3 A₂ A₃ L hL Q hQ c₀ c₂ c₃ kappa delta hk u hu j)
  have hrat (j : Fin 3) : (fun i => (z j.castSucc i : ℚ)) ∈ P :=
    integer_real_span_mem_kernel3 (fun k => (F.w k : Fin 4 → ℤ)) n P hP hPF (z j.castSucc) (hreal j)
  have hi : LinearIndependent ℝ (fun j : Fin 3 => integerReal (z j.castSucc)) :=
    hu.1.2.2.2.1.comp (fun j : Fin 3 => j.castSucc) (Fin.castSucc_injective _)
  have hiq := OriginalSpanTransport4.integer_three_rational_independent4 (fun j : Fin 3 => z j.castSucc) hi
  have hinc : firstThreeSpan4 (fun j i => (z j i : ℚ)) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hrat j
  have hdim : Module.finrank ℚ (firstThreeSpan4 (fun j i => (z j i : ℚ))) = 3 :=
    finrank_span_eq_card hiq
  exact ⟨hreal,hrat,hiq,(Submodule.eq_of_le_of_finrank_eq hinc (hdim.trans hPdim.symm)).symm⟩

def originalWedgeSpan3_4 (z w : Fin 4 → Fin 4 → ℤ) (P : Submodule ℚ (Fin 4 → ℚ)) : Prop :=
  (∀ j : Fin 3, integerReal (z j.castSucc) ∈
    Submodule.span ℝ (Set.range (fun k : Fin 3 => integerReal (w k.castSucc)))) ∧
  (∀ j : Fin 3, (fun i => (z j.castSucc i : ℚ)) ∈ P) ∧
  LinearIndependent ℚ (fun j : Fin 3 => fun i => (z j.castSucc i : ℚ)) ∧
  P = firstThreeSpan4 (fun j i => (z j i : ℚ))

def fixedOriginalWedgeSpanData3_4
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (delta : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (U V : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) (hVU : V ⊆ U)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃)
    (Vprime : Set ℝ) (hVpV : Vprime ⊆ V) (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R) : Prop :=
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    ∃ Uc : Set ℝ, ∃ hUcW : Uc ⊆ W, ¬ BddAbove Uc ∧
      ∃ uc : (q : Uc) → Fin 4 → originalSourceGroup4 B₂ B₃ q.val (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃),
      ∃ Fc : (q : Uc) → DeformedAttaining4 B₂ B₃ B₀ (sourceUnit42 B₀ hBdet) q.val
        (hWR q.val (hUcW q.property)) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) (delta/12) (uc q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ Wc : Set ℝ, ∃ hWcU : Wc ⊆ Uc, ¬ BddAbove Wc ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' Wc) ∧
        (∀ q : Uc, q.val ∈ Wc →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) ((delta/12)/24)
            (OriginalDeformation4.deformedWidths4 q.val (normalizedWeights3_4 c₀)
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 B₂ B₃ B₀ (sourceUnit42 B₀ hBdet) q.val
                  (hWR q.val (hUcW q.property)) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃))) (Fc q).sigma) (fun i => (normalizedWeights3_4 c₂) i/5) (fun i => (normalizedWeights3_4 c₃) i/5) = S) ∧
        ∃ (q1 : Uc) (b : Fin 4 → ℤ) (B : ℝ), q1.val ∈ Wc ∧
          b = integerLastDual4 (fun j => ((Fc q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
          Submodule.span ℚ {fun i => (b i : ℚ)} =
            Submodule.span ℚ {lastDual4 (fun j i => (((Fc q1).w j : Fin 4 → ℤ) i : ℚ)) (Fc q1).rational_independent} ∧
          (∀ s ∈ S, mixedProduct4 B₂ B₃ B₀ b s = 0) ∧
          1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ Wc ∧ B < q} ∧
          (∀ q : Uc, q.val ∈ Wc → B < q.val →
            Submodule.span ℚ {lastDual4 (fun j i => (((Fc q).w j : Fin 4 → ℤ) i : ℚ)) (Fc q).rational_independent} =
              Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
          ∃ (Tspan : ℝ) (Wfixed : Set ℝ) (P : Submodule ℚ (Fin 4 → ℚ)),
            1 < Tspan ∧ Wfixed = {Q | Q ∈ Wc ∧ max B Tspan < Q} ∧
            ¬ BddAbove Wfixed ∧ P = LinearMap.ker (normalForm4 b) ∧
            Module.finrank ℚ P = 3 ∧
            (∀ q : Uc, q.val ∈ Wfixed →
              P = firstThreeSpan4 (fun j i => ((uc q j : Fin 4 → ℤ) i : ℚ)) ∧
              P = firstThreeSpan4 (fun j i => (((Fc q).w j : Fin 4 → ℤ) i : ℚ)) ∧
              minimaFlag4 (fun j => integerReal (uc q j : Fin 4 → ℤ)) 3 =
                minimaFlag4 (fun j => integerReal ((Fc q).w j : Fin 4 → ℤ)) 3 ∧
              Module.finrank ℝ (minimaFlag4 (fun j => integerReal (uc q j : Fin 4 → ℤ)) 3) = 3 ∧
              LinearIndependent ℚ (fun j : Fin 3 => fun i => ((uc q j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
            ∃ C₄ kappa : ℝ, 0 < C₄ ∧ 0 < kappa ∧ kappa = ((1 : ℝ)/24)/(216*C₄^3) ∧
              ∃ (Qfixed : Set ℝ) (hQfV : Qfixed ⊆ Vprime),
                Qfixed = cubePreimage3_4 Vprime Wfixed ∧ ¬ BddAbove Qfixed ∧
                (∀ Q ∈ Qfixed, Q^(3 : ℕ) ∈ Wfixed) ∧
                (∀ q : Qfixed,
                  let qV : V := ⟨q.val,hVpV (hQfV q.property)⟩
                  let hq := hQU q.val (hVU qV.property)
                  retainedOriginalWedges3_4 A₂ A₃ L hL q.val hq c₀ c₂ c₃ kappa delta (u qV)) ∧
              ∃ R₀ : ℝ, 1 < R₀ ∧
                (∀ R : ℝ, R₀ < R → max 16 (216/kappa) < R^(delta/12)) ∧
                ∃ (Qfinal : Set ℝ) (hQfinal : Qfinal ⊆ Qfixed),
                  Qfinal = cubeTail3_4 Qfixed R₀ ∧ ¬ BddAbove Qfinal ∧
                  ∀ q : Qfinal,
                    let qV : V := ⟨q.val,hVpV (hQfV (hQfinal q.property))⟩
                    let hq := hQU q.val (hVU qV.property)
                    ∃ r : Uc, r.val = q.val^(3 : ℕ) ∧
                      retainedOriginalWedges3_4 A₂ A₃ L hL q.val hq c₀ c₂ c₃ kappa delta (u qV) ∧
                      originalWedgeSpan3_4 (tripleFrame4 (fun j => (u qV j : Fin 4 → ℤ)))
                        (fun j => ((Fc r).w j : Fin 4 → ℤ)) P

theorem fixed_wedge_span_data3_of_persisted
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (delta : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (U V : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) (hVU : V ⊆ U)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃)
    (Vprime : Set ℝ) (hVpV : Vprime ⊆ V) (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R)
    (hd : 0 < delta)
    (hsource : fixedCompoundPreimages3_4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR) :
    fixedOriginalWedgeSpanData3_4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR := by
  classical
  dsimp only [fixedOriginalWedgeSpanData3_4]
  obtain ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,n,B,hq1,hbint,hn,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,P,hTspan,hF_eq,hF,hP,hPdim,hflags,C₄,kappa,hC₄,hk,hkeq,
    Qfixed,hQfV,hQfeq,hQf,hQcube,hret⟩ := hsource
  obtain ⟨R₀,hR₀,hcut⟩ := wedge_flag_cutoff3 kappa delta hd
  let Qfinal := cubeTail3_4 Qfixed R₀
  have hQfinal : Qfinal ⊆ Qfixed := fun _ h => h.1
  refine ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,n,B,hq1,hbint,hn,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,P,hTspan,hF_eq,hF,hP,hPdim,hflags,C₄,kappa,hC₄,hk,hkeq,
    Qfixed,hQfV,hQfeq,hQf,hQcube,hret,R₀,hR₀,hcut,Qfinal,hQfinal,rfl,cubeTail3_unbounded Qfixed hQf R₀,?_⟩
  intro q
  let qF : Qfixed := ⟨q.val,hQfinal q.property⟩
  let qV : V := ⟨q.val,hVpV (hQfV qF.property)⟩
  have hq := hQU q.val (hVU qV.property)
  have hRfixed := hQcube q.val qF.property
  have hRU : q.val^(3 : ℕ) ∈ Uc := by
    rw [hF_eq] at hRfixed
    exact hWcU hRfixed.1
  let r : Uc := ⟨q.val^(3 : ℕ),hRU⟩
  have hc := hret qF
  refine ⟨r,rfl,hc,?_⟩
  exact original_wedge_flag_at3 A₂ A₃ L hL q.val hq c₀ c₂ c₃ kappa delta hk (u qV) hc
    (uc r) (Fc r) n P hP hPdim ((hflags r hRfixed).2.1) (hcut _ q.property.2)

theorem source_original_wedges_fixed_compound_rank3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    let hBunit := sourceUnit42 B₀ hBdet
    ∃ Told T : ℝ, 1 < Told ∧ 1 < T ∧ Told ≤ T ∧ 0 < delta/12 ∧
      (∀ Q : ℝ, T < Q → 36 < Q^(delta/4)) ∧
      B₂.det = 1 ∧ B₃.det = 1 ∧ B₀.det = 1 ∧ IsUnit B₂ ∧ IsUnit B₃ ∧ IsUnit B₀ ∧
      (∀ s t, IsAlgebraic ℚ (B₀ s t)) ∧
      ∀ (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
        (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
        (_hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0),
        (∀ s, |normalizedWeights3_4 c₀ s| ≤ 1) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₂ s ∧ normalizedWeights3_4 c₂ s ≤ 0) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₃ s ∧ normalizedWeights3_4 c₃ s ≤ 0) ∧
        (∑ s, (normalizedWeights3_4 c₀ s+normalizedWeights3_4 c₂ s+normalizedWeights3_4 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 0 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 1*Q^(-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), V = {Q | Q ∈ U ∧ Told < Q} ∧ ¬ BddAbove V ∧
            ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              (∀ q : V, originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q) ∧ Told < q.val ∧
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 2 <
                  compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 3*q.val^(-delta/2)) ∧
              ∃ (Vprime : Set ℝ) (hVpV : Vprime ⊆ V), Vprime = {Q | Q ∈ V ∧ T < Q} ∧ ¬ BddAbove Vprime ∧
                ∃ (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R), W = cubeImage3_4 Vprime ∧ ¬ BddAbove W ∧
                  (∀ q : Vprime,
                    normalizationTransport3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ ∧
                    (∀ s, tripleFrame4 (fun j => (u ⟨q.val,hVpV q.property⟩ j : Fin 4 → ℤ)) s ∈
                      normalizedGroup3_4 A₂ A₃ q.val c₂ c₃) ∧
                    normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 2 <
                      normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 3*(q.val^(3 : ℕ))^(-delta/12)) ∧
                  (∀ (R : ℝ) (hR : R ∈ W), ∃ q : Vprime, R = q.val^(3 : ℕ) ∧
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 2 <
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 3*R^(-delta/12)) ∧
fixedOriginalWedgeSpanData3_4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR := by
  classical
  dsimp only
  obtain ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,htails⟩ :=
    source_exterior3_fixed_compound_rank3_4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,?_⟩
  intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨ha₀,ha₂,ha₃,hab,hfamilies⟩ := htails c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  refine ⟨ha₀,ha₂,ha₃,hab,?_⟩
  intro U hU hQU hgap
  obtain ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre,hsource⟩ :=
    hfamilies U hU hQU hgap
  exact ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre,
    fixed_wedge_span_data3_of_persisted A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR hd hsource⟩

end
end CompoundFeasibility.Exterior3WedgeFlagLiteral185
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.original_deformed_coordinate_mul3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.original_deformed_coordinate_mul3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.original_deformed_coordinate_mul3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.gap_original_gauge_bound3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.gap_original_gauge_bound3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.gap_original_gauge_bound3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.deformed_first_three_original_gauge3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.deformed_first_three_original_gauge3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.deformed_first_three_original_gauge3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.lattice4_short_span_three3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.lattice4_short_span_three3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.lattice4_short_span_three3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.minima_gap_short_bound3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.minima_gap_short_bound3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.minima_gap_short_bound3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.deformed_short_span3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.deformed_short_span3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.deformed_short_span3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.retained_wedge_gauge_bound3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.retained_wedge_gauge_bound3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.retained_wedge_gauge_bound3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.wedge_flag_cutoff3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.wedge_flag_cutoff3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.wedge_flag_cutoff3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.cubeTail3_4
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.cubeTail3_4
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.cubeTail3_4
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.cubeTail3_unbounded
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.cubeTail3_unbounded
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.cubeTail3_unbounded
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.integer_real_span_mem_kernel3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.integer_real_span_mem_kernel3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.integer_real_span_mem_kernel3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.original_wedge_flag_at3
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.original_wedge_flag_at3
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.original_wedge_flag_at3
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.originalWedgeSpan3_4
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.originalWedgeSpan3_4
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.originalWedgeSpan3_4
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.fixedOriginalWedgeSpanData3_4
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.fixedOriginalWedgeSpanData3_4
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.fixedOriginalWedgeSpanData3_4
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.fixed_wedge_span_data3_of_persisted
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.fixed_wedge_span_data3_of_persisted
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.fixed_wedge_span_data3_of_persisted
#check CompoundFeasibility.Exterior3WedgeFlagLiteral185.source_original_wedges_fixed_compound_rank3_4
#print CompoundFeasibility.Exterior3WedgeFlagLiteral185.source_original_wedges_fixed_compound_rank3_4
#print axioms CompoundFeasibility.Exterior3WedgeFlagLiteral185.source_original_wedges_fixed_compound_rank3_4
