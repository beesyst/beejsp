import SubspaceBridge.OriginalExterior3Source4
open scoped BigOperators Matrix
open CompoundFeasibility.Exterior3
namespace CompoundFeasibility.Exterior3MinimaLiteral182
noncomputable section

theorem compound_group3_eq (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃ =
      sourceLattice4 (compound3Matrix4 A₂) (compound3Matrix4 A₃)
        (summedExponents3_4 2 Q c₂) (summedExponents3_4 3 Q c₃) := rfl

instance compound_group3_isZLattice (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    IsZLattice ℝ (integerRealImage (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃)) := by
  rw [compound_group3_eq]
  infer_instance

def compoundBasis3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
  sourceRealBasis4 (compound3Matrix4 A₂) (compound3Matrix4 A₃)
    (summedExponents3_4 2 Q c₂) (summedExponents3_4 3 Q c₃)

def compoundCoordinates3_4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  originalCoordinates4 (compound3Matrix4 L) (compound3_unit L hL) Q hQ (tripleWeights4 c₀)

def compoundMinima3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) : Fin 4 → ℝ :=
  successiveRadius4 (compoundBasis3_4 A₂ A₃ Q c₂ c₃) (compoundCoordinates3_4 L hL Q hQ c₀)

theorem compoundBasis3_span (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    lattice4Span (compoundBasis3_4 A₂ A₃ Q c₂ c₃) =
      integerRealImage (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃) :=
  sourceRealBasis4_span _ _ _ _

theorem compound_covolume3_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    (2 : ℝ) ^ (∑ s, summedExponents3_4 2 Q c₂ s) * 3 ^ (∑ s, summedExponents3_4 3 Q c₃ s) ≤
      ZLattice.covolume (integerRealImage (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃)) := by
  obtain ⟨b⟩ := sourceLattice4_has_basis (compound3Matrix4 A₂) (compound3Matrix4 A₃)
    (summedExponents3_4 2 Q c₂) (summedExponents3_4 3 Q c₃)
  have hd₂ : (compound3Matrix4 A₂).det = 1 := by rw [compound3_det,h₂,one_pow]
  have hd₃ : (compound3Matrix4 A₃).det = 1 := by rw [compound3_det,h₃,one_pow]
  have h := integerRealImage_padic_covolume_lower (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃) b
    (compound3Matrix4 A₂) (compound3Matrix4 A₃) (summedExponents3_4 2 Q c₂) (summedExponents3_4 3 Q c₃)
    (fun x hx i => (lattice4_spec 2 _ _ x).mp hx.1 i)
    (fun x hx i => (lattice4_spec 3 _ _ x).mp hx.2 i)
  simpa only [hd₂,hd₃,padicNorm.one,Rat.cast_one,one_mul] using h

theorem compound_width_product3 (Q : ℝ) (hQ : 0 < Q) (c : Fin 4 → ℝ) :
    (∏ s, Q ^ tripleWeights4 c s) = (∏ i : Fin 4, Q ^ c i) ^ (3 : ℕ) := by
  simp [Fin.prod_univ_succ,tripleWeights4,tripleIndex4,Real.rpow_add hQ]
  ring

theorem compound_covolume3_width_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    (∏ s, Q ^ tripleWeights4 c₀ s) ≤
      ZLattice.covolume (integerRealImage (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃)) := by
  have h := q_width_product_le_prime_powers4 Q hQ c₀ c₂ c₃ hb
  change (∏ i, Q ^ c₀ i) ≤ (2 : ℝ) ^ (∑ i, originalExponents3_4 2 Q c₂ i) *
    3 ^ (∑ i, originalExponents3_4 3 Q c₃ i) at h
  have hW : 0 ≤ ∏ i, Q ^ c₀ i := (Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)).le
  have hp := pow_le_pow_left₀ hW h 3
  have he : ((2 : ℝ) ^ (∑ i, originalExponents3_4 2 Q c₂ i) *
      3 ^ (∑ i, originalExponents3_4 3 Q c₃ i))^3 =
      2 ^ (∑ s, summedExponents3_4 2 Q c₂ s) * 3 ^ (∑ s, summedExponents3_4 3 Q c₃ s) := by
    rw [summedExponents3_4_sum,summedExponents3_4_sum,mul_pow,← pow_mul,← pow_mul]
    simp only [Nat.mul_comm]
  rw [he] at hp
  rw [compound_width_product3 Q (lt_trans zero_lt_one hQ)]
  exact hp.trans (compound_covolume3_lower A₂ A₃ h₂ h₃ Q c₂ c₃)

theorem exists_compoundMinima3_attaining (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ u : Fin 4 → originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun j => integerReal (u j : Fin 4 → ℤ)) ∧
      (∀ j, 0 < compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ j, coordinateGauge4 (compoundCoordinates3_4 L hL Q hQ c₀)
        (integerReal (u j : Fin 4 → ℤ)) = compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      ∀ j s, |(compound3Matrix4 L *ᵥ integerReal (u j : Fin 4 → ℤ)) s| ≤
        compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j * Q ^ tripleWeights4 c₀ s := by
  classical
  let b := compoundBasis3_4 A₂ A₃ Q c₂ c₃
  let e := compoundCoordinates3_4 L hL Q hQ c₀
  obtain ⟨v,hv,hvL,hpos,hmono,hatt⟩ := exists_successive_minima4 b e
  have hvImage (j : Fin 4) : v j ∈ integerRealImage (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃) := by
    rw [← compoundBasis3_span]
    exact hvL j
  have hlift (j : Fin 4) : ∃ x : originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃,
      integerReal (x : Fin 4 → ℤ) = v j := by
    obtain ⟨x,hx,he⟩ := hvImage j
    exact ⟨⟨x,hx⟩,he⟩
  choose u hu using hlift
  have hfun : (fun j => integerReal (u j : Fin 4 → ℤ)) = v := funext hu
  refine ⟨u,?_,hpos,hmono,?_,?_⟩
  · rw [hfun]
    exact hv
  · intro j
    rw [hu j]
    exact hatt j
  · intro j
    apply (originalCoordinates4_bounds (compound3Matrix4 L) (compound3_unit L hL)
      Q hQ (tripleWeights4 c₀) _ _).mp
    change coordinateGauge4 e (integerReal (u j : Fin 4 → ℤ)) ≤ _
    rw [hu j,hatt j]
    exact le_rfl

theorem compoundMinima3_product_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    (1 : ℝ)/24 ≤ ∏ j, compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ j := by
  obtain ⟨u,hu,_,_,_,hpoint⟩ := exists_compoundMinima3_attaining A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  obtain ⟨c⟩ := sourceLattice4_has_basis (compound3Matrix4 A₂) (compound3Matrix4 A₃)
    (summedExponents3_4 2 Q c₂) (summedExponents3_4 3 Q c₃)
  have hp := integerRealImage_frame_product_lower (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃) c
    (compound3Matrix4 L) u hu (fun s => Q ^ tripleWeights4 c₀ s)
    (compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃) hpoint
  have hd : (compound3Matrix4 L).det = 1 := by rw [compound3_det,hL,one_pow]
  have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hd,abs_one,one_mul,hfac] at hp
  have hw := compound_covolume3_width_lower A₂ A₃ h₂ h₃ Q hQ c₀ c₂ c₃ hb
  have hW : 0 < ∏ s, Q ^ tripleWeights4 c₀ s :=
    Finset.prod_pos (fun s _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  have hcancel : (1 : ℝ) ≤ 24 * ∏ j, compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ j := by
    apply (mul_le_mul_right hW).mp
    simpa only [one_mul] using hw.trans hp
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mpr
  simpa only [mul_comm] using hcancel
theorem compound_covolume3_ratio_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    1 ≤ ZLattice.covolume (integerRealImage (originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃)) /
      (∏ s, Q ^ tripleWeights4 c₀ s) := by
  apply (le_div_iff₀ (Finset.prod_pos (fun s _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _))).mpr
  simpa only [one_mul] using compound_covolume3_width_lower A₂ A₃ h₂ h₃ Q hQ c₀ c₂ c₃ hb

theorem compoundMinima3_pos_mono (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∀ j, 0 < compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j) ∧
      Monotone (compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨_,_,hp,hm,_,_⟩ := exists_compoundMinima3_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  exact ⟨hp,hm⟩

def tripleProducts3_4 (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun s => a (tripleIndex4 s 0)*a (tripleIndex4 s 1)*a (tripleIndex4 s 2)

theorem tripleProducts3_pos_mono (a : Fin 4 → ℝ) (hp : ∀ i, 0 < a i) (hm : Monotone a) :
    (∀ s, 0 < tripleProducts3_4 a s) ∧ Monotone (tripleProducts3_4 a) := by
  refine ⟨fun s => mul_pos (mul_pos (hp _) (hp _)) (hp _),?_⟩
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  fin_cases i
  · change a 0*a 1*a 2 ≤ a 0*a 1*a 3
    exact mul_le_mul_of_nonneg_left (hm (by decide)) (mul_nonneg (hp 0).le (hp 1).le)
  · change a 0*a 1*a 3 ≤ a 0*a 2*a 3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hm (by decide)) (hp 0).le) (hp 3).le
  · change a 0*a 2*a 3 ≤ a 1*a 2*a 3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm (by decide)) (hp 2).le) (hp 3).le

theorem tripleProducts3_product (a : Fin 4 → ℝ) :
    (∏ s, tripleProducts3_4 a s) = (∏ i : Fin 4, a i)^3 := by
  simp [tripleProducts3_4,tripleIndex4,Fin.prod_univ_succ]
  ring

def originalFrameControl3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃) : Prop :=
  let uZ : Fin 4 → Fin 4 → ℤ := fun j => (u j : Fin 4 → ℤ)
  let lam := sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  LinearIndependent ℝ (fun j => integerReal (uZ j)) ∧
    (∀ j, coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal (uZ j)) = lam j) ∧
    (∀ s, tripleFrame4 uZ s ∈ originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃) ∧
    LinearIndependent ℝ (fun s => integerReal (tripleFrame4 uZ s)) ∧
    ∀ j, coordinateGauge4 (compoundCoordinates3_4 L hL Q hQ c₀) (integerReal (tripleFrame4 uZ j)) ≤
      6*tripleProducts3_4 lam j

theorem exists_originalFrameControl3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₀ : ∀ i, |c₀ i| ≤ 1) (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0)
    (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    ∃ u, originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ u := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,u,hu,_,_,_,hatt,hm,_,hi,hg,_,_,_⟩ :=
    source_original_exterior3_bridge4 A₂ A₃ L h₂ h₃ hL hAlg Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  refine ⟨u,hu,hatt,hm,hi,?_⟩
  intro j
  simpa only [tripleProducts3_4,mul_assoc] using hg j

theorem compoundMinima3_upper_of_frame (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (hu : originalFrameControl3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ u) :
    ∀ j, compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
      6*tripleProducts3_4 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) j := by
  let w : Fin 4 → (Fin 4 → ℝ) := fun s => integerReal (tripleFrame4 (fun j => (u j : Fin 4 → ℤ)) s)
  obtain ⟨_,_,hm,hi,hg⟩ := hu
  have hmono := (tripleProducts3_pos_mono _
    (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
    (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).2).2
  intro j
  let f : Fin (j.val+1) → Fin 4 := Fin.castLE (by omega)
  apply successiveRadius4_le_family (compoundBasis3_4 A₂ A₃ Q c₂ c₃) (compoundCoordinates3_4 L hL Q hQ c₀)
    j (w ∘ f) (hi.comp f (Fin.castLE_injective _))
  · intro i
    rw [compoundBasis3_span]
    exact ⟨_,hm (f i),rfl⟩
  · intro i
    exact (hg (f i)).trans (mul_le_mul_of_nonneg_left
      (hmono (show f i ≤ j from (by change i.val ≤ j.val; omega))) (by norm_num))

theorem triple_prod_erase_upper (mu nu : Fin 4 → ℝ)
    (hnu : ∀ k, 0 < nu k) (hupper : ∀ k, nu k ≤ 6*mu k) (j : Fin 4) :
    (∏ k ∈ Finset.univ.erase j, nu k) ≤ 216 * ∏ k ∈ Finset.univ.erase j, mu k := by
  have h := Finset.prod_le_prod (fun k _ => (hnu k).le)
    (fun k (_ : k ∈ Finset.univ.erase j) => hupper k)
  have hc : (Finset.univ.erase j).card = 3 := by simp
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,hc,show (6 : ℝ)^3 = 216 by norm_num] using h

theorem triple_product_reverse (mu nu : Fin 4 → ℝ) (c C : ℝ)
    (hmu : ∀ k, 0 < mu k) (hnu : ∀ k, 0 < nu k)
    (hupper : ∀ k, nu k ≤ 6*mu k) (hlower : c ≤ ∏ k, nu k)
    (hprod : (∏ k, mu k) ≤ C^3) (hC : 0 < C) (j : Fin 4) :
    (c/(216*C^3))*mu j ≤ nu j := by
  have hdecomp (f : Fin 4 → ℝ) :
      f j*(∏ k ∈ Finset.univ.erase j, f k) = ∏ k, f k :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hstep : c*mu j ≤ 216*nu j*(∏ k, mu k) := by
    calc
      c*mu j ≤ (∏ k, nu k)*mu j := mul_le_mul_of_nonneg_right hlower (hmu j).le
      _ = (nu j*(∏ k ∈ Finset.univ.erase j, nu k))*mu j := by rw [hdecomp]
      _ ≤ (nu j*(216*∏ k ∈ Finset.univ.erase j, mu k))*mu j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (triple_prod_erase_upper mu nu hnu hupper j) (hnu j).le) (hmu j).le
      _ = 216*nu j*(∏ k, mu k) := by rw [← hdecomp mu]; ring
  have hfinal : c*mu j ≤ nu j*(216*C^3) := by
    calc
      _ ≤ 216*nu j*(∏ k, mu k) := hstep
      _ ≤ 216*nu j*C^3 := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hnu j).le)
      _ = _ := by ring
  rw [div_mul_eq_mul_div,div_le_iff₀ (show 0 < 216*C^3 by positivity)]
  exact hfinal

def sourceComparison3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (kappa : ℝ) : Prop :=
  ∃ u, originalFrameControl3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ u ∧
    ∀ j, kappa*tripleProducts3_4 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) j ≤
      compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ∧
      compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
        6*tripleProducts3_4 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) j

theorem source_compound_uniform_comparison3 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C₄ kappa : ℝ, 0 < C₄ ∧ 0 < kappa ∧ kappa = ((1 : ℝ)/24)/(216*C₄^3) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        sourceComparison3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ kappa := by
  let hLu := sourceUnit42 L hL
  obtain ⟨_,C₄,_,hC₄,_,hfour⟩ := source_original_uniform_minima_upper4 A₂ A₃ L
    (sourceUnit42 A₂ h₂) (sourceUnit42 A₃ h₃) hLu
  refine ⟨C₄,((1 : ℝ)/24)/(216*C₄^3),hC₄,by positivity,rfl,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨u,hcontrol⟩ := exists_originalFrameControl3 A₂ A₃ L h₂ h₃ hL hAlg Q hQ c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  have hu := compoundMinima3_upper_of_frame A₂ A₃ L hLu Q hQ c₀ c₂ c₃ u hcontrol
  have hp := sourceMinima4_pos_mono A₂ A₃ L hLu Q hQ c₀ c₂ c₃
  have hprod : (∏ j, tripleProducts3_4 (sourceMinima4 A₂ A₃ L hLu Q hQ c₀ c₂ c₃) j) ≤ C₄^3 := by
    rw [tripleProducts3_product]
    exact pow_le_pow_left₀ (Finset.prod_pos (fun i _ => hp.1 i)).le
      (hfour Q hQ c₀ c₂ c₃ (fun i => (hc₂ i).2) (fun i => (hc₃ i).2) hb) 3
  refine ⟨u,hcontrol,fun j => ⟨?_,hu j⟩⟩
  exact triple_product_reverse _ _ (1/24) C₄ (tripleProducts3_pos_mono _ hp.1 hp.2).1
    (compoundMinima3_pos_mono A₂ A₃ L hLu Q hQ c₀ c₂ c₃).1 hu
    (compoundMinima3_product_lower A₂ A₃ L h₂ h₃ hL Q hQ c₀ c₂ c₃ hb) hprod hC₄ j

theorem source_compound3_gap_bound (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (kappa Q delta : ℝ)
    (hk : 0 < kappa) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hcompare : ∀ j, kappa*tripleProducts3_4 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) j ≤
      compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ∧
      compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
        6*tripleProducts3_4 (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) j)
    (hgap : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 0 <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1*Q^(-delta)) :
    compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 <
      (6/kappa)*compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 3*Q^(-delta) := by
  let lam := sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let mu := tripleProducts3_4 lam
  let nu := compoundMinima3_4 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hp := (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
  have hm : mu 2 < mu 3*Q^(-delta) := by
    change lam 0*lam 2*lam 3 < (lam 1*lam 2*lam 3)*Q^(-delta)
    convert mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hgap (hp 2)) (hp 3) using 1 <;> ring
  change nu 2 < (6/kappa)*nu 3*Q^(-delta)
  calc
    _ ≤ 6*mu 2 := (hcompare 2).2
    _ < 6*(mu 3*Q^(-delta)) := mul_lt_mul_of_pos_left hm (by norm_num)
    _ = (6/kappa)*(kappa*mu 3)*Q^(-delta) := by field_simp [hk.ne']; ring
    _ ≤ (6/kappa)*nu 3*Q^(-delta) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcompare 3).1 (by positivity))
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).le

theorem source_exterior3_top_gap4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    ∃ C₄ kappa T : ℝ, 0 < C₄ ∧ 0 < kappa ∧ 1 < T ∧ kappa = ((1 : ℝ)/24)/(216*C₄^3) ∧
      (∀ Q : ℝ, T < Q → 6/kappa < Q^(delta/2)) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, |c₀ i| ≤ 1) → (∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) →
        (∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        sourceComparison3_4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ kappa) ∧
      ∀ (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
        (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
        (_hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) (U : Set ℝ) (_hU : ¬ BddAbove U)
        (hQU : ∀ Q ∈ U, 1 < Q),
        (∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 0 <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 1*Q^(-delta)) →
        ∃ (V : Set ℝ) (hVU : V ⊆ U), V = {Q | Q ∈ U ∧ T < Q} ∧ ¬ BddAbove V ∧
          ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
            ∀ q : V,
              originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q) ∧
              (∀ j, kappa*tripleProducts3_4
                (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃) j ≤
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ j ∧
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ j ≤
                  6*tripleProducts3_4
                    (sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃) j) ∧
              T < q.val ∧
              compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 2 <
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 3 * q.val^(-delta/2) := by
  classical
  obtain ⟨C₄,kappa,hC,hk,hkeq,hcompare⟩ := source_compound_uniform_comparison3 A₂ A₃ L h₂ h₃ hL hAlg
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 (6/kappa) delta hd
  refine ⟨C₄,kappa,T,hC,hk,hT,hkeq,hcut,hcompare,?_⟩
  intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb U hU hQU hgap
  let V : Set ℝ := {Q | Q ∈ U ∧ T < Q}
  have hVU : V ⊆ U := fun _ h => h.1
  have hwit (q : V) : sourceComparison3_4 A₂ A₃ L (sourceUnit42 L hL)
      q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ kappa :=
    hcompare q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  simp only [sourceComparison3_4] at hwit
  choose u hctrl hcomp using hwit
  refine ⟨V,hVU,rfl,JSP000334.sourceDual_unbounded_tail3 U hU T,u,?_⟩
  intro q
  refine ⟨hctrl q,hcomp q,q.property.2,?_⟩
  have hQ := hQU q.val (hVU q.property)
  have hraw := source_compound3_gap_bound A₂ A₃ L (sourceUnit42 L hL) kappa q.val delta hk hQ
    c₀ c₂ c₃ (hcomp q) (hgap q.val (hVU q.property))
  exact absorb_compound_gap42 _ _ (6/kappa) q.val delta
    ((compoundMinima3_pos_mono A₂ A₃ L (sourceUnit42 L hL) q.val hQ c₀ c₂ c₃).1 3)
    hQ (hcut q.val q.property.2) hraw

end
end CompoundFeasibility.Exterior3MinimaLiteral182

#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compound_group3_eq
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compound_group3_isZLattice
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compoundBasis3_4
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compoundCoordinates3_4
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compoundMinima3_4
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compoundBasis3_span
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compound_covolume3_lower
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compound_width_product3
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compound_covolume3_width_lower
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.exists_compoundMinima3_attaining
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compoundMinima3_product_lower
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compound_covolume3_ratio_lower
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compoundMinima3_pos_mono
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.tripleProducts3_4
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.tripleProducts3_pos_mono
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.tripleProducts3_product
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.originalFrameControl3_4
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.exists_originalFrameControl3
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.compoundMinima3_upper_of_frame
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.triple_prod_erase_upper
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.triple_product_reverse
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.sourceComparison3_4
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.source_compound_uniform_comparison3
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.source_compound3_gap_bound
#print axioms CompoundFeasibility.Exterior3MinimaLiteral182.source_exterior3_top_gap4
