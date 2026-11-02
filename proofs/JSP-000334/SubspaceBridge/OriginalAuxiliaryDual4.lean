import SubspaceBridge.OriginalLastDual4
import SubspaceBridge.DualFrame3
import SubspaceBridge.SchlickeweiIntegerPairing6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalAuxiliaryDual4
open OriginalLastDual4

theorem integerFrame4_det_cast (u : Matrix (Fin 4) (Fin 4) ℤ) :
    (u.map (Int.castRingHom ℚ)).det = (u.det : ℚ) := by
  exact ((Int.castRingHom ℚ).map_det u).symm

theorem integerFrame4_det_ne_zero (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    Matrix.det (u : Matrix (Fin 4) (Fin 4) ℤ) ≠ 0 := by
  have hd : (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hu))
  rw [integerFrame4_det_cast] at hd
  exact_mod_cast hd

theorem integerLastDual4_form (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    normalForm4 (integerLastDual4 u) = ((Matrix.det u : ℤ) : ℚ) •
      rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 3 := by
  apply (rationalFrameBasis42 (fun j i => (u j i : ℚ)) hu).ext
  intro j
  rw [rationalFrameBasis42_apply,normalForm4_apply,LinearMap.smul_apply,
    rationalFrameDual42_pairing]
  have he := integerLastDual4_pairing u j
  have hrat : (∑ i, (u j i : ℚ) * (integerLastDual4 u i : ℚ)) =
      if j = 3 then ((Matrix.det u : ℤ) : ℚ) else 0 := by
    exact_mod_cast he
  by_cases hj : j = 3 <;> simpa [hj,smul_eq_mul,mul_comm] using hrat

theorem integerLastDual4_nonzero (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) : integerLastDual4 u ≠ 0 := by
  intro hz
  have hp := integerLastDual4_pairing u 3
  rw [hz] at hp
  simp at hp
  exact integerFrame4_det_ne_zero u hu hp.symm

theorem integerLastDual4_eq (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    (fun i => (integerLastDual4 u i : ℚ)) =
      ((Matrix.det u : ℤ) : ℚ) • lastDual4 (fun j i => (u j i : ℚ)) hu := by
  funext i
  have hi := congrArg (fun f : Module.Dual ℚ (Fin 4 → ℚ) => f (Pi.single i 1))
    (integerLastDual4_form u hu)
  simpa [normalForm4,lastDual4,Pi.single_apply] using hi

theorem integerLastDual4_line (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    Submodule.span ℚ {fun i => (integerLastDual4 u i : ℚ)} =
      Submodule.span ℚ {lastDual4 (fun j i => (u j i : ℚ)) hu} := by
  rw [integerLastDual4_eq u hu]
  apply Submodule.span_singleton_smul_eq
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast integerFrame4_det_ne_zero u hu


theorem cofactor_dual_cast4 {K : Type*} [Field K] [CharZero K]
    (u : Fin 4 → Fin 4 → ℤ) (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin 4) :
    (integerLastDual4 u i : K) = ((Matrix.det u : ℤ) : K) *
      (lastDual4 (fun j i => (u j i : ℚ)) hu i : K) := by
  have h := congrFun (integerLastDual4_eq u hu) i
  change (integerLastDual4 u i : ℚ) = ((Matrix.det u : ℤ) : ℚ) * _ at h
  have hh := congrArg (fun z : ℚ => (z : K)) h
  simpa only [Rat.cast_mul,Rat.cast_intCast] using hh

theorem cofactor_dual_coordinates4 {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin 4) :
    (B⁻¹.transpose *ᵥ (fun k => (integerLastDual4 u k : K))) i =
      ((Matrix.det u : ℤ) : K) *
        (∑ k, B⁻¹ k i * (lastDual4 (fun j i => (u j i : ℚ)) hu k : K)) := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [cofactor_dual_cast4 u hu k]
  ring

theorem cofactor_change_of_forms4 {K : Type*} [Field K]
    (B : Matrix (Fin 4) (Fin 4) K) (hB : B.det = 1)
    (u : Matrix (Fin 4) (Fin 4) ℤ) (i : Fin 4) :
    (B⁻¹.transpose *ᵥ (fun k => (integerLastDual4 u k : K))) i =
      (u.map (Int.castRingHom K) * B.transpose).adjugate i 3 := by
  have hInv : B⁻¹ = B.adjugate := by
    rw [Matrix.inv_def,hB,Ring.inverse_one,one_smul]
  have hm : (u.map (Int.castRingHom K)).adjugate = u.adjugate.map (Int.castRingHom K) :=
    ((Int.castRingHom K).map_adjugate u).symm
  rw [Matrix.adjugate_mul_distrib,← Matrix.adjugate_transpose,hm,← hInv]
  rfl

theorem native_matrix_pairing4 {K : Type*} [Field K]
    (B : Matrix (Fin 4) (Fin 4) K) (hB : B.det ≠ 0) (x y : Fin 4 → K) :
    (∑ k, x k * y k) = ∑ i, (B *ᵥ x) i * (B⁻¹.transpose *ᵥ y) i := by
  change x ⬝ᵥ y = (B *ᵥ x) ⬝ᵥ (B⁻¹.transpose *ᵥ y)
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),Matrix.one_mulVec]

def integerPairing4 (x y : Fin 4 → ℤ) : ℤ := ∑ i, x i * y i

theorem native_integer_pairing4 {K : Type*} [Field K]
    (B : Matrix (Fin 4) (Fin 4) K) (hB : B.det ≠ 0) (x y : Fin 4 → ℤ) :
    (integerPairing4 x y : K) =
      ∑ i, (B *ᵥ (fun k => (x k : K))) i *
        (B⁻¹.transpose *ᵥ (fun k => (y k : K))) i := by
  have hc : (integerPairing4 x y : K) = ∑ k, (x k : K) * (y k : K) := by
    simp [integerPairing4]
  exact hc.trans (native_matrix_pairing4 B hB _ _)


theorem cofactor_minor_norm4 {K : Type*} [NormedField K]
    (B : Matrix (Fin 4) (Fin 4) K) (hB : B.det = 1)
    (u : Matrix (Fin 4) (Fin 4) ℤ) (i : Fin 4) :
    ‖(B⁻¹.transpose *ᵥ (fun k => (integerLastDual4 u k : K))) i‖ =
      ‖((u.map (Int.castRingHom K) * B.transpose).submatrix Fin.castSucc i.succAbove).det‖ := by
  rw [cofactor_change_of_forms4 B hB u i,Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    show (3 : Fin 4) = Fin.last 3 from rfl,Fin.succAbove_last]

theorem real_cofactor_bound4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1)
    (u : Matrix (Fin 4) (Fin 4) ℤ) (s : Fin 3 → ℝ) (t : Fin 4 → ℝ)
    (hpoint : ∀ (j : Fin 3) i, |(L *ᵥ (fun k => (u j.castSucc k : ℝ))) i| ≤ s j * t i)
    (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual4 u k : ℝ))) i‖ ≤
      6 * (∏ j : Fin 3, s j) * (∏ k : Fin 3, t (i.succAbove k)) := by
  rw [cofactor_minor_norm4 L hL u i]
  apply JSP000334.dualFrame3_abs_det_row_column_bounds
  intro j k
  simpa [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using
    hpoint j (i.succAbove k)

theorem source_cofactor_real4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge4 (originalCoordinates4 L hL Q hQ c0)
      (integerReal (u j : Fin 4 → ℤ)) = sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j)
    (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual4 (fun j => (u j : Fin 4 → ℤ)) k : ℝ))) i‖ ≤
      6 * (∏ j : Fin 3, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc) *
        (∏ k : Fin 3, Q^(c0 (i.succAbove k))) := by
  apply real_cofactor_bound4 L hLdet (fun j => (u j : Fin 4 → ℤ))
    (fun j : Fin 3 => sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc)
    (fun k => Q^(c0 k)) _ i
  intro j k
  exact (originalCoordinates4_bounds L hL Q hQ c0
    (integerReal (u j.castSucc : Fin 4 → ℤ)) _).mp (hatt j.castSucc).le k

theorem real_pairing_bound4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det ≠ 0)
    (x y : Fin 4 → ℤ) (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hx : ∀ i, ‖(L *ᵥ (fun k => (x k : ℝ))) i‖ ≤ a i)
    (hy : ∀ i, ‖(L⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i‖ ≤ b i) :
    ‖(integerPairing4 x y : ℝ)‖ ≤ ∑ i, a i * b i := by
  rw [native_integer_pairing4 L hL x y]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul (hx i) (hy i) (norm_nonneg _) (ha i)


theorem mapped_det_one4 {K : Type*} [Field K] [CharZero K]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
    (A.map (algebraMap ℚ K)).det = 1 := by
  have he := (algebraMap ℚ K).map_det A
  change (algebraMap ℚ K) A.det = (A.map (algebraMap ℚ K)).det at he
  rw [hA,map_one] at he
  exact he.symm

theorem finite_form_norm4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → ℤ) (i : Fin 4) :
    ‖(A.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun k => (x k : ℚ_[p]))) i‖ =
      (padicNorm p ((A *ᵥ (fun k => (x k : ℚ))) i) : ℝ) := by
  rw [← Auxiliary6.SourceExpansion.finite_norm p]
  congr 1

theorem original_lattice_finite_bound4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 → ℕ) (x : Fin 4 → ℤ)
    (hx : x ∈ lattice4 p A e) (i : Fin 4) :
    ‖(A.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun k => (x k : ℚ_[p]))) i‖ ≤
      (p : ℝ)^(-(e i : ℤ)) := by
  rw [finite_form_norm4]
  have hi := (lattice4_spec p A e x).mp hx i
  have hr := (Rat.cast_le (K := ℝ)
    (p := padicNorm p ((A *ᵥ (fun k => (x k : ℚ))) i))
    (q := (p : ℚ)^(-(e i : ℤ)))).mpr hi
  simpa only [Rat.cast_zpow,Rat.cast_natCast] using hr

theorem padic_det3_bound4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 3) (Fin 3) ℚ_[p]) (b : Fin 3 → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hA : ∀ j k, ‖A j k‖ ≤ b k) :
    ‖A.det‖ ≤ ∏ k, b k := by
  rw [Matrix.det_apply]
  apply SourceLocalUpper6.padic_sum_bound6 p Finset.univ _ _
    (Finset.prod_nonneg (fun k _ => hb k))
  intro sigma _
  rw [norm_units_zsmul,norm_prod]
  exact Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hA (sigma k) k)

theorem finite_cofactor_bound4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (e : Fin 4 → ℕ) (u : Fin 4 → Fin 4 → ℤ)
    (hu : ∀ j, u j ∈ lattice4 p A e) (i : Fin 4) :
    ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual4 u k : ℚ_[p]))) i‖ ≤
        (p : ℝ)^(∑ k : Fin 3, -(e (i.succAbove k) : ℤ)) := by
  rw [cofactor_minor_norm4 _ (mapped_det_one4 A hA)]
  have hb : ‖((Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ_[p]) *
      (A.map (algebraMap ℚ ℚ_[p])).transpose).submatrix Fin.castSucc i.succAbove).det‖ ≤
      ∏ k : Fin 3, (p : ℝ)^(-(e (i.succAbove k) : ℤ)) := by
    apply padic_det3_bound4 p _ _ (fun k => by positivity)
    intro j k
    simpa [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using
      original_lattice_finite_bound4 p A e (u j.castSucc) (hu j.castSucc) (i.succAbove k)
  apply hb.trans_eq
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hprod (s : Finset (Fin 3)) :
      (∏ k ∈ s, (p : ℝ)^(-(e (i.succAbove k) : ℤ))) =
        (p : ℝ)^(∑ k ∈ s, -(e (i.succAbove k) : ℤ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,zpow_add₀ hp]
  exact hprod Finset.univ

theorem native_ultrametric_pairing4 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 4) (Fin 4) ℚ_[p]) (hB : B.det ≠ 0)
    (f : Fin 4 → ℤ) (x y : Fin 4 → ℤ)
    (hx : ∀ i, ‖(B *ᵥ (fun k => (x k : ℚ_[p]))) i‖ ≤ (p : ℝ)^f i)
    (hy : ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ)^(∑ k : Fin 3, f (i.succAbove k))) :
    ‖(integerPairing4 x y : ℚ_[p])‖ ≤ (p : ℝ)^(∑ i, f i) := by
  rw [native_integer_pairing4 B hB x y]
  apply SourceLocalUpper6.padic_sum_bound6 p Finset.univ _ _ (by positivity)
  intro i _
  rw [norm_mul]
  calc
    _ ≤ (p : ℝ)^f i * (p : ℝ)^(∑ k : Fin 3, f (i.succAbove k)) :=
      mul_le_mul (hx i) (hy i) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero),
        ← Fin.sum_univ_succAbove f i]

theorem source_cofactor_pairing_dvd4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1)
    (e : Fin 4 → ℕ) (u : Fin 4 → Fin 4 → ℤ) (hu : ∀ j, u j ∈ lattice4 p A e)
    (x : Fin 4 → ℤ) (hx : x ∈ lattice4 p A e) :
    (p : ℤ)^(∑ i, e i) ∣ integerPairing4 x (integerLastDual4 u) := by
  have hB : (A.map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
    rw [mapped_det_one4 A hA]
    exact one_ne_zero
  have h := native_ultrametric_pairing4 p (A.map (algebraMap ℚ ℚ_[p])) hB
    (fun i => -(e i : ℤ)) x (integerLastDual4 u)
    (original_lattice_finite_bound4 p A e x hx) (finite_cofactor_bound4 p A hA e u hu)
  apply (SchlickeweiIntegerPairing6.integer_norm_dvd6 p _ (∑ i, e i)).mp
  simpa only [Finset.sum_neg_distrib,← Nat.cast_sum] using h



theorem source_cofactor_real_pairing4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge4 (originalCoordinates4 L hL Q hQ c0)
      (integerReal (u j : Fin 4 → ℤ)) = sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j)
    (x : Fin 4 → ℤ) (r : ℝ)
    (hx : coordinateGauge4 (originalCoordinates4 L hL Q hQ c0) (integerReal x) ≤ r) :
    ‖(integerPairing4 x (integerLastDual4 (fun j => (u j : Fin 4 → ℤ))) : ℝ)‖ ≤
      24 * r * (∏ j : Fin 3, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc) *
        (∏ i : Fin 4, Q^(c0 i)) := by
  let S := ∏ j : Fin 3, sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc
  let T := fun i : Fin 4 => Q^(c0 i)
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hpoint := (originalCoordinates4_bounds L hL Q hQ c0 (integerReal x) r).mp hx
  have hb := source_cofactor_real4 A2 A3 L hL hLdet Q hQ c0 c2 c3 u hatt
  have hn : L.det ≠ 0 := by rw [hLdet]; exact one_ne_zero
  have hp := real_pairing_bound4 L hn x (integerLastDual4 (fun j => (u j : Fin 4 → ℤ)))
    (fun i => r*T i) (fun i => 6*S*(∏ k : Fin 3, T (i.succAbove k)))
    (fun i => mul_nonneg hr (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le)
    (fun i => by simpa only [Real.norm_eq_abs] using hpoint i) hb
  apply hp.trans_eq
  calc
    (∑ i : Fin 4, (r*T i)*(6*S*(∏ k : Fin 3, T (i.succAbove k)))) =
        ∑ _i : Fin 4, 6*r*S*(∏ k : Fin 4, T k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.prod_univ_succAbove T i]
      ring
    _ = 24*r*S*(∏ k : Fin 4, T k) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem source_original_cofactor_estimates4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : IsUnit L) (hLdet : L.det = 1)
    (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ) (V : Set ℝ)
    (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQ : Q ∈ V),
      sourceMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 3 * Q^(-delta)) :
    ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ¬ BddAbove V ∧ ∀ q : V,
      LinearIndependent ℝ (fun j => integerReal (u q j : Fin 4 → ℤ)) ∧
      ∃ hu : LinearIndependent ℚ (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)),
      let w : Matrix (Fin 4) (Fin 4) ℤ := fun j => (u q j : Fin 4 → ℤ)
      let y := integerLastDual4 w
      (∀ j, coordinateGauge4 (originalCoordinates4 L hL q.val (hQV q.val q.property) c0)
        (integerReal (u q j : Fin 4 → ℤ)) =
          sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 j) ∧
      (∀ j, 0 < sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 j) ∧
      Monotone (sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3) ∧
      sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 2 <
        sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 3 * q.val^(-delta) ∧
      w.det ≠ 0 ∧ y ≠ 0 ∧
      (fun i => (y i : ℚ)) = (w.det : ℚ) • lastDual4 (fun j i => (w j i : ℚ)) hu ∧
      (Submodule.span ℚ {fun i => (y i : ℚ)} =
        Submodule.span ℚ {lastDual4 (fun j i => (w j i : ℚ)) hu}) ∧
      (∀ j, integerPairing4 (w j) y = if j = 3 then w.det else 0) ∧
      (∀ i, ‖(L⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i‖ ≤
        6 * (∏ j : Fin 3, sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 j.castSucc) *
          (∏ k : Fin 3, q.val^(c0 (i.succAbove k)))) ∧
      (∀ (x : Fin 4 → ℤ) (r : ℝ),
        coordinateGauge4 (originalCoordinates4 L hL q.val (hQV q.val q.property) c0)
          (integerReal x) ≤ r →
        ‖(integerPairing4 x y : ℝ)‖ ≤
          24*r*(∏ j : Fin 3, sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 j.castSucc)*
            (∏ i : Fin 4, q.val^(c0 i))) ∧
      (∀ i, ‖((A2.map (algebraMap ℚ ℚ_[2]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[2]))) i‖ ≤
        (2 : ℝ)^(∑ k : Fin 3, -(Nat.ceil (JSP000334.qThreshold 2 q.val (c2 (i.succAbove k))) : ℤ))) ∧
      (∀ i, ‖((A3.map (algebraMap ℚ ℚ_[3]))⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[3]))) i‖ ≤
        (3 : ℝ)^(∑ k : Fin 3, -(Nat.ceil (JSP000334.qThreshold 3 q.val (c3 (i.succAbove k))) : ℤ))) ∧
      (∀ x : originalSourceGroup4 A2 A3 q.val c2 c3,
        (2 : ℤ)^(∑ i : Fin 4, Nat.ceil (JSP000334.qThreshold 2 q.val (c2 i))) ∣
          integerPairing4 (x : Fin 4 → ℤ) y ∧
        (3 : ℤ)^(∑ i : Fin 4, Nat.ceil (JSP000334.qThreshold 3 q.val (c3 i))) ∣
          integerPairing4 (x : Fin 4 → ℤ) y) ∧
      LinearMap.ker (normalForm4 y) = firstThreeSpan4 (fun j i => (w j i : ℚ)) ∧
      Module.finrank ℚ (LinearMap.ker (normalForm4 y)) = 3 := by
  obtain ⟨u,hVsame,hframes⟩ := source_original_last_dual_frame4
    A2 A3 L hL c0 c2 c3 delta V hV hQV hgap
  refine ⟨u,hVsame,?_⟩
  intro q
  obtain ⟨hir,hu,hatt,hpos,hmono,hg,_,_,_⟩ := hframes q
  let w : Matrix (Fin 4) (Fin 4) ℤ := fun j => (u q j : Fin 4 → ℤ)
  let y := integerLastDual4 w
  have hm2 (j : Fin 4) : w j ∈ lattice4 2 A2
      (fun i => Nat.ceil (JSP000334.qThreshold 2 q.val (c2 i))) := (u q j).property.1
  have hm3 (j : Fin 4) : w j ∈ lattice4 3 A3
      (fun i => Nat.ceil (JSP000334.qThreshold 3 q.val (c3 i))) := (u q j).property.2
  have hy : y ≠ 0 := integerLastDual4_nonzero w hu
  have hline := integerLastDual4_line w hu
  have hk := fixed_line_kernel4 (fun j i => (w j i : ℚ)) hu y hy hline.symm
  refine ⟨hir,hu,hatt,hpos,hmono,hg,integerFrame4_det_ne_zero w hu,hy,
    integerLastDual4_eq w hu,hline,integerLastDual4_pairing w,
    source_cofactor_real4 A2 A3 L hL hLdet q.val (hQV q.val q.property) c0 c2 c3 (u q) hatt,
    source_cofactor_real_pairing4 A2 A3 L hL hLdet q.val (hQV q.val q.property) c0 c2 c3 (u q) hatt,
    finite_cofactor_bound4 2 A2 h2 _ w hm2,
    finite_cofactor_bound4 3 A3 h3 _ w hm3,?_,hk.2.1,hk.2.2⟩
  intro x
  exact ⟨source_cofactor_pairing_dvd4 2 A2 h2 _ w hm2 x x.property.1,
    source_cofactor_pairing_dvd4 3 A3 h3 _ w hm3 x x.property.2⟩

end CompoundFeasibility.OriginalAuxiliaryDual4
