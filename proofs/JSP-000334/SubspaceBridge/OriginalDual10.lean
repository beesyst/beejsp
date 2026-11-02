import SubspaceBridge.NormalIndex10
import SubspaceBridge.SchlickeweiIntegerPairing6
import SubspaceBridge.SourceLocalUpper6
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.OriginalDual10
open SchmidtNormal10
noncomputable section

def integerNormalForm10 {n : ℕ} (M : Fin n → ℤ) : Module.Dual ℚ (Fin n → ℚ) :=
  ∑ i, (M i : ℚ) • LinearMap.proj i

theorem integerNormalForm10_apply {n : ℕ} (M : Fin n → ℤ) (x : Fin n → ℚ) :
    integerNormalForm10 M x = ∑ i, (M i : ℚ)*x i := by simp [integerNormalForm10]

theorem functional_coordinates_dual10 {n : ℕ} (f : Module.Dual ℚ (Fin n → ℚ)) (x : Fin n → ℚ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply,mul_ite]
  conv_lhs => rw [hx]
  simp

def integerLastDual10 {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℤ) : Fin (n+1) → ℤ :=
  fun i => Matrix.adjugate (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) i (Fin.last n)

theorem integerLastDual10_pairing {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℤ) (j : Fin (n+1)) :
    ∑ i, u j i * integerLastDual10 u i =
      if j = Fin.last n then Matrix.det (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) else 0 := by
  have he := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℤ => M j (Fin.last n))
    (Matrix.mul_adjugate (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ))
  simpa [Matrix.mul_apply,integerLastDual10,Matrix.smul_apply,Matrix.one_apply] using he

def lastDual10 {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℚ) (hu : LinearIndependent ℚ u) : Fin (n+1) → ℚ :=
  fun i => rationalFrameDual42 u hu (Fin.last n) (Pi.single i 1)

theorem det_row_column_bounds10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s t : Fin n → ℝ) (hA : ∀ i j, |A i j| ≤ s i * t j) :
    |A.det| ≤ (n.factorial : ℝ) * (∏ i, s i) * (∏ i, t i) := by
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  change abv A.det ≤ _
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n), abv (Equiv.Perm.sign σ • ∏ j, A (σ j) j) := by
      rw [Matrix.det_apply]
      exact abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ j, |A (σ j) j| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ∏ j, s (σ j) * t j := by
      exact Finset.sum_le_sum fun σ _ => Finset.prod_le_prod
        (fun j _ => abs_nonneg _) (fun j _ => hA (σ j) j)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Equiv.prod_comp]
      simp [Fintype.card_perm, mul_assoc]

theorem integerFrame10_det_cast {n : ℕ} (u : Matrix (Fin n) (Fin n) ℤ) :
    (u.map (Int.castRingHom ℚ)).det = (u.det : ℚ) := by
  exact ((Int.castRingHom ℚ).map_det u).symm

theorem integerFrame10_det_ne_zero {n : ℕ} (u : Fin n → Fin n → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    Matrix.det (u : Matrix (Fin n) (Fin n) ℤ) ≠ 0 := by
  have hd : (Matrix.map (u : Matrix (Fin n) (Fin n) ℤ) (Int.castRingHom ℚ)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hu))
  rw [integerFrame10_det_cast] at hd
  exact_mod_cast hd

theorem integerLastDual10_form {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    integerNormalForm10 (integerLastDual10 u) = ((Matrix.det u : ℤ) : ℚ) •
      rationalFrameDual42 (fun j i => (u j i : ℚ)) hu (Fin.last n) := by
  apply (rationalFrameBasis42 (fun j i => (u j i : ℚ)) hu).ext
  intro j
  rw [rationalFrameBasis42_apply,integerNormalForm10_apply,LinearMap.smul_apply,
    rationalFrameDual42_pairing]
  have he := integerLastDual10_pairing u j
  have hrat : (∑ i, (u j i : ℚ) * (integerLastDual10 u i : ℚ)) =
      if j = Fin.last n then ((Matrix.det u : ℤ) : ℚ) else 0 := by
    exact_mod_cast he
  by_cases hj : j = Fin.last n <;> simpa [hj,smul_eq_mul,mul_comm] using hrat

theorem integerLastDual10_nonzero {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) : integerLastDual10 u ≠ 0 := by
  intro hz
  have hp := integerLastDual10_pairing u (Fin.last n)
  rw [hz] at hp
  simp at hp
  exact integerFrame10_det_ne_zero u hu hp.symm

theorem integerLastDual10_eq {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    (fun i => (integerLastDual10 u i : ℚ)) =
      ((Matrix.det u : ℤ) : ℚ) • lastDual10 (fun j i => (u j i : ℚ)) hu := by
  funext i
  have hi := congrArg (fun f : Module.Dual ℚ (Fin (n+1) → ℚ) => f (Pi.single i 1))
    (integerLastDual10_form u hu)
  simpa [integerNormalForm10,lastDual10,Pi.single_apply] using hi

theorem integerLastDual10_line {n : ℕ} (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    Submodule.span ℚ {fun i => (integerLastDual10 u i : ℚ)} =
      Submodule.span ℚ {lastDual10 (fun j i => (u j i : ℚ)) hu} := by
  rw [integerLastDual10_eq u hu]
  apply Submodule.span_singleton_smul_eq
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast integerFrame10_det_ne_zero u hu


theorem cofactor_dual_cast10 {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (u : Fin (n+1) → Fin (n+1) → ℤ) (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin (n+1)) :
    (integerLastDual10 u i : K) = ((Matrix.det u : ℤ) : K) *
      (lastDual10 (fun j i => (u j i : ℚ)) hu i : K) := by
  have h := congrFun (integerLastDual10_eq u hu) i
  change (integerLastDual10 u i : ℚ) = ((Matrix.det u : ℤ) : ℚ) * _ at h
  have hh := congrArg (fun z : ℚ => (z : K)) h
  simpa only [Rat.cast_mul,Rat.cast_intCast] using hh

theorem cofactor_dual_coordinates10 {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (B : Matrix (Fin (n+1)) (Fin (n+1)) K) (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (i : Fin (n+1)) :
    (B⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : K))) i =
      ((Matrix.det u : ℤ) : K) *
        (∑ k, B⁻¹ k i * (lastDual10 (fun j i => (u j i : ℚ)) hu k : K)) := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [cofactor_dual_cast10 u hu k]
  ring

theorem cofactor_change_of_forms10 {n : ℕ} {K : Type*} [Field K]
    (B : Matrix (Fin (n+1)) (Fin (n+1)) K) (hB : B.det = 1)
    (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (i : Fin (n+1)) :
    (B⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : K))) i =
      (u.map (Int.castRingHom K) * B.transpose).adjugate i (Fin.last n) := by
  have hInv : B⁻¹ = B.adjugate := by
    rw [Matrix.inv_def,hB,Ring.inverse_one,one_smul]
  have hm : (u.map (Int.castRingHom K)).adjugate = u.adjugate.map (Int.castRingHom K) :=
    ((Int.castRingHom K).map_adjugate u).symm
  rw [Matrix.adjugate_mul_distrib,← Matrix.adjugate_transpose,hm,← hInv]
  rfl

theorem native_matrix_pairing10 {n : ℕ} {K : Type*} [Field K]
    (B : Matrix (Fin n) (Fin n) K) (hB : B.det ≠ 0) (x y : Fin n → K) :
    (∑ k, x k * y k) = ∑ i, (B *ᵥ x) i * (B⁻¹.transpose *ᵥ y) i := by
  change x ⬝ᵥ y = (B *ᵥ x) ⬝ᵥ (B⁻¹.transpose *ᵥ y)
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),Matrix.one_mulVec]

def integerPairing10 {n : ℕ} (x y : Fin n → ℤ) : ℤ := ∑ i, x i * y i

theorem native_integer_pairing10 {n : ℕ} {K : Type*} [Field K]
    (B : Matrix (Fin n) (Fin n) K) (hB : B.det ≠ 0) (x y : Fin n → ℤ) :
    (integerPairing10 x y : K) =
      ∑ i, (B *ᵥ (fun k => (x k : K))) i *
        (B⁻¹.transpose *ᵥ (fun k => (y k : K))) i := by
  have hc : (integerPairing10 x y : K) = ∑ k, (x k : K) * (y k : K) := by
    simp [integerPairing10]
  exact hc.trans (native_matrix_pairing10 B hB _ _)


theorem cofactor_minor_norm10 {n : ℕ} {K : Type*} [NormedField K]
    (B : Matrix (Fin (n+1)) (Fin (n+1)) K) (hB : B.det = 1)
    (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (i : Fin (n+1)) :
    ‖(B⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : K))) i‖ =
      ‖((u.map (Int.castRingHom K) * B.transpose).submatrix Fin.castSucc i.succAbove).det‖ := by
  rw [cofactor_change_of_forms10 B hB u i,Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    show (Fin.last n : Fin (n+1)) = Fin.last n from rfl,Fin.succAbove_last]

theorem real_cofactor_bound10 {n : ℕ} (L : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hL : L.det = 1)
    (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (s : Fin n → ℝ) (t : Fin (n+1) → ℝ)
    (hpoint : ∀ (j : Fin n) i, |(L *ᵥ (fun k => (u j.castSucc k : ℝ))) i| ≤ s j * t i)
    (i : Fin (n+1)) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : ℝ))) i‖ ≤
      (n.factorial : ℝ) * (∏ j : Fin n, s j) * (∏ k : Fin n, t (i.succAbove k)) := by
  rw [cofactor_minor_norm10 L hL u i]
  change _ ≤ (Nat.factorial n : ℝ) * _ * _
  apply det_row_column_bounds10
  intro j k
  simpa [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using
    hpoint j (i.succAbove k)

theorem real_pairing_bound10 {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.det ≠ 0)
    (x y : Fin n → ℤ) (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hx : ∀ i, ‖(L *ᵥ (fun k => (x k : ℝ))) i‖ ≤ a i)
    (hy : ∀ i, ‖(L⁻¹.transpose *ᵥ (fun k => (y k : ℝ))) i‖ ≤ b i) :
    ‖(integerPairing10 x y : ℝ)‖ ≤ ∑ i, a i * b i := by
  rw [native_integer_pairing10 L hL x y]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul (hx i) (hy i) (norm_nonneg _) (ha i)


theorem mapped_det_one10 {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.det = 1) :
    (A.map (algebraMap ℚ K)).det = 1 := by
  have he := (algebraMap ℚ K).map_det A
  change (algebraMap ℚ K) A.det = (A.map (algebraMap ℚ K)).det at he
  rw [hA,map_one] at he
  exact he.symm

theorem finite_form_norm10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℤ) (i : Fin n) :
    ‖(A.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun k => (x k : ℚ_[p]))) i‖ =
      (padicNorm p ((A *ᵥ (fun k => (x k : ℚ))) i) : ℝ) := by
  rw [← Auxiliary6.SourceExpansion.finite_norm p]
  congr 1
  simp [Matrix.mulVec,dotProduct,map_sum,map_mul]

theorem original_lattice_finite_bound10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℚ) (e : Fin n → ℕ) (x : Fin n → ℤ)
    (hx : x ∈ lattice10 p A e) (i : Fin n) :
    ‖(A.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun k => (x k : ℚ_[p]))) i‖ ≤
      (p : ℝ)^(-(e i : ℤ)) := by
  rw [finite_form_norm10]
  have hi := (lattice10_spec p A e x).mp hx i
  have hr := (Rat.cast_le (K := ℝ)
    (p := padicNorm p ((A *ᵥ (fun k => (x k : ℚ))) i))
    (q := (p : ℚ)^(-(e i : ℤ)))).mpr hi
  simpa only [Rat.cast_zpow,Rat.cast_natCast] using hr

theorem padic_det3_bound10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℚ_[p]) (b : Fin n → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hA : ∀ j k, ‖A j k‖ ≤ b k) :
    ‖A.det‖ ≤ ∏ k, b k := by
  rw [Matrix.det_apply]
  apply SourceLocalUpper6.padic_sum_bound6 p Finset.univ _ _
    (Finset.prod_nonneg (fun k _ => hb k))
  intro sigma _
  rw [norm_units_zsmul,norm_prod]
  exact Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hA (sigma k) k)

theorem finite_cofactor_bound10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hA : A.det = 1)
    (e : Fin (n+1) → ℕ) (u : Fin (n+1) → Fin (n+1) → ℤ)
    (hu : ∀ j, u j ∈ lattice10 p A e) (i : Fin (n+1)) :
    ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual10 u k : ℚ_[p]))) i‖ ≤
        (p : ℝ)^(∑ k : Fin n, -(e (i.succAbove k) : ℤ)) := by
  rw [cofactor_minor_norm10 _ (mapped_det_one10 A hA)]
  have hb : ‖((Matrix.map (u : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (Int.castRingHom ℚ_[p]) *
      (A.map (algebraMap ℚ ℚ_[p])).transpose).submatrix Fin.castSucc i.succAbove).det‖ ≤
      ∏ k : Fin n, (p : ℝ)^(-(e (i.succAbove k) : ℤ)) := by
    apply padic_det3_bound10 p _ _ (fun k => by positivity)
    intro j k
    simpa [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using
      original_lattice_finite_bound10 p A e (u j.castSucc) (hu j.castSucc) (i.succAbove k)
  apply hb.trans_eq
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hprod (s : Finset (Fin n)) :
      (∏ k ∈ s, (p : ℝ)^(-(e (i.succAbove k) : ℤ))) =
        (p : ℝ)^(∑ k ∈ s, -(e (i.succAbove k) : ℤ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,zpow_add₀ hp]
  exact hprod Finset.univ

theorem native_ultrametric_pairing10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) (hB : B.det ≠ 0)
    (f : Fin (n+1) → ℤ) (x y : Fin (n+1) → ℤ)
    (hx : ∀ i, ‖(B *ᵥ (fun k => (x k : ℚ_[p]))) i‖ ≤ (p : ℝ)^f i)
    (hy : ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ)^(∑ k : Fin n, f (i.succAbove k))) :
    ‖(integerPairing10 x y : ℚ_[p])‖ ≤ (p : ℝ)^(∑ i, f i) := by
  rw [native_integer_pairing10 B hB x y]
  apply SourceLocalUpper6.padic_sum_bound6 p Finset.univ _ _ (by positivity)
  intro i _
  rw [norm_mul]
  calc
    _ ≤ (p : ℝ)^f i * (p : ℝ)^(∑ k : Fin n, f (i.succAbove k)) :=
      mul_le_mul (hx i) (hy i) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero),
        ← Fin.sum_univ_succAbove f i]

theorem source_cofactor_pairing_dvd10 {n : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hA : A.det = 1)
    (e : Fin (n+1) → ℕ) (u : Fin (n+1) → Fin (n+1) → ℤ) (hu : ∀ j, u j ∈ lattice10 p A e)
    (x : Fin (n+1) → ℤ) (hx : x ∈ lattice10 p A e) :
    (p : ℤ)^(∑ i, e i) ∣ integerPairing10 x (integerLastDual10 u) := by
  have hB : (A.map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
    rw [mapped_det_one10 A hA]
    exact one_ne_zero
  have h := native_ultrametric_pairing10 p (A.map (algebraMap ℚ ℚ_[p])) hB
    (fun i => -(e i : ℤ)) x (integerLastDual10 u)
    (original_lattice_finite_bound10 p A e x hx) (finite_cofactor_bound10 p A hA e u hu)
  apply (SchlickeweiIntegerPairing6.integer_norm_dvd6 p _ (∑ i, e i)).mp
  simpa only [Finset.sum_neg_distrib,← Nat.cast_sum] using h





def minorMatrix10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (u : Fin 10 → Fin 10 → ℤ) (i : Fin 10) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun j k => (L *ᵥ (fun a => (u j.castSucc a : ℝ))) (i.succAbove k)

theorem minorMatrix10_bounds (L : Matrix (Fin 10) (Fin 10) ℝ)
    (u : Fin 10 → Fin 10 → ℤ) (s : Fin 9 → ℝ) (t : Fin 10 → ℝ)
    (hpoint : ∀ (j : Fin 9) (a : Fin 10),
      |(L *ᵥ (fun k => (u j.castSucc k : ℝ))) a| ≤ s j * t a) (i : Fin 10) :
    ∀ j k, |minorMatrix10 L u i j k| ≤ s j * t (i.succAbove k) :=
  fun j k => hpoint j (i.succAbove k)

theorem minorMatrix10_det_bound (L : Matrix (Fin 10) (Fin 10) ℝ)
    (u : Fin 10 → Fin 10 → ℤ) (s : Fin 9 → ℝ) (t : Fin 10 → ℝ)
    (hpoint : ∀ (j : Fin 9) (a : Fin 10),
      |(L *ᵥ (fun k => (u j.castSucc k : ℝ))) a| ≤ s j * t a) (i : Fin 10) :
    |(minorMatrix10 L u i).det| ≤
      362880 * (∏ j : Fin 9, s j) * (∏ k : Fin 9, t (i.succAbove k)) := by
  have hb := det_row_column_bounds10 (minorMatrix10 L u i) s
    (fun k => t (i.succAbove k)) (minorMatrix10_bounds L u s t hpoint i)
  norm_num only [Nat.factorial] at hb
  exact hb



theorem inverse_adjugate_fin10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : L.det = 1) :
    L⁻¹ = L.adjugate := by
  rw [Matrix.inv_def, hL, Ring.inverse_one, one_smul]

theorem integer_dual_change_fin10 (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : L.det = 1) (u : Matrix (Fin 10) (Fin 10) ℤ) (i : Fin 10) :
    (L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : ℝ))) i =
      (u.map (Int.castRingHom ℝ) * L.transpose).adjugate i (Fin.last 9) := by
  have hm : (u.map (Int.castRingHom ℝ)).adjugate = u.adjugate.map (Int.castRingHom ℝ) :=
    ((Int.castRingHom ℝ).map_adjugate u).symm
  rw [Matrix.adjugate_mul_distrib, ← Matrix.adjugate_transpose, hm,
    ← inverse_adjugate_fin10 L hL]
  rfl

theorem minorMatrix10_eq (L : Matrix (Fin 10) (Fin 10) ℝ)
    (u : Matrix (Fin 10) (Fin 10) ℤ) (i : Fin 10) :
    minorMatrix10 L u i =
      (u.map (Int.castRingHom ℝ) * L.transpose).submatrix Fin.castSucc i.succAbove := by
  ext j k
  simp only [minorMatrix10, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Int.coe_castRingHom, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem dual_minor_abs10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : L.det = 1)
    (u : Matrix (Fin 10) (Fin 10) ℤ) (i : Fin 10) :
    |(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : ℝ))) i| =
      |(minorMatrix10 L u i).det| := by
  rw [integer_dual_change_fin10 L hL u i,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Fin.succAbove_last, ← minorMatrix10_eq]

theorem real_cofactor_fin10 (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : L.det = 1)
    (u : Matrix (Fin 10) (Fin 10) ℤ) (s : Fin 9 → ℝ) (t : Fin 10 → ℝ)
    (hpoint : ∀ (j : Fin 9) (i : Fin 10),
      |(L *ᵥ (fun k => (u j.castSucc k : ℝ))) i| ≤ s j * t i) (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 u k : ℝ))) i‖ ≤
      362880 * (∏ j : Fin 9, s j) * (∏ k : Fin 9, t (i.succAbove k)) := by
  rw [Real.norm_eq_abs, dual_minor_abs10 L hL u i]
  exact minorMatrix10_det_bound L u s t hpoint i

theorem source_original_coordinate_bounds10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u j : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j) :
    ∀ (j : Fin 9) (i : Fin 10),
      |(L *ᵥ (fun k => ((u j.castSucc : Fin 10 → ℤ) k : ℝ))) i| ≤
        sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc * Q^(c0 i) := by
  intro j i
  exact (originalCoordinates10_bounds L hL Q hQ c0
    (integerReal (u j.castSucc : Fin 10 → ℤ)) _).mp (hatt j.castSucc).le i

theorem source_cofactor_real10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u j : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j)
    (i : Fin 10) :
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) k : ℝ))) i‖ ≤
      362880 * (∏ j : Fin 9, sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc) *
        (∏ k : Fin 9, Q^(c0 (i.succAbove k))) := by
  exact real_cofactor_fin10 L hLdet (fun j => (u j : Fin 10 → ℤ))
    (fun j : Fin 9 => sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc)
    (fun k => Q^(c0 k)) (source_original_coordinate_bounds10 A2 A3 L hL Q hQ c0 c2 c3 u hatt) i

theorem source_cofactor_real_pairing10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (hLdet : L.det = 1) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hatt : ∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u j : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j)
    (x : Fin 10 → ℤ) (r : ℝ)
    (hx : coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) (integerReal x) ≤ r) :
    ‖(integerPairing10 x (integerLastDual10 (fun j => (u j : Fin 10 → ℤ))) : ℝ)‖ ≤
      3628800 * r * (∏ j : Fin 9, sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc) *
        (∏ i : Fin 10, Q^(c0 i)) := by
  let S := ∏ j : Fin 9, sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc
  let T := fun i : Fin 10 => Q^(c0 i)
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hpoint := (originalCoordinates10_bounds L hL Q hQ c0 (integerReal x) r).mp hx
  have hb := source_cofactor_real10 A2 A3 L hL hLdet Q hQ c0 c2 c3 u hatt
  have hn : L.det ≠ 0 := by rw [hLdet]; exact one_ne_zero
  have hp := real_pairing_bound10 L hn x (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)))
    (fun i => r*T i) (fun i => 362880*S*(∏ k : Fin 9, T (i.succAbove k)))
    (fun i => mul_nonneg hr (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le)
    (fun i => by simpa only [Real.norm_eq_abs] using hpoint i) hb
  apply hp.trans_eq
  calc
    (∑ i : Fin 10, (r*T i)*(362880*S*(∏ k : Fin 9, T (i.succAbove k)))) =
        ∑ _i : Fin 10, 362880*r*S*(∏ k : Fin 10, T k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.prod_univ_succAbove T i]
      ring
    _ = 3628800*r*S*(∏ k : Fin 10, T k) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

def lastCofactorDimension10 {N : ℕ} (hN : 0 < N)
    (u : Matrix (Fin N) (Fin N) ℤ) : Fin N → ℤ :=
  fun i => u.adjugate i ⟨N-1, Nat.sub_lt hN (by omega)⟩

theorem finite_cofactor_dimension10 {N : ℕ} (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin N) (Fin N) ℚ) (hA : A.det = 1)
    (e : Fin N → ℕ) (u : Fin N → Fin N → ℤ)
    (hu : ∀ j, u j ∈ lattice10 p A e) (i : Fin N) :
    ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ
      (fun k => (lastCofactorDimension10 hN u k : ℚ_[p]))) i‖ ≤
        (p : ℝ)^((∑ k : Fin N, -(e k : ℤ)) + (e i : ℤ)) := by
  cases N with
  | zero => omega
  | succ n =>
    have hd : lastCofactorDimension10 hN u = integerLastDual10 u := by
      funext k
      rfl
    rw [hd]
    have hb := finite_cofactor_bound10 p A hA e u hu i
    have he : (∑ k : Fin n, -(e (i.succAbove k) : ℤ)) =
        (∑ k : Fin (n+1), -(e k : ℤ)) + (e i : ℤ) := by
      rw [Fin.sum_univ_succAbove (fun k => -(e k : ℤ)) i]
      ring
    exact hb.trans_eq (congrArg (fun z : ℤ => (p : ℝ)^z) he)

theorem cofactor_divisibility_dimension10 {N : ℕ} (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin N) (Fin N) ℚ) (hA : A.det = 1)
    (e : Fin N → ℕ) (u : Fin N → Fin N → ℤ) (hu : ∀ j, u j ∈ lattice10 p A e)
    (x : Fin N → ℤ) (hx : x ∈ lattice10 p A e) :
    (p : ℤ)^(∑ i, e i) ∣ integerPairing10 x (lastCofactorDimension10 hN u) := by
  cases N with
  | zero => omega
  | succ n =>
    have hd : lastCofactorDimension10 hN u = integerLastDual10 u := by
      funext k
      rfl
    rw [hd]
    exact source_cofactor_pairing_dvd10 p A hA e u hu x hx

theorem finite_cofactor_fin10 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1)
    (e : Fin 10 → ℕ) (u : Fin 10 → Fin 10 → ℤ)
    (hu : ∀ j, u j ∈ lattice10 p A e) (i : Fin 10) :
    ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ
      (fun k => (integerLastDual10 u k : ℚ_[p]))) i‖ ≤
        (p : ℝ)^(∑ k : Fin 9, -(e (i.succAbove k) : ℤ)) := by
  have hb := finite_cofactor_dimension10 (by decide : 0 < 10) p A hA e u hu i
  have hd : lastCofactorDimension10 (by decide : 0 < 10) u = integerLastDual10 u := by
    funext k
    rfl
  rw [hd] at hb
  have he : ((∑ k : Fin 10, -(e k : ℤ)) + (e i : ℤ)) =
      ∑ k : Fin 9, -(e (i.succAbove k) : ℤ) := by
    rw [Fin.sum_univ_succAbove (fun k => -(e k : ℤ)) i]
    ring
  exact hb.trans_eq (congrArg (fun z : ℤ => (p : ℝ)^z) he)

theorem cofactor_lattice_divisibility_fin10 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (hA : A.det = 1)
    (e : Fin 10 → ℕ) (u : Fin 10 → Fin 10 → ℤ) (hu : ∀ j, u j ∈ lattice10 p A e)
    (x : Fin 10 → ℤ) (hx : x ∈ lattice10 p A e) :
    (p : ℤ)^(∑ i, e i) ∣ integerPairing10 x (integerLastDual10 u) := by
  have hd : lastCofactorDimension10 (by decide : 0 < 10) u = integerLastDual10 u := by
    funext k
    rfl
  have hb := cofactor_divisibility_dimension10 (by decide : 0 < 10) p A hA e u hu x hx
  rw [hd] at hb
  exact hb

def sourceFiniteDualBound10 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 10) (Fin 10) ℚ) (Q : ℝ) (c : Fin 10 → ℝ) (y : Fin 10 → ℤ) : Prop :=
  ∀ i : Fin 10, ‖((A.map (algebraMap ℚ ℚ_[p]))⁻¹.transpose *ᵥ
    (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ)^(∑ k : Fin 9, -(Nat.ceil (JSP000334.qThreshold p Q (c (i.succAbove k))) : ℤ))

theorem source_finite_cofactor10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (Q : ℝ) (c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3) :
    sourceFiniteDualBound10 2 A2 Q c2 (integerLastDual10 (fun j => (u j : Fin 10 → ℤ))) ∧
    sourceFiniteDualBound10 3 A3 Q c3 (integerLastDual10 (fun j => (u j : Fin 10 → ℤ))) := by
  constructor
  · intro i
    exact finite_cofactor_fin10 2 A2 h2 _ (fun j => (u j : Fin 10 → ℤ))
      (fun j => (u j).property.1) i
  · intro i
    exact finite_cofactor_fin10 3 A3 h3 _ (fun j => (u j : Fin 10 → ℤ))
      (fun j => (u j).property.2) i

theorem source_cofactor_divisibility10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (Q : ℝ) (c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (x : originalSourceGroup10 A2 A3 Q c2 c3) :
    (2 : ℤ)^(∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c2 i))) ∣
      integerPairing10 (x : Fin 10 → ℤ) (integerLastDual10 (fun j => (u j : Fin 10 → ℤ))) ∧
    (3 : ℤ)^(∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))) ∣
      integerPairing10 (x : Fin 10 → ℤ) (integerLastDual10 (fun j => (u j : Fin 10 → ℤ))) := by
  constructor
  · exact cofactor_lattice_divisibility_fin10 2 A2 h2 _ (fun j => (u j : Fin 10 → ℤ))
      (fun j => (u j).property.1) (x : Fin 10 → ℤ) x.property.1
  · exact cofactor_lattice_divisibility_fin10 3 A3 h3 _ (fun j => (u j : Fin 10 → ℤ))
      (fun j => (u j).property.2) (x : Fin 10 → ℤ) x.property.2

theorem adjugate_pairing_dimension10 {N : ℕ} (hN : 0 < N)
    (u : Matrix (Fin N) (Fin N) ℤ) (j : Fin N) :
    ∑ i, u j i * lastCofactorDimension10 hN u i =
      if j = ⟨N-1, Nat.sub_lt hN (by omega)⟩ then u.det else 0 := by
  cases N with
  | zero => omega
  | succ n =>
    have hd : lastCofactorDimension10 hN u = integerLastDual10 u := by
      funext k
      rfl
    rw [hd]
    exact integerLastDual10_pairing u j

theorem integerLastDual10_pairing_fin10 (u : Matrix (Fin 10) (Fin 10) ℤ) (j : Fin 10) :
    ∑ i, u j i * integerLastDual10 u i =
      if j = Fin.last 9 then u.det else 0 := by
  exact adjugate_pairing_dimension10 (by decide : 0 < 10) u j

def lastDualDimension10 {N : ℕ} (hN : 0 < N)
    (u : Fin N → Fin N → ℚ) (hu : LinearIndependent ℚ u) : Fin N → ℚ :=
  fun i => rationalFrameDual42 u hu ⟨N-1, Nat.sub_lt hN (by omega)⟩ (Pi.single i 1)

theorem rational_cast_dimension10 {N : ℕ} (hN : 0 < N)
    (u : Matrix (Fin N) (Fin N) ℤ) (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    (fun i => (lastCofactorDimension10 hN u i : ℚ)) =
      (u.det : ℚ) • lastDualDimension10 hN (fun j i => (u j i : ℚ)) hu := by
  cases N with
  | zero => omega
  | succ n =>
    exact integerLastDual10_eq u hu

structure SourceOriginalDualCertificate10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3) : Prop where
  nonzero : integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) ≠ 0
  adjugate_pairing : ∀ j : Fin 10, ∑ i, (u j : Fin 10 → ℤ) i *
    integerLastDual10 (fun a => (u a : Fin 10 → ℤ)) i =
      if j = Fin.last 9 then Matrix.det (fun a => (u a : Fin 10 → ℤ)) else 0
  real_bound : ∀ i : Fin 10,
    ‖(L⁻¹.transpose *ᵥ (fun k => (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) k : ℝ))) i‖ ≤
      362880 * (∏ j : Fin 9, sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc) *
        (∏ k : Fin 9, Q^(c0 (i.succAbove k)))
  finite_two : sourceFiniteDualBound10 2 A2 Q c2 (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)))
  finite_three : sourceFiniteDualBound10 3 A3 Q c3 (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)))
  finite_divisibility : ∀ x : originalSourceGroup10 A2 A3 Q c2 c3,
    (2 : ℤ)^(∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c2 i))) ∣
      integerPairing10 (x : Fin 10 → ℤ) (integerLastDual10 (fun j => (u j : Fin 10 → ℤ))) ∧
    (3 : ℤ)^(∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))) ∣
      integerPairing10 (x : Fin 10 → ℤ) (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)))
  real_pairing : ∀ (x : Fin 10 → ℤ) (r : ℝ),
    coordinateGauge10 (originalCoordinates10 L hL Q hQ c0) (integerReal x) ≤ r →
      ‖(integerPairing10 x (integerLastDual10 (fun j => (u j : Fin 10 → ℤ))) : ℝ)‖ ≤
        3628800 * r * (∏ j : Fin 9, sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j.castSucc) *
          (∏ i : Fin 10, Q^(c0 i))
  rational_cast : ∀ hu : LinearIndependent ℚ (fun j i => ((u j : Fin 10 → ℤ) i : ℚ)),
    (fun i => (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) i : ℚ)) =
      ((Matrix.det (fun j => (u j : Fin 10 → ℤ)) : ℤ) : ℚ) •
        lastDual10 (fun j i => ((u j : Fin 10 → ℤ) i : ℚ)) hu
  real_cast : ∀ hu : LinearIndependent ℚ (fun j i => ((u j : Fin 10 → ℤ) i : ℚ)), ∀ i : Fin 10,
    (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) i : ℝ) =
      ((Matrix.det (fun j => (u j : Fin 10 → ℤ)) : ℤ) : ℝ) *
        (lastDual10 (fun j i => ((u j : Fin 10 → ℤ) i : ℚ)) hu i : ℝ)

theorem source_original_dual_certificate10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (hLdet : L.det = 1)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 10 → ℝ)
    (u : Fin 10 → originalSourceGroup10 A2 A3 Q c2 c3)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j : Fin 10 → ℤ)))
    (hatt : ∀ j, coordinateGauge10 (originalCoordinates10 L hL Q hQ c0)
      (integerReal (u j : Fin 10 → ℤ)) = sourceMinima10 A2 A3 L hL Q hQ c0 c2 c3 j) :
    SourceOriginalDualCertificate10 A2 A3 L hL Q hQ c0 c2 c3 u := by
  let f : (Fin 10 → ℚ) →ₗ[ℚ] (Fin 10 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have huQ : LinearIndependent ℚ (fun j i => ((u j : Fin 10 → ℤ) i : ℚ)) := by
    apply LinearIndependent.of_comp f
    convert hu.restrict_scalars' ℚ using 1
  obtain ⟨hfinite2, hfinite3⟩ := source_finite_cofactor10 A2 A3 h2 h3 Q c2 c3 u
  have hcast : ∀ h : LinearIndependent ℚ (fun j i => ((u j : Fin 10 → ℤ) i : ℚ)),
      (fun i => (integerLastDual10 (fun j => (u j : Fin 10 → ℤ)) i : ℚ)) =
        ((Matrix.det (fun j => (u j : Fin 10 → ℤ)) : ℤ) : ℚ) •
          lastDual10 (fun j i => ((u j : Fin 10 → ℤ) i : ℚ)) h := by
    intro h
    exact rational_cast_dimension10 (by decide : 0 < 10) _ h
  exact {
    nonzero := integerLastDual10_nonzero _ huQ
    adjugate_pairing := integerLastDual10_pairing_fin10 _
    real_bound := source_cofactor_real10 A2 A3 L hL hLdet Q hQ c0 c2 c3 u hatt
    finite_two := hfinite2
    finite_three := hfinite3
    finite_divisibility := source_cofactor_divisibility10 A2 A3 h2 h3 Q c2 c3 u
    real_pairing := source_cofactor_real_pairing10 A2 A3 L hL hLdet Q hQ c0 c2 c3 u hatt
    rational_cast := hcast
    real_cast := by
      intro h i
      have hi := congrFun (hcast h) i
      have hr := congrArg (fun z : ℚ => (z : ℝ)) hi
      simpa only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_intCast] using hr
  }

end
end CompoundFeasibility.OriginalDual10
