import Mathlib.RingTheory.Localization.Integer
import SubspaceBridge.CompoundBridge42
open scoped BigOperators Matrix
namespace CompoundFeasibility

theorem abs_det_le_column_bounds {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hM : ∀ i j, |M i j| ≤ r j) :
    |M.det| ≤ (n.factorial : ℝ) * ∏ j, r j := by
  classical
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  change abv M.det ≤ _
  calc
    abv M.det = abv (∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ∏ j, M (σ j) j) := congrArg abv (Matrix.det_apply M)
    _ ≤ ∑ σ : Equiv.Perm (Fin n), abv (Equiv.Perm.sign σ • ∏ j, M (σ j) j) := abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ j, |M (σ j) j| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, r j :=
      Finset.sum_le_sum fun σ _ =>
        Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hM (σ j) j)
    _ = _ := by simp [Fintype.card_perm]

private theorem integer_frame_det_lower_generic {n : ℕ}
    (u : Matrix (Fin n) (Fin n) ℤ)
    (hu : LinearIndependent ℝ (fun j i => (u j i : ℝ))) :
    1 ≤ |(u.map (Int.castRingHom ℝ)).det| := by

  have hv :
      LinearIndependent ℝ (u.map (Int.castRingHom ℝ)).row := by
    change LinearIndependent ℝ (fun j i => (u j i : ℝ))
    exact hu

  have hunit : IsUnit (u.map (Int.castRingHom ℝ)) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hv

  have hd : (u.map (Int.castRingHom ℝ)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

  have hmatrix :
      (Int.castRingHom ℝ).mapMatrix u =
        u.map (Int.castRingHom ℝ) := by
    ext i j
    rfl

  have hcast :
      (u.det : ℝ) =
        (u.map (Int.castRingHom ℝ)).det := by
    calc
      (u.det : ℝ) =
          ((Int.castRingHom ℝ).mapMatrix u).det :=
        (Int.castRingHom ℝ).map_det u
      _ = (u.map (Int.castRingHom ℝ)).det :=
        congrArg
          (fun M : Matrix (Fin n) (Fin n) ℝ => M.det)
          hmatrix

  have hz : u.det ≠ 0 := by
    intro hzero
    apply hd
    calc
      (u.map (Int.castRingHom ℝ)).det =
          (u.det : ℝ) := hcast.symm
      _ = 0 := by rw [hzero, Int.cast_zero]

  have habs : (1 : ℝ) ≤ |(u.det : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hz

  calc
    1 ≤ |(u.det : ℝ)| := habs
    _ = |(u.map (Int.castRingHom ℝ)).det| :=
      congrArg abs hcast


theorem integer_frame_det_lower6 (u : Fin 6 → Fin 6 → ℤ)
    (hu : LinearIndependent ℝ (fun j i => (u j i : ℝ))) :
    1 ≤ |(Matrix.map (u : Matrix (Fin 6) (Fin 6) ℤ)
      (Int.castRingHom ℝ)).det| := by
  exact integer_frame_det_lower_generic
    (u := (u : Matrix (Fin 6) (Fin 6) ℤ)) hu

theorem abs_det_le_weighted_bounds {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (w r : Fin n → ℝ) (hbound : ∀ i j, |M i j| ≤ r j * w i) :
    |M.det| ≤ (n.factorial : ℝ) * (∏ j, r j) * ∏ i, w i := by
  classical
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  change abv M.det ≤ _
  calc
    abv M.det = abv (∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ∏ j, M (σ j) j) := congrArg abv (Matrix.det_apply M)
    _ ≤ ∑ σ : Equiv.Perm (Fin n), abv (Equiv.Perm.sign σ • ∏ j, M (σ j) j) := abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ j, |M (σ j) j| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ∏ j, (r j * w (σ j)) :=
      Finset.sum_le_sum fun σ _ =>
        Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hbound (σ j) j)
    _ = _ := by
      simp_rw [Finset.prod_mul_distrib, Equiv.prod_comp]
      simp [Fintype.card_perm, mul_assoc]

theorem integer_frame_body_product_lower6
    (B : Matrix (Fin 6) (Fin 6) ℝ)
    (u : Fin 6 → Fin 6 → ℤ)
    (hu : LinearIndependent ℝ (fun j i => (u j i : ℝ)))
    (w r : Fin 6 → ℝ)
    (hbound : ∀ j i,
      |(B *ᵥ (fun k => (u j k : ℝ))) i| ≤ r j * w i) :
    |B.det| ≤ 720 * (∏ j, r j) * ∏ i, w i := by

  let U : Matrix (Fin 6) (Fin 6) ℝ :=
    Matrix.map (u : Matrix (Fin 6) (Fin 6) ℤ)
      (Int.castRingHom ℝ)

  have hnorm :
      ∀ i j, |(B * U.transpose) i j| ≤ r j * w i := by
    intro i j
    change
      |(B *ᵥ (fun k => (u j k : ℝ))) i| ≤ r j * w i
    exact hbound j i

  have hfac : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by
    norm_num [Nat.factorial]

  have hbd :
      |(B * U.transpose).det| ≤
        720 * (∏ j, r j) * ∏ i, w i := by
    have h := abs_det_le_weighted_bounds
      (B * U.transpose) w r hnorm
    simpa only [hfac] using h

  have hdetU : (1 : ℝ) ≤ |U.det| := by
    simpa only [U] using integer_frame_det_lower6 u hu

  have hh :
      |B.det| ≤ |(B * U.transpose).det| := by
    calc
      |B.det| ≤ |B.det| * |U.det| :=
        le_mul_of_one_le_right (abs_nonneg _) hdetU
      _ = |(B * U.transpose).det| := by
        rw [Matrix.det_mul, Matrix.det_transpose, abs_mul]

  exact hh.trans hbd

end CompoundFeasibility

namespace CompoundFeasibility

theorem clear_matrix_denominators {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ i j, ∃ z : ℤ, (z : ℚ) = (D : ℚ) * B i j := by
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun ij : Fin n × Fin n => B ij.1 ij.2)
  refine ⟨D, mem_nonZeroDivisors_iff_ne_zero.mp D.property, ?_⟩
  intro i j
  obtain ⟨z,hz⟩ := hD (i,j)
  exact ⟨z, by simpa only [Algebra.smul_def, map_intCast] using hz⟩

theorem local_multiple_bounds {n : ℕ} (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin n) (Fin n) ℚ) (e : Fin n → ℕ)
    (D : ℤ) (hD : ∀ i j, ∃ z : ℤ, (z : ℚ) = (D : ℚ) * B i j)
    (T : ℤ) (j : Fin n) :
    ∀ i, padicNorm p ((B *ᵥ (fun k =>
      ((Pi.single j (D * (p : ℤ) ^ (∑ a, e a) * T) : Fin n → ℤ) k : ℚ))) i) ≤
        (p : ℚ) ^ (-(e i : ℤ)) := by
  intro i
  obtain ⟨z,hz⟩ := hD i j
  have hm : (B *ᵥ (fun k =>
      ((Pi.single j (D * (p : ℤ) ^ (∑ a, e a) * T) : Fin n → ℤ) k : ℚ))) i =
      (((p : ℤ) ^ (∑ a, e a) * T * z : ℤ) : ℚ) := by
    have hc : (fun k => ((Pi.single j (D * (p : ℤ) ^ (∑ a, e a) * T) : Fin n → ℤ) k : ℚ)) =
        Pi.single j ((D : ℚ) * (p : ℚ) ^ (∑ a, e a) * (T : ℚ)) := by
      ext k
      by_cases hk : k = j <;> simp [Pi.single_apply,hk]
    rw [hc,Matrix.mulVec_single]
    change B i j * ((D : ℚ) * (p : ℚ) ^ (∑ a, e a) * (T : ℚ)) = _
    push_cast
    rw [hz]
    ring
  rw [hm]
  apply padicNorm.dvd_iff_norm_le.mp
  have hi : e i ≤ ∑ a, e a := Finset.single_le_sum (fun a _ => Nat.zero_le (e a)) (Finset.mem_univ i)
  have hd : (p : ℤ) ^ e i ∣ (p : ℤ) ^ (∑ a, e a) * T * z :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hi) T) z
  exact_mod_cast hd


theorem sourceLattice6_multiple (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ j : Fin 6, Pi.single j D ∈ sourceLattice6 A₂ A₃ e₂ e₃ := by
  obtain ⟨D₂,h₂,hD₂⟩ := clear_matrix_denominators (compound A₂)
  obtain ⟨D₃,h₃,hD₃⟩ := clear_matrix_denominators (compound A₃)
  let f₂ := fun s : Fin 6 => e₂ (lo s) + e₂ (hi s)
  let f₃ := fun s : Fin 6 => e₃ (lo s) + e₃ (hi s)
  let D : ℤ := D₂ * D₃ * 2 ^ (∑ s, f₂ s) * 3 ^ (∑ s, f₃ s)
  refine ⟨D, by dsimp [D]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h₂ h₃) (by positivity)) (by positivity), ?_⟩
  intro j
  constructor
  · apply (lattice6_spec 2 A₂ e₂ _).mpr
    have he : D = D₂ * 2 ^ (∑ s, f₂ s) * (D₃ * 3 ^ (∑ s, f₃ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 2 (compound A₂) f₂ D₂ hD₂ _ j
  · apply (lattice6_spec 3 A₃ e₃ _).mpr
    have he : D = D₃ * 3 ^ (∑ s, f₃ s) * (D₂ * 2 ^ (∑ s, f₂ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 3 (compound A₃) f₃ D₃ hD₃ _ j

theorem integer_subgroup_has_basis {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    (D : ℤ) (hD : D ≠ 0) (hm : ∀ j, Pi.single j D ∈ G) :
    Nonempty (Basis (Fin n) ℤ G) := by
  classical
  let f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) := D • LinearMap.id
  have hf : Function.Injective f := by
    intro x y h
    funext i
    exact mul_left_cancel₀ hD (congrFun h i)
  have hm' (j : Fin n) : f (Pi.basisFun ℤ (Fin n) j) ∈ G := by
    convert hm j using 1
    ext i
    simp [f,Pi.basisFun_apply,Pi.single_apply]
  let u : Fin n → G := fun j => ⟨f (Pi.basisFun ℤ (Fin n) j),hm' j⟩
  have hu : LinearIndependent ℤ u := by
    apply LinearIndependent.of_comp G.toIntSubmodule.subtype
    exact (Pi.basisFun ℤ (Fin n)).linearIndependent.map' f
      (LinearMap.ker_eq_bot_of_injective hf)
  letI : Module.Finite ℤ G := Module.Finite.of_injective G.subtype.toIntLinearMap Subtype.val_injective
  letI : NoZeroSMulDivisors ℤ G := Function.Injective.noZeroSMulDivisors
    (fun x : G => (x : Fin n → ℤ)) Subtype.val_injective rfl (fun _ _ => rfl)
  have hr : Module.finrank ℤ G = n := by
    have hl := hu.fintype_card_le_finrank
    have hh := G.toIntSubmodule.finrank_le
    have hd : Module.finrank ℤ (Fin n → ℤ) = n := by simp [Module.finrank_pi]
    rw [hd] at hh
    change Module.finrank ℤ G ≤ n at hh
    have hl' : n ≤ Module.finrank ℤ G := by simpa using hl
    exact le_antisymm hh hl'
  exact ⟨Module.finBasisOfFinrankEq ℤ G hr⟩

theorem sourceLattice6_has_basis (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : Nonempty (Basis (Fin 6) ℤ (sourceLattice6 A₂ A₃ e₂ e₃)) := by
  obtain ⟨D,hD,hm⟩ := sourceLattice6_multiple A₂ A₃ e₂ e₃
  exact integer_subgroup_has_basis _ D hD hm


def integerReal {n : ℕ} : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' z x := by ext i; simp [Int.cast_mul]

theorem integerReal_injective {n : ℕ} : Function.Injective (integerReal (n := n)) := by
  intro x y h
  ext i
  have hh : (x i : ℝ) = (y i : ℝ) := congrFun h i
  exact_mod_cast hh

def integerRealImage {n : ℕ} (G : AddSubgroup (Fin n → ℤ)) : Submodule ℤ (Fin n → ℝ) :=
  G.toIntSubmodule.map integerReal

instance integerRealImage_discrete {n : ℕ} (G : AddSubgroup (Fin n → ℤ)) :
    DiscreteTopology (integerRealImage G) := by
  let H := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
  have hle : integerRealImage G ≤ H := by
    rintro x ⟨z,hz,rfl⟩
    apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
    intro i
    exact ⟨z i,rfl⟩
  let f : integerRealImage G → H := fun x => ⟨x,hle x.property⟩
  have hc : Continuous f := continuous_subtype_val.subtype_mk _
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : H => (z : Fin n → ℝ)) h
  exact DiscreteTopology.of_continuous_injective hc hf

theorem integerRealImage_span_top {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    (D : ℤ) (hD : D ≠ 0) (hm : ∀ j, Pi.single j D ∈ G) :
    Submodule.span ℝ (integerRealImage G : Set (Fin n → ℝ)) = ⊤ := by
  let W := Submodule.span ℝ (integerRealImage G : Set (Fin n → ℝ))
  have hm' (j : Fin n) : integerReal (Pi.single j D : Fin n → ℤ) ∈ W :=
    Submodule.subset_span ⟨Pi.single j D,hm j,rfl⟩
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hb (j : Fin n) : Pi.basisFun ℝ (Fin n) j ∈ W := by
    have hh := W.smul_mem (D : ℝ)⁻¹ (hm' j)
    convert hh using 1
    ext i
    simp [integerReal,Pi.basisFun_apply,Pi.single_apply,Pi.smul_apply,hD']
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin n)).span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hb j)

noncomputable def integerRealImageBasis {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    (c : Basis (Fin n) ℤ G) : Basis (Fin n) ℤ (integerRealImage G) :=
  c.map (Submodule.equivMapOfInjective integerReal integerReal_injective G.toIntSubmodule)

instance sourceLattice6_isZLattice (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : IsZLattice ℝ (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) where
  span_top := by
    obtain ⟨D,hD,hm⟩ := sourceLattice6_multiple A₂ A₃ e₂ e₃
    exact integerRealImage_span_top _ D hD hm

theorem integerRealImage_covolume_det {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    [IsZLattice ℝ (integerRealImage G)] (c : Basis (Fin n) ℤ G) :
    ZLattice.covolume (integerRealImage G) =
      |(Matrix.of (fun j i => ((c j : Fin n → ℤ) i : ℝ))).det| := by
  rw [ZLattice.covolume_eq_det _ (integerRealImageBasis _ c)]
  rfl

theorem sourceLattice6_covolume_det (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) (c : Basis (Fin 6) ℤ (sourceLattice6 A₂ A₃ e₂ e₃)) :
    ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) =
      |(Matrix.of (fun j i => ((c j : Fin 6 → ℤ) i : ℝ))).det| :=
  integerRealImage_covolume_det _ c


theorem integer_matrix_det_cast {n : ℕ} {K : Type*} [CommRing K]
    (U : Matrix (Fin n) (Fin n) ℤ) :
    (U.det : K) = (U.map (Int.castRingHom K)).det := by
  have hm : (Int.castRingHom K).mapMatrix U = U.map (Int.castRingHom K) := by ext i j; rfl
  exact ((Int.castRingHom K).map_det U).trans (congrArg Matrix.det hm)

theorem padic_det_row_bound {n : ℕ} (p : ℕ) [Fact p.Prime]
    (M : Matrix (Fin n) (Fin n) ℚ) (r : Fin n → ℚ) (hr : ∀ i, 0 ≤ r i)
    (hM : ∀ i j, padicNorm p (M i j) ≤ r i) :
    padicNorm p M.det ≤ ∏ i, r i := by
  classical
  let abv : AbsoluteValue ℚ ℚ := IsAbsoluteValue.toAbsoluteValue (padicNorm p)
  rw [Matrix.det_apply]
  apply padicNorm.sum_le'
  · intro σ _
    change abv (Equiv.Perm.sign σ • ∏ j, M (σ j) j) ≤ _
    rw [abv.map_units_int_smul,abv.map_prod]
    calc
      (∏ j, abv (M (σ j) j)) ≤ ∏ j, r (σ j) :=
        Finset.prod_le_prod (fun j _ => padicNorm.nonneg _) (fun j _ => hM _ _)
      _ = _ := Equiv.prod_comp σ r
  · exact Finset.prod_nonneg (fun i _ => hr i)

theorem padic_det_frame_bound {n : ℕ} (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin n) (Fin n) ℚ) (e : Fin n → ℕ)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : ∀ j i, padicNorm p ((B *ᵥ (fun k => (U j k : ℚ))) i) ≤
      (p : ℚ) ^ (-(e i : ℤ))) :
    padicNorm p B.det * padicNorm p (U.map (Int.castRingHom ℚ)).det ≤
      ((p : ℚ) ^ (∑ i, e i))⁻¹ := by
  let M := B * (U.map (Int.castRingHom ℚ)).transpose
  have hm : ∀ i j, padicNorm p (M i j) ≤ (p : ℚ) ^ (-(e i : ℤ)) := fun i j => hU j i
  have h := padic_det_row_bound p M (fun i => (p : ℚ) ^ (-(e i : ℤ)))
    (by intro i; positivity) hm
  dsimp [M] at h
  rw [Matrix.det_mul,Matrix.det_transpose,padicNorm.mul] at h
  simpa only [zpow_neg,zpow_natCast,Finset.prod_inv_distrib,Finset.prod_pow_eq_pow_sum] using h

theorem integerRealImage_basis_independent {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    [IsZLattice ℝ (integerRealImage G)] (c : Basis (Fin n) ℤ G) :
    LinearIndependent ℝ (fun j i => ((c j : Fin n → ℤ) i : ℝ)) := by
  let b := (integerRealImageBasis G c).ofZLatticeBasis ℝ (integerRealImage G)
  have he : (b : Fin n → (Fin n → ℝ)) = (fun j i => ((c j : Fin n → ℤ) i : ℝ)) := by
    funext j
    exact Basis.ofZLatticeBasis_apply ℝ (integerRealImage G) (integerRealImageBasis G c) j
  rw [← he]
  exact b.linearIndependent

theorem integer_matrix_three_place_lower {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : LinearIndependent ℝ (fun j i => (U j i : ℝ))) :
    1 ≤ |(U.map (Int.castRingHom ℝ)).det| *
      (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ) *
      (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ) := by
  have hdR : (U.map (Int.castRingHom ℝ)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hU))
  have hd : U.det ≠ 0 := by
    intro h
    apply hdR
    rw [← integer_matrix_det_cast, h,Int.cast_zero]
  have h := JSP000334.rothInteger_three_place_lower U.det hd
  change 1 ≤ |((U.det : ℚ) : ℝ)| * (padicNorm 2 (U.det : ℚ) : ℝ) * (padicNorm 3 (U.det : ℚ) : ℝ) at h
  rw [Rat.cast_intCast,integer_matrix_det_cast (K := ℝ) U,integer_matrix_det_cast (K := ℚ) U] at h
  exact h


theorem integerRealImage_padic_covolume_lower {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    [IsZLattice ℝ (integerRealImage G)] (c : Basis (Fin n) ℤ G)
    (B₂ B₃ : Matrix (Fin n) (Fin n) ℚ) (e₂ e₃ : Fin n → ℕ)
    (h₂ : ∀ x ∈ G, ∀ i, padicNorm 2 ((B₂ *ᵥ (fun j => (x j : ℚ))) i) ≤ (2 : ℚ) ^ (-(e₂ i : ℤ)))
    (h₃ : ∀ x ∈ G, ∀ i, padicNorm 3 ((B₃ *ᵥ (fun j => (x j : ℚ))) i) ≤ (3 : ℚ) ^ (-(e₃ i : ℤ))) :
    (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ) *
      (2 : ℝ) ^ (∑ i, e₂ i) * 3 ^ (∑ i, e₃ i) ≤ ZLattice.covolume (integerRealImage G) := by
  let U : Matrix (Fin n) (Fin n) ℤ := fun j i => (c j : Fin n → ℤ) i
  let d := ZLattice.covolume (integerRealImage G)
  let a : ℝ := padicNorm 2 B₂.det
  let b : ℝ := padicNorm 3 B₃.det
  let s : ℝ := padicNorm 2 (U.map (Int.castRingHom ℚ)).det
  let t : ℝ := padicNorm 3 (U.map (Int.castRingHom ℚ)).det
  let P : ℝ := 2 ^ (∑ i, e₂ i)
  let R : ℝ := 3 ^ (∑ i, e₃ i)
  have ha : 0 ≤ a := Rat.cast_nonneg.mpr (padicNorm.nonneg (p := 2) B₂.det)
  have hb : 0 ≤ b := Rat.cast_nonneg.mpr (padicNorm.nonneg (p := 3) B₃.det)
  have hs : 0 ≤ s := Rat.cast_nonneg.mpr (padicNorm.nonneg (p := 2) (U.map (Int.castRingHom ℚ)).det)
  have ht : 0 ≤ t := Rat.cast_nonneg.mpr (padicNorm.nonneg (p := 3) (U.map (Int.castRingHom ℚ)).det)
  have hP : 0 < P := by dsimp [P]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hd : 0 ≤ d := (ZLattice.covolume_pos (integerRealImage G) MeasureTheory.volume).le
  have hc : d = |(U.map (Int.castRingHom ℝ)).det| := integerRealImage_covolume_det G c
  have h1 : 1 ≤ d * s * t := by
    rw [hc]
    exact integer_matrix_three_place_lower U (integerRealImage_basis_independent G c)
  have h2 : a * s ≤ P⁻¹ := by
    have h := padic_det_frame_bound 2 B₂ e₂ U (fun j i => h₂ (c j) (c j).property i)
    change (padicNorm 2 B₂.det : ℝ) * (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ) ≤ ((2 : ℝ) ^ (∑ i, e₂ i))⁻¹
    simpa only [Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_mono (K := ℝ) h)
  have h3 : b * t ≤ R⁻¹ := by
    have h := padic_det_frame_bound 3 B₃ e₃ U (fun j i => h₃ (c j) (c j).property i)
    change (padicNorm 3 B₃.det : ℝ) * (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ) ≤ ((3 : ℝ) ^ (∑ i, e₃ i))⁻¹
    simpa only [Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_mono (K := ℝ) h)
  have hmul := mul_le_mul h2 h3 (mul_nonneg hb ht) (inv_nonneg.mpr hP.le)
  have hlo : a*b ≤ (a*b)*(d*s*t) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 (mul_nonneg ha hb)
  have hhi : (a*b)*(d*s*t) ≤ d*(P⁻¹*R⁻¹) := by
    convert mul_le_mul_of_nonneg_left hmul hd using 1 <;> ring
  have hdiv : a*b ≤ d/(P*R) := by
    calc
      a*b ≤ d*(P⁻¹*R⁻¹) := hlo.trans hhi
      _ = d/(P*R) := by rw [div_eq_mul_inv,mul_inv]
  have hfinal := (le_div_iff₀ (mul_pos hP hR)).mp hdiv
  change a*b*P*R ≤ d
  convert hfinal using 1 <;> ring

theorem sourceLattice6_covolume_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) :
    (padicNorm 2 (compound A₂).det : ℝ) * (padicNorm 3 (compound A₃).det : ℝ) *
      (2 : ℝ) ^ (3 * ∑ i, e₂ i) * 3 ^ (3 * ∑ i, e₃ i) ≤
      ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) := by
  obtain ⟨c⟩ := sourceLattice6_has_basis A₂ A₃ e₂ e₃
  have h := integerRealImage_padic_covolume_lower _ c (compound A₂) (compound A₃)
    (fun s => e₂ (lo s) + e₂ (hi s)) (fun s => e₃ (lo s) + e₃ (hi s))
    (fun x hx => (lattice6_spec 2 A₂ e₂ x).mp hx.1)
    (fun x hx => (lattice6_spec 3 A₃ e₃ x).mp hx.2)
  simpa only [compound_exponent_sum] using h


noncomputable def sourceLocalDetFactor42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) : ℝ :=
  (padicNorm 2 (compound A₂).det : ℝ) * (padicNorm 3 (compound A₃).det : ℝ)

theorem sourceLocalDetFactor42_pos (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) : 0 < sourceLocalDetFactor42 A₂ A₃ := by
  have hd₂ : (compound A₂).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (compound_unit A₂ h₂))
  have hd₃ : (compound A₃).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (compound_unit A₃ h₃))
  apply mul_pos
  · exact Rat.cast_pos.mpr ((IsAbsoluteValue.toAbsoluteValue (padicNorm 2)).pos_iff.mpr hd₂)
  · exact Rat.cast_pos.mpr ((IsAbsoluteValue.toAbsoluteValue (padicNorm 3)).pos_iff.mpr hd₃)

theorem q_width_product_le_prime_powers4 (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (∏ i, Q ^ c₀ i) ≤
      (2 : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
      3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) := by
  have hQpos : 0 < Q := lt_trans zero_lt_one hQ
  have hi (p : ℕ) (hp : 1 < p) (c : ℝ) :
      Q ^ (-c) ≤ (p : ℝ) ^ Nat.ceil (JSP000334.qThreshold p Q c) := by
    rw [← JSP000334.qThreshold_rpow p hp Q c hQ, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
  have heq : (∏ i, Q ^ (-c₂ i) * Q ^ (-c₃ i)) = ∏ i, Q ^ c₀ i := by
    simp_rw [← Real.rpow_add hQpos]
    rw [← Real.rpow_sum_of_pos hQpos _ Finset.univ, ← Real.rpow_sum_of_pos hQpos _ Finset.univ]
    congr 1
    simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib]
    simp only [Finset.sum_add_distrib] at hb
    linarith
  rw [← heq, ← Finset.prod_pow_eq_pow_sum Finset.univ _ (2 : ℝ),
    ← Finset.prod_pow_eq_pow_sum Finset.univ _ (3 : ℝ), ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => mul_nonneg (Real.rpow_pos_of_pos hQpos _).le (Real.rpow_pos_of_pos hQpos _).le)
    (fun i _ => mul_le_mul (hi 2 (by decide) _) (hi 3 (by decide) _)
      (Real.rpow_pos_of_pos hQpos _).le (by positivity))

theorem sourceLattice6_covolume_width_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hW : (∏ i, A i) ≤ (2 : ℝ) ^ (∑ i, e₂ i) * 3 ^ (∑ i, e₃ i)) :
    sourceLocalDetFactor42 A₂ A₃ * (∏ s : Fin 6, A (lo s) * A (hi s)) ≤
      ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) := by
  have hp := pow_le_pow_left₀ (Finset.prod_pos (fun i _ => hA i)).le hW 3
  have he : ((2 : ℝ) ^ (∑ i, e₂ i) * 3 ^ (∑ i, e₃ i)) ^ 3 =
      (2 : ℝ) ^ (3 * ∑ i, e₂ i) * 3 ^ (3 * ∑ i, e₃ i) := by
    rw [mul_pow,← pow_mul,← pow_mul]
    simp only [Nat.mul_comm]
  rw [he] at hp
  have hα : 0 ≤ sourceLocalDetFactor42 A₂ A₃ :=
    mul_nonneg (Rat.cast_nonneg.mpr (padicNorm.nonneg _)) (Rat.cast_nonneg.mpr (padicNorm.nonneg _))
  rw [compound_width_product]
  have h := mul_le_mul_of_nonneg_left hp hα
  exact h.trans (by simpa only [sourceLocalDetFactor42,mul_assoc] using sourceLattice6_covolume_lower A₂ A₃ e₂ e₃)

theorem sourceLattice6_Q_normalized_covolume_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    sourceLocalDetFactor42 A₂ A₃ ≤
      ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))) /
      (∏ s : Fin 6, Q ^ c₀ (lo s) * Q ^ c₀ (hi s)) := by
  have hA (i : Fin 4) : 0 < Q ^ c₀ i := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  have hW : 0 < ∏ s : Fin 6, Q ^ c₀ (lo s) * Q ^ c₀ (hi s) :=
    Finset.prod_pos (fun s _ => mul_pos (hA _) (hA _))
  apply (le_div_iff₀ hW).mpr
  exact sourceLattice6_covolume_width_lower A₂ A₃ _ _ (fun i => Q ^ c₀ i) hA
    (q_width_product_le_prime_powers4 Q hQ c₀ c₂ c₃ hb)


theorem real_basis_integer_frame_det_lower {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (v : Fin n → (Fin n → ℝ))
    (hv : ∀ j, v j ∈ Submodule.span ℤ (Set.range b)) (hli : LinearIndependent ℝ v) :
    |(Matrix.of b).det| ≤ |(Matrix.of v).det| := by
  classical
  let C : Matrix (Fin n) (Fin n) ℤ := fun j i => (b.restrictScalars ℤ).repr ⟨v j,hv j⟩ i
  let R := C.map (Int.castRingHom ℝ)
  have hR : R = (b.toMatrix v).transpose := by
    ext j i
    exact b.restrictScalars_repr_apply ℤ ⟨v j,hv j⟩ i
  have hmul : R * Matrix.of b = Matrix.of v := by
    ext j i
    rw [hR]
    change (∑ k, b.repr (v j) k * b k i) = v j i
    have h := congrFun (b.sum_repr (v j)) i
    simpa [Finset.sum_apply,smul_eq_mul,mul_comm] using h
  have hdetv : (Matrix.of v).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli))
  have hdetR : R.det ≠ 0 := by
    intro h0
    apply hdetv
    rw [← hmul,Matrix.det_mul,h0,zero_mul]
  have hOne : 1 ≤ |R.det| :=
    integer_frame_det_lower_generic C (Matrix.linearIndependent_rows_of_det_ne_zero hdetR)
  calc
    |(Matrix.of b).det| ≤ |R.det| * |(Matrix.of b).det| := le_mul_of_one_le_left (abs_nonneg _) hOne
    _ = |(Matrix.of v).det| := by rw [← abs_mul,← Matrix.det_mul,hmul]

theorem integerRealImage_frame_det_lower {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    [IsZLattice ℝ (integerRealImage G)] (c : Basis (Fin n) ℤ G)
    (u : Fin n → G) (hu : LinearIndependent ℝ (fun j i => ((u j : Fin n → ℤ) i : ℝ))) :
    ZLattice.covolume (integerRealImage G) ≤
      |(Matrix.of (fun j i => ((u j : Fin n → ℤ) i : ℝ))).det| := by
  let b := (integerRealImageBasis G c).ofZLatticeBasis ℝ (integerRealImage G)
  have he : Matrix.of b = Matrix.of (fun j i => ((c j : Fin n → ℤ) i : ℝ)) := by
    have hfun : (b : Fin n → (Fin n → ℝ)) = (fun j i => ((c j : Fin n → ℤ) i : ℝ)) := by
      funext j
      exact Basis.ofZLatticeBasis_apply ℝ (integerRealImage G) (integerRealImageBasis G c) j
    exact congrArg Matrix.of hfun
  rw [integerRealImage_covolume_det G c,← he]
  apply real_basis_integer_frame_det_lower b _ _ hu
  intro j
  rw [Basis.ofZLatticeBasis_span]
  exact ⟨(u j : Fin n → ℤ),(u j).property,rfl⟩

theorem integerRealImage_frame_product_lower {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    [IsZLattice ℝ (integerRealImage G)] (c : Basis (Fin n) ℤ G)
    (B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → G)
    (hu : LinearIndependent ℝ (fun j i => ((u j : Fin n → ℤ) i : ℝ)))
    (w r : Fin n → ℝ)
    (hpoint : ∀ j i, |(B *ᵥ (fun k => ((u j : Fin n → ℤ) k : ℝ))) i| ≤ r j * w i) :
    |B.det| * ZLattice.covolume (integerRealImage G) ≤
      (n.factorial : ℝ) * (∏ j, r j) * ∏ i, w i := by
  let U : Matrix (Fin n) (Fin n) ℝ := fun j i => ((u j : Fin n → ℤ) i : ℝ)
  have hm : ∀ i j, |(B * U.transpose) i j| ≤ r j * w i := fun i j => hpoint j i
  have hbound := abs_det_le_weighted_bounds (B * U.transpose) w r hm
  calc
    |B.det| * ZLattice.covolume (integerRealImage G) ≤ |B.det| * |U.det| :=
      mul_le_mul_of_nonneg_left (integerRealImage_frame_det_lower G c u hu) (abs_nonneg _)
    _ = |(B * U.transpose).det| := by rw [Matrix.det_mul,Matrix.det_transpose,abs_mul]
    _ ≤ _ := hbound

theorem sourceLattice6_frame_product_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) (B : Matrix (Fin 6) (Fin 6) ℝ)
    (u : Fin 6 → sourceLattice6 A₂ A₃ e₂ e₃)
    (hu : LinearIndependent ℝ (fun j i => ((u j : Fin 6 → ℤ) i : ℝ)))
    (w r : Fin 6 → ℝ)
    (hpoint : ∀ j i, |(B *ᵥ (fun k => ((u j : Fin 6 → ℤ) k : ℝ))) i| ≤ r j * w i) :
    |B.det| * ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) ≤
      720 * (∏ j, r j) * ∏ i, w i := by
  obtain ⟨c⟩ := sourceLattice6_has_basis A₂ A₃ e₂ e₃
  have h := integerRealImage_frame_product_lower _ c B u hu w r hpoint
  have hfac : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  simpa only [hfac] using h

theorem sourceLattice6_Q_frame_product_lower (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (u : Fin 6 → sourceLattice6 A₂ A₃
      (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))
    (hu : LinearIndependent ℝ (fun j i => ((u j : Fin 6 → ℤ) i : ℝ)))
    (r : Fin 6 → ℝ)
    (hpoint : ∀ j s, |(compound L *ᵥ (fun k => ((u j : Fin 6 → ℤ) k : ℝ))) s| ≤
      r j * (Q ^ c₀ (lo s) * Q ^ c₀ (hi s))) :
    |(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720 ≤ ∏ j, r j := by
  let W := ∏ s : Fin 6, Q ^ c₀ (lo s) * Q ^ c₀ (hi s)
  have hW : 0 < W := Finset.prod_pos (fun s _ => mul_pos
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _))
  have hc := sourceLattice6_Q_normalized_covolume_lower A₂ A₃ Q hQ c₀ c₂ c₃ hb
  have hc' := (le_div_iff₀ hW).mp hc
  have hp := sourceLattice6_frame_product_lower A₂ A₃ _ _ (compound L) u hu
    (fun s => Q ^ c₀ (lo s) * Q ^ c₀ (hi s)) r hpoint
  have hlo := mul_le_mul_of_nonneg_left hc' (abs_nonneg (compound L).det)
  have hfinal : (|(compound L).det| * sourceLocalDetFactor42 A₂ A₃) * W ≤ (720 * ∏ j, r j) * W := by
    simpa only [mul_assoc] using hlo.trans hp
  have h := (mul_le_mul_right hW).mp hfinal
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 720)).mpr
  simpa only [mul_comm] using h


theorem source_compound_lower_constant_pos42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    0 < |(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720 := by
  have hd : (compound L).det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (compound_unit L hL))
  exact div_pos (mul_pos (abs_pos.mpr hd) (sourceLocalDetFactor42_pos A₂ A₃ h₂ h₃)) (by norm_num)

theorem source_compound_uniform_frame_lower42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c : ℝ, 0 < c ∧ c = |(compound L).det| * sourceLocalDetFactor42 A₂ A₃ / 720 ∧
      ∀ (Q : ℝ) (_hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        ∀ (u : Fin 6 → sourceLattice6 A₂ A₃
          (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
          (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))),
          LinearIndependent ℝ (fun j i => ((u j : Fin 6 → ℤ) i : ℝ)) →
          ∀ r : Fin 6 → ℝ,
            (∀ j s, |(compound L *ᵥ (fun k => ((u j : Fin 6 → ℤ) k : ℝ))) s| ≤
              r j * (Q ^ c₀ (lo s) * Q ^ c₀ (hi s))) → c ≤ ∏ j, r j := by
  refine ⟨_,source_compound_lower_constant_pos42 A₂ A₃ L h₂ h₃ hL,rfl,?_⟩
  intro Q hQ c₀ c₂ c₃ hb u hu r hpoint
  exact sourceLattice6_Q_frame_product_lower A₂ A₃ L Q hQ c₀ c₂ c₃ hb u hu r hpoint


theorem integerRealImage_covolume_index {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    [IsZLattice ℝ (integerRealImage G)] (c : Basis (Fin n) ℤ G) :
    ZLattice.covolume (integerRealImage G) = (G.index : ℝ) := by
  let U : Matrix (Fin n) (Fin n) ℤ := fun j i => (c j : Fin n → ℤ) i
  have hstd : (Pi.basisFun ℤ (Fin n)).det (fun j => (c j : Fin n → ℤ)) = U.det := by
    rw [Basis.det_apply]
    have hm : (Pi.basisFun ℤ (Fin n)).toMatrix (fun j => (c j : Fin n → ℤ)) = U.transpose := by ext i j; rfl
    rw [hm,Matrix.det_transpose]
  have hi := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin n)) G c
  rw [hstd] at hi
  have hreal : (G.index : ℝ) = |(U.det : ℝ)| := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hi
    simpa only [Int.cast_natAbs,Int.cast_abs] using h
  rw [integerRealImage_covolume_det G c]
  change |(U.map (Int.castRingHom ℝ)).det| = (G.index : ℝ)
  rw [← integer_matrix_det_cast (K := ℝ) U]
  exact hreal.symm

theorem sourceLattice6_covolume_index (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) :
    ZLattice.covolume (integerRealImage (sourceLattice6 A₂ A₃ e₂ e₃)) =
      ((sourceLattice6 A₂ A₃ e₂ e₃).index : ℝ) := by
  obtain ⟨c⟩ := sourceLattice6_has_basis A₂ A₃ e₂ e₃
  exact integerRealImage_covolume_index _ c

end CompoundFeasibility
