import SubspaceBridge.AuxiliaryPolynomial4
import SubspaceBridge.SourceForms4
open scoped BigOperators Matrix Classical NumberField
noncomputable section
namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

noncomputable def integralMatrix4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4) :
    Matrix (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
      (RothAuxCoefficients r) ℤ :=
  fun q b => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix4 r eta a p q.1 b) q.2

theorem integralMatrix4_kernel {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → ℤ) :
    (integralMatrix4 r eta a p).mulVec c = 0 ↔
      (matrix4 r eta a p).mulVec (fun b => (c b : 𝓞 𝕂)) = 0 := by
  let b := Module.finBasis ℤ (𝓞 𝕂)
  have he (q : Equations4 r eta) (k : Fin (Module.finrank ℤ (𝓞 𝕂))) :
      (integralMatrix4 r eta a p).mulVec c (q,k) =
        b.repr ((matrix4 r eta a p).mulVec (fun j => (c j : 𝓞 𝕂)) q) k := by
    simp only [Matrix.mulVec, dotProduct, integralMatrix4, map_sum, Finsupp.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg (fun x => x k) (b.repr.map_smul (c j) (matrix4 r eta a p q j))
    simpa only [Finsupp.smul_apply, smul_eq_mul, Algebra.smul_def, map_intCast, mul_comm, eq_intCast, b] using h.symm
  constructor
  · intro hz
    funext q
    apply b.repr.injective
    ext k
    rw [Pi.zero_apply, map_zero]
    simpa only [← he, Pi.zero_apply] using congrFun hz (q,k)
  · intro hz
    funext q
    rw [he, hz, Pi.zero_apply, map_zero]
    rfl

noncomputable def integralHeightBase4 (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) : ℝ :=
  letI := Aux6Norm.integralNormModel 𝕂
  max 1 (∑ tau : Fin 3, ∑ s : Fin 4, ∑ j : Fin 4, ‖a tau s j‖)

noncomputable def integralCoordinateConstant4 (𝕂 : Type*) [Field 𝕂] [NumberField 𝕂] : ℝ :=
  max 1 ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖

theorem integralMatrix4_entry_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4)
    (q : Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
    (b : RothAuxCoefficients r) :
    ‖integralMatrix4 r eta a p q b‖ ≤ integralCoordinateConstant4 𝕂 *
      (8 * integralHeightBase4 a)^(∑ h, r h) := by
  letI := Aux6Norm.integralNormModel 𝕂
  letI : NormOneClass (𝓞 𝕂) := ⟨Aux6Norm.integralNormModel_one⟩
  have ha : ∀ tau s j, ‖a tau s j‖ ≤ integralHeightBase4 a := by
    intro tau s j
    apply le_trans _ (le_max_right _ _)
    apply le_trans (Finset.single_le_sum (fun j _ => norm_nonneg (a tau s j)) (Finset.mem_univ j))
    apply le_trans (Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j))) (Finset.mem_univ s))
    exact Finset.single_le_sum (fun tau _ => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j)))) (Finset.mem_univ tau)
  have hx : ‖matrix4 r eta a p q.1 b‖ ≤ (8 * integralHeightBase4 a)^(∑ h, r h) := by
    apply Aux4Height.transformed_entry_norm4
    · exact le_max_left _ _
    · exact ha _ _
  have hc := Aux6Norm.integralNormModel_coordinates (matrix4 r eta a p q.1 b)
  have hcoord := norm_le_pi_norm (fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr
    (matrix4 r eta a p q.1 b) i) q.2
  calc
    _ ≤ ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix4 r eta a p q.1 b) i)‖ := hcoord
    _ ≤ ‖matrix4 r eta a p q.1 b‖ *
        ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖ := hc
    _ ≤ (8 * integralHeightBase4 a)^(∑ h, r h) * integralCoordinateConstant4 𝕂 :=
      mul_le_mul hx (le_max_right _ _) (norm_nonneg _) (pow_nonneg (by have hh : 1 ≤ integralHeightBase4 a := le_max_left _ _; linarith) _)
    _ = _ := mul_comm _ _

end CompoundFeasibility.Auxiliary4
namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]
attribute [local instance] Matrix.seminormedAddCommGroup

theorem dimension4_le_pow {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) :
    rothAuxDimension r ≤ 16^(∑ h, r h) := by
  rw [rothAuxDimension_eq]
  calc
    _ ≤ ∏ h, 16^r h := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro h _
      calc
        (r h + 3).choose 3 ≤ 2^(r h + 3) :=
          (Nat.choose_le_two_pow _ _ (by omega)).le
        _ ≤ 2^(4 * r h) := Nat.pow_le_pow_right (by decide) (by have hh := hr h; omega)
        _ = 16^r h := by rw [pow_mul]; norm_num
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

noncomputable def integralSiegelConstant4 (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) : ℝ :=
  16 * (8 * integralHeightBase4 a * integralCoordinateConstant4 𝕂)

theorem integralSiegelConstant4_ge_one (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) :
    1 ≤ integralSiegelConstant4 a := by
  have hA : 1 ≤ integralHeightBase4 a := le_max_left _ _
  have hC : 1 ≤ integralCoordinateConstant4 𝕂 := le_max_left _ _
  dsimp [integralSiegelConstant4]
  nlinarith

theorem integralMatrix4_uniform_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (hm : 0 < m) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4) :
    (Fintype.card (RothAuxCoefficients r) : ℝ) * max 1 ‖integralMatrix4 r eta a p‖ ≤
      integralSiegelConstant4 a ^ (∑ h, r h) := by
  let A := integralHeightBase4 a
  let C := integralCoordinateConstant4 𝕂
  have hA : 1 ≤ A := le_max_left _ _
  have hC : 1 ≤ C := le_max_left _ _
  have hR : 1 ≤ ∑ h, r h := by
    have hp := hr ⟨0, hm⟩
    have hh : r ⟨0, hm⟩ ≤ ∑ h, r h :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  have hbase : 1 ≤ 8 * A * C := by nlinarith
  have hnorm : ‖integralMatrix4 r eta a p‖ ≤ (8 * A * C)^(∑ h, r h) := by
    apply (Matrix.norm_le_iff (by positivity)).mpr
    intro q b
    calc
      _ ≤ C * (8 * A)^(∑ h, r h) := integralMatrix4_entry_bound r eta a p q b
      _ ≤ C^(∑ h, r h) * (8 * A)^(∑ h, r h) :=
        mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ hC hR) (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  calc
    _ ≤ (16 : ℝ)^(∑ h, r h) * (8 * A * C)^(∑ h, r h) :=
      mul_le_mul (by exact_mod_cast dimension4_le_pow r hr)
        (max_le (one_le_pow₀ hbase) hnorm) (by positivity) (by positivity)
    _ = _ := by rw [← mul_pow]; rfl

theorem integralMatrix4_bounded_kernel {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ))
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂) (p : Fin 3 → Fin 4 → Fin 4) :
    ∃ c : RothAuxCoefficients r → ℤ, c ≠ 0 ∧
      (integralMatrix4 r eta a p).mulVec c = 0 ∧
      ‖c‖ ≤ integralSiegelConstant4 a ^ (∑ h, r h) := by
  have hd : 0 < Module.finrank ℚ 𝕂 := Module.finrank_pos
  have hN := dimension4_pos r
  have hhalf := coordinate_rows4_le_half r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hlt := coordinate_rows4_lt r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hmpos : 0 < m := by
    have hd' : (1 : ℝ) ≤ Module.finrank ℚ 𝕂 := by exact_mod_cast hd
    have hlog : 0 < Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) := Real.log_pos (by linarith)
    have hh : 0 < (m : ℝ) := lt_of_lt_of_le (mul_pos (by positivity) hlog) hm
    exact_mod_cast hh
  have hD := integralSiegelConstant4_ge_one a
  by_cases hrows : Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) = 0
  · obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hN
    let c : RothAuxCoefficients r → ℤ := fun b => if b = b₀ then 1 else 0
    refine ⟨c, ?_, ?_, ?_⟩
    · intro hc
      have hh := congrFun hc b₀
      simp [c] at hh
    · funext q
      have hh := Fintype.card_pos_iff.mpr (Nonempty.intro q)
      omega
    · have hc : ‖c‖ ≤ (1 : ℝ) := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro b
        dsimp [c]
        split_ifs <;> norm_num
      exact hc.trans (one_le_pow₀ hD)
  · have hcount : Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) <
        Fintype.card (RothAuxCoefficients r) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm] using hlt
    obtain ⟨c, hc, hker, hbound⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le
      (integralMatrix4 r eta a p) hcount (Nat.pos_of_ne_zero hrows)
    refine ⟨c, hc, hker, ?_⟩
    have hrowsR : (Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) ≤
        (Fintype.card (RothAuxCoefficients r) : ℝ) / 2 := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm, Nat.cast_mul, rothAuxDimension] using hhalf
    have hden : 0 < (Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) := by
      exact sub_pos.mpr (by exact_mod_cast hcount)
    have hexp : (Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) /
        ((Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations4 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))) ≤ 1 := by
      apply (div_le_one hden).mpr
      linarith
    have hbase : 1 ≤ (Fintype.card (RothAuxCoefficients r) : ℝ) *
        max 1 ‖integralMatrix4 r eta a p‖ := by
      have hn : (1 : ℝ) ≤ Fintype.card (RothAuxCoefficients r) := by exact_mod_cast hN
      nlinarith [le_max_left (1 : ℝ) ‖integralMatrix4 r eta a p‖]
    exact hbound.trans ((Real.rpow_le_self_of_one_le hbase hexp).trans
      (integralMatrix4_uniform_bound r hr hmpos eta a p))

end CompoundFeasibility.Auxiliary4
namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4

noncomputable def height4 {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ) : ℕ :=
  P.support.sup (fun d => (P.coeff d).natAbs)

theorem polynomial4_ne_zero {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ)
    (hc : c ≠ 0) : polynomial4 c ≠ 0 := by
  intro hz
  apply hc
  funext b
  have hh := polynomial4_coeff c b
  rw [hz, MvPolynomial.coeff_zero] at hh
  exact hh.symm

theorem polynomial4_height_le {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ) :
    (height4 (polynomial4 c) : ℝ) ≤ ‖c‖ := by
  have hs : ∀ d ∈ (polynomial4 c).support,
      ((polynomial4 c).coeff d).natAbs ≤ Nat.floor ‖c‖ := by
    intro d hd
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    subst d
    rw [polynomial4_coeff]
    apply Nat.le_floor
    simpa only [Int.norm_eq_abs, Int.cast_natAbs, Int.cast_abs] using norm_le_pi_norm c b
  have hh : height4 (polynomial4 c) ≤ Nat.floor ‖c‖ := Finset.sup_le hs
  exact (by exact_mod_cast hh : (height4 (polynomial4 c) : ℝ) ≤ Nat.floor ‖c‖).trans
    (Nat.floor_le (norm_nonneg _))

variable {𝕂 : Type*} [Field 𝕂]

theorem kernelChart4_scale {m : ℕ} (a : Fin 4 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 4) (u : Vars4 m) :
    kernelChart4 (fun j => M * a j) k u = kernelChart4 a k u := by
  unfold kernelChart4
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_div_mul_left _ _ hM]
  · rfl

theorem kernelRestriction4_scale {m : ℕ} (a : Fin 4 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 4) (P : MvPolynomial (Vars4 m) 𝕂) :
    kernelRestriction4 (fun j => M * a j) k P = kernelRestriction4 a k P := by
  have he : kernelChart4 (m := m) (fun j => M * a j) k = kernelChart4 a k :=
    funext (kernelChart4_scale a M hM k)
  simp only [kernelRestriction4, he]

theorem kernelRestriction4_map {𝕃 : Type*} [Field 𝕃] {m : ℕ}
    (f : 𝕂 →+* 𝕃) (a : Fin 4 → 𝕂) (k : Fin m → Fin 4)
    (P : MvPolynomial (Vars4 m) 𝕂) :
    (kernelRestriction4 a k P).map f =
      kernelRestriction4 (fun j => f (a j)) k (P.map f) := by
  have hchart (u : Vars4 m) :
      (kernelChart4 a k u).map f = kernelChart4 (fun j => f (a j)) k u := by
    unfold kernelChart4
    split_ifs <;> simp [map_sum, map_mul, map_div₀]
  induction P using MvPolynomial.induction_on with
  | C c => simp [kernelRestriction4]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show kernelRestriction4 a k (MvPolynomial.X v) = kernelChart4 a k v by simp [kernelRestriction4]]
    rw [hchart]
    simp [kernelRestriction4]

variable [NumberField 𝕂]

theorem integral_auxiliary4
    (a : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, (a tau s (k h) : 𝕂) ≠ 0) →
          kernelRestriction4 (fun j => (a tau s j : 𝕂)) k
            (derivative4 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  let p : Fin 3 → Fin 4 → Fin 4 := fun tau s => Classical.choose (ha tau s)
  have hp : ∀ tau s, a tau s (p tau s) ≠ 0 := fun tau s => Classical.choose_spec (ha tau s)
  refine ⟨integralSiegelConstant4 a, integralSiegelConstant4_ge_one a, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨c, hc, hker, hbound⟩ := integralMatrix4_bounded_kernel r hr eta heta hm a p
  refine ⟨polynomial4 c, polynomial4_ne_zero c hc, polynomial4_homogeneous c,
    (polynomial4_height_le c).trans hbound, ?_⟩
  let f : 𝓞 𝕂 →+* 𝕂 := algebraMap _ _
  have hkerO := (integralMatrix4_kernel r eta a p c).mp hker
  have hkerK : (matrix4 r eta (fun tau s j => f (a tau s j)) p).mulVec
      (fun b => (c b : 𝕂)) = 0 := by
    funext q
    have hh := congrArg f (congrFun hkerO q)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast,
      matrix4_map, Pi.zero_apply, map_zero] using hh
  intro tau s J hJ k hk
  have hpK : ∀ tau s, f (a tau s (p tau s)) ≠ 0 := fun tau s =>
    (map_ne_zero_iff f (IsFractionRing.injective (𝓞 𝕂) 𝕂)).mpr (hp tau s)
  have hh := matrix4_kernel_all_derivatives r eta (fun tau s j => f (a tau s j)) p
    hpK (fun b => (c b : 𝕂)) hkerK tau s J hJ k hk
  simpa only [polynomial4_map, map_intCast] using hh

end CompoundFeasibility.Auxiliary4
namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

theorem source_integral_scaling4 (a : Fin 3 → Fin 4 → Fin 4 → 𝕂) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ b : Fin 3 → Fin 4 → Fin 4 → 𝓞 𝕂,
      ∀ tau s j, (b tau s j : 𝕂) = (M : 𝕂) * a tau s j := by
  haveI : Algebra.IsAlgebraic ℚ 𝕂 := Algebra.IsAlgebraic.of_finite ℚ 𝕂
  haveI : Algebra.IsAlgebraic ℤ 𝕂 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := 𝕂)).mpr inferInstance
  obtain ⟨M, hM, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun q : Fin 3 × Fin 4 × Fin 4 => a q.1 q.2.1 q.2.2))
  have hint : ∀ tau s j, IsIntegral ℤ ((M : 𝕂) * a tau s j) := by
    intro tau s j
    simpa only [Algebra.smul_def, eq_intCast] using
      hi (a tau s j) (Finset.mem_image.mpr ⟨(tau,s,j),Finset.mem_univ _,rfl⟩)
  exact ⟨M, hM, (fun tau s j => ⟨(M : 𝕂) * a tau s j, hint tau s j⟩), fun _ _ _ => rfl⟩

theorem algebraic_auxiliary4 (a : Fin 3 → Fin 4 → Fin 4 → 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, a tau s (k h) ≠ 0) →
          kernelRestriction4 (a tau s) k
            (derivative4 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  obtain ⟨M, hM, b, hb⟩ := source_integral_scaling4 a
  have hMK : (M : 𝕂) ≠ 0 := by exact_mod_cast hM
  have hbn : ∀ tau s, ∃ j, b tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := ha tau s
    refine ⟨j, ?_⟩
    intro hz
    exact (mul_ne_zero hMK hj) (by rw [← hb tau s j, hz]; rfl)
  obtain ⟨D, hD, hconstruction⟩ := integral_auxiliary4 b hbn
  refine ⟨D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hderiv⟩ := hconstruction eta heta m hm r hr
  refine ⟨P, hP, hhom, hheight, ?_⟩
  intro tau s J hJ k hk
  have hbk : ∀ h, (b tau s (k h) : 𝕂) ≠ 0 := by
    intro h
    rw [hb]
    exact mul_ne_zero hMK (hk h)
  have hh := hderiv tau s J hJ k hbk
  simp only [hb] at hh
  rw [kernelRestriction4_scale (a tau s) (M : 𝕂) hMK] at hh
  exact hh

end CompoundFeasibility.Auxiliary4


namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4

theorem source_restriction4_real (K : IntermediateField ℚ ℝ) {m : ℕ}
    (a : Fin 4 → K) (k : Fin m → Fin 4) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ) :
    (kernelRestriction4 a k (derivative4 J (P.map (Int.castRingHom K)))).map
      K.val.toRingHom =
      kernelRestriction4 (fun j => (a j : ℝ)) k
        (derivative4 J (P.map (Int.castRingHom ℝ))) := by
  rw [kernelRestriction4_map, derivative4_map, MvPolynomial.map_map]
  have hf : K.val.toRingHom.comp (Int.castRingHom K) = Int.castRingHom ℝ :=
    Subsingleton.elim _ _
  rw [hf]
  rfl

theorem source_auxiliary4_field (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau s j, SourceForms4.forms4 A2 A3 L tau s j ∈ K,
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        (∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4,
            (∀ h, (⟨SourceForms4.forms4 A2 A3 L tau s (k h), hmem tau s (k h)⟩ : K) ≠ 0) →
            kernelRestriction4 (fun j => (⟨SourceForms4.forms4 A2 A3 L tau s j, hmem tau s j⟩ : K)) k
              (derivative4 J (P.map (Int.castRingHom K))) = 0) ∧
        (∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, SourceForms4.forms4 A2 A3 L tau s (k h) ≠ 0) →
            kernelRestriction4 (SourceForms4.forms4 A2 A3 L tau s) k
              (derivative4 J (P.map (Int.castRingHom ℝ))) = 0) := by
  obtain ⟨K, hK, hmem⟩ := SourceForms4.common_source_field4 A2 A3 L ha
  letI : FiniteDimensional ℚ K := hK
  letI : NumberField K := {}
  let a : Fin 3 → Fin 4 → Fin 4 → K := fun tau s j =>
    ⟨SourceForms4.forms4 A2 A3 L tau s j, hmem tau s j⟩
  have hnonzero : ∀ tau s, ∃ j, a tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := SourceForms4.source_rows_nonzero4 A2 A3 L h2 h3 hL tau s
    refine ⟨j, ?_⟩
    intro hh
    exact hj (congrArg Subtype.val hh)
  obtain ⟨D, hD, hconstruction⟩ := algebraic_auxiliary4 a hnonzero
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hderiv⟩ := hconstruction eta heta m hm r hr
  refine ⟨P, hP, hhom, hheight, hderiv, ?_⟩
  intro tau s J hJ k hk
  have hkK : ∀ h, a tau s (k h) ≠ 0 := by
    intro h hh
    exact hk h (congrArg Subtype.val hh)
  have he := source_restriction4_real K (a tau s) k J P
  rw [hderiv tau s J hJ k hkK, map_zero] at he
  exact he.symm

theorem source_auxiliary4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau s j, SourceForms4.forms4 A2 A3 L tau s j ∈ K) ∧
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (24 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ,
        P ≠ 0 ∧ homogeneous4 r P ∧ (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars4 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 4 - eta) * m →
          ∀ k : Fin m → Fin 4, (∀ h, SourceForms4.forms4 A2 A3 L tau s (k h) ≠ 0) →
          kernelRestriction4 (SourceForms4.forms4 A2 A3 L tau s) k
            (derivative4 J (P.map (Int.castRingHom ℝ))) = 0 := by
  obtain ⟨K, hK, hmem, D, hD, hconstruction⟩ := source_auxiliary4_field A2 A3 L h2 h3 hL ha
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hfield, hreal⟩ := hconstruction eta heta m hm r hr
  exact ⟨P, hP, hhom, hheight, hreal⟩

end CompoundFeasibility.Auxiliary4

namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4

def matrixIndex4 {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (B : Matrix (Fin 4) (Fin 4) K) (r : Fin m → ℕ) (eta : ℝ)
    (P : MvPolynomial (Vars4 m) ℤ) : Prop :=
  ∀ i (J : Vars4 m →₀ ℕ), rothSourceDerivativeWeight r J < (1/4-eta)*m →
    ∀ k : Fin m → Fin 4, (∀ h, B i (k h) ≠ 0) →
      kernelRestriction4 (B i) k (derivative4 J (P.map (Int.castRingHom K))) = 0

theorem restriction4_map_int {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
    (f : K →+* E) {m : ℕ} (a : Fin 4 → K) (k : Fin m → Fin 4)
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) ℤ) :
    (kernelRestriction4 a k (derivative4 J (P.map (Int.castRingHom K)))).map f =
      kernelRestriction4 (fun j => f (a j)) k (derivative4 J (P.map (Int.castRingHom E))) := by
  rw [kernelRestriction4_map,derivative4_map,MvPolynomial.map_map]
  have hf : f.comp (Int.castRingHom K) = Int.castRingHom E := Subsingleton.elim _ _
  rw [hf]

theorem padic_restriction4_zero (p : ℕ) [Fact p.Prime] {m : ℕ}
    (a : Fin 4 → ℚ) (k : Fin m → Fin 4) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) ℤ)
    (hz : kernelRestriction4 (fun j => (a j : ℝ)) k
      (derivative4 J (P.map (Int.castRingHom ℝ))) = 0) :
    kernelRestriction4 (fun j => (algebraMap ℚ ℚ_[p]) (a j)) k
      (derivative4 J (P.map (Int.castRingHom ℚ_[p]))) = 0 := by
  have hq : kernelRestriction4 a k (derivative4 J (P.map (Int.castRingHom ℚ))) = 0 := by
    apply MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [map_zero,restriction4_map_int]
    exact hz
  have he := congrArg (MvPolynomial.map (algebraMap ℚ ℚ_[p])) hq
  rw [restriction4_map_int,map_zero] at he
  exact he

theorem finite_matrix_index4 (p : ℕ) [Fact p.Prime] {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) ℚ) (r : Fin m → ℕ) (eta : ℝ)
    (P : MvPolynomial (Vars4 m) ℤ)
    (hreal : matrixIndex4 (A.map (algebraMap ℚ ℝ)) r eta P) :
    matrixIndex4 (SourceForms4.finiteMatrix4 p A) r eta P := by
  intro i J hJ k hk
  apply padic_restriction4_zero p (A i) k J P
  apply hreal i J hJ k
  intro h hz
  have hq : A i (k h) = 0 := by
    change (A i (k h) : ℝ) = 0 at hz
    exact_mod_cast hz
  apply hk h
  simp [SourceForms4.finiteMatrix4,hq]

theorem source_auxiliary4_all_places (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms4.forms4 A2 A3 L tau i j ∈ K,
      ∃ D : ℝ, 1 ≤ D ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
      (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex4 (fun i j => (⟨SourceForms4.forms4 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex4 (SourceForms4.forms4 A2 A3 L tau) r eta P) ∧
      matrixIndex4 (SourceForms4.finiteMatrix4 2 A2) r eta P ∧
      matrixIndex4 (SourceForms4.finiteMatrix4 3 A3) r eta P := by
  obtain ⟨K,hK,hmem,D,hD,hconstruction⟩ := source_auxiliary4_field A2 A3 L h2 h3 hL ha
  refine ⟨K,hK,hmem,D,hD,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hP,hhom,hheight,hfield,hreal⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hP,hhom,hheight,hfield,hreal,?_,?_⟩
  · apply finite_matrix_index4 2 A2 r eta P
    exact hreal 1
  · apply finite_matrix_index4 3 A3 r eta P
    exact hreal 2

end CompoundFeasibility.Auxiliary4
