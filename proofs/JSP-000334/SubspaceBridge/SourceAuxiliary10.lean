import SubspaceBridge.AuxiliaryPolynomial10
import SubspaceBridge.SourceForms10
open scoped BigOperators Matrix Classical NumberField
noncomputable section
namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

noncomputable def integralMatrix10 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) (p : Fin 3 → Fin 10 → Fin 10) :
    Matrix (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
      (RothAuxCoefficients r) ℤ :=
  fun q b => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix10 r eta a p q.1 b) q.2

theorem integralMatrix10_strict_count {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta^2)⁻¹ * Real.log (60 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ)) :
    Fintype.card (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) <
      Fintype.card (RothAuxCoefficients r) := by
  have hlt := coordinate_rows10_lt r hr eta heta (Module.finrank ℚ 𝕂)
    Module.finrank_pos hm
  simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
    Nat.mul_comm] using hlt

theorem integralMatrix10_kernel {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) (p : Fin 3 → Fin 10 → Fin 10)
    (c : RothAuxCoefficients r → ℤ) :
    (integralMatrix10 r eta a p).mulVec c = 0 ↔
      (matrix10 r eta a p).mulVec (fun b => (c b : 𝓞 𝕂)) = 0 := by
  let b := Module.finBasis ℤ (𝓞 𝕂)
  have he (q : Equations10 r eta) (k : Fin (Module.finrank ℤ (𝓞 𝕂))) :
      (integralMatrix10 r eta a p).mulVec c (q,k) =
        b.repr ((matrix10 r eta a p).mulVec (fun j => (c j : 𝓞 𝕂)) q) k := by
    simp only [Matrix.mulVec, dotProduct, integralMatrix10, map_sum, Finsupp.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg (fun x => x k) (b.repr.map_smul (c j) (matrix10 r eta a p q j))
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

noncomputable def integralHeightBase10 (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) : ℝ :=
  letI := Aux6Norm.integralNormModel 𝕂
  max 1 (∑ tau : Fin 3, ∑ s : Fin 10, ∑ j : Fin 10, ‖a tau s j‖)

noncomputable def integralCoordinateConstant10 (𝕂 : Type*) [Field 𝕂] [NumberField 𝕂] : ℝ :=
  max 1 ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖

theorem integralMatrix10_entry_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) (p : Fin 3 → Fin 10 → Fin 10)
    (q : Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))
    (b : RothAuxCoefficients r) :
    ‖integralMatrix10 r eta a p q b‖ ≤ integralCoordinateConstant10 𝕂 *
      (20 * integralHeightBase10 a)^(∑ h, r h) := by
  letI := Aux6Norm.integralNormModel 𝕂
  letI : NormOneClass (𝓞 𝕂) := ⟨Aux6Norm.integralNormModel_one⟩
  have ha : ∀ tau s j, ‖a tau s j‖ ≤ integralHeightBase10 a := by
    intro tau s j
    apply le_trans _ (le_max_right _ _)
    apply le_trans (Finset.single_le_sum (fun j _ => norm_nonneg (a tau s j)) (Finset.mem_univ j))
    apply le_trans (Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j))) (Finset.mem_univ s))
    exact Finset.single_le_sum (fun tau _ => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun j _ => norm_nonneg (a tau s j)))) (Finset.mem_univ tau)
  have hx : ‖matrix10 r eta a p q.1 b‖ ≤ (20 * integralHeightBase10 a)^(∑ h, r h) := by
    apply Aux10Height.transformed_entry_norm10
    · exact le_max_left _ _
    · exact ha _ _
  have hc := Aux6Norm.integralNormModel_coordinates (matrix10 r eta a p q.1 b)
  have hcoord := norm_le_pi_norm (fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr
    (matrix10 r eta a p q.1 b) i) q.2
  calc
    _ ≤ ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (matrix10 r eta a p q.1 b) i)‖ := hcoord
    _ ≤ ‖matrix10 r eta a p q.1 b‖ *
        ‖(fun i => (Module.finBasis ℤ (𝓞 𝕂)).repr (1 : 𝓞 𝕂) i)‖ := hc
    _ ≤ (20 * integralHeightBase10 a)^(∑ h, r h) * integralCoordinateConstant10 𝕂 :=
      mul_le_mul hx (le_max_right _ _) (norm_nonneg _) (pow_nonneg (by have hh : 1 ≤ integralHeightBase10 a := le_max_left _ _; linarith) _)
    _ = _ := mul_comm _ _

end CompoundFeasibility.Auxiliary10
namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]
attribute [local instance] Matrix.seminormedAddCommGroup

theorem dimension10_le_pow {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h) :
    rothAuxDimension r ≤ 1024^(∑ h, r h) := by
  rw [rothAuxDimension_eq]
  calc
    _ ≤ ∏ h, 1024^r h := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro h _
      calc
        (r h + 9).choose 9 ≤ 2^(r h + 9) :=
          (Nat.choose_le_two_pow _ _ (by omega)).le
        _ ≤ 2^(10 * r h) := Nat.pow_le_pow_right (by decide) (by have hh := hr h; omega)
        _ = 1024^r h := by rw [pow_mul]; norm_num
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

noncomputable def integralSiegelConstant10 (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) : ℝ :=
  1024 * (20 * integralHeightBase10 a * integralCoordinateConstant10 𝕂)

theorem integralSiegelConstant10_ge_one (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) :
    1 ≤ integralSiegelConstant10 a := by
  have hA : 1 ≤ integralHeightBase10 a := le_max_left _ _
  have hC : 1 ≤ integralCoordinateConstant10 𝕂 := le_max_left _ _
  dsimp [integralSiegelConstant10]
  nlinarith

theorem integralMatrix10_uniform_bound {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (hm : 0 < m) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) (p : Fin 3 → Fin 10 → Fin 10) :
    (Fintype.card (RothAuxCoefficients r) : ℝ) * max 1 ‖integralMatrix10 r eta a p‖ ≤
      integralSiegelConstant10 a ^ (∑ h, r h) := by
  let A := integralHeightBase10 a
  let C := integralCoordinateConstant10 𝕂
  have hA : 1 ≤ A := le_max_left _ _
  have hC : 1 ≤ C := le_max_left _ _
  have hR : 1 ≤ ∑ h, r h := by
    have hp := hr ⟨0, hm⟩
    have hh : r ⟨0, hm⟩ ≤ ∑ h, r h :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  have hbase : 1 ≤ 20 * A * C := by nlinarith
  have hnorm : ‖integralMatrix10 r eta a p‖ ≤ (20 * A * C)^(∑ h, r h) := by
    apply (Matrix.norm_le_iff (by positivity)).mpr
    intro q b
    calc
      _ ≤ C * (20 * A)^(∑ h, r h) := integralMatrix10_entry_bound r eta a p q b
      _ ≤ C^(∑ h, r h) * (20 * A)^(∑ h, r h) :=
        mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ hC hR) (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  calc
    _ ≤ (1024 : ℝ)^(∑ h, r h) * (20 * A * C)^(∑ h, r h) :=
      mul_le_mul (by exact_mod_cast dimension10_le_pow r hr)
        (max_le (one_le_pow₀ hbase) hnorm) (by positivity) (by positivity)
    _ = _ := by rw [← mul_pow]; rfl

theorem integralMatrix10_bounded_kernel {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta^2)⁻¹ * Real.log (60 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ))
    (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂) (p : Fin 3 → Fin 10 → Fin 10) :
    ∃ c : RothAuxCoefficients r → ℤ, c ≠ 0 ∧
      (integralMatrix10 r eta a p).mulVec c = 0 ∧
      ‖c‖ ≤ integralSiegelConstant10 a ^ (∑ h, r h) := by
  have hd : 0 < Module.finrank ℚ 𝕂 := Module.finrank_pos
  have hN := dimension10_pos r
  have hhalf := coordinate_rows10_le_half r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hlt := coordinate_rows10_lt r hr eta heta (Module.finrank ℚ 𝕂) hd hm
  have hmpos : 0 < m := by
    have hd' : (1 : ℝ) ≤ Module.finrank ℚ 𝕂 := by exact_mod_cast hd
    have hlog : 0 < Real.log (60 * (Module.finrank ℚ 𝕂 : ℝ)) := Real.log_pos (by linarith)
    have hh : 0 < (m : ℝ) := lt_of_lt_of_le (mul_pos (by positivity) hlog) hm
    exact_mod_cast hh
  have hD := integralSiegelConstant10_ge_one a
  by_cases hrows : Fintype.card (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) = 0
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
  · have hcount : Fintype.card (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) <
        Fintype.card (RothAuxCoefficients r) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm] using hlt
    obtain ⟨c, hc, hker, hbound⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le
      (integralMatrix10 r eta a p) hcount (Nat.pos_of_ne_zero hrows)
    refine ⟨c, hc, hker, ?_⟩
    have hrowsR : (Fintype.card (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) ≤
        (Fintype.card (RothAuxCoefficients r) : ℝ) / 2 := by
      simpa only [Fintype.card_prod, Fintype.card_fin, NumberField.RingOfIntegers.rank,
        Nat.mul_comm, Nat.cast_mul, rothAuxDimension] using hhalf
    have hden : 0 < (Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) := by
      exact sub_pos.mpr (by exact_mod_cast hcount)
    have hexp : (Fintype.card (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂))) : ℝ) /
        ((Fintype.card (RothAuxCoefficients r) : ℝ) -
        Fintype.card (Equations10 r eta × Fin (Module.finrank ℤ (𝓞 𝕂)))) ≤ 1 := by
      apply (div_le_one hden).mpr
      linarith
    have hbase : 1 ≤ (Fintype.card (RothAuxCoefficients r) : ℝ) *
        max 1 ‖integralMatrix10 r eta a p‖ := by
      have hn : (1 : ℝ) ≤ Fintype.card (RothAuxCoefficients r) := by exact_mod_cast hN
      nlinarith [le_max_left (1 : ℝ) ‖integralMatrix10 r eta a p‖]
    exact hbound.trans ((Real.rpow_le_self_of_one_le hbase hexp).trans
      (integralMatrix10_uniform_bound r hr hmpos eta a p))

end CompoundFeasibility.Auxiliary10
namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10

theorem polynomial10_ne_zero {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ)
    (hc : c ≠ 0) : polynomial10 c ≠ 0 := by
  intro hz
  apply hc
  funext b
  have hh := polynomial10_coeff c b
  rw [hz, MvPolynomial.coeff_zero] at hh
  exact hh.symm

theorem polynomial10_height_le {m : ℕ} {r : Fin m → ℕ} (c : RothAuxCoefficients r → ℤ) :
    (height10 (polynomial10 c) : ℝ) ≤ ‖c‖ := by
  have hs : ∀ d ∈ (polynomial10 c).support,
      ((polynomial10 c).coeff d).natAbs ≤ Nat.floor ‖c‖ := by
    intro d hd
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    subst d
    rw [polynomial10_coeff]
    apply Nat.le_floor
    simpa only [Int.norm_eq_abs, Int.cast_natAbs, Int.cast_abs] using norm_le_pi_norm c b
  have hh : height10 (polynomial10 c) ≤ Nat.floor ‖c‖ := Finset.sup_le hs
  exact (by exact_mod_cast hh : (height10 (polynomial10 c) : ℝ) ≤ Nat.floor ‖c‖).trans
    (Nat.floor_le (norm_nonneg _))

variable {𝕂 : Type*} [Field 𝕂]

theorem kernelChart10_scale {m : ℕ} (a : Fin 10 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 10) (u : Vars10 m) :
    kernelChart10 (fun j => M * a j) k u = kernelChart10 a k u := by
  unfold kernelChart10
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_div_mul_left _ _ hM]
  · rfl

theorem kernelRestriction10_scale {m : ℕ} (a : Fin 10 → 𝕂) (M : 𝕂) (hM : M ≠ 0)
    (k : Fin m → Fin 10) (P : MvPolynomial (Vars10 m) 𝕂) :
    kernelRestriction10 (fun j => M * a j) k P = kernelRestriction10 a k P := by
  have he : kernelChart10 (m := m) (fun j => M * a j) k = kernelChart10 a k :=
    funext (kernelChart10_scale a M hM k)
  simp only [kernelRestriction10, he]

theorem kernelRestriction10_map {𝕃 : Type*} [Field 𝕃] {m : ℕ}
    (f : 𝕂 →+* 𝕃) (a : Fin 10 → 𝕂) (k : Fin m → Fin 10)
    (P : MvPolynomial (Vars10 m) 𝕂) :
    (kernelRestriction10 a k P).map f =
      kernelRestriction10 (fun j => f (a j)) k (P.map f) := by
  have hchart (u : Vars10 m) :
      (kernelChart10 a k u).map f = kernelChart10 (fun j => f (a j)) k u := by
    unfold kernelChart10
    split_ifs <;> simp [map_sum, map_mul, map_div₀]
  induction P using MvPolynomial.induction_on with
  | C c => simp [kernelRestriction10]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show kernelRestriction10 a k (MvPolynomial.X v) = kernelChart10 a k v by simp [kernelRestriction10]]
    rw [hchart]
    simp [kernelRestriction10]

variable [NumberField 𝕂]

theorem integral_auxiliary10
    (a : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (60 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ,
        P ≠ 0 ∧ homogeneous10 r P ∧ (height10 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars10 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 10 - eta) * m →
          ∀ k : Fin m → Fin 10, (∀ h, (a tau s (k h) : 𝕂) ≠ 0) →
          kernelRestriction10 (fun j => (a tau s j : 𝕂)) k
            (derivative10 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  let p : Fin 3 → Fin 10 → Fin 10 := fun tau s => Classical.choose (ha tau s)
  have hp : ∀ tau s, a tau s (p tau s) ≠ 0 := fun tau s => Classical.choose_spec (ha tau s)
  refine ⟨integralSiegelConstant10 a, integralSiegelConstant10_ge_one a, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨c, hc, hker, hbound⟩ := integralMatrix10_bounded_kernel r hr eta heta hm a p
  refine ⟨polynomial10 c, polynomial10_ne_zero c hc, polynomial10_homogeneous c,
    (polynomial10_height_le c).trans hbound, ?_⟩
  let f : 𝓞 𝕂 →+* 𝕂 := algebraMap _ _
  have hkerO := (integralMatrix10_kernel r eta a p c).mp hker
  have hkerK : (matrix10 r eta (fun tau s j => f (a tau s j)) p).mulVec
      (fun b => (c b : 𝕂)) = 0 := by
    funext q
    have hh := congrArg f (congrFun hkerO q)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_intCast,
      matrix10_map, Pi.zero_apply, map_zero] using hh
  intro tau s J hJ k hk
  have hpK : ∀ tau s, f (a tau s (p tau s)) ≠ 0 := fun tau s =>
    (map_ne_zero_iff f (IsFractionRing.injective (𝓞 𝕂) 𝕂)).mpr (hp tau s)
  have hh := matrix10_kernel_all_derivatives r eta (fun tau s j => f (a tau s j)) p
    hpK (fun b => (c b : 𝕂)) hkerK tau s J hJ k hk
  simpa only [polynomial10_map, map_intCast] using hh

end CompoundFeasibility.Auxiliary10
namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10
variable {𝕂 : Type*} [Field 𝕂] [NumberField 𝕂]

theorem source_integral_scaling10 (a : Fin 3 → Fin 10 → Fin 10 → 𝕂) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ b : Fin 3 → Fin 10 → Fin 10 → 𝓞 𝕂,
      ∀ tau s j, (b tau s j : 𝕂) = (M : 𝕂) * a tau s j := by
  haveI : Algebra.IsAlgebraic ℚ 𝕂 := Algebra.IsAlgebraic.of_finite ℚ 𝕂
  haveI : Algebra.IsAlgebraic ℤ 𝕂 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := 𝕂)).mpr inferInstance
  obtain ⟨M, hM, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun q : Fin 3 × Fin 10 × Fin 10 => a q.1 q.2.1 q.2.2))
  have hint : ∀ tau s j, IsIntegral ℤ ((M : 𝕂) * a tau s j) := by
    intro tau s j
    simpa only [Algebra.smul_def, eq_intCast] using
      hi (a tau s j) (Finset.mem_image.mpr ⟨(tau,s,j),Finset.mem_univ _,rfl⟩)
  exact ⟨M, hM, (fun tau s j => ⟨(M : 𝕂) * a tau s j, hint tau s j⟩), fun _ _ _ => rfl⟩

theorem algebraic_auxiliary10 (a : Fin 3 → Fin 10 → Fin 10 → 𝕂)
    (ha : ∀ tau s, ∃ j, a tau s j ≠ 0) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (60 * (Module.finrank ℚ 𝕂 : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ,
        P ≠ 0 ∧ homogeneous10 r P ∧ (height10 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars10 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 10 - eta) * m →
          ∀ k : Fin m → Fin 10, (∀ h, a tau s (k h) ≠ 0) →
          kernelRestriction10 (a tau s) k
            (derivative10 J (P.map (Int.castRingHom 𝕂))) = 0 := by
  obtain ⟨M, hM, b, hb⟩ := source_integral_scaling10 a
  have hMK : (M : 𝕂) ≠ 0 := by exact_mod_cast hM
  have hbn : ∀ tau s, ∃ j, b tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := ha tau s
    refine ⟨j, ?_⟩
    intro hz
    exact (mul_ne_zero hMK hj) (by rw [← hb tau s j, hz]; rfl)
  obtain ⟨D, hD, hconstruction⟩ := integral_auxiliary10 b hbn
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
  rw [kernelRestriction10_scale (a tau s) (M : 𝕂) hMK] at hh
  exact hh

end CompoundFeasibility.Auxiliary10


namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10

theorem source_restriction10_real (K : IntermediateField ℚ ℝ) {m : ℕ}
    (a : Fin 10 → K) (k : Fin m → Fin 10) (J : Vars10 m →₀ ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) :
    (kernelRestriction10 a k (derivative10 J (P.map (Int.castRingHom K)))).map
      K.val.toRingHom =
      kernelRestriction10 (fun j => (a j : ℝ)) k
        (derivative10 J (P.map (Int.castRingHom ℝ))) := by
  rw [kernelRestriction10_map, derivative10_map, MvPolynomial.map_map]
  have hf : K.val.toRingHom.comp (Int.castRingHom K) = Int.castRingHom ℝ :=
    Subsingleton.elim _ _
  rw [hf]
  rfl

theorem source_auxiliary10_field (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau s j, SourceForms10.forms10 A2 A3 L tau s j ∈ K,
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (60 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ,
        P ≠ 0 ∧ homogeneous10 r P ∧ (height10 P : ℝ) ≤ D^(∑ h, r h) ∧
        (∀ tau s (J : Vars10 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 10 - eta) * m →
          ∀ k : Fin m → Fin 10,
            (∀ h, (⟨SourceForms10.forms10 A2 A3 L tau s (k h), hmem tau s (k h)⟩ : K) ≠ 0) →
            kernelRestriction10 (fun j => (⟨SourceForms10.forms10 A2 A3 L tau s j, hmem tau s j⟩ : K)) k
              (derivative10 J (P.map (Int.castRingHom K))) = 0) ∧
        (∀ tau s (J : Vars10 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 10 - eta) * m →
          ∀ k : Fin m → Fin 10, (∀ h, SourceForms10.forms10 A2 A3 L tau s (k h) ≠ 0) →
            kernelRestriction10 (SourceForms10.forms10 A2 A3 L tau s) k
              (derivative10 J (P.map (Int.castRingHom ℝ))) = 0) := by
  obtain ⟨K, hK, hmem⟩ := SourceForms10.common_source_field10 A2 A3 L ha
  letI : FiniteDimensional ℚ K := hK
  letI : NumberField K := {}
  let a : Fin 3 → Fin 10 → Fin 10 → K := fun tau s j =>
    ⟨SourceForms10.forms10 A2 A3 L tau s j, hmem tau s j⟩
  have hnonzero : ∀ tau s, ∃ j, a tau s j ≠ 0 := by
    intro tau s
    obtain ⟨j, hj⟩ := SourceForms10.source_rows_nonzero10 A2 A3 L h2 h3 hL tau s
    refine ⟨j, ?_⟩
    intro hh
    exact hj (congrArg Subtype.val hh)
  obtain ⟨D, hD, hconstruction⟩ := algebraic_auxiliary10 a hnonzero
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hderiv⟩ := hconstruction eta heta m hm r hr
  refine ⟨P, hP, hhom, hheight, hderiv, ?_⟩
  intro tau s J hJ k hk
  have hkK : ∀ h, a tau s (k h) ≠ 0 := by
    intro h hh
    exact hk h (congrArg Subtype.val hh)
  have he := source_restriction10_real K (a tau s) k J P
  rw [hderiv tau s J hJ k hkK, map_zero] at he
  exact he.symm

theorem source_auxiliary10 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau s j, SourceForms10.forms10 A2 A3 L tau s j ∈ K) ∧
      ∃ D : ℝ, 1 ≤ D ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4 * (eta^2)⁻¹ * Real.log (60 * (Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ,
        P ≠ 0 ∧ homogeneous10 r P ∧ (height10 P : ℝ) ≤ D^(∑ h, r h) ∧
        ∀ tau s (J : Vars10 m →₀ ℕ),
          rothSourceDerivativeWeight r J < (1 / 10 - eta) * m →
          ∀ k : Fin m → Fin 10, (∀ h, SourceForms10.forms10 A2 A3 L tau s (k h) ≠ 0) →
          kernelRestriction10 (SourceForms10.forms10 A2 A3 L tau s) k
            (derivative10 J (P.map (Int.castRingHom ℝ))) = 0 := by
  obtain ⟨K, hK, hmem, D, hD, hconstruction⟩ := source_auxiliary10_field A2 A3 L h2 h3 hL ha
  refine ⟨K, hK, hmem, D, hD, ?_⟩
  intro eta heta m hm r hr
  obtain ⟨P, hP, hhom, hheight, hfield, hreal⟩ := hconstruction eta heta m hm r hr
  exact ⟨P, hP, hhom, hheight, hreal⟩

end CompoundFeasibility.Auxiliary10

namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10

def matrixIndex10 {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (B : Matrix (Fin 10) (Fin 10) K) (r : Fin m → ℕ) (eta : ℝ)
    (P : MvPolynomial (Vars10 m) ℤ) : Prop :=
  ∀ i (J : Vars10 m →₀ ℕ), rothSourceDerivativeWeight r J < (1/10-eta)*m →
    ∀ k : Fin m → Fin 10, (∀ h, B i (k h) ≠ 0) →
      kernelRestriction10 (B i) k (derivative10 J (P.map (Int.castRingHom K))) = 0

theorem restriction10_map_int {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
    (f : K →+* E) {m : ℕ} (a : Fin 10 → K) (k : Fin m → Fin 10)
    (J : Vars10 m →₀ ℕ) (P : MvPolynomial (Vars10 m) ℤ) :
    (kernelRestriction10 a k (derivative10 J (P.map (Int.castRingHom K)))).map f =
      kernelRestriction10 (fun j => f (a j)) k (derivative10 J (P.map (Int.castRingHom E))) := by
  rw [kernelRestriction10_map,derivative10_map,MvPolynomial.map_map]
  have hf : f.comp (Int.castRingHom K) = Int.castRingHom E := Subsingleton.elim _ _
  rw [hf]

theorem padic_restriction10_zero (p : ℕ) [Fact p.Prime] {m : ℕ}
    (a : Fin 10 → ℚ) (k : Fin m → Fin 10) (J : Vars10 m →₀ ℕ)
    (P : MvPolynomial (Vars10 m) ℤ)
    (hz : kernelRestriction10 (fun j => (a j : ℝ)) k
      (derivative10 J (P.map (Int.castRingHom ℝ))) = 0) :
    kernelRestriction10 (fun j => (algebraMap ℚ ℚ_[p]) (a j)) k
      (derivative10 J (P.map (Int.castRingHom ℚ_[p]))) = 0 := by
  have hq : kernelRestriction10 a k (derivative10 J (P.map (Int.castRingHom ℚ))) = 0 := by
    apply MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    rw [map_zero,restriction10_map_int]
    exact hz
  have he := congrArg (MvPolynomial.map (algebraMap ℚ ℚ_[p])) hq
  rw [restriction10_map_int,map_zero] at he
  exact he

theorem finite_matrix_index10 (p : ℕ) [Fact p.Prime] {m : ℕ}
    (A : Matrix (Fin 10) (Fin 10) ℚ) (r : Fin m → ℕ) (eta : ℝ)
    (P : MvPolynomial (Vars10 m) ℤ)
    (hreal : matrixIndex10 (A.map (algebraMap ℚ ℝ)) r eta P) :
    matrixIndex10 (SourceForms10.finiteMatrix10 p A) r eta P := by
  intro i J hJ k hk
  apply padic_restriction10_zero p (A i) k J P
  apply hreal i J hJ k
  intro h hz
  have hq : A i (k h) = 0 := by
    change (A i (k h) : ℝ) = 0 at hz
    exact_mod_cast hz
  apply hk h
  simp [SourceForms10.finiteMatrix10,hq]

theorem source_auxiliary10_all_places (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      ∃ hmem : ∀ tau i j, SourceForms10.forms10 A2 A3 L tau i j ∈ K,
      ∃ D : ℝ, 1 ≤ D ∧ ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (Vars10 m) ℤ, P ≠ 0 ∧ homogeneous10 r P ∧
      (height10 P : ℝ) ≤ D^(∑ h, r h) ∧
      (∀ tau, matrixIndex10 (fun i j => (⟨SourceForms10.forms10 A2 A3 L tau i j,hmem tau i j⟩ : K)) r eta P) ∧
      (∀ tau, matrixIndex10 (SourceForms10.forms10 A2 A3 L tau) r eta P) ∧
      matrixIndex10 (SourceForms10.finiteMatrix10 2 A2) r eta P ∧
      matrixIndex10 (SourceForms10.finiteMatrix10 3 A3) r eta P := by
  obtain ⟨K,hK,hmem,D,hD,hconstruction⟩ := source_auxiliary10_field A2 A3 L h2 h3 hL ha
  refine ⟨K,hK,hmem,D,hD,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hP,hhom,hheight,hfield,hreal⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hP,hhom,hheight,hfield,hreal,?_,?_⟩
  · apply finite_matrix_index10 2 A2 r eta P
    exact hreal 1
  · apply finite_matrix_index10 3 A3 r eta P
    exact hreal 2

end CompoundFeasibility.Auxiliary10
