import SubspaceBridge.InvertibleCriterion4
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open CompoundFeasibility
open scoped BigOperators Pointwise
open MeasureTheory
noncomputable section
namespace M196LiteralCompoundFeasibility.Minkowski5

def dyadicBasis (a : Fin 5 → ℕ) : Basis (Fin 5) ℝ (Fin 5 → ℝ) :=
  (Pi.basisFun ℝ (Fin 5)).isUnitSMul (w := fun i => (2 : ℝ)^a i)
    (fun i => isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)))

theorem dyadic_lattice_coordinates (a : Fin 5 → ℕ)
    (x : Fin 5 → ℝ) (hx : x ∈ Submodule.span ℤ (Set.range (dyadicBasis a))) :
    ∃ z : Fin 5 → ℤ, ∀ i, x i = (2 : ℝ) ^ a i * (z i : ℝ) := by
  let b := dyadicBasis a
  let z : Fin 5 → ℤ := fun i => (b.restrictScalars ℤ).repr ⟨x,hx⟩ i
  refine ⟨z,?_⟩
  intro i
  have hr (j) : b.repr x j = (z j : ℝ) :=
    (b.restrictScalars_repr_apply ℤ ⟨x,hx⟩ j).symm
  have h := congrFun (b.sum_repr x) i
  simp only [hr] at h
  simpa [b,dyadicBasis,Basis.isUnitSMul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Pi.basisFun_apply,Pi.single_apply,mul_comm] using h.symm

theorem dyadic_lattice_avoids (a : Fin 5 → ℕ) (ha : Antitone a)
    (f : (Fin 5 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 5 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 5 → ℝ) (hmu : ∀ i, 1 < (2 : ℝ)^a i * mu i)
    (hlower : ∀ (z : Fin 5 → ℤ) (i : Fin 5), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (x : Fin 5 → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (dyadicBasis a)))
    (hxf : f x ≤ 1) : x = 0 := by
  classical
  by_contra hne
  obtain ⟨z,hz⟩ := dyadic_lattice_coordinates a x hx
  let support := Finset.univ.filter (fun i => z i ≠ 0)
  have hs : support.Nonempty := by
    by_contra h
    apply hne
    ext i
    have hzi : z i = 0 := by
      by_contra hzi
      exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hzi⟩⟩
    simp [hz i,hzi]
  let k := support.max' hs
  have hk : z k ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem support hs)).2
  have htail : ∀ j, k < j → z j = 0 := by
    intro j hj
    by_contra h
    have hle : j ≤ k := Finset.le_max' support j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,h⟩)
    exact (not_le_of_gt hj) hle
  let w : Fin 5 → ℤ := fun i => if i ≤ k then (2 : ℤ)^(a i-a k)*z i else 0
  have hwk : w k ≠ 0 := by simpa [w] using hk
  have hw : (fun i => (w i : ℝ)) = ((2 : ℝ)^a k)⁻¹ • x := by
    ext i
    by_cases hi : i ≤ k
    · have hai : a k ≤ a i := ha hi
      simp only [w,if_pos hi,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Pi.smul_apply,smul_eq_mul]
      rw [hz i,← Nat.sub_add_cancel hai, pow_add]
      field_simp
      ring
    · have hit : k < i := lt_of_not_ge hi
      simp [w,hi,hz i,htail i hit]
  have hlow := hlower w k hwk (fun j hj => by simp [w,not_le_of_gt hj])
  rw [hw,hf,abs_of_pos (inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _))] at hlow
  have hp : (0 : ℝ) < 2^a k := pow_pos (by norm_num) _
  have hle : mu k ≤ ((2 : ℝ)^a k)⁻¹ :=
    hlow.trans (by simpa using mul_le_mul_of_nonneg_left hxf (inv_nonneg.mpr hp.le))
  have hbound : (2 : ℝ)^a k * mu k ≤ 1 := by
    calc
      _ ≤ (2 : ℝ)^a k * ((2 : ℝ)^a k)⁻¹ := mul_le_mul_of_nonneg_left hle hp.le
      _ = 1 := mul_inv_cancel₀ hp.ne'
  exact (not_le_of_gt (hmu k)) hbound


theorem dyadic_fundamental_volume (a : Fin 5 → ℕ) :
    volume (ZSpan.fundamentalDomain (dyadicBasis a)) =
      ENNReal.ofReal (∏ i, (2 : ℝ)^a i) := by
  have hm : Matrix.of (dyadicBasis a) = Matrix.diagonal (fun i => (2 : ℝ)^a i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [dyadicBasis,Basis.isUnitSMul_apply,Pi.basisFun_apply]
    · simp [dyadicBasis,Basis.isUnitSMul_apply,Pi.basisFun_apply,Pi.single_apply,h]
  rw [ZSpan.volume_fundamentalDomain,hm,Matrix.det_diagonal,abs_of_pos]
  exact Finset.prod_pos (fun _ _ => pow_pos (by norm_num) _)

theorem dyadic_volume_bound (a : Fin 5 → ℕ) (ha : Antitone a)
    (f : (Fin 5 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 5 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 5 → ℝ) (hmu : ∀ i, 1 < (2 : ℝ)^a i * mu i)
    (hlower : ∀ (z : Fin 5 → ℤ) (i : Fin 5), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    volume.real {x | f x ≤ 1} ≤ (∏ i, (2 : ℝ)^a i) * 2^5 := by
  let b := dyadicBasis a
  letI : Countable (Submodule.span ℤ (Set.range b)) :=
    inferInstance
  letI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hvol : volume {x | f x ≤ 1} ≤
      volume (ZSpan.fundamentalDomain b) * 2^Module.finrank ℝ (Fin 5 → ℝ) := by
    by_contra h
    obtain ⟨x,hx,hfx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' b volume)
      (fun x hx => by simpa only [Set.mem_setOf_eq,hsymm] using hx) hconv (lt_of_not_ge h)
    apply hx
    apply Subtype.ext
    exact dyadic_lattice_avoids a ha f hf mu hmu hlower x x.property hfx
  rw [dyadic_fundamental_volume,Module.finrank_pi,Fintype.card_fin] at hvol
  have hfinite : ENNReal.ofReal (∏ i, (2 : ℝ)^a i) * (2 : ENNReal)^5 ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have h := ENNReal.toReal_mono hfinite hvol
  have hprod : (0 : ℝ) ≤ ∏ i : Fin 5, (2 : ℝ)^a i :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (a i))
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hprod,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat] using h


theorem exists_dyadic_exponents (mu : Fin 5 → ℝ)
    (hpos : ∀ i, 0 < mu i) (hone : ∀ i, mu i ≤ 1) (hmono : Monotone mu) :
    ∃ a : Fin 5 → ℕ, Antitone a ∧ ∀ i,
      1 < (2 : ℝ)^a i * mu i ∧ (2 : ℝ)^a i * mu i ≤ 2 := by
  classical
  have hex (i : Fin 5) : ∃ n : ℕ, 1 < (2 : ℝ)^n * mu i := by
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (mu i)⁻¹ (by norm_num : (1 : ℝ) < 2)
    refine ⟨n,?_⟩
    exact (div_lt_iff₀ (hpos i)).mp (by simpa only [one_div] using hn)
  let a := fun i => Nat.find (hex i)
  refine ⟨a,?_,?_⟩
  · intro i j hij
    apply Nat.find_min' (hex j)
    exact (Nat.find_spec (hex i)).trans_le
      (mul_le_mul_of_nonneg_left (hmono hij) (pow_nonneg (by norm_num) _))
  · intro i
    refine ⟨Nat.find_spec (hex i),?_⟩
    have ha0 : a i ≠ 0 := by
      intro h
      have hg := Nat.find_spec (hex i)
      change 1 < (2 : ℝ)^a i * mu i at hg
      rw [h,pow_zero,one_mul] at hg
      exact (not_lt_of_ge (hone i)) hg
    have hpred : (2 : ℝ)^(a i-1) * mu i ≤ 1 := by
      apply le_of_not_gt
      exact Nat.find_min (hex i) (Nat.sub_lt (Nat.pos_of_ne_zero ha0) (by decide))
    have heq : a i = (a i-1)+1 := by omega
    rw [heq,pow_succ]
    nlinarith

theorem normalized_product_volume_upper
    (f : (Fin 5 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 5 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 5 → ℝ) (hpos : ∀ i, 0 < mu i)
    (hone : ∀ i, mu i ≤ 1) (hmono : Monotone mu)
    (hlower : ∀ (z : Fin 5 → ℤ) (i : Fin 5), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    (∏ i, mu i) * volume.real {x | f x ≤ 1} ≤ 4^5 := by
  obtain ⟨a,ha,hscale⟩ := exists_dyadic_exponents mu hpos hone hmono
  have hvol := dyadic_volume_bound a ha f hf mu (fun i => (hscale i).1) hlower hsymm hconv
  have hp : 0 ≤ ∏ i, mu i := Finset.prod_nonneg (fun i _ => (hpos i).le)
  have hprod : (∏ i, (2 : ℝ)^a i * mu i) ≤ 2^5 := by
    calc
      _ ≤ ∏ _ : Fin 5, (2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => mul_nonneg (pow_nonneg (by norm_num) _) (hpos i).le)
          (fun i _ => (hscale i).2)
      _ = _ := by simp
  calc
    _ ≤ (∏ i, mu i) * ((∏ i, (2 : ℝ)^a i) * 2^5) := mul_le_mul_of_nonneg_left hvol hp
    _ = (∏ i, (2 : ℝ)^a i * mu i) * 2^5 := by rw [Finset.prod_mul_distrib]; ring
    _ ≤ 2^5 * 2^5 := mul_le_mul_of_nonneg_right hprod (pow_nonneg (by norm_num) _)
    _ = 4^5 := by rw [← mul_pow]; norm_num


theorem homogeneous_sublevel_dilate (f : (Fin 5 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 5 → ℝ), f (r • x) = |r| * f x)
    (t : ℝ) (ht : 0 < t) : {x | f x / t ≤ 1} = t • {x | f x ≤ 1} := by
  ext x
  constructor
  · intro hx
    refine ⟨t⁻¹ • x,?_,smul_inv_smul₀ ht.ne' x⟩
    change f (t⁻¹ • x) ≤ 1
    rw [hf,abs_of_pos (inv_pos.mpr ht)]
    simpa only [div_eq_mul_inv,mul_comm] using hx
  · rintro ⟨y,hy,rfl⟩
    change f (t • y) / t ≤ 1
    rw [hf,abs_of_pos ht,mul_div_cancel_left₀ _ ht.ne']
    exact hy

theorem adapted_product_volume_upper
    (f : (Fin 5 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 5 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 5 → ℝ) (hpos : ∀ i, 0 < mu i) (hmono : Monotone mu)
    (hlower : ∀ (z : Fin 5 → ℤ) (i : Fin 5), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    (∏ i, mu i) * volume.real {x | f x ≤ 1} ≤ 4^5 := by
  let t := 1 + ∑ i, mu i
  have ht : 0 < t := by
    dsimp [t]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hpos i).le))
  have hle (i : Fin 5) : mu i ≤ t := by
    have h := Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)
    dsimp [t]
    linarith
  have heq := homogeneous_sublevel_dilate f hf t ht
  have hconv' : Convex ℝ {x | f x / t ≤ 1} := by rw [heq]; exact hconv.smul t
  have h := normalized_product_volume_upper (fun x => f x / t)
    (fun r x => by dsimp only; rw [hf]; ring) (fun i => mu i/t)
    (fun i => div_pos (hpos i) ht) (fun i => (div_le_one ht).mpr (hle i))
    (fun i j hij => div_le_div_of_nonneg_right (hmono hij) ht.le)
    (fun z i hz htail => div_le_div_of_nonneg_right (hlower z i hz htail) ht.le)
    (fun x => by dsimp only; rw [hsymm]) hconv'
  have hvol : volume.real {x | f x/t ≤ 1} = t^5 * volume.real {x | f x ≤ 1} := by
    rw [heq,measureReal_def,Measure.addHaar_smul,Module.finrank_pi,Fintype.card_fin,
      abs_of_pos (pow_pos ht _),ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
    rfl
  rw [hvol,Finset.prod_div_distrib] at h
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  have hcancel : (∏ i, mu i) / t^5 * (t^5 * volume.real {x | f x ≤ 1}) =
      (∏ i, mu i) * volume.real {x | f x ≤ 1} := by
    field_simp
    ring
  rwa [hcancel] at h

end M196LiteralCompoundFeasibility.Minkowski5

open scoped BigOperators Matrix Pointwise
open MeasureTheory Filter
namespace M196LiteralCompoundFeasibility
noncomputable section

def row5 (A : Matrix (Fin 5) (Fin 5) ℚ) (i : Fin 5) : (Fin 5 → ℤ) →+ ℚ where
  toFun x := (A *ᵥ (fun j => (x j : ℚ))) i
  map_zero' := by
    change (A *ᵥ (0 : Fin 5 → ℚ)) i = 0
    rw [Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    simp only [Pi.add_apply,Int.cast_add]
    change (A *ᵥ ((fun j => (x j : ℚ)) + (fun j => (y j : ℚ)))) i = _
    rw [Matrix.mulVec_add]
    rfl

def lattice5 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (e : Fin 5 → ℕ) : AddSubgroup (Fin 5 → ℤ) :=
  ⨅ i, (normBall p (e i)).comap (row5 A i)

theorem lattice5_spec (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (e : Fin 5 → ℕ) (x : Fin 5 → ℤ) : x ∈ lattice5 p A e ↔
    ∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ (p : ℚ) ^ (-(e i : ℤ)) := by
  simp only [lattice5,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  change (∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹) ↔ _
  simp only [zpow_neg,zpow_natCast]

def sourceLattice5 (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : AddSubgroup (Fin 5 → ℤ) := lattice5 2 A₂ e₂ ⊓ lattice5 3 A₃ e₃

theorem sourceLattice5_multiple (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ j : Fin 5, Pi.single j D ∈ sourceLattice5 A₂ A₃ e₂ e₃ := by
  obtain ⟨D₂,h₂,hD₂⟩ := clear_matrix_denominators A₂
  obtain ⟨D₃,h₃,hD₃⟩ := clear_matrix_denominators A₃
  let D : ℤ := D₂ * D₃ * 2 ^ (∑ s, e₂ s) * 3 ^ (∑ s, e₃ s)
  refine ⟨D, by dsimp [D]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h₂ h₃) (by positivity)) (by positivity), ?_⟩
  intro j
  constructor
  · apply (lattice5_spec 2 A₂ e₂ _).mpr
    have he : D = D₂ * 2 ^ (∑ s, e₂ s) * (D₃ * 3 ^ (∑ s, e₃ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 2 A₂ e₂ D₂ hD₂ _ j
  · apply (lattice5_spec 3 A₃ e₃ _).mpr
    have he : D = D₃ * 3 ^ (∑ s, e₃ s) * (D₂ * 2 ^ (∑ s, e₂ s)) := by dsimp [D]; ring
    rw [he]
    exact local_multiple_bounds 3 A₃ e₃ D₃ hD₃ _ j

theorem sourceLattice5_has_basis (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : Nonempty (Basis (Fin 5) ℤ (sourceLattice5 A₂ A₃ e₂ e₃)) := by
  obtain ⟨D,hD,hm⟩ := sourceLattice5_multiple A₂ A₃ e₂ e₃
  exact integer_subgroup_has_basis _ D hD hm

instance sourceLattice5_isZLattice (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : IsZLattice ℝ (integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃)) where
  span_top := by
    obtain ⟨D,hD,hm⟩ := sourceLattice5_multiple A₂ A₃ e₂ e₃
    exact integerRealImage_span_top _ D hD hm

theorem sourceLattice5_covolume_det (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) (c : Basis (Fin 5) ℤ (sourceLattice5 A₂ A₃ e₂ e₃)) :
    ZLattice.covolume (integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃)) =
      |(Matrix.of (fun j i => ((c j : Fin 5 → ℤ) i : ℝ))).det| :=
  integerRealImage_covolume_det _ c

theorem sourceLattice5_covolume_index (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) :
    ZLattice.covolume (integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃)) =
      ((sourceLattice5 A₂ A₃ e₂ e₃).index : ℝ) := by
  obtain ⟨c⟩ := sourceLattice5_has_basis A₂ A₃ e₂ e₃
  exact integerRealImage_covolume_index _ c

theorem integer_span5_index_det
    {n : ℕ} {M : Type*} [AddCommGroup M]
    (c : Basis (Fin n) ℤ M) (u : Fin n → M) (hu : LinearIndependent ℤ u) :
    Finite (M ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index = (c.toMatrix u).det.natAbs ∧
      (c.toMatrix u).det ≠ 0 := by
  letI : Module.Free ℤ M := Module.Free.of_basis c
  letI : Module.Finite ℤ M := Module.Finite.of_basis c
  let N := Submodule.span ℤ (Set.range u)
  let e : M ≃+ N := by
    letI : Module ℤ N := N.module
    exact (c.equiv (Basis.span hu) (Equiv.refl _)).toAddEquiv
  have hfinite : Finite (M ⧸ N) :=
    Submodule.finiteQuotientOfFreeOfRankEq N e.toIntLinearEquiv.symm.finrank_eq
  have hcard : Nat.card (M ⧸ N) = (c.toMatrix u).det.natAbs := by
    have h := (Submodule.natAbs_det_basis_change c N (Basis.span hu)).symm

    have hspan :
        (Subtype.val ∘ (Basis.span hu : Fin n → N)) = u := by
      funext i
      exact Basis.span_apply hu i

    have hmat :
        c.toMatrix (Subtype.val ∘ (Basis.span hu : Fin n → N)) =
          c.toMatrix u :=
      congrArg (fun w : Fin n → M => c.toMatrix w) hspan

    calc
      Nat.card (M ⧸ N) =
          (c.toMatrix (Subtype.val ∘ (Basis.span hu : Fin n → N))).det.natAbs := by
            simpa only [Basis.det_apply] using h
      _ = (c.toMatrix u).det.natAbs := by
            rw [hmat]
  refine ⟨hfinite, hcard, ?_⟩
  letI := hfinite
  have hpos := Nat.card_pos (α := M ⧸ N)
  rw [hcard] at hpos
  exact Int.natAbs_ne_zero.mp (ne_of_gt hpos)


theorem integer_matrix_index_upper5 {n : ℕ} (G : AddSubgroup (Fin n → ℤ))
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : U.det ≠ 0) (hm : ∀ j, U.col j ∈ G) :
    G.index ≤ U.det.natAbs := by
  classical
  let N := Submodule.span ℤ (Set.range U.col)
  obtain ⟨hf,hi,hd⟩ := integer_span5_index_det (Pi.basisFun ℤ (Fin n)) U.col
    (Matrix.linearIndependent_cols_of_det_ne_zero hU)
  have he : (Pi.basisFun ℤ (Fin n)).toMatrix U.col = U := by ext i j; rfl
  have hiMatrix := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.det.natAbs) he
  have hi := hi.trans hiMatrix
  letI : N.toAddSubgroup.FiniteIndex := ⟨by rw [hi]; exact Int.natAbs_ne_zero.mpr hU⟩
  have hle : N.toAddSubgroup ≤ G := by
    change N ≤ G.toIntSubmodule
    exact Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hm j)
  exact (AddSubgroup.index_antitone hle).trans_eq hi

theorem inverse_integral_frame5 (A : Matrix (Fin 5) (Fin 5) ℚ) (hA : IsUnit A) :
    ∃ (D : ℤ) (B : Matrix (Fin 5) (Fin 5) ℤ), D ≠ 0 ∧ B.det ≠ 0 ∧
      B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
  classical
  obtain ⟨D,hD,hm⟩ := clear_matrix_denominators A⁻¹
  choose b hB using hm
  let B : Matrix (Fin 5) (Fin 5) ℤ := b
  have he : (B : Matrix (Fin 5) (Fin 5) ℤ).map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹ := by
    ext i j
    exact hB i j
  refine ⟨D,B,hD,?_,he⟩
  have hd : ((B : Matrix (Fin 5) (Fin 5) ℤ).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [he, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hD))
      (inv_ne_zero (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)))
  intro h
  apply hd
  rw [← integer_matrix_det_cast, h, Int.cast_zero]

theorem lattice5_index_upper (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (D : ℤ) (B : Matrix (Fin 5) (Fin 5) ℤ)
    (hB : B.det ≠ 0)
    (he : B.map (Int.castRingHom ℚ) = (D : ℚ) • A⁻¹) (hA : IsUnit A)
    (e : Fin 5 → ℕ) :
    (lattice5 p A e).index ≤ B.det.natAbs * p ^ (∑ i, e i) := by
  classical
  let U := B * Matrix.diagonal (fun i => (p : ℤ) ^ e i)
  have hd : U.det = B.det * (p : ℤ) ^ (∑ i, e i) := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hU : U.det ≠ 0 := by rw [hd]; exact mul_ne_zero hB (pow_ne_zero _ (by exact_mod_cast hp))
  have hm (j : Fin 5) : U.col j ∈ lattice5 p A e := by
    apply (lattice5_spec p A e _).mpr
    have hcol : (fun k => (U.col j k : ℚ)) =
        (p : ℚ) ^ e j • (B.map (Int.castRingHom ℚ)).col j := by
      ext k
      simp [U,Matrix.mul_diagonal,Matrix.col_apply,smul_eq_mul,mul_comm]
    have hmul : A * B.map (Int.castRingHom ℚ) = (D : ℚ) • (1 : Matrix (Fin 5) (Fin 5) ℚ) := by
      rw [he,Matrix.mul_smul,Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    have hact : A *ᵥ (B.map (Int.castRingHom ℚ)).col j =
        ((D : ℚ) • (1 : Matrix (Fin 5) (Fin 5) ℚ)).col j := by
      change (A * B.map (Int.castRingHom ℚ)).col j = _
      rw [hmul]
    intro i
    rw [hcol,Matrix.mulVec_smul,hact]
    by_cases hij : i = j
    · subst i
      simp only [Pi.smul_apply,smul_eq_mul,Matrix.col_apply,Matrix.smul_apply,Matrix.one_apply_eq,mul_one]
      rw [show (p : ℚ) ^ e j * (D : ℚ) = (((p : ℤ) ^ e j * D : ℤ) : ℚ) by push_cast; ring]
      apply padicNorm.dvd_iff_norm_le.mp
      exact_mod_cast (dvd_mul_right ((p : ℤ) ^ e j) D)
    · simp [Matrix.col_apply,Matrix.one_apply,hij,Ne.symm hij]
  have h := integer_matrix_index_upper5 (lattice5 p A e) U hU hm
  rw [hd,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at h
  exact h

theorem sourceLattice5_uniform_index_upper (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) :
    ∃ K : ℕ, 0 < K ∧ ∀ e₂ e₃ : Fin 5 → ℕ,
      (sourceLattice5 A₂ A₃ e₂ e₃).index ≤
        K * 2 ^ (∑ i, e₂ i) * 3 ^ (∑ i, e₃ i) := by
  obtain ⟨D₂,B₂,hD₂,hB₂,he₂⟩ := inverse_integral_frame5 A₂ h₂
  obtain ⟨D₃,B₃,hD₃,hB₃,he₃⟩ := inverse_integral_frame5 A₃ h₃
  refine ⟨B₂.det.natAbs * B₃.det.natAbs,
    Nat.mul_pos (Int.natAbs_pos.mpr hB₂) (Int.natAbs_pos.mpr hB₃),?_⟩
  intro e₂ e₃
  have h2 := lattice5_index_upper 2 A₂ D₂ B₂ hB₂ he₂ h₂ e₂
  have h3 := lattice5_index_upper 3 A₃ D₃ B₃ hB₃ he₃ h₃ e₃
  have h := (AddSubgroup.index_inf_le (H := lattice5 2 A₂ e₂) (K := lattice5 3 A₃ e₃)).trans
    (Nat.mul_le_mul h2 h3)
  simpa only [sourceLattice5, Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

theorem q_prime_powers_product_upper5 (p : ℕ) (hp : 1 < p)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (hc : ∀ i, c i ≤ 0) :
    (p : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold p Q (c i))) ≤
      (p : ℝ) ^ 5 * ∏ i, Q ^ (-c i) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hstep (i : Fin 5) :
      (p : ℝ) ^ Nat.ceil (JSP000334.qThreshold p Q (c i)) ≤ (p : ℝ) * Q ^ (-c i) := by
    rw [← JSP000334.qThreshold_rpow p hp Q (c i) hQ, ← Real.rpow_natCast]
    calc
      _ ≤ (p : ℝ) ^ (JSP000334.qThreshold p Q (c i) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le)
          (Nat.ceil_lt_add_one (JSP000334.qThreshold_nonneg p hp Q (c i) hQ (hc i))).le
      _ = _ := by rw [Real.rpow_add hp0,Real.rpow_one]; ring
  rw [← Finset.prod_pow_eq_pow_sum]
  have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => pow_nonneg hp0.le _) (fun i _ => hstep i)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem q_prime_powers_normalized_upper5 (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 5 → ℝ) (h₂ : ∀ i, c₂ i ≤ 0) (h₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (2 : ℝ) ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
      3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) ≤
      7776 * ∏ i, Q ^ c₀ i := by
  have hQ0 := lt_trans zero_lt_one hQ
  have hprod : (∏ i, Q ^ (-c₂ i)) * (∏ i, Q ^ (-c₃ i)) = ∏ i, Q ^ c₀ i := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [← Real.rpow_add hQ0]
    rw [← Real.rpow_sum_of_pos hQ0 _ Finset.univ, ← Real.rpow_sum_of_pos hQ0 _ Finset.univ]
    congr 1
    simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib] at hb ⊢
    linarith
  have h := mul_le_mul (q_prime_powers_product_upper5 2 (by decide) Q hQ c₂ h₂)
    (q_prime_powers_product_upper5 3 (by decide) Q hQ c₃ h₃)
    (by positivity) (by positivity)
  calc
    _ ≤ ((2 : ℝ) ^ 5 * ∏ i, Q ^ (-c₂ i)) * (3 ^ 5 * ∏ i, Q ^ (-c₃ i)) := h
    _ = ((2 : ℝ) ^ 5 * 3 ^ 5) * ((∏ i, Q ^ (-c₂ i)) * ∏ i, Q ^ (-c₃ i)) := by ring
    _ = _ := by rw [hprod]; norm_num

theorem sourceLattice5_uniform_normalized_covolume_upper
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) :
    ∃ K : ℕ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q → ∀ c₀ c₂ c₃ : Fin 5 → ℝ,
      (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
      (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
      ZLattice.covolume (integerRealImage (sourceLattice5 A₂ A₃
        (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
        (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))) /
        (∏ i, Q ^ c₀ i) ≤ (K : ℝ) * 7776 := by
  obtain ⟨K,hK,hindex⟩ := sourceLattice5_uniform_index_upper A₂ A₃ h₂ h₃
  refine ⟨K,hK,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  have hW : 0 < ∏ i, Q ^ c₀ i := Finset.prod_pos
    (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  apply (div_le_iff₀ hW).mpr
  rw [sourceLattice5_covolume_index]
  have hi := hindex (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hiR : (((sourceLattice5 A₂ A₃
      (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))))).index : ℝ) ≤
      (K : ℝ) * 2 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))) *
        3 ^ (∑ i, Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))) := by exact_mod_cast hi
  have hn := mul_le_mul_of_nonneg_left (q_prime_powers_normalized_upper5 Q hQ c₀ c₂ c₃ hc₂ hc₃ hb)
    (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  exact hiR.trans (by simpa only [mul_assoc] using hn)


end
end M196LiteralCompoundFeasibility

open scoped BigOperators Matrix
namespace M196LiteralCompoundFeasibility
noncomputable section
abbrev lattice5Span (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) : Submodule ℤ (Fin 5 → ℝ) :=
  Submodule.span ℤ (Set.range b)
def coordinateGauge5 (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (x : Fin 5 → ℝ) : ℝ := ‖e x‖
theorem lattice5Span_gauge_ball_finite (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (r : ℝ) :
    ({x : (Fin 5 → ℝ) | coordinateGauge5 e x ≤ r} ∩ (lattice5Span b : Set (Fin 5 → ℝ))).Finite := by
  have hf := ZSpan.setFinite_inter (b.map e) (Metric.isBounded_closedBall (x := 0) (r := r))
  apply (hf.preimage e.injective.injOn).subset
  intro x hx
  refine ⟨?_, ?_⟩
  · simpa [coordinateGauge5, Metric.mem_closedBall, dist_zero_right] using hx.1
  · have hm := Submodule.mem_map_of_mem (f := (e.restrictScalars ℤ).toLinearMap) hx.2
    simpa only [lattice5Span, Submodule.map_span, Set.range_comp,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Basis.coe_map] using hm

theorem exists_shortest_lattice5Span_vector_outside (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (W : Submodule ℝ (Fin 5 → ℝ)) (hW : W ≠ ⊤) :
    ∃ x ∈ lattice5Span b, x ∉ W ∧ 0 < coordinateGauge5 e x ∧
      ∀ y ∈ lattice5Span b, y ∉ W → coordinateGauge5 e x ≤ coordinateGauge5 e y := by
  classical
  have hex : ∃ i, b i ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  obtain ⟨i, hi⟩ := hex
  let s : Set (Fin 5 → ℝ) :=
    {x | coordinateGauge5 e x ≤ coordinateGauge5 e (b i)} ∩
      (lattice5Span b : Set (Fin 5 → ℝ)) ∩ {x | x ∉ W}
  have hs : s.Finite := (lattice5Span_gauge_ball_finite b e _).inter_of_left _
  have hbi : b i ∈ lattice5Span b := Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image s (coordinateGauge5 e) hs
    ⟨b i, ⟨⟨show coordinateGauge5 e (b i) ≤ coordinateGauge5 e (b i) from le_rfl, hbi⟩, hi⟩⟩
  refine ⟨x, hx.1.2, hx.2, ?_, ?_⟩
  · apply norm_pos_iff.mpr
    intro h0
    have : x = 0 := e.injective (h0.trans e.map_zero.symm)
    exact hx.2 (this ▸ W.zero_mem)
  · intro y hy hyW
    by_cases hle : coordinateGauge5 e y ≤ coordinateGauge5 e (b i)
    · exact hmin y ⟨⟨hle, hy⟩, hyW⟩
    · exact hx.1.1.trans (le_of_not_ge hle)

noncomputable def successiveRadius5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (k : Fin 5) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val + 1) → (Fin 5 → ℝ),
    LinearIndependent ℝ u ∧ (∀ i, u i ∈ lattice5Span b) ∧
      ∀ i, coordinateGauge5 e (u i) ≤ r}

theorem independent_family_escapes_subspace5 {n : ℕ} (u : Fin n → (Fin 5 → ℝ))
    (hu : LinearIndependent ℝ u) (W : Submodule ℝ (Fin 5 → ℝ))
    (hW : Module.finrank ℝ W < n) : ∃ i, u i ∉ W := by
  by_contra! h
  have hs : Submodule.span ℝ (Set.range u) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  have hd := Submodule.finrank_mono hs
  rw [finrank_span_eq_card hu, Fintype.card_fin] at hd
  omega



def minimaPrefix5 {n : ℕ} (v : Fin n → Fin 5 → ℝ) (i : Fin n) : Submodule ℝ (Fin 5 → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : Fin i.val => v (Fin.castLE (by omega) j)))

theorem minimaPrefix5_snoc_castSucc {n : ℕ} (v : Fin n → Fin 5 → ℝ)
    (x : Fin 5 → ℝ) (i : Fin n) :
    minimaPrefix5 (Fin.snoc v x) i.castSucc = minimaPrefix5 v i := by
  unfold minimaPrefix5
  apply congrArg (fun u : Fin i.val → Fin 5 → ℝ => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) =
      (Fin.castLE (Nat.le_of_lt i.isLt) j).castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]

theorem minimaPrefix5_snoc_last {n : ℕ} (v : Fin n → Fin 5 → ℝ) (x : Fin 5 → ℝ) :
    minimaPrefix5 (Fin.snoc v x) (Fin.last n) = Submodule.span ℝ (Set.range v) := by
  unfold minimaPrefix5
  apply congrArg (fun u : Fin n → Fin 5 → ℝ => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) = j.castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]

theorem exists_greedy_prefix5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) :
    ∀ n ≤ 5, ∃ v : Fin n → Fin 5 → ℝ,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ lattice5Span b) ∧
      ∀ i, ∀ y ∈ lattice5Span b, y ∉ minimaPrefix5 v i →
        coordinateGauge5 e (v i) ≤ coordinateGauge5 e y := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨Fin.elim0,linearIndependent_empty_type,(fun i => Fin.elim0 i),fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro hn
    obtain ⟨v,hv,hvL,hmin⟩ := ih (by omega)
    let W := Submodule.span ℝ (Set.range v)
    have hW : W ≠ ⊤ := by
      intro h
      have hd := finrank_span_eq_card hv
      simp only [Fintype.card_fin] at hd
      change Module.finrank ℝ W = n at hd
      rw [h,finrank_top,Module.finrank_pi,Fintype.card_fin] at hd
      omega
    obtain ⟨x,hxL,hxW,hxpos,hxmin⟩ := exists_shortest_lattice5Span_vector_outside b e W hW
    refine ⟨Fin.snoc v x,linearIndependent_fin_snoc.mpr ⟨hv,hxW⟩,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hxL
      · simpa only [Fin.snoc_castSucc] using hvL j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [minimaPrefix5_snoc_last]
        simpa only [Fin.snoc_last] using hxmin
      · rw [minimaPrefix5_snoc_castSucc]
        simpa only [Fin.snoc_castSucc] using hmin j

theorem minimaPrefix5_not_mem {n : ℕ} (v : Fin n → Fin 5 → ℝ)
    (hv : LinearIndependent ℝ v) (i j : Fin n) (hij : i ≤ j) : v j ∉ minimaPrefix5 v i := by
  have hle : minimaPrefix5 v i ≤ Submodule.span ℝ (v '' {t | t < i}) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact Submodule.subset_span ⟨Fin.castLE (by omega) a,by change a.val < i.val; exact a.isLt,rfl⟩
  exact fun h => hv.not_mem_span_image (s := {t | t < i}) (x := j) (not_lt_of_ge hij) (hle h)

theorem minimaPrefix5_finrank {n : ℕ} (v : Fin n → Fin 5 → ℝ)
    (hv : LinearIndependent ℝ v) (i : Fin n) : Module.finrank ℝ (minimaPrefix5 v i) = i.val := by
  exact (finrank_span_eq_card (hv.comp (Fin.castLE (by omega) : Fin i.val → Fin n)
    (Fin.castLE_injective _))).trans (Fintype.card_fin i.val)

theorem exists_successive_minima5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) :
    ∃ v : Fin 5 → Fin 5 → ℝ, LinearIndependent ℝ v ∧
      (∀ i, v i ∈ lattice5Span b) ∧ (∀ i, 0 < successiveRadius5 b e i) ∧
      Monotone (successiveRadius5 b e) ∧
      (∀ i, coordinateGauge5 e (v i) = successiveRadius5 b e i) ∧
      ∀ i, ∀ y ∈ lattice5Span b, y ∉ minimaPrefix5 v i → coordinateGauge5 e (v i) ≤ coordinateGauge5 e y := by
  obtain ⟨v,hv,hvL,hmin⟩ := exists_greedy_prefix5 b e 5 le_rfl
  let f := coordinateGauge5 e
  have hmono : Monotone (fun i => f (v i)) := by
    intro i j hij
    exact hmin i (v j) (hvL j) (minimaPrefix5_not_mem v hv i j hij)
  have heq (k : Fin 5) : successiveRadius5 b e k = f (v k) := by
    apply IsLeast.csInf_eq
    constructor
    · let emb : Fin (k.val+1) → Fin 5 := Fin.castLE (by omega)
      refine ⟨fun i => v (emb i),hv.comp emb (Fin.castLE_injective _),fun i => hvL (emb i),?_⟩
      intro i
      exact hmono (show emb i ≤ k by change i.val ≤ k.val; omega)
    · rintro r ⟨a,ha,haL,har⟩
      obtain ⟨i,hi⟩ := independent_family_escapes_subspace5 a ha (minimaPrefix5 v k)
        (by rw [minimaPrefix5_finrank v hv k]; omega)
      exact (hmin k (a i) (haL i) hi).trans (har i)
  refine ⟨v,hv,hvL,?_,?_,?_,hmin⟩
  · intro i
    rw [heq]
    exact norm_pos_iff.mpr (fun h => hv.ne_zero i (e.injective (h.trans e.map_zero.symm)))
  · intro i j hij
    rw [heq,heq]
    exact hmono hij
  · intro i
    exact (heq i).symm

end
end M196LiteralCompoundFeasibility

open scoped BigOperators Matrix
open MeasureTheory
namespace M196LiteralCompoundFeasibility
noncomputable section

def minimaFlag5 (v : Fin 5 → Fin 5 → ℝ) (k : Fin 5) : Submodule ℝ (Fin 5 → ℝ) := minimaPrefix5 v k

theorem minimaFlag5_finrank (v : Fin 5 → Fin 5 → ℝ) (hv : LinearIndependent ℝ v) (k : Fin 5) :
    Module.finrank ℝ (minimaFlag5 v k) = k.val := minimaPrefix5_finrank v hv k

theorem minimaFlag5_mono (v : Fin 5 → (Fin 5 → ℝ)) (k l : Fin 5) (hkl : k ≤ l) :
    minimaFlag5 v k ≤ minimaFlag5 v l := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨Fin.castLE hkl i, ?_⟩
  rfl

def latticeFlag5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → (Fin 5 → ℝ))
    (k : Fin 5) : Submodule ℤ (lattice5Span b) :=
  ((minimaFlag5 v k).restrictScalars ℤ).comap (lattice5Span b).subtype

def flagLattice5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → (Fin 5 → ℝ))
    (k : Fin 5) : Submodule ℤ (minimaFlag5 v k) :=
  (lattice5Span b).comap ((minimaFlag5 v k).subtype.restrictScalars ℤ)

theorem latticeFlag5_saturated (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (k : Fin 5) (n : ℤ) (hn : n ≠ 0)
    (x : lattice5Span b) (hx : n • x ∈ latticeFlag5 b v k) :
    x ∈ latticeFlag5 b v k := by
  change n • (x : (Fin 5 → ℝ)) ∈ minimaFlag5 v k at hx
  rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  change (x : (Fin 5 → ℝ)) ∈ minimaFlag5 v k
  exact (Submodule.smul_mem_iff (minimaFlag5 v k) (by exact_mod_cast hn : (n : ℝ) ≠ 0)).mp hx

noncomputable def latticeFlag5_equiv_flagLattice5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (k : Fin 5) :
    latticeFlag5 b v k ≃ₗ[ℤ] flagLattice5 b v k where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance flagLattice5_discrete (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (k : Fin 5) : DiscreteTopology (flagLattice5 b v k) := by
  let f : flagLattice5 b v k → lattice5Span b := fun x => ⟨x.val.val, x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : lattice5Span b => (z : (Fin 5 → ℝ))) h

instance flagLattice5_isZLattice (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice5Span b) (k : Fin 5) :
    IsZLattice ℝ (flagLattice5 b v k) where
  span_top := by
    let u : Fin k.val → (Fin 5 → ℝ) := fun i => v (Fin.castLE (by omega) i)
    let B : Basis (Fin k.val) ℝ (minimaFlag5 v k) :=
      Basis.span (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    change (B i : (Fin 5 → ℝ)) ∈ lattice5Span b
    have hB : (B i : (Fin 5 → ℝ)) = u i :=
      Basis.span_apply (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _)) i
    rw [hB]
    exact hvL (Fin.castLE (by omega) i)

theorem latticeFlag5_finrank (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice5Span b) (k : Fin 5) :
    Module.finrank ℤ (latticeFlag5 b v k) = k.val := by
  letI := flagLattice5_isZLattice b v hv hvL k
  rw [(latticeFlag5_equiv_flagLattice5 b v k).finrank_eq,
    ZLattice.rank ℝ (flagLattice5 b v k), minimaFlag5_finrank v hv k]


theorem latticeFlag5_basis_real_span {ι : Type*}
    (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → (Fin 5 → ℝ))
    (hvL : ∀ i, v i ∈ lattice5Span b) (k : Fin 5)
    (a : @Basis ι ℤ (latticeFlag5 b v k) _ _ (latticeFlag5 b v k).module) :
    Submodule.span ℝ (Set.range (fun i =>
      (((a i : latticeFlag5 b v k) : lattice5Span b) : (Fin 5 → ℝ)))) = minimaFlag5 v k := by
  let N := latticeFlag5 b v k
  letI nModule : Module ℤ N := N.module
  let W := Submodule.span ℝ (Set.range (fun i =>
    (((a i : latticeFlag5 b v k) : lattice5Span b) : (Fin 5 → ℝ))))
  have hw : ∀ x : N, ((x : lattice5Span b) : (Fin 5 → ℝ)) ∈ W := by
    have h : Submodule.span ℤ (Set.range a) ≤
        ((W.restrictScalars ℤ).comap (lattice5Span b).subtype).comap N.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [a.span_eq] at h
    intro x
    exact h (Submodule.mem_top : x ∈ (⊤ : Submodule ℤ N))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (a i).property
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let x : N := ⟨⟨v (Fin.castLE (by omega) i), hvL _⟩,
      Submodule.subset_span (Set.mem_range_self i)⟩
    exact hw x


theorem exists_adapted_integer_basis5
    (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → Fin 5 → ℝ)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice5Span b) :
    ∃ c : Basis (Fin 5) ℤ (lattice5Span b), ∀ k : Fin 5,
      Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        ((c (Fin.castLE (by omega) i) : lattice5Span b) : Fin 5 → ℝ))) = minimaFlag5 v k := by
  classical
  let L := lattice5Span b
  letI lModule : Module ℤ L := (lattice5Span b).module
  letI lFinite : Module.Finite ℤ L := Module.Finite.of_basis (b.restrictScalars ℤ)
  letI lFree : Module.Free ℤ L := Module.Free.of_basis (b.restrictScalars ℤ)
  letI lNoZero : NoZeroSMulDivisors ℤ L := Submodule.noZeroSMulDivisors L
  let N1 : Submodule ℤ L := latticeFlag5 b v 1
  letI n1Module : Module ℤ N1 := N1.module
  letI n1Finite : Module.Finite ℤ N1 := Module.Finite.of_injective N1.subtype N1.subtype_injective
  letI n1NoZero : NoZeroSMulDivisors ℤ N1 := Submodule.noZeroSMulDivisors N1
  letI n1Free : Module.Free ℤ N1 := Module.free_of_finite_type_torsion_free'
  have hr1 : Module.finrank ℤ N1 = 1 := latticeFlag5_finrank b v hv hvL 1
  let N2 : Submodule ℤ L := latticeFlag5 b v 2
  letI n2Module : Module ℤ N2 := N2.module
  letI n2Finite : Module.Finite ℤ N2 := Module.Finite.of_injective N2.subtype N2.subtype_injective
  letI n2NoZero : NoZeroSMulDivisors ℤ N2 := Submodule.noZeroSMulDivisors N2
  letI n2Free : Module.Free ℤ N2 := Module.free_of_finite_type_torsion_free'
  have hr2 : Module.finrank ℤ N2 = 2 := latticeFlag5_finrank b v hv hvL 2
  let N3 : Submodule ℤ L := latticeFlag5 b v 3
  letI n3Module : Module ℤ N3 := N3.module
  letI n3Finite : Module.Finite ℤ N3 := Module.Finite.of_injective N3.subtype N3.subtype_injective
  letI n3NoZero : NoZeroSMulDivisors ℤ N3 := Submodule.noZeroSMulDivisors N3
  letI n3Free : Module.Free ℤ N3 := Module.free_of_finite_type_torsion_free'
  have hr3 : Module.finrank ℤ N3 = 3 := latticeFlag5_finrank b v hv hvL 3
  let N4 : Submodule ℤ L := latticeFlag5 b v 4
  letI n4Module : Module ℤ N4 := N4.module
  letI n4Finite : Module.Finite ℤ N4 := Module.Finite.of_injective N4.subtype N4.subtype_injective
  letI n4NoZero : NoZeroSMulDivisors ℤ N4 := Submodule.noZeroSMulDivisors N4
  letI n4Free : Module.Free ℤ N4 := Module.free_of_finite_type_torsion_free'
  have hr4 : Module.finrank ℤ N4 = 4 := latticeFlag5_finrank b v hv hvL 4
  have h12 : N1 ≤ N2 := fun _ hx => minimaFlag5_mono v 1 2 (by decide) hx
  let S12 : Submodule ℤ N2 := N1.comap N2.subtype
  letI s12Module : Module ℤ S12 := S12.module
  let e12 : S12 ≃ₗ[ℤ] N1 := Submodule.comapSubtypeEquivOfLe h12
  have h23 : N2 ≤ N3 := fun _ hx => minimaFlag5_mono v 2 3 (by decide) hx
  let S23 : Submodule ℤ N3 := N2.comap N3.subtype
  letI s23Module : Module ℤ S23 := S23.module
  let e23 : S23 ≃ₗ[ℤ] N2 := Submodule.comapSubtypeEquivOfLe h23
  have h34 : N3 ≤ N4 := fun _ hx => minimaFlag5_mono v 3 4 (by decide) hx
  let S34 : Submodule ℤ N4 := N3.comap N4.subtype
  letI s34Module : Module ℤ S34 := S34.module
  let e34 : S34 ≃ₗ[ℤ] N3 := Submodule.comapSubtypeEquivOfLe h34
  have hrL : Module.finrank ℤ L = 5 := by
    simpa using Module.finrank_eq_card_basis (b.restrictScalars ℤ)
  let a1 : @Basis (Fin 1) ℤ N1 _ _ n1Module := Module.finBasisOfFinrankEq ℤ N1 hr1
  let aS12 : @Basis (Fin 1) ℤ S12 _ _ s12Module := a1.map e12.symm
  obtain ⟨a2,ha2⟩ := JSP000334.saturated_integer_basis_extend S12 aS12 hr2
    (fun z hz x hx => latticeFlag5_saturated b v 1 z hz (x : L) hx)
  have he1 (i : Fin 1) : ((a2 i.castSucc : N2) : L) = (a1 i : L) := by
    simpa only [aS12,Basis.map_apply,e12,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N2 => (x : L)) (ha2 i)
  let aS23 : @Basis (Fin 2) ℤ S23 _ _ s23Module := a2.map e23.symm
  obtain ⟨a3,ha3⟩ := JSP000334.saturated_integer_basis_extend S23 aS23 hr3
    (fun z hz x hx => latticeFlag5_saturated b v 2 z hz (x : L) hx)
  have he2 (i : Fin 2) : ((a3 i.castSucc : N3) : L) = (a2 i : L) := by
    simpa only [aS23,Basis.map_apply,e23,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N3 => (x : L)) (ha3 i)
  let aS34 : @Basis (Fin 3) ℤ S34 _ _ s34Module := a3.map e34.symm
  obtain ⟨a4,ha4⟩ := JSP000334.saturated_integer_basis_extend S34 aS34 hr4
    (fun z hz x hx => latticeFlag5_saturated b v 3 z hz (x : L) hx)
  have he3 (i : Fin 3) : ((a4 i.castSucc : N4) : L) = (a3 i : L) := by
    simpa only [aS34,Basis.map_apply,e34,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N4 => (x : L)) (ha4 i)
  obtain ⟨c,hc⟩ := JSP000334.saturated_integer_basis_extend N4 a4 hrL (latticeFlag5_saturated b v 4)
  refine ⟨c,?_⟩
  intro k
  fin_cases k
  · simp [minimaFlag5,minimaPrefix5]
  · have heq : (fun i : Fin 1 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 1 => (((a1 i : N1) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) ((((hc (((i).castSucc).castSucc).castSucc).trans (he3 ((i).castSucc).castSucc)).trans (he2 (i).castSucc)).trans (he1 i))
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 1 a1
  · have heq : (fun i : Fin 2 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 2 => (((a2 i : N2) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) (((hc ((i).castSucc).castSucc).trans (he3 (i).castSucc)).trans (he2 i))
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 2 a2
  · have heq : (fun i : Fin 3 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 3 => (((a3 i : N3) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) ((hc (i).castSucc).trans (he3 i))
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 3 a3
  · have heq : (fun i : Fin 4 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 4 => (((a4 i : N4) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) (hc i)
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 4 a4

end
end M196LiteralCompoundFeasibility

open scoped BigOperators Matrix
open MeasureTheory
namespace M196LiteralCompoundFeasibility
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
end M196LiteralCompoundFeasibility

open scoped BigOperators Matrix
open MeasureTheory
namespace M196LiteralCompoundFeasibility
noncomputable section

def integerPoint5 {b : Basis (Fin 5) ℝ (Fin 5 → ℝ)}
    (c : Basis (Fin 5) ℤ (lattice5Span b)) (z : Fin 5 → ℤ) : Fin 5 → ℝ :=
  (c.equivFun.symm z : lattice5Span b)

theorem integerPoint5_coord {b : Basis (Fin 5) ℝ (Fin 5 → ℝ)}
    (c : Basis (Fin 5) ℤ (lattice5Span b)) (z : Fin 5 → ℤ) (i : Fin 5) :
    (c.ofZLatticeBasis ℝ _).repr (integerPoint5 c z) i = (z i : ℝ) := by
  rw [integerPoint5,Basis.ofZLatticeBasis_repr_apply]
  change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = (z i : ℝ)
  rw [LinearEquiv.apply_symm_apply]

theorem integerPoint5_outside {b : Basis (Fin 5) ℝ (Fin 5 → ℝ)}
    (c : Basis (Fin 5) ℤ (lattice5Span b)) (v : Fin 5 → Fin 5 → ℝ)
    (hadapt : ∀ k : Fin 5, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice5Span b) : Fin 5 → ℝ))) = minimaFlag5 v k)
    (z : Fin 5 → ℤ) (k : Fin 5) (hk : z k ≠ 0) : integerPoint5 c z ∉ minimaFlag5 v k := by
  let a := c.ofZLatticeBasis ℝ (lattice5Span b)
  have hle : minimaFlag5 v k ≤ LinearMap.ker (a.coord k) := by
    rw [← hadapt k]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change a.repr ((c (Fin.castLE (by omega) j) : lattice5Span b) : Fin 5 → ℝ) k = 0
    have hne : (Fin.castLE (by omega) j : Fin 5) ≠ k := by
      intro h
      have heq := congrArg Fin.val h
      change j.val = k.val at heq
      omega
    simp [a,Basis.ofZLatticeBasis_repr_apply,hne]
  intro h
  have hzero := hle h
  change a.repr (integerPoint5 c z) k = 0 at hzero
  rw [integerPoint5_coord] at hzero
  exact hk (by exact_mod_cast hzero)

theorem successive_minima5_product_volume_upper
    (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (e : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) :
    (∏ i, successiveRadius5 b e i) * volume.real {x | coordinateGauge5 e x ≤ 1} /
      ZLattice.covolume (lattice5Span b) ≤ (4 : ℝ)^5 := by
  obtain ⟨v,hv,hvL,hpos,hmono,hatt,hshort⟩ := exists_successive_minima5 b e
  obtain ⟨c,hc⟩ := exists_adapted_integer_basis5 b v hv hvL
  let a := c.ofZLatticeBasis ℝ (lattice5Span b)
  let F := a.equivFun.symm
  let f : (Fin 5 → ℝ) → ℝ := fun x => coordinateGauge5 e (F x)
  have hf : ∀ (r : ℝ) (x : Fin 5 → ℝ), f (r • x) = |r| * f x := by
    intro r x
    simp [f,coordinateGauge5,map_smul,norm_smul,Real.norm_eq_abs]
  have hp (z : Fin 5 → ℤ) : F (fun i => (z i : ℝ)) = integerPoint5 c z := by
    apply a.equivFun.injective
    ext i
    change (a.equivFun (a.equivFun.symm (fun i => (z i : ℝ)))) i = _
    rw [LinearEquiv.apply_symm_apply]
    exact (integerPoint5_coord c z i).symm
  have hbody : {x | f x ≤ 1} = a.equivFun '' {x | coordinateGauge5 e x ≤ 1} := by
    rw [LinearEquiv.image_eq_preimage]
    rfl
  have hconv : Convex ℝ {x | f x ≤ 1} := by
    simpa only [Metric.closedBall,dist_zero_right] using
      (convex_closedBall (0 : Fin 5 → ℝ) 1).linear_preimage (e.toLinearMap.comp F.toLinearMap)
  have hsymm : ∀ x, f (-x) = f x := by intro x; simp [f,coordinateGauge5,map_neg]
  have hu := Minkowski5.adapted_product_volume_upper f hf (successiveRadius5 b e) hpos hmono
    (fun z k hk _ => by
      change _ ≤ coordinateGauge5 e (F (fun i => (z i : ℝ)))
      rw [hp,← hatt k]
      exact hshort k _ (c.equivFun.symm z).property (integerPoint5_outside c v hc z k hk)) hsymm hconv
  have hvol : volume.real (a.equivFun '' {x | coordinateGauge5 e x ≤ 1}) =
      volume.real {x | coordinateGauge5 e x ≤ 1} / ZLattice.covolume (lattice5Span b) := by
    rw [measureReal_def,ZLattice.volume_image_eq_volume_div_covolume (lattice5Span b) c,
      ENNReal.toReal_div,ENNReal.toReal_ofReal (ZLattice.covolume_pos (lattice5Span b) volume).le]
    rfl
  rw [hbody,hvol] at hu
  simpa only [div_eq_mul_inv,mul_assoc] using hu

end
end M196LiteralCompoundFeasibility

open scoped BigOperators Matrix Topology
open MeasureTheory
namespace M196LiteralCompoundFeasibility
noncomputable section

theorem q_width_product_le_prime_powers5 (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 5 → ℝ) (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
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


def sourceLocalDetFactor5 (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) : ℝ :=
  (padicNorm 2 A₂.det : ℝ) * (padicNorm 3 A₃.det : ℝ)

theorem sourceLocalDetFactor5_pos (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) : 0 < sourceLocalDetFactor5 A₂ A₃ := by
  have hd₂ := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h₂)
  have hd₃ := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h₃)
  exact mul_pos
    (Rat.cast_pos.mpr ((IsAbsoluteValue.toAbsoluteValue (padicNorm 2)).pos_iff.mpr hd₂))
    (Rat.cast_pos.mpr ((IsAbsoluteValue.toAbsoluteValue (padicNorm 3)).pos_iff.mpr hd₃))

theorem sourceLattice5_covolume_width_lower (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    sourceLocalDetFactor5 A₂ A₃ * (∏ i, Q^c₀ i) ≤
      ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) := by
  let e₂ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i))
  let e₃ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i))
  obtain ⟨c⟩ := sourceLattice5_has_basis A₂ A₃ e₂ e₃
  have hlow := integerRealImage_padic_covolume_lower (sourceLattice5 A₂ A₃ e₂ e₃) c A₂ A₃ e₂ e₃
    (fun x hx => (lattice5_spec 2 A₂ e₂ x).mp hx.1)
    (fun x hx => (lattice5_spec 3 A₃ e₃ x).mp hx.2)
  have hf : 0 ≤ sourceLocalDetFactor5 A₂ A₃ := mul_nonneg
    (Rat.cast_nonneg.mpr (padicNorm.nonneg _)) (Rat.cast_nonneg.mpr (padicNorm.nonneg _))
  exact (mul_le_mul_of_nonneg_left (q_width_product_le_prime_powers5 Q hQ c₀ c₂ c₃ hb) hf).trans
    (by simpa only [sourceLocalDetFactor5,mul_assoc] using hlow)

theorem originalBody5_compact_convex (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) :
    IsCompact (originalBody5 L Q c₀) ∧ Convex ℝ (originalBody5 L Q c₀) := by
  let e := originalCoordinates5 L hL Q hQ c₀
  have he : originalBody5 L Q c₀ = e ⁻¹' Metric.closedBall (0 : Fin 5 → ℝ) 1 := by
    ext x
    rw [originalBody5_mem_iff L hL Q hQ c₀ x]
    simp only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,e]
  rw [he]
  exact ⟨e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _),
    (convex_closedBall (0 : Fin 5 → ℝ) 1).linear_preimage e.toLinearMap⟩

theorem originalBody5_symmetric (L : Matrix (Fin 5) (Fin 5) ℝ) (Q : ℝ) (c₀ : Fin 5 → ℝ) :
    ∀ x ∈ originalBody5 L Q c₀, -x ∈ originalBody5 L Q c₀ := by
  intro x hx i
  simpa only [Matrix.mulVec_neg,Pi.neg_apply,abs_neg] using hx i

theorem originalBody5_zero_interior (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) : 0 ∈ interior (originalBody5 L Q c₀) := by
  let e := originalCoordinates5 L hL Q hQ c₀
  have ho : IsOpen (e ⁻¹' Metric.ball (0 : Fin 5 → ℝ) 1) :=
    Metric.isOpen_ball.preimage e.toContinuousLinearEquiv.continuous
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ho.mem_nhds (by simp))
  intro x hx
  rw [originalBody5_mem_iff L hL Q hQ c₀ x]
  exact (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx : ‖e x‖ < 1).le

theorem originalBody5_volume_pos (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 5 → ℝ) : 0 < volume.real (originalBody5 L Q c₀) := by
  rw [originalBody5_volume L hL Q hQ]
  have hd : L.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL)
  exact div_pos (mul_pos (by norm_num) (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _))) (abs_pos.mpr hd)

end
end M196LiteralCompoundFeasibility

open scoped BigOperators Matrix
open MeasureTheory
namespace M196LiteralCompoundFeasibility
noncomputable section

instance originalSourceGroup5_isZLattice (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) :
    IsZLattice ℝ (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) := by
  change IsZLattice ℝ (integerRealImage (sourceLattice5 A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))))
  infer_instance


theorem scalar_product_comparison5 (W D A d l u : ℝ)
    (hW : 0 < W) (hD : 0 < D) (hd : 0 < d)
    (hl : l*W ≤ D) (hu : D ≤ u*W)
    (hdet : d*D ≤ 120*A*W) (hm : A*(32*W/d)/D ≤ 1024) :
    d*l/120 ≤ A ∧ A ≤ 32*d*u := by
  have hlo : (d*l)*W ≤ (120*A)*W := by
    calc
      (d*l)*W = d*(l*W) := by ring
      _ ≤ d*D := mul_le_mul_of_nonneg_left hl hd.le
      _ ≤ (120*A)*W := hdet
  have hlc := (mul_le_mul_right hW).mp hlo
  have hm' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hD).mp hm) hd.le
  have he : A*(32*W/d)*d = (A*32)*W := by field_simp; ring
  rw [he] at hm'
  have hhi : (A*32)*W ≤ (1024*d*u)*W := hm'.trans (by
    convert mul_le_mul_of_nonneg_left hu (show 0 ≤ 1024*d by positivity) using 1 <;> ring)
  have hhc := (mul_le_mul_right hW).mp hhi
  constructor <;> nlinarith

theorem scalar_volume_ratio5 (W D d l u : ℝ) (hW : 0 < W) (hD : 0 < D)
    (hd : 0 < d) (hl : 0 < l) (hu : 0 < u) (hlo : l*W ≤ D) (hhi : D ≤ u*W) :
    32/(d*u) ≤ (32*W/d)/D ∧ (32*W/d)/D ≤ 32/(d*l) := by
  have hv : 0 ≤ 32*W/d := by positivity
  constructor
  · calc
      _ = (32*W/d)/(u*W) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left hv hD hhi
  · calc
      _ ≤ (32*W/d)/(l*W) := div_le_div_of_nonneg_left hv (mul_pos hl hW) hlo
      _ = _ := by field_simp; ring

theorem sourceMinima5_product_volume_upper (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) :
    (∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) * volume.real (originalBody5 L Q c₀) /
      ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ≤ (4 : ℝ)^5 := by
  let b := sourceRealBasis5 A₂ A₃ (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hu := successive_minima5_product_volume_upper b (originalCoordinates5 L hL Q hQ c₀)
  have hbody : {x | coordinateGauge5 (originalCoordinates5 L hL Q hQ c₀) x ≤ 1} = originalBody5 L Q c₀ := by
    ext x
    exact (originalBody5_mem_iff L hL Q hQ c₀ x).symm
  have heq : sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = successiveRadius5 b (originalCoordinates5 L hL Q hQ c₀) :=
    funext (sourceMinima5_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  rw [← heq,hbody,sourceRealBasis5_span] at hu
  exact hu

theorem source_original_uniform_minima_two_sided5
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c5 C5 : ℝ, 0 < c5 ∧ 0 < C5 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        c5 ≤ (∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
          (∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤ C5 := by
  obtain ⟨K,hK,hupper⟩ := sourceLattice5_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  have hd : 0 < |L.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL))
  have hl := sourceLocalDetFactor5_pos A₂ A₃ h₂ h₃
  refine ⟨|L.det| * sourceLocalDetFactor5 A₂ A₃/120,32*|L.det| * ((K : ℝ)*7776),by positivity,by positivity,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let G := originalSourceGroup5 A₂ A₃ Q c₂ c₃
  let W := ∏ i, Q^c₀ i
  have hW : 0 < W := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  have hD : 0 < ZLattice.covolume (integerRealImage G) := ZLattice.covolume_pos _ volume
  obtain ⟨u,hu,hpos,hmono,hatt,hpoint⟩ := exists_sourceMinima5_attaining A₂ A₃ L hL Q hQ c₀ c₂ c₃
  obtain ⟨c⟩ := sourceLattice5_has_basis A₂ A₃
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ i)))
  have hdet := integerRealImage_frame_product_lower G c L u hu (fun i => Q^c₀ i)
    (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃) hpoint
  have hcovlo := sourceLattice5_covolume_width_lower A₂ A₃ Q hQ c₀ c₂ c₃ hb
  have hcovhi := (div_le_iff₀ hW).mp (hupper Q hQ c₀ c₂ c₃ hc₂ hc₃ hb)
  have hm := sourceMinima5_product_volume_upper A₂ A₃ L hL Q hQ c₀ c₂ c₃
  rw [originalBody5_volume L hL Q hQ] at hm
  exact scalar_product_comparison5 W _ _ |L.det| (sourceLocalDetFactor5 A₂ A₃) ((K : ℝ)*7776)
    hW hD hd hcovlo hcovhi (by simpa using hdet) (by norm_num only [show (4 : ℝ)^5 = 1024 by norm_num] at hm; exact hm)

theorem sourceLattice5_full_rank (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : Module.finrank ℤ (sourceLattice5 A₂ A₃ e₂ e₃) = 5 := by
  obtain ⟨c⟩ := sourceLattice5_has_basis A₂ A₃ e₂ e₃
  simpa using Module.finrank_eq_card_basis c

theorem sourceLattice5_index_pos (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (e₂ e₃ : Fin 5 → ℕ) : 0 < (sourceLattice5 A₂ A₃ e₂ e₃).index := by
  have h := ZLattice.covolume_pos (integerRealImage (sourceLattice5 A₂ A₃ e₂ e₃)) volume
  rw [sourceLattice5_covolume_index] at h
  exact_mod_cast h

theorem source_original_uniform_volume_ratio5
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        a ≤ volume.real (originalBody5 L Q c₀) /
          ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ∧
        volume.real (originalBody5 L Q c₀) /
          ZLattice.covolume (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) ≤ b := by
  obtain ⟨K,hK,hupper⟩ := sourceLattice5_uniform_normalized_covolume_upper A₂ A₃ h₂ h₃
  have hd : 0 < |L.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hL))
  have hl := sourceLocalDetFactor5_pos A₂ A₃ h₂ h₃
  refine ⟨32/(|L.det| * ((K : ℝ)*7776)),32/(|L.det| * sourceLocalDetFactor5 A₂ A₃),
    by positivity,by positivity,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let W := ∏ i, Q^c₀ i
  have hW : 0 < W := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith) _)
  have hD := ZLattice.covolume_pos (integerRealImage (originalSourceGroup5 A₂ A₃ Q c₂ c₃)) volume
  rw [originalBody5_volume L hL Q hQ]
  exact scalar_volume_ratio5 W _ |L.det| (sourceLocalDetFactor5 A₂ A₃) ((K : ℝ)*7776)
    hW hD hd hl (by positivity)
    (sourceLattice5_covolume_width_lower A₂ A₃ Q hQ c₀ c₂ c₃ hb)
    ((div_le_iff₀ hW).mp (hupper Q hQ c₀ c₂ c₃ hc₂ hc₃ hb))

end
end M196LiteralCompoundFeasibility

open scoped BigOperators Classical Matrix
noncomputable section
namespace M196LiteralCompoundFeasibility.OriginalVariableGap5

def originalSourceSolution5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ)
    (Q delta : ℝ) (x : Fin 5 → ℤ) : Prop :=
  x ≠ 0 ∧ 1 < Q ∧ 0 < delta ∧
    (∀ i, |(L *ᵥ integerReal x) i| ≤ Q^(c0 i-delta)) ∧
    (∀ i, (padicNorm 2 ((A2 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c2 i)) ∧
    (∀ i, (padicNorm 3 ((A3 *ᵥ (fun j => (x j : ℚ))) i) : ℝ) ≤ Q^(c3 i))

def originalRothProperty5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ B : ℝ, ∀ Q : ℝ, B < Q →
    ¬ ∃ x : Fin 5 → ℤ, originalSourceSolution5 A2 A3 L c0 c2 c3 Q delta x

theorem nonroth_iff_unbounded_solutions5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ) :
    ¬ originalRothProperty5 A2 A3 L c0 c2 c3 ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ¬ BddAbove {Q : ℝ | ∃ x : Fin 5 → ℤ,
          originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x} := by
  constructor
  · intro hn
    unfold originalRothProperty5 at hn
    push_neg at hn
    obtain ⟨epsilon,he,hsol⟩ := hn
    refine ⟨epsilon,he,not_bddAbove_iff.mpr ?_⟩
    intro B
    obtain ⟨Q,hBQ,x,hx⟩ := hsol B
    exact ⟨Q,⟨x,hx⟩,hBQ⟩
  · rintro ⟨epsilon,he,hU⟩ hR
    obtain ⟨B,hB⟩ := hR epsilon he
    obtain ⟨Q,⟨x,hx⟩,hBQ⟩ := not_bddAbove_iff.mp hU B
    exact hB Q hBQ ⟨x,hx⟩


theorem source_solution_lattice5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (c0 c2 c3 : Fin 5 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (Q epsilon : ℝ) (x : Fin 5 → ℤ)
    (hs : originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x) :
    x ∈ originalSourceGroup5 A2 A3 Q c2 c3 := by
  change (x ∈ lattice5 2 A2 (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))) ∧
    (x ∈ lattice5 3 A3 (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))))
  constructor
  · apply (lattice5_spec 2 A2 _ x).mpr
    intro i
    simpa only [zpow_neg,zpow_natCast] using
      (padic_rpow_ceil42 2 Q (c2 i) hs.2.1 (hc2 i) _).mp (hs.2.2.2.2.1 i)
  · apply (lattice5_spec 3 A3 _ x).mpr
    intro i
    simpa only [zpow_neg,zpow_natCast] using
      (padic_rpow_ceil42 3 Q (c3 i) hs.2.1 (hc3 i) _).mp (hs.2.2.2.2.2 i)

theorem source_solution_gauge5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (Q epsilon : ℝ) (hQ : 1 < Q) (x : Fin 5 → ℤ)
    (hs : originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x) :
    coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x) ≤ Q^(-epsilon) := by
  apply (originalCoordinates5_bounds L hL Q hQ c0 (integerReal x) _).mpr
  intro i
  have he : Q^(c0 i-epsilon) = Q^(-epsilon)*Q^(c0 i) := by
    rw [← Real.rpow_add (lt_trans zero_lt_one hQ)]
    congr 1
    ring
  rw [← he]
  exact hs.2.2.2.1 i

theorem source_first_minimum_le_gauge5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (Q : ℝ) (hQ : 1 < Q) (x : Fin 5 → ℤ) (hx : x ≠ 0)
    (hm : x ∈ originalSourceGroup5 A2 A3 Q c2 c3) :
    sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 ≤
      coordinateGauge5 (originalCoordinates5 L hL Q hQ c0) (integerReal x) := by
  have hn : integerReal x ≠ 0 := by
    intro hz
    exact hx (integerReal_injective (hz.trans integerReal.map_zero.symm))
  have hi : LinearIndependent ℝ (fun _ : Fin 1 => integerReal x) :=
    (linearIndependent_unique_iff _).mpr hn
  apply (sourceMinima5_radius_set_properties A2 A3 L hL Q hQ c0 c2 c3 0).2.2.2
  exact ⟨fun _ : Fin 1 => integerReal x,hi,fun _ => ⟨x,hm,rfl⟩,fun _ => le_rfl⟩

theorem source_solution_small_first5 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 5 → ℝ)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (Q epsilon : ℝ) (hQ : 1 < Q) (x : Fin 5 → ℤ)
    (hs : originalSourceSolution5 A2 A3 L c0 c2 c3 Q epsilon x) :
    sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 0 < Q^(-(epsilon/2)) := by
  have hm := source_solution_lattice5 A2 A3 L c0 c2 c3 hc2 hc3 Q epsilon x hs
  have hfirst := source_first_minimum_le_gauge5 A2 A3 L hL c0 c2 c3 Q hQ x hs.1 hm
  have hg := source_solution_gauge5 A2 A3 L hL c0 c2 c3 Q epsilon hQ x hs
  exact (hfirst.trans hg).trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hQ (by linarith [hs.2.2.1]))


theorem finite5_adjacent_gap (lam : Fin 5 → ℝ)
    (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (c Q s : ℝ) (hprod : c ≤ ∏ i, lam i) (hQ : 1 < Q)
    (hfirst : lam 0 < Q^(-s)) (hcut : Q^(-s) < c) :
    ∃ j : Fin 4, lam j.castSucc < lam j.succ * Q^(-(s/5)) := by
  by_contra hn
  push_neg at hn
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  let r : ℝ := Q^(s/5)
  have hr : 0 < r := Real.rpow_pos_of_pos hQ0 _
  have hcancel : Q^(-(s/5))*r = 1 := by
    dsimp [r]
    rw [← Real.rpow_add hQ0]
    simp
  have hstep (j : Fin 4) : lam j.succ ≤ lam j.castSucc * r := by
    have hh := mul_le_mul_of_nonneg_right (hn j) hr.le
    simpa only [mul_assoc,hcancel,mul_one] using hh
  have h1 : lam 1 ≤ lam 0*r := hstep 0
  have h2 : lam 2 ≤ (lam 0*r)*r := (hstep 1).trans (mul_le_mul_of_nonneg_right h1 hr.le)
  have h3 : lam 3 ≤ ((lam 0*r)*r)*r := (hstep 2).trans (mul_le_mul_of_nonneg_right h2 hr.le)
  have h4 : lam 4 ≤ (((lam 0*r)*r)*r)*r := (hstep 3).trans (mul_le_mul_of_nonneg_right h3 hr.le)
  have he : (((Q^(-s)*r)*r)*r)*r = Q^(-(s/5)) := by
    dsimp [r]
    rw [← Real.rpow_add hQ0,← Real.rpow_add hQ0,← Real.rpow_add hQ0,← Real.rpow_add hQ0]
    congr 1
    ring
  have hlast : lam 4 < Q^(-(s/5)) := by
    rw [← he]
    exact h4.trans_lt (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hfirst hr) hr) hr) hr)
  have hprod' : (∏ i, lam i) ≤ (lam 4)^5 := by
    calc
      _ ≤ ∏ _i : Fin 5, lam 4 := Finset.prod_le_prod (fun i _ => (hp i).le) (fun i _ => hm (Fin.le_last i))
      _ = _ := by simp
  have hpow : (Q^(-(s/5)))^5 = Q^(-s) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ0.le]
    congr 1
    norm_num
  have hsmall : (lam 4)^5 < Q^(-s) := by
    rw [← hpow]
    exact pow_lt_pow_left₀ hlast (hp 4).le (by decide)
  exact (not_lt_of_ge hprod) (hprod'.trans_lt (hsmall.trans hcut))

theorem finite4_unbounded_cover (U : Set ℝ) (E : Fin 4 → Set ℝ)
    (hU : ¬ BddAbove U) (hcover : ∀ Q ∈ U, ∃ j, Q ∈ E j) : ∃ j, ¬ BddAbove (E j) := by
  by_contra hn
  push_neg at hn
  have hb : BddAbove (⋃ j ∈ (Set.univ : Set (Fin 4)), E j) :=
    Set.finite_univ.bddAbove_biUnion.mpr (fun j _ => hn j)
  apply hU
  apply hb.mono
  intro Q hQ
  obtain ⟨j,hj⟩ := hcover Q hQ
  exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Set.mem_univ j,hj⟩⟩

theorem first_minimum_cutoff5 (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    ∃ B : ℝ, 1 < B ∧ ∀ Q : ℝ, B < Q → Q^(-s) < c :=
  OriginalVariableGap4.first_minimum_cutoff4 c s hc hs

theorem matrixUnit5 {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)


end M196LiteralCompoundFeasibility.OriginalVariableGap5

namespace M196LiteralCompoundFeasibility
theorem literal_uniform_product5
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ c5 C5 : ℝ, 0 < c5 ∧ 0 < C5 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i+c₂ i+c₃ i) = 0) →
        c5 ≤ (∏ i : Fin 5, (sInf {r : ℝ | ∃ u : Fin (i.val+1) → (Fin 5 → ℝ), LinearIndependent ℝ u ∧
          (∀ k, u k ∈ integerRealImage (sourceLattice5 A₂ A₃
            (fun k => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ k)))
            (fun k => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ k))))) ∧
          ∀ k, ‖(fun s => (L *ᵥ u k) s / Q^(c₀ s))‖ ≤ r})) ∧
          (∏ i : Fin 5, (sInf {r : ℝ | ∃ u : Fin (i.val+1) → (Fin 5 → ℝ), LinearIndependent ℝ u ∧
          (∀ k, u k ∈ integerRealImage (sourceLattice5 A₂ A₃
            (fun k => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ k)))
            (fun k => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ k))))) ∧
          ∀ k, ‖(fun s => (L *ᵥ u k) s / Q^(c₀ s))‖ ≤ r})) ≤ C5 := by
  exact source_original_uniform_minima_two_sided5 A₂ A₃ L h₂ h₃ hL
end M196LiteralCompoundFeasibility

#check M196LiteralCompoundFeasibility.Minkowski5.dyadicBasis
#print M196LiteralCompoundFeasibility.Minkowski5.dyadicBasis
#print axioms M196LiteralCompoundFeasibility.Minkowski5.dyadicBasis

#check M196LiteralCompoundFeasibility.Minkowski5.dyadic_lattice_coordinates
#print M196LiteralCompoundFeasibility.Minkowski5.dyadic_lattice_coordinates
#print axioms M196LiteralCompoundFeasibility.Minkowski5.dyadic_lattice_coordinates

#check M196LiteralCompoundFeasibility.Minkowski5.dyadic_lattice_avoids
#print M196LiteralCompoundFeasibility.Minkowski5.dyadic_lattice_avoids
#print axioms M196LiteralCompoundFeasibility.Minkowski5.dyadic_lattice_avoids

#check M196LiteralCompoundFeasibility.Minkowski5.dyadic_fundamental_volume
#print M196LiteralCompoundFeasibility.Minkowski5.dyadic_fundamental_volume
#print axioms M196LiteralCompoundFeasibility.Minkowski5.dyadic_fundamental_volume

#check M196LiteralCompoundFeasibility.Minkowski5.dyadic_volume_bound
#print M196LiteralCompoundFeasibility.Minkowski5.dyadic_volume_bound
#print axioms M196LiteralCompoundFeasibility.Minkowski5.dyadic_volume_bound

#check M196LiteralCompoundFeasibility.Minkowski5.exists_dyadic_exponents
#print M196LiteralCompoundFeasibility.Minkowski5.exists_dyadic_exponents
#print axioms M196LiteralCompoundFeasibility.Minkowski5.exists_dyadic_exponents

#check M196LiteralCompoundFeasibility.Minkowski5.normalized_product_volume_upper
#print M196LiteralCompoundFeasibility.Minkowski5.normalized_product_volume_upper
#print axioms M196LiteralCompoundFeasibility.Minkowski5.normalized_product_volume_upper

#check M196LiteralCompoundFeasibility.Minkowski5.homogeneous_sublevel_dilate
#print M196LiteralCompoundFeasibility.Minkowski5.homogeneous_sublevel_dilate
#print axioms M196LiteralCompoundFeasibility.Minkowski5.homogeneous_sublevel_dilate

#check M196LiteralCompoundFeasibility.Minkowski5.adapted_product_volume_upper
#print M196LiteralCompoundFeasibility.Minkowski5.adapted_product_volume_upper
#print axioms M196LiteralCompoundFeasibility.Minkowski5.adapted_product_volume_upper

#check M196LiteralCompoundFeasibility.row5
#print M196LiteralCompoundFeasibility.row5
#print axioms M196LiteralCompoundFeasibility.row5

#check M196LiteralCompoundFeasibility.lattice5
#print M196LiteralCompoundFeasibility.lattice5
#print axioms M196LiteralCompoundFeasibility.lattice5

#check M196LiteralCompoundFeasibility.lattice5_spec
#print M196LiteralCompoundFeasibility.lattice5_spec
#print axioms M196LiteralCompoundFeasibility.lattice5_spec

#check M196LiteralCompoundFeasibility.sourceLattice5
#print M196LiteralCompoundFeasibility.sourceLattice5
#print axioms M196LiteralCompoundFeasibility.sourceLattice5

#check M196LiteralCompoundFeasibility.sourceLattice5_multiple
#print M196LiteralCompoundFeasibility.sourceLattice5_multiple
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_multiple

#check M196LiteralCompoundFeasibility.sourceLattice5_has_basis
#print M196LiteralCompoundFeasibility.sourceLattice5_has_basis
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_has_basis

#check M196LiteralCompoundFeasibility.sourceLattice5_isZLattice
#print M196LiteralCompoundFeasibility.sourceLattice5_isZLattice
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_isZLattice

#check M196LiteralCompoundFeasibility.sourceLattice5_covolume_det
#print M196LiteralCompoundFeasibility.sourceLattice5_covolume_det
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_covolume_det

#check M196LiteralCompoundFeasibility.sourceLattice5_covolume_index
#print M196LiteralCompoundFeasibility.sourceLattice5_covolume_index
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_covolume_index

#check M196LiteralCompoundFeasibility.integer_span5_index_det
#print M196LiteralCompoundFeasibility.integer_span5_index_det
#print axioms M196LiteralCompoundFeasibility.integer_span5_index_det

#check M196LiteralCompoundFeasibility.integer_matrix_index_upper5
#print M196LiteralCompoundFeasibility.integer_matrix_index_upper5
#print axioms M196LiteralCompoundFeasibility.integer_matrix_index_upper5

#check M196LiteralCompoundFeasibility.inverse_integral_frame5
#print M196LiteralCompoundFeasibility.inverse_integral_frame5
#print axioms M196LiteralCompoundFeasibility.inverse_integral_frame5

#check M196LiteralCompoundFeasibility.lattice5_index_upper
#print M196LiteralCompoundFeasibility.lattice5_index_upper
#print axioms M196LiteralCompoundFeasibility.lattice5_index_upper

#check M196LiteralCompoundFeasibility.sourceLattice5_uniform_index_upper
#print M196LiteralCompoundFeasibility.sourceLattice5_uniform_index_upper
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_uniform_index_upper

#check M196LiteralCompoundFeasibility.q_prime_powers_product_upper5
#print M196LiteralCompoundFeasibility.q_prime_powers_product_upper5
#print axioms M196LiteralCompoundFeasibility.q_prime_powers_product_upper5

#check M196LiteralCompoundFeasibility.q_prime_powers_normalized_upper5
#print M196LiteralCompoundFeasibility.q_prime_powers_normalized_upper5
#print axioms M196LiteralCompoundFeasibility.q_prime_powers_normalized_upper5

#check M196LiteralCompoundFeasibility.sourceLattice5_uniform_normalized_covolume_upper
#print M196LiteralCompoundFeasibility.sourceLattice5_uniform_normalized_covolume_upper
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_uniform_normalized_covolume_upper

#check M196LiteralCompoundFeasibility.lattice5Span
#print M196LiteralCompoundFeasibility.lattice5Span
#print axioms M196LiteralCompoundFeasibility.lattice5Span

#check M196LiteralCompoundFeasibility.coordinateGauge5
#print M196LiteralCompoundFeasibility.coordinateGauge5
#print axioms M196LiteralCompoundFeasibility.coordinateGauge5

#check M196LiteralCompoundFeasibility.lattice5Span_gauge_ball_finite
#print M196LiteralCompoundFeasibility.lattice5Span_gauge_ball_finite
#print axioms M196LiteralCompoundFeasibility.lattice5Span_gauge_ball_finite

#check M196LiteralCompoundFeasibility.exists_shortest_lattice5Span_vector_outside
#print M196LiteralCompoundFeasibility.exists_shortest_lattice5Span_vector_outside
#print axioms M196LiteralCompoundFeasibility.exists_shortest_lattice5Span_vector_outside

#check M196LiteralCompoundFeasibility.successiveRadius5
#print M196LiteralCompoundFeasibility.successiveRadius5
#print axioms M196LiteralCompoundFeasibility.successiveRadius5

#check M196LiteralCompoundFeasibility.independent_family_escapes_subspace5
#print M196LiteralCompoundFeasibility.independent_family_escapes_subspace5
#print axioms M196LiteralCompoundFeasibility.independent_family_escapes_subspace5

#check M196LiteralCompoundFeasibility.minimaPrefix5
#print M196LiteralCompoundFeasibility.minimaPrefix5
#print axioms M196LiteralCompoundFeasibility.minimaPrefix5

#check M196LiteralCompoundFeasibility.minimaPrefix5_snoc_castSucc
#print M196LiteralCompoundFeasibility.minimaPrefix5_snoc_castSucc
#print axioms M196LiteralCompoundFeasibility.minimaPrefix5_snoc_castSucc

#check M196LiteralCompoundFeasibility.minimaPrefix5_snoc_last
#print M196LiteralCompoundFeasibility.minimaPrefix5_snoc_last
#print axioms M196LiteralCompoundFeasibility.minimaPrefix5_snoc_last

#check M196LiteralCompoundFeasibility.exists_greedy_prefix5
#print M196LiteralCompoundFeasibility.exists_greedy_prefix5
#print axioms M196LiteralCompoundFeasibility.exists_greedy_prefix5

#check M196LiteralCompoundFeasibility.minimaPrefix5_not_mem
#print M196LiteralCompoundFeasibility.minimaPrefix5_not_mem
#print axioms M196LiteralCompoundFeasibility.minimaPrefix5_not_mem

#check M196LiteralCompoundFeasibility.minimaPrefix5_finrank
#print M196LiteralCompoundFeasibility.minimaPrefix5_finrank
#print axioms M196LiteralCompoundFeasibility.minimaPrefix5_finrank

#check M196LiteralCompoundFeasibility.exists_successive_minima5
#print M196LiteralCompoundFeasibility.exists_successive_minima5
#print axioms M196LiteralCompoundFeasibility.exists_successive_minima5

#check M196LiteralCompoundFeasibility.minimaFlag5
#print M196LiteralCompoundFeasibility.minimaFlag5
#print axioms M196LiteralCompoundFeasibility.minimaFlag5

#check M196LiteralCompoundFeasibility.minimaFlag5_finrank
#print M196LiteralCompoundFeasibility.minimaFlag5_finrank
#print axioms M196LiteralCompoundFeasibility.minimaFlag5_finrank

#check M196LiteralCompoundFeasibility.minimaFlag5_mono
#print M196LiteralCompoundFeasibility.minimaFlag5_mono
#print axioms M196LiteralCompoundFeasibility.minimaFlag5_mono

#check M196LiteralCompoundFeasibility.latticeFlag5
#print M196LiteralCompoundFeasibility.latticeFlag5
#print axioms M196LiteralCompoundFeasibility.latticeFlag5

#check M196LiteralCompoundFeasibility.flagLattice5
#print M196LiteralCompoundFeasibility.flagLattice5
#print axioms M196LiteralCompoundFeasibility.flagLattice5

#check M196LiteralCompoundFeasibility.latticeFlag5_saturated
#print M196LiteralCompoundFeasibility.latticeFlag5_saturated
#print axioms M196LiteralCompoundFeasibility.latticeFlag5_saturated

#check M196LiteralCompoundFeasibility.latticeFlag5_equiv_flagLattice5
#print M196LiteralCompoundFeasibility.latticeFlag5_equiv_flagLattice5
#print axioms M196LiteralCompoundFeasibility.latticeFlag5_equiv_flagLattice5

#check M196LiteralCompoundFeasibility.flagLattice5_discrete
#print M196LiteralCompoundFeasibility.flagLattice5_discrete
#print axioms M196LiteralCompoundFeasibility.flagLattice5_discrete

#check M196LiteralCompoundFeasibility.flagLattice5_isZLattice
#print M196LiteralCompoundFeasibility.flagLattice5_isZLattice
#print axioms M196LiteralCompoundFeasibility.flagLattice5_isZLattice

#check M196LiteralCompoundFeasibility.latticeFlag5_finrank
#print M196LiteralCompoundFeasibility.latticeFlag5_finrank
#print axioms M196LiteralCompoundFeasibility.latticeFlag5_finrank

#check M196LiteralCompoundFeasibility.latticeFlag5_basis_real_span
#print M196LiteralCompoundFeasibility.latticeFlag5_basis_real_span
#print axioms M196LiteralCompoundFeasibility.latticeFlag5_basis_real_span

#check M196LiteralCompoundFeasibility.exists_adapted_integer_basis5
#print M196LiteralCompoundFeasibility.exists_adapted_integer_basis5
#print axioms M196LiteralCompoundFeasibility.exists_adapted_integer_basis5

#check M196LiteralCompoundFeasibility.weightedCoordinates5
#print M196LiteralCompoundFeasibility.weightedCoordinates5
#print axioms M196LiteralCompoundFeasibility.weightedCoordinates5

#check M196LiteralCompoundFeasibility.originalFormEquiv5
#print M196LiteralCompoundFeasibility.originalFormEquiv5
#print axioms M196LiteralCompoundFeasibility.originalFormEquiv5

#check M196LiteralCompoundFeasibility.originalFormEquiv5_apply
#print M196LiteralCompoundFeasibility.originalFormEquiv5_apply
#print axioms M196LiteralCompoundFeasibility.originalFormEquiv5_apply

#check M196LiteralCompoundFeasibility.originalCoordinates5
#print M196LiteralCompoundFeasibility.originalCoordinates5
#print axioms M196LiteralCompoundFeasibility.originalCoordinates5

#check M196LiteralCompoundFeasibility.originalBody5
#print M196LiteralCompoundFeasibility.originalBody5
#print axioms M196LiteralCompoundFeasibility.originalBody5

#check M196LiteralCompoundFeasibility.originalCoordinates5_bounds
#print M196LiteralCompoundFeasibility.originalCoordinates5_bounds
#print axioms M196LiteralCompoundFeasibility.originalCoordinates5_bounds

#check M196LiteralCompoundFeasibility.originalBody5_mem_iff
#print M196LiteralCompoundFeasibility.originalBody5_mem_iff
#print axioms M196LiteralCompoundFeasibility.originalBody5_mem_iff

#check M196LiteralCompoundFeasibility.sourceRealBasis5
#print M196LiteralCompoundFeasibility.sourceRealBasis5
#print axioms M196LiteralCompoundFeasibility.sourceRealBasis5

#check M196LiteralCompoundFeasibility.sourceRealBasis5_span
#print M196LiteralCompoundFeasibility.sourceRealBasis5_span
#print axioms M196LiteralCompoundFeasibility.sourceRealBasis5_span

#check M196LiteralCompoundFeasibility.originalSourceGroup5
#print M196LiteralCompoundFeasibility.originalSourceGroup5
#print axioms M196LiteralCompoundFeasibility.originalSourceGroup5

#check M196LiteralCompoundFeasibility.sourceMinima5
#print M196LiteralCompoundFeasibility.sourceMinima5
#print axioms M196LiteralCompoundFeasibility.sourceMinima5

#check M196LiteralCompoundFeasibility.sourceMinima5_eq_radius
#print M196LiteralCompoundFeasibility.sourceMinima5_eq_radius
#print axioms M196LiteralCompoundFeasibility.sourceMinima5_eq_radius

#check M196LiteralCompoundFeasibility.exists_sourceMinima5_attaining
#print M196LiteralCompoundFeasibility.exists_sourceMinima5_attaining
#print axioms M196LiteralCompoundFeasibility.exists_sourceMinima5_attaining

#check M196LiteralCompoundFeasibility.sourceMinima5_admissible
#print M196LiteralCompoundFeasibility.sourceMinima5_admissible
#print axioms M196LiteralCompoundFeasibility.sourceMinima5_admissible

#check M196LiteralCompoundFeasibility.sourceMinima5_radius_set_properties
#print M196LiteralCompoundFeasibility.sourceMinima5_radius_set_properties
#print axioms M196LiteralCompoundFeasibility.sourceMinima5_radius_set_properties

#check M196LiteralCompoundFeasibility.sourceMinima5_pos_mono
#print M196LiteralCompoundFeasibility.sourceMinima5_pos_mono
#print axioms M196LiteralCompoundFeasibility.sourceMinima5_pos_mono

#check M196LiteralCompoundFeasibility.weightedCoordinates5_det
#print M196LiteralCompoundFeasibility.weightedCoordinates5_det
#print axioms M196LiteralCompoundFeasibility.weightedCoordinates5_det

#check M196LiteralCompoundFeasibility.originalCoordinates5_det
#print M196LiteralCompoundFeasibility.originalCoordinates5_det
#print axioms M196LiteralCompoundFeasibility.originalCoordinates5_det

#check M196LiteralCompoundFeasibility.originalBody5_volume
#print M196LiteralCompoundFeasibility.originalBody5_volume
#print axioms M196LiteralCompoundFeasibility.originalBody5_volume

#check M196LiteralCompoundFeasibility.integerPoint5
#print M196LiteralCompoundFeasibility.integerPoint5
#print axioms M196LiteralCompoundFeasibility.integerPoint5

#check M196LiteralCompoundFeasibility.integerPoint5_coord
#print M196LiteralCompoundFeasibility.integerPoint5_coord
#print axioms M196LiteralCompoundFeasibility.integerPoint5_coord

#check M196LiteralCompoundFeasibility.integerPoint5_outside
#print M196LiteralCompoundFeasibility.integerPoint5_outside
#print axioms M196LiteralCompoundFeasibility.integerPoint5_outside

#check M196LiteralCompoundFeasibility.successive_minima5_product_volume_upper
#print M196LiteralCompoundFeasibility.successive_minima5_product_volume_upper
#print axioms M196LiteralCompoundFeasibility.successive_minima5_product_volume_upper

#check M196LiteralCompoundFeasibility.q_width_product_le_prime_powers5
#print M196LiteralCompoundFeasibility.q_width_product_le_prime_powers5
#print axioms M196LiteralCompoundFeasibility.q_width_product_le_prime_powers5

#check M196LiteralCompoundFeasibility.sourceLocalDetFactor5
#print M196LiteralCompoundFeasibility.sourceLocalDetFactor5
#print axioms M196LiteralCompoundFeasibility.sourceLocalDetFactor5

#check M196LiteralCompoundFeasibility.sourceLocalDetFactor5_pos
#print M196LiteralCompoundFeasibility.sourceLocalDetFactor5_pos
#print axioms M196LiteralCompoundFeasibility.sourceLocalDetFactor5_pos

#check M196LiteralCompoundFeasibility.sourceLattice5_covolume_width_lower
#print M196LiteralCompoundFeasibility.sourceLattice5_covolume_width_lower
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_covolume_width_lower

#check M196LiteralCompoundFeasibility.originalBody5_compact_convex
#print M196LiteralCompoundFeasibility.originalBody5_compact_convex
#print axioms M196LiteralCompoundFeasibility.originalBody5_compact_convex

#check M196LiteralCompoundFeasibility.originalBody5_symmetric
#print M196LiteralCompoundFeasibility.originalBody5_symmetric
#print axioms M196LiteralCompoundFeasibility.originalBody5_symmetric

#check M196LiteralCompoundFeasibility.originalBody5_zero_interior
#print M196LiteralCompoundFeasibility.originalBody5_zero_interior
#print axioms M196LiteralCompoundFeasibility.originalBody5_zero_interior

#check M196LiteralCompoundFeasibility.originalBody5_volume_pos
#print M196LiteralCompoundFeasibility.originalBody5_volume_pos
#print axioms M196LiteralCompoundFeasibility.originalBody5_volume_pos

#check M196LiteralCompoundFeasibility.originalSourceGroup5_isZLattice
#print M196LiteralCompoundFeasibility.originalSourceGroup5_isZLattice
#print axioms M196LiteralCompoundFeasibility.originalSourceGroup5_isZLattice

#check M196LiteralCompoundFeasibility.scalar_product_comparison5
#print M196LiteralCompoundFeasibility.scalar_product_comparison5
#print axioms M196LiteralCompoundFeasibility.scalar_product_comparison5

#check M196LiteralCompoundFeasibility.scalar_volume_ratio5
#print M196LiteralCompoundFeasibility.scalar_volume_ratio5
#print axioms M196LiteralCompoundFeasibility.scalar_volume_ratio5

#check M196LiteralCompoundFeasibility.sourceMinima5_product_volume_upper
#print M196LiteralCompoundFeasibility.sourceMinima5_product_volume_upper
#print axioms M196LiteralCompoundFeasibility.sourceMinima5_product_volume_upper

#check M196LiteralCompoundFeasibility.source_original_uniform_minima_two_sided5
#print M196LiteralCompoundFeasibility.source_original_uniform_minima_two_sided5
#print axioms M196LiteralCompoundFeasibility.source_original_uniform_minima_two_sided5

#check M196LiteralCompoundFeasibility.sourceLattice5_full_rank
#print M196LiteralCompoundFeasibility.sourceLattice5_full_rank
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_full_rank

#check M196LiteralCompoundFeasibility.sourceLattice5_index_pos
#print M196LiteralCompoundFeasibility.sourceLattice5_index_pos
#print axioms M196LiteralCompoundFeasibility.sourceLattice5_index_pos

#check M196LiteralCompoundFeasibility.source_original_uniform_volume_ratio5
#print M196LiteralCompoundFeasibility.source_original_uniform_volume_ratio5
#print axioms M196LiteralCompoundFeasibility.source_original_uniform_volume_ratio5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.originalSourceSolution5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.originalSourceSolution5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.originalSourceSolution5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.originalRothProperty5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.originalRothProperty5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.originalRothProperty5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.nonroth_iff_unbounded_solutions5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.nonroth_iff_unbounded_solutions5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.nonroth_iff_unbounded_solutions5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_lattice5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_lattice5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_lattice5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_gauge5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_gauge5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_gauge5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.source_first_minimum_le_gauge5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.source_first_minimum_le_gauge5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.source_first_minimum_le_gauge5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_small_first5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_small_first5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.source_solution_small_first5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.finite5_adjacent_gap
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.finite5_adjacent_gap
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.finite5_adjacent_gap

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.finite4_unbounded_cover
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.finite4_unbounded_cover
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.finite4_unbounded_cover

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.first_minimum_cutoff5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.first_minimum_cutoff5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.first_minimum_cutoff5

#check M196LiteralCompoundFeasibility.OriginalVariableGap5.matrixUnit5
#print M196LiteralCompoundFeasibility.OriginalVariableGap5.matrixUnit5
#print axioms M196LiteralCompoundFeasibility.OriginalVariableGap5.matrixUnit5

#check M196LiteralCompoundFeasibility.literal_uniform_product5
#print M196LiteralCompoundFeasibility.literal_uniform_product5
#print axioms M196LiteralCompoundFeasibility.literal_uniform_product5
