import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
open scoped BigOperators Pointwise
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.Minkowski10

def dyadicBasis {n : ℕ} (a : Fin n → ℕ) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).isUnitSMul (w := fun i => (2 : ℝ)^a i)
    (fun i => isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)))

theorem dyadic_lattice_coordinates (a : Fin 10 → ℕ)
    (x : Fin 10 → ℝ) (hx : x ∈ Submodule.span ℤ (Set.range (dyadicBasis a))) :
    ∃ z : Fin 10 → ℤ, ∀ i, x i = (2 : ℝ) ^ a i * (z i : ℝ) := by
  let b := dyadicBasis a
  let z : Fin 10 → ℤ := fun i => (b.restrictScalars ℤ).repr ⟨x,hx⟩ i
  refine ⟨z,?_⟩
  intro i
  have hr (j) : b.repr x j = (z j : ℝ) :=
    (b.restrictScalars_repr_apply ℤ ⟨x,hx⟩ j).symm
  have h := congrFun (b.sum_repr x) i
  simp only [hr] at h
  simpa [b,dyadicBasis,Basis.isUnitSMul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Pi.basisFun_apply,Pi.single_apply,mul_comm] using h.symm

theorem dyadic_lattice_avoids (a : Fin 10 → ℕ) (ha : Antitone a)
    (f : (Fin 10 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 10 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 10 → ℝ) (hmu : ∀ i, 1 < (2 : ℝ)^a i * mu i)
    (hlower : ∀ (z : Fin 10 → ℤ) (i : Fin 10), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (x : Fin 10 → ℝ)
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
  let w : Fin 10 → ℤ := fun i => if i ≤ k then (2 : ℤ)^(a i-a k)*z i else 0
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


theorem dyadic_fundamental_volume {n : ℕ} (a : Fin n → ℕ) :
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

theorem dyadic_volume_bound (a : Fin 10 → ℕ) (ha : Antitone a)
    (f : (Fin 10 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 10 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 10 → ℝ) (hmu : ∀ i, 1 < (2 : ℝ)^a i * mu i)
    (hlower : ∀ (z : Fin 10 → ℤ) (i : Fin 10), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    volume.real {x | f x ≤ 1} ≤ (∏ i, (2 : ℝ)^a i) * 2^10 := by
  let b := dyadicBasis a
  letI : Countable (Submodule.span ℤ (Set.range b)) :=
    inferInstance
  letI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hvol : volume {x | f x ≤ 1} ≤
      volume (ZSpan.fundamentalDomain b) * 2^Module.finrank ℝ (Fin 10 → ℝ) := by
    by_contra h
    obtain ⟨x,hx,hfx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' b volume)
      (fun x hx => by simpa only [Set.mem_setOf_eq,hsymm] using hx) hconv (lt_of_not_ge h)
    apply hx
    apply Subtype.ext
    exact dyadic_lattice_avoids a ha f hf mu hmu hlower x x.property hfx
  rw [dyadic_fundamental_volume,Module.finrank_pi,Fintype.card_fin] at hvol
  have hfinite : ENNReal.ofReal (∏ i, (2 : ℝ)^a i) * (2 : ENNReal)^10 ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have h := ENNReal.toReal_mono hfinite hvol
  have hprod : (0 : ℝ) ≤ ∏ i : Fin 10, (2 : ℝ)^a i :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (a i))
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hprod,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat] using h


theorem exists_dyadic_exponents (mu : Fin 10 → ℝ)
    (hpos : ∀ i, 0 < mu i) (hone : ∀ i, mu i ≤ 1) (hmono : Monotone mu) :
    ∃ a : Fin 10 → ℕ, Antitone a ∧ ∀ i,
      1 < (2 : ℝ)^a i * mu i ∧ (2 : ℝ)^a i * mu i ≤ 2 := by
  classical
  have hex (i : Fin 10) : ∃ n : ℕ, 1 < (2 : ℝ)^n * mu i := by
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
    (f : (Fin 10 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 10 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 10 → ℝ) (hpos : ∀ i, 0 < mu i)
    (hone : ∀ i, mu i ≤ 1) (hmono : Monotone mu)
    (hlower : ∀ (z : Fin 10 → ℤ) (i : Fin 10), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    (∏ i, mu i) * volume.real {x | f x ≤ 1} ≤ 4^10 := by
  obtain ⟨a,ha,hscale⟩ := exists_dyadic_exponents mu hpos hone hmono
  have hvol := dyadic_volume_bound a ha f hf mu (fun i => (hscale i).1) hlower hsymm hconv
  have hp : 0 ≤ ∏ i, mu i := Finset.prod_nonneg (fun i _ => (hpos i).le)
  have hprod : (∏ i, (2 : ℝ)^a i * mu i) ≤ 2^10 := by
    calc
      _ ≤ ∏ _ : Fin 10, (2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => mul_nonneg (pow_nonneg (by norm_num) _) (hpos i).le)
          (fun i _ => (hscale i).2)
      _ = _ := by simp
  calc
    _ ≤ (∏ i, mu i) * ((∏ i, (2 : ℝ)^a i) * 2^10) := mul_le_mul_of_nonneg_left hvol hp
    _ = (∏ i, (2 : ℝ)^a i * mu i) * 2^10 := by rw [Finset.prod_mul_distrib]; ring
    _ ≤ 2^10 * 2^10 := mul_le_mul_of_nonneg_right hprod (pow_nonneg (by norm_num) _)
    _ = 4^10 := by rw [← mul_pow]; norm_num


theorem homogeneous_sublevel_dilate (f : (Fin 10 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 10 → ℝ), f (r • x) = |r| * f x)
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
    (f : (Fin 10 → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin 10 → ℝ), f (r • x) = |r| * f x)
    (mu : Fin 10 → ℝ) (hpos : ∀ i, 0 < mu i) (hmono : Monotone mu)
    (hlower : ∀ (z : Fin 10 → ℤ) (i : Fin 10), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    (∏ i, mu i) * volume.real {x | f x ≤ 1} ≤ 4^10 := by
  let t := 1 + ∑ i, mu i
  have ht : 0 < t := by
    dsimp [t]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hpos i).le))
  have hle (i : Fin 10) : mu i ≤ t := by
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
  have hvol : volume.real {x | f x/t ≤ 1} = t^10 * volume.real {x | f x ≤ 1} := by
    rw [heq,measureReal_def,Measure.addHaar_smul,Module.finrank_pi,Fintype.card_fin,
      abs_of_pos (pow_pos ht _),ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
    rfl
  rw [hvol,Finset.prod_div_distrib] at h
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  have hcancel : (∏ i, mu i) / t^10 * (t^10 * volume.real {x | f x ≤ 1}) =
      (∏ i, mu i) * volume.real {x | f x ≤ 1} := by
    field_simp
    ring
  rwa [hcancel] at h

end CompoundFeasibility.Minkowski10
