import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import SubspaceBridge.NonrothFixedFlag4
open scoped BigOperators Pointwise
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4

def dyadicBasis (d : Fin 4) (a : Fin d.val → ℕ) : Basis (Fin d.val) ℝ (Fin d.val → ℝ) :=
  (Pi.basisFun ℝ (Fin d.val)).isUnitSMul (w := fun i => (2 : ℝ)^a i)
    (fun i => isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)))

theorem dyadic_lattice_coordinates (d : Fin 4) (a : Fin d.val → ℕ)
    (x : Fin d.val → ℝ) (hx : x ∈ Submodule.span ℤ (Set.range (dyadicBasis d a))) :
    ∃ z : Fin d.val → ℤ, ∀ i, x i = (2 : ℝ) ^ a i * (z i : ℝ) := by
  let b := dyadicBasis d a
  let z : Fin d.val → ℤ := fun i => (b.restrictScalars ℤ).repr ⟨x,hx⟩ i
  refine ⟨z,?_⟩
  intro i
  have hr (j) : b.repr x j = (z j : ℝ) :=
    (b.restrictScalars_repr_apply ℤ ⟨x,hx⟩ j).symm
  have h := congrFun (b.sum_repr x) i
  simp only [hr] at h
  simpa [b,dyadicBasis,Basis.isUnitSMul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Pi.basisFun_apply,Pi.single_apply,mul_comm] using h.symm

theorem dyadic_lattice_avoids (d : Fin 4) (a : Fin d.val → ℕ) (ha : Antitone a)
    (f : (Fin d.val → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin d.val → ℝ), f (r • x) = |r| * f x)
    (mu : Fin d.val → ℝ) (hmu : ∀ i, 1 < (2 : ℝ)^a i * mu i)
    (hlower : ∀ (z : Fin d.val → ℤ) (i : Fin d.val), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (x : Fin d.val → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (dyadicBasis d a)))
    (hxf : f x ≤ 1) : x = 0 := by
  classical
  by_contra hne
  obtain ⟨z,hz⟩ := dyadic_lattice_coordinates d a x hx
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
  let w : Fin d.val → ℤ := fun i => if i ≤ k then (2 : ℤ)^(a i-a k)*z i else 0
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


theorem dyadic_fundamental_volume (d : Fin 4) (a : Fin d.val → ℕ) :
    volume (ZSpan.fundamentalDomain (dyadicBasis d a)) =
      ENNReal.ofReal (∏ i, (2 : ℝ)^a i) := by
  have hm : Matrix.of (dyadicBasis d a) = Matrix.diagonal (fun i => (2 : ℝ)^a i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [dyadicBasis,Basis.isUnitSMul_apply,Pi.basisFun_apply]
    · simp [dyadicBasis,Basis.isUnitSMul_apply,Pi.basisFun_apply,Pi.single_apply,h]
  rw [ZSpan.volume_fundamentalDomain,hm,Matrix.det_diagonal,abs_of_pos]
  exact Finset.prod_pos (fun _ _ => pow_pos (by norm_num) _)

theorem dyadic_volume_bound (d : Fin 4) (a : Fin d.val → ℕ) (ha : Antitone a)
    (f : (Fin d.val → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin d.val → ℝ), f (r • x) = |r| * f x)
    (mu : Fin d.val → ℝ) (hmu : ∀ i, 1 < (2 : ℝ)^a i * mu i)
    (hlower : ∀ (z : Fin d.val → ℤ) (i : Fin d.val), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    volume.real {x | f x ≤ 1} ≤ (∏ i, (2 : ℝ)^a i) * 2^d.val := by
  let b := dyadicBasis d a
  letI : Countable (Submodule.span ℤ (Set.range b)) :=
    inferInstance
  letI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hvol : volume {x | f x ≤ 1} ≤
      volume (ZSpan.fundamentalDomain b) * 2^Module.finrank ℝ (Fin d.val → ℝ) := by
    by_contra h
    obtain ⟨x,hx,hfx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' b volume)
      (fun x hx => by simpa only [Set.mem_setOf_eq,hsymm] using hx) hconv (lt_of_not_ge h)
    apply hx
    apply Subtype.ext
    exact dyadic_lattice_avoids d a ha f hf mu hmu hlower x x.property hfx
  rw [dyadic_fundamental_volume,Module.finrank_pi,Fintype.card_fin] at hvol
  have hfinite : ENNReal.ofReal (∏ i, (2 : ℝ)^a i) * (2 : ENNReal)^d.val ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have h := ENNReal.toReal_mono hfinite hvol
  have hprod : (0 : ℝ) ≤ ∏ i : Fin d.val, (2 : ℝ)^a i :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (a i))
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hprod,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat] using h


theorem exists_dyadic_exponents (d : Fin 4) (mu : Fin d.val → ℝ)
    (hpos : ∀ i, 0 < mu i) (hone : ∀ i, mu i ≤ 1) (hmono : Monotone mu) :
    ∃ a : Fin d.val → ℕ, Antitone a ∧ ∀ i,
      1 < (2 : ℝ)^a i * mu i ∧ (2 : ℝ)^a i * mu i ≤ 2 := by
  classical
  have hex (i : Fin d.val) : ∃ n : ℕ, 1 < (2 : ℝ)^n * mu i := by
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

theorem normalized_product_volume_upper (d : Fin 4)
    (f : (Fin d.val → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin d.val → ℝ), f (r • x) = |r| * f x)
    (mu : Fin d.val → ℝ) (hpos : ∀ i, 0 < mu i)
    (hone : ∀ i, mu i ≤ 1) (hmono : Monotone mu)
    (hlower : ∀ (z : Fin d.val → ℤ) (i : Fin d.val), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    (∏ i, mu i) * volume.real {x | f x ≤ 1} ≤ 4^d.val := by
  obtain ⟨a,ha,hscale⟩ := exists_dyadic_exponents d mu hpos hone hmono
  have hvol := dyadic_volume_bound d a ha f hf mu (fun i => (hscale i).1) hlower hsymm hconv
  have hp : 0 ≤ ∏ i, mu i := Finset.prod_nonneg (fun i _ => (hpos i).le)
  have hprod : (∏ i, (2 : ℝ)^a i * mu i) ≤ 2^d.val := by
    calc
      _ ≤ ∏ _ : Fin d.val, (2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => mul_nonneg (pow_nonneg (by norm_num) _) (hpos i).le)
          (fun i _ => (hscale i).2)
      _ = _ := by simp
  calc
    _ ≤ (∏ i, mu i) * ((∏ i, (2 : ℝ)^a i) * 2^d.val) := mul_le_mul_of_nonneg_left hvol hp
    _ = (∏ i, (2 : ℝ)^a i * mu i) * 2^d.val := by rw [Finset.prod_mul_distrib]; ring
    _ ≤ 2^d.val * 2^d.val := mul_le_mul_of_nonneg_right hprod (pow_nonneg (by norm_num) _)
    _ = 4^d.val := by rw [← mul_pow]; norm_num


theorem homogeneous_sublevel_dilate (d : Fin 4) (f : (Fin d.val → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin d.val → ℝ), f (r • x) = |r| * f x)
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

theorem adapted_product_volume_upper (d : Fin 4)
    (f : (Fin d.val → ℝ) → ℝ)
    (hf : ∀ (r : ℝ) (x : Fin d.val → ℝ), f (r • x) = |r| * f x)
    (mu : Fin d.val → ℝ) (hpos : ∀ i, 0 < mu i) (hmono : Monotone mu)
    (hlower : ∀ (z : Fin d.val → ℤ) (i : Fin d.val), z i ≠ 0 →
      (∀ j, i < j → z j = 0) → mu i ≤ f (fun j => (z j : ℝ)))
    (hsymm : ∀ x, f (-x) = f x) (hconv : Convex ℝ {x | f x ≤ 1}) :
    (∏ i, mu i) * volume.real {x | f x ≤ 1} ≤ 4^d.val := by
  let t := 1 + ∑ i, mu i
  have ht : 0 < t := by
    dsimp [t]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hpos i).le))
  have hle (i : Fin d.val) : mu i ≤ t := by
    have h := Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)
    dsimp [t]
    linarith
  have heq := homogeneous_sublevel_dilate d f hf t ht
  have hconv' : Convex ℝ {x | f x / t ≤ 1} := by rw [heq]; exact hconv.smul t
  have h := normalized_product_volume_upper d (fun x => f x / t)
    (fun r x => by dsimp only; rw [hf]; ring) (fun i => mu i/t)
    (fun i => div_pos (hpos i) ht) (fun i => (div_le_one ht).mpr (hle i))
    (fun i j hij => div_le_div_of_nonneg_right (hmono hij) ht.le)
    (fun z i hz htail => div_le_div_of_nonneg_right (hlower z i hz htail) ht.le)
    (fun x => by dsimp only; rw [hsymm]) hconv'
  have hvol : volume.real {x | f x/t ≤ 1} = t^d.val * volume.real {x | f x ≤ 1} := by
    rw [heq,measureReal_def,Measure.addHaar_smul,Module.finrank_pi,Fintype.card_fin,
      abs_of_pos (pow_pos ht _),ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
    rfl
  rw [hvol,Finset.prod_div_distrib] at h
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  have hcancel : (∏ i, mu i) / t^d.val * (t^d.val * volume.real {x | f x ≤ 1}) =
      (∏ i, mu i) * volume.real {x | f x ≤ 1} := by
    field_simp
    ring
  rwa [hcancel] at h

end CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4
open scoped BigOperators Matrix
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4

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

end CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4
set_option pp.all true

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadicBasis
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadicBasis
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadicBasis

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_lattice_coordinates
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_lattice_coordinates
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_lattice_coordinates

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_lattice_avoids
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_lattice_avoids
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_lattice_avoids

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_fundamental_volume
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_fundamental_volume
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_fundamental_volume

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_volume_bound
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_volume_bound
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.dyadic_volume_bound

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.exists_dyadic_exponents
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.exists_dyadic_exponents
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.exists_dyadic_exponents

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.normalized_product_volume_upper
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.normalized_product_volume_upper
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.normalized_product_volume_upper

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.homogeneous_sublevel_dilate
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.homogeneous_sublevel_dilate
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.homogeneous_sublevel_dilate

#check CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.adapted_product_volume_upper
#print CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.adapted_product_volume_upper
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedMinkowski4.adapted_product_volume_upper

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rational_real_independent4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rational_real_independent4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rational_real_independent4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_basis_span
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_basis_span
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_basis_span

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_finrank
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_finrank
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_finrank

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rational_source_multiple4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rational_source_multiple4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rational_source_multiple4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_discrete
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_discrete
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_discrete

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_isZLattice
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_isZLattice
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_isZLattice

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_borel
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_borel
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.rationalRealSpan4_borel

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMeasure4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMeasure4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMeasure4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMeasure4_haar
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMeasure4_haar
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMeasure4_haar

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_rank
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_rank
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_rank

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_covolume_pos
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_covolume_pos
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedLattice4_covolume_pos

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_gauge
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_gauge
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_gauge

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_compact_convex
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_compact_convex
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_compact_convex

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_symmetric
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_symmetric
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_symmetric

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_zero_interior
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_zero_interior
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_zero_interior

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_volume_pos_finite
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_volume_pos_finite
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedBody4_volume_pos_finite

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4_bddBelow
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4_bddBelow
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4_bddBelow

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.ambientPrefixIndex4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.ambientPrefixIndex4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.ambientPrefixIndex4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.source_restricted_prefix_eq4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.source_restricted_prefix_eq4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.source_restricted_prefix_eq4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRealBasis4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRealBasis4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRealBasis4

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRealBasis4_span
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRealBasis4_span
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRealBasis4_span

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4_nonempty
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4_nonempty
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedRadii4_nonempty

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4_ge_ambient
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4_ge_ambient
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4_ge_ambient

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4_pos
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4_pos
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedMinima4_pos

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4_ball_compact
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4_ball_compact
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4_ball_compact

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4_ball_finite
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4_ball_finite
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.restrictedGauge4_ball_finite

#check CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.exists_restricted_shortest_outside4
#print CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.exists_restricted_shortest_outside4
#print axioms CompoundFeasibility.RestrictedLiteral190.RestrictedGeometry4.exists_restricted_shortest_outside4
