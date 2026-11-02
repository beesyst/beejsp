import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Polynomial.HasseDeriv
import Analytic
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.GCD

import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace JSP000334

open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def PrimitivePair (z : Fin 2 → ℤ) : Prop :=
  ∃ c : Fin 2 → ℤ, ∑ i, c i * z i = 1

def integralPair (q : ℚ) : Fin 2 → ℤ := ![(q.den : ℤ), q.num]

def archPairHeight (z : Fin 2 → ℤ) : ℚ := max |(z 0 : ℚ)| |(z 1 : ℚ)|

theorem integralPair_primitive (q : ℚ) : PrimitivePair (integralPair q) := by
  have hg : Int.gcd (q.den : ℤ) q.num = 1 := by
    simpa [Int.gcd_def] using q.reduced.symm
  have hb := Int.gcd_eq_gcd_ab (q.den : ℤ) q.num
  rw [hg] at hb
  refine ⟨![Int.gcdA (q.den : ℤ) q.num, Int.gcdB (q.den : ℤ) q.num], ?_⟩
  simpa [integralPair, Fin.sum_univ_succ, mul_comm] using hb.symm

theorem integralPair_ne_zero (q : ℚ) : integralPair q ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [integralPair, q.den_ne_zero] at h0

theorem integralPair_scale (q : ℚ) (i : Fin 2) :
    ((integralPair q i : ℤ) : ℚ) = (q.den : ℚ) * (![1, q] i) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hn : (q.num : ℚ) = q * q.den := (div_eq_iff hd).mp (Rat.num_div_den q)
  fin_cases i
  · simp [integralPair]
  · change (q.num : ℚ) = (q.den : ℚ) * q
    exact hn.trans (mul_comm _ _)

theorem sunit_den_prime_support (u : fixedSUnitGroup) (p : ℕ)
    (hp : p.Prime) (hpd : p ∣ (((u : ℚˣ) : ℚ)).den) : p = 2 ∨ p = 3 := by
  let q : ℚ := ((u : ℚˣ) : ℚ)
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  by_cases hp3 : p = 3
  · exact Or.inr hp3
  have hpn : ¬p ∣ q.num.natAbs := by
    intro hpn
    have h := Nat.dvd_gcd hpn hpd
    rw [q.reduced] at h
    exact hp.not_dvd_one h
  have hnum : padicNorm p (q.num : ℚ) = 1 :=
    (padicNorm.int_eq_one_iff _).mpr (fun h => hpn (Int.natCast_dvd.mp h))
  have hunit : padicNorm p q = 1 := fixed_sunit_norm_outside p hp2 hp3 u
  rw [← Rat.num_div_den q, padicNorm.div, hnum] at hunit
  have hd0 : padicNorm p (q.den : ℚ) ≠ 0 :=
    padicNorm.nonzero (by exact_mod_cast q.den_ne_zero)
  have hden : padicNorm p (q.den : ℚ) = 1 := ((div_eq_one_iff_eq hd0).mp hunit).symm
  exact False.elim ((padicNorm.nat_eq_one_iff _).mp hden hpd)

theorem sunit_denominator (u : fixedSUnitGroup) :
    ∃ s : fixedSUnitGroup, ((s : ℚˣ) : ℚ) = ((((u : ℚˣ) : ℚ)).den : ℚ) := by
  classical
  let d := (((u : ℚˣ) : ℚ)).den
  have hsupp : d.factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have h := Nat.mem_primeFactors.mp hp
    rcases sunit_den_prime_support u p h.1 h.2.1 with rfl | rfl <;> simp
  have hd : d = 2 ^ d.factorization 2 * 3 ^ d.factorization 3 := by
    have hd0 : d ≠ 0 := Rat.den_ne_zero _
    calc
      d = d.factorization.prod (fun p k => p ^ k) := (Nat.factorization_prod_pow_eq_self hd0).symm
      _ = ∏ p ∈ ({2, 3} : Finset ℕ), p ^ d.factorization p :=
        Finsupp.prod_of_support_subset _ hsupp (fun p k => p ^ k) (by simp)
      _ = _ := by simp
  have htwo : twoUnit ∈ fixedSUnitGroup := Subgroup.subset_closure (by simp)
  have hthree : threeUnit ∈ fixedSUnitGroup := Subgroup.subset_closure (by simp)
  refine ⟨⟨twoUnit ^ d.factorization 2 * threeUnit ^ d.factorization 3,
    fixedSUnitGroup.mul_mem (fixedSUnitGroup.pow_mem htwo _) (fixedSUnitGroup.pow_mem hthree _)⟩, ?_⟩
  change _ = (d : ℚ)
  calc
    _ = ((2 ^ d.factorization 2 * 3 ^ d.factorization 3 : ℕ) : ℚ) := by
      simp [twoUnit, threeUnit]
    _ = (d : ℚ) := congrArg ((↑) : ℕ → ℚ) hd.symm

theorem primitive_pair_local_height (z : Fin 2 → ℤ) (hz : PrimitivePair z)
    (p : ℕ) [Fact p.Prime] : max (padicNorm p (z 0 : ℚ)) (padicNorm p (z 1 : ℚ)) = 1 := by
  obtain ⟨c, hc⟩ := hz
  have hsum : c 0 * z 0 + c 1 * z 1 = 1 := by simpa [Fin.sum_univ_succ] using hc
  have hnot : ¬ ((p : ℤ) ∣ z 0 ∧ (p : ℤ) ∣ z 1) := by
    rintro ⟨h0, h1⟩
    have h := dvd_add (dvd_mul_of_dvd_right h0 (c 0)) (dvd_mul_of_dvd_right h1 (c 1))
    rw [hsum] at h
    exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp h)
  have h0 := padicNorm.of_int (p := p) (z 0)
  have h1 := padicNorm.of_int (p := p) (z 1)
  by_cases hd0 : (p : ℤ) ∣ z 0
  · have hn1 : padicNorm p (z 1 : ℚ) = 1 :=
      (padicNorm.int_eq_one_iff _).mpr (fun hd1 => hnot ⟨hd0, hd1⟩)
    rw [hn1, max_eq_right h0]
  · have hn0 := (padicNorm.int_eq_one_iff (p := p) (z 0)).mpr hd0
    rw [hn0, max_eq_left h1]

theorem primitive_pair_height (z : Fin 2 → ℤ) (hz : PrimitivePair z) :
    pairHeight (z 0 : ℚ) (z 1 : ℚ) = archPairHeight z := by
  simp only [pairHeight, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change archPairHeight z *
    (max (padicNorm 2 (z 0 : ℚ)) (padicNorm 2 (z 1 : ℚ)) *
      max (padicNorm 3 (z 0 : ℚ)) (padicNorm 3 (z 1 : ℚ))) = archPairHeight z
  rw [primitive_pair_local_height z hz 2, primitive_pair_local_height z hz 3]
  simp

theorem exists_primitive_sunit_pair {x : Fin 3 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 2) :
    ∃ z : Fin 2 → ℤ, ∃ s : fixedSUnitGroup,
      PrimitivePair z ∧ z ≠ 0 ∧
      (∀ i : Fin 2, (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i.castSucc) ∧
      pairHeight (x 0) (x 1) = archPairHeight z := by
  obtain ⟨u, hu⟩ := hx.2.1 1
  obtain ⟨s, hs⟩ := sunit_denominator u
  have hden : ((s : ℚˣ) : ℚ) = ((x 1).den : ℚ) := by simpa [hu] using hs
  let z := integralPair (x 1)
  have hscale (i : Fin 2) : (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i.castSucc := by
    rw [hden]
    have h := integralPair_scale (x 1) i
    fin_cases i <;> simpa [hx.1] using h
  refine ⟨z, s, integralPair_primitive _, integralPair_ne_zero _, hscale, ?_⟩
  have h0 := hscale 0
  have h1 := hscale 1
  have h := primitive_pair_height z (integralPair_primitive _)
  rw [h0, h1, pairHeight_sunit_scale] at h
  exact h


def choiceFormsProduct (choice : Fin 3 → Fin 2) (y : Fin 2 → ℚ) : ℚ :=
  ∏ v : Fin 3, ∏ j : Fin 2, rationalPlaceNorm v (coordinateSumForms (choice v) j y)

theorem choice_forms_independent (choice : Fin 3 → Fin 2) (v : Fin 3) :
    LinearIndependent ℚ (coordinateSumForms (choice v)) :=
  coordinateSumForms_independent _

theorem choiceFormsProduct_sunit_scale (choice : Fin 3 → Fin 2)
    (s : fixedSUnitGroup) (y : Fin 2 → ℚ) :
    choiceFormsProduct choice (fun i => ((s : ℚˣ) : ℚ) * y i) = choiceFormsProduct choice y := by
  have hform (v : Fin 3) (j : Fin 2) :
      coordinateSumForms (choice v) j (fun i => ((s : ℚˣ) : ℚ) * y i) =
        ((s : ℚˣ) : ℚ) * coordinateSumForms (choice v) j y := by
    exact (coordinateSumForms (choice v) j).map_smul ((s : ℚˣ) : ℚ) y
  have hnorm (v : Fin 3) (q : ℚ) :
      rationalPlaceNorm v (((s : ℚˣ) : ℚ) * q) =
        rationalPlaceNorm v ((s : ℚˣ) : ℚ) * rationalPlaceNorm v q := by
    fin_cases v <;> simp [rationalPlaceNorm, abs_mul]
  unfold choiceFormsProduct
  simp_rw [hform, hnorm, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow, rationalPlaceNorm_product, fixed_sunit_product_formula]
  simp

theorem choiceFormsProduct_retained (choice : Fin 3 → Fin 2) (u w : ℚ)
    (hchoice : ∀ v, rationalPlaceNorm v (![u, w] (choice v)) =
      min (rationalPlaceNorm v u) (rationalPlaceNorm v w)) :
    choiceFormsProduct choice ![u, w] = retainedFormsProduct u w := by
  unfold choiceFormsProduct retainedFormsProduct
  apply Finset.prod_congr rfl
  intro v _
  simpa [coordinateSumForms, Fin.prod_univ_succ] using
    congrArg (fun t => t * rationalPlaceNorm v (u + w)) (hchoice v)

theorem exists_primitive_strong_pair {x : Fin 3 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 2) :
    ∃ choice : Fin 3 → Fin 2, ∃ z : Fin 2 → ℤ, ∃ s : fixedSUnitGroup,
      PrimitivePair z ∧ z ≠ 0 ∧
      (∀ i : Fin 2, (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i.castSucc) ∧
      pairHeight (x 0) (x 1) = archPairHeight z ∧
      choiceFormsProduct choice (fun i => (z i : ℚ)) * archPairHeight z = 1 := by
  classical
  obtain ⟨z, s, hz, hnz, hscale, hheight⟩ := exists_primitive_sunit_pair hx
  choose choice hchoice using (fun v => exists_retained_coordinate v (x 0) (x 1))
  have hpair : (fun i => (z i : ℚ)) = (fun i => ((s : ℚˣ) : ℚ) * (![x 0, x 1] i)) := by
    funext i
    fin_cases i <;> exact hscale _
  have hproduct : choiceFormsProduct choice (fun i => (z i : ℚ)) =
      retainedFormsProduct (x 0) (x 1) := by
    rw [hpair, choiceFormsProduct_sunit_scale]
    exact choiceFormsProduct_retained choice _ _ hchoice
  have hH : pairHeight (x 0) (x 1) ≠ 0 := ne_of_gt (pairHeight_pos (by simp [hx.1]))
  have hnorm : normalizedFormsProduct (x 0) (x 1) =
      retainedFormsProduct (x 0) (x 1) / pairHeight (x 0) (x 1) ^ 2 := by
    unfold normalizedFormsProduct retainedFormsProduct pairHeight
    simp only [div_mul_div_comm, ← pow_two]
    rw [Finset.prod_div_distrib, Finset.prod_pow]
  have hanalytic := three_term_normalized_product_height hx
  rw [hnorm] at hanalytic
  have hret := (div_eq_iff (pow_ne_zero 2 hH)).mp hanalytic
  refine ⟨choice, z, s, hz, hnz, hscale, hheight, ?_⟩
  rw [hproduct, ← hheight, hret]
  field_simp
  ring


def ThreePlaceSubspaceCover : Prop :=
  ∀ choice : Fin 3 → Fin 2,
    ∃ B : Finset (Fin 2 → ℚ),
      (∀ b ∈ B, b ≠ 0) ∧
      ∀ z : Fin 2 → ℤ, PrimitivePair z →
        choiceFormsProduct choice (fun i => (z i : ℚ)) * archPairHeight z ≤ 1 →
        ∃ b ∈ B, ∑ i, b i * (z i : ℚ) = 0

theorem local_pattern_count : Fintype.card (Fin 3 → Fin 2) = 8 := by decide

theorem three_term_cover_of_subspace (hST : ThreePlaceSubspaceCover) :
    ThreeTermHyperplaneCover fixedSUnitGroup := by
  classical
  choose B hproper hcover using hST
  let coefficients : Finset (ℚ × ℚ) :=
    Finset.univ.biUnion (fun choice => (B choice).image (fun b => (b 0, b 1)))
  refine ⟨coefficients, ?_, ?_⟩
  · intro p hp
    obtain ⟨choice, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    intro hzero
    have hbzero : b = 0 := by
      funext i
      fin_cases i
      · exact congrArg Prod.fst hzero
      · exact congrArg Prod.snd hzero
    exact hproper choice b hb hbzero
  · intro x hx
    obtain ⟨choice, z, s, hz, _, hscale, _, hstrong⟩ := exists_primitive_strong_pair hx
    obtain ⟨b, hb, hzero⟩ := hcover choice z hz hstrong.le
    refine ⟨(b 0, b 1), ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨choice, Finset.mem_univ _, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    · have h0 := hscale 0
      have h1 := hscale 1
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hzero
      change b 0 * (z 0 : ℚ) + b 1 * (z 1 : ℚ) = 0 at hzero
      change (z 0 : ℚ) = ((s : ℚˣ) : ℚ) * x 0 at h0
      change (z 1 : ℚ) = ((s : ℚˣ) : ℚ) * x 1 at h1
      rw [h0, h1] at hzero
      have hmul : ((s : ℚˣ) : ℚ) * (b 0 * x 0 + b 1 * x 1) = 0 := by
        nlinarith [hzero]
      exact (mul_eq_zero.mp hmul).resolve_left (Units.ne_zero _)

theorem three_term_finite_of_subspace (hST : ThreePlaceSubspaceCover) :
    (normalizedRelations fixedSUnitGroup 2).Finite :=
  normalized_three_term_finite_of_hyperplane_cover fixedSUnitGroup (three_term_cover_of_subspace hST)



def threeCoordinateSumForms (i : Fin 3) : Fin 3 → ((Fin 3 → ℚ) →ₗ[ℚ] ℚ) :=
  ![LinearMap.proj (i.succAbove 0), LinearMap.proj (i.succAbove 1),
    LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) 0 +
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) 1 +
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) 2]

def localTripleHeight (v : Fin 3) (y : Fin 3 → ℚ) : ℚ :=
  max (rationalPlaceNorm v (y 0))
    (max (rationalPlaceNorm v (y 1)) (rationalPlaceNorm v (y 2)))

def tripleHeight (y : Fin 3 → ℚ) : ℚ := ∏ v : Fin 3, localTripleHeight v y

def tripleChoiceFormsProduct (choice : Fin 3 → Fin 3) (y : Fin 3 → ℚ) : ℚ :=
  ∏ v : Fin 3, ∏ j : Fin 3, rationalPlaceNorm v (threeCoordinateSumForms (choice v) j y)

def tripleNormalizedFormsProduct (choice : Fin 3 → Fin 3) (y : Fin 3 → ℚ) : ℚ :=
  ∏ v : Fin 3, ∏ j : Fin 3,
    rationalPlaceNorm v (threeCoordinateSumForms (choice v) j y) / localTripleHeight v y

theorem threeCoordinateSumForms_independent (i : Fin 3) :
    LinearIndependent ℚ (threeCoordinateSumForms i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h (y : Fin 3 → ℚ) :
      c 0 * y (i.succAbove 0) + c 1 * y (i.succAbove 1) +
        c 2 * (y 0 + y 1 + y 2) = 0 := by
    simpa [threeCoordinateSumForms, Fin.sum_univ_succ, mul_add, add_assoc] using
      LinearMap.congr_fun hc y
  have h0 := h ![1, 0, 0]
  have h1 := h ![0, 1, 0]
  have h2 := h ![0, 0, 1]
  fin_cases i <;> simp [Fin.succAbove, Fin.lt_def, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  all_goals
    have hc0 : c 0 = 0 := by linarith
    have hc1 : c 1 = 0 := by linarith
    have hc2 : c 2 = 0 := by linarith
    fin_cases j <;> assumption

theorem triple_local_pattern_count : Fintype.card (Fin 3 → Fin 3) = 27 := by decide

theorem exists_maximal_triple_coordinate (v : Fin 3) (y : Fin 3 → ℚ) :
    ∃ i : Fin 3, rationalPlaceNorm v (y i) = localTripleHeight v y := by
  unfold localTripleHeight
  by_cases h : rationalPlaceNorm v (y 1) ≤ rationalPlaceNorm v (y 2)
  · rw [max_eq_right h]
    by_cases h0 : rationalPlaceNorm v (y 0) ≤ rationalPlaceNorm v (y 2)
    · exact ⟨2, (max_eq_right h0).symm⟩
    · exact ⟨0, (max_eq_left (le_of_not_ge h0)).symm⟩
  · rw [max_eq_left (le_of_not_ge h)]
    by_cases h0 : rationalPlaceNorm v (y 0) ≤ rationalPlaceNorm v (y 1)
    · exact ⟨1, (max_eq_right h0).symm⟩
    · exact ⟨0, (max_eq_left (le_of_not_ge h0)).symm⟩

theorem tripleHeight_pos {y : Fin 3 → ℚ} (h0 : y 0 ≠ 0) : 0 < tripleHeight y := by
  apply Finset.prod_pos
  intro v _
  exact (rationalPlaceNorm_pos v h0).trans_le (le_max_left _ _)

theorem four_term_forms_full_product {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    threePlaceProduct (x 0) * threePlaceProduct (x 1) * threePlaceProduct (x 2) *
      threePlaceProduct (x 0 + x 1 + x 2) = 1 := by
  have hu (i : Fin 4) : threePlaceProduct (x i) = 1 := by
    obtain ⟨u, he⟩ := hx.2.1 i
    rw [← he]
    exact fixed_sunit_product_formula u
  have hs : x 0 + x 1 + x 2 = -x 3 := by
    have hsum := hx.2.2.1
    simp [Fin.sum_univ_succ] at hsum
    linarith
  have hneg : threePlaceProduct (-x 3) = threePlaceProduct (x 3) := by
    simp [threePlaceProduct]
  rw [hs, hneg, hu 0, hu 1, hu 2, hu 3]
  norm_num

theorem triple_retained_product_height (choice : Fin 3 → Fin 3) (y : Fin 3 → ℚ)
    (hchoice : ∀ v, rationalPlaceNorm v (y (choice v)) = localTripleHeight v y) :
    tripleChoiceFormsProduct choice y * tripleHeight y =
      threePlaceProduct (y 0) * threePlaceProduct (y 1) * threePlaceProduct (y 2) *
        threePlaceProduct (y 0 + y 1 + y 2) := by
  have hlocal (v : Fin 3) :
      (∏ j : Fin 3, rationalPlaceNorm v (threeCoordinateSumForms (choice v) j y)) *
        localTripleHeight v y =
      rationalPlaceNorm v (y 0) * rationalPlaceNorm v (y 1) * rationalPlaceNorm v (y 2) *
        rationalPlaceNorm v (y 0 + y 1 + y 2) := by
    rw [← hchoice v]
    generalize choice v = i
    fin_cases i <;> simp [threeCoordinateSumForms, Fin.prod_univ_succ, Fin.succAbove,
      Fin.lt_def, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> ring
  unfold tripleChoiceFormsProduct tripleHeight
  rw [← Finset.prod_mul_distrib]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [rationalPlaceNorm_product]

theorem four_term_retained_product_height {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    ∃ choice : Fin 3 → Fin 3,
      tripleChoiceFormsProduct choice (fun i => x i.castSucc) *
        tripleHeight (fun i => x i.castSucc) = 1 := by
  classical
  choose choice hchoice using (fun v => exists_maximal_triple_coordinate v (fun i => x i.castSucc))
  refine ⟨choice, ?_⟩
  have h := triple_retained_product_height choice (fun i => x i.castSucc) hchoice
  exact h.trans (four_term_forms_full_product hx)

theorem four_term_normalized_product_height {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    ∃ choice : Fin 3 → Fin 3,
      tripleNormalizedFormsProduct choice (fun i => x i.castSucc) =
        (tripleHeight (fun i => x i.castSucc))⁻¹ ^ 4 := by
  obtain ⟨choice, hret⟩ := four_term_retained_product_height hx
  refine ⟨choice, ?_⟩
  have hnorm : tripleNormalizedFormsProduct choice (fun i => x i.castSucc) =
      tripleChoiceFormsProduct choice (fun i => x i.castSucc) /
        tripleHeight (fun i => x i.castSucc) ^ 3 := by
    unfold tripleNormalizedFormsProduct tripleChoiceFormsProduct tripleHeight
    simp_rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_pow]
  rw [hnorm]
  have hne : tripleHeight (fun i => x i.castSucc) ≠ 0 :=
    ne_of_gt (tripleHeight_pos (by simp [hx.1]))
  field_simp
  have hmul := congrArg (fun t : ℚ => t * tripleHeight (fun i => x i.castSucc) ^ 3) hret
  dsimp only at hmul
  ring_nf at hmul ⊢
  exact hmul


def PrimitiveTriple (z : Fin 3 → ℤ) : Prop :=
  ∃ c : Fin 3 → ℤ, ∑ i, c i * z i = 1

def archTripleHeight (z : Fin 3 → ℤ) : ℚ :=
  max |(z 0 : ℚ)| (max |(z 1 : ℚ)| |(z 2 : ℚ)|)

theorem primitive_triple_local_height (z : Fin 3 → ℤ) (hz : PrimitiveTriple z)
    (p : ℕ) [Fact p.Prime] :
    max (padicNorm p (z 0 : ℚ))
      (max (padicNorm p (z 1 : ℚ)) (padicNorm p (z 2 : ℚ))) = 1 := by
  classical
  obtain ⟨c, hc⟩ := hz
  have hex : ∃ i : Fin 3, ¬ (p : ℤ) ∣ z i := by
    by_contra h
    push_neg at h
    have hd : (p : ℤ) ∣ ∑ i, c i * z i := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_mul_of_dvd_right (h i) _
    rw [hc] at hd
    exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp hd)
  obtain ⟨i, hi⟩ := hex
  have heq := (padicNorm.int_eq_one_iff (p := p) (z i)).mpr hi
  have h0 := padicNorm.of_int (p := p) (z 0)
  have h1 := padicNorm.of_int (p := p) (z 1)
  have h2 := padicNorm.of_int (p := p) (z 2)
  apply le_antisymm
  · exact max_le h0 (max_le h1 h2)
  · fin_cases i
    · rw [← heq]
      exact le_max_left _ _
    · rw [← heq]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · rw [← heq]
      exact (le_max_right _ _).trans (le_max_right _ _)

theorem primitive_triple_height (z : Fin 3 → ℤ) (hz : PrimitiveTriple z) :
    tripleHeight (fun i => (z i : ℚ)) = archTripleHeight z := by
  simp only [tripleHeight, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change archTripleHeight z *
    (max (padicNorm 2 (z 0 : ℚ)) (max (padicNorm 2 (z 1 : ℚ)) (padicNorm 2 (z 2 : ℚ))) *
      max (padicNorm 3 (z 0 : ℚ)) (max (padicNorm 3 (z 1 : ℚ)) (padicNorm 3 (z 2 : ℚ)))) =
      archTripleHeight z
  rw [primitive_triple_local_height z hz 2, primitive_triple_local_height z hz 3]
  simp

theorem tripleHeight_sunit_scale (s : fixedSUnitGroup) (y : Fin 3 → ℚ) :
    tripleHeight (fun i => ((s : ℚˣ) : ℚ) * y i) = tripleHeight y := by
  have hnorm (v : Fin 3) (q : ℚ) :
      rationalPlaceNorm v (((s : ℚˣ) : ℚ) * q) =
        rationalPlaceNorm v ((s : ℚˣ) : ℚ) * rationalPlaceNorm v q := by
    fin_cases v <;> simp [rationalPlaceNorm, abs_mul]
  have hlocal (v : Fin 3) :
      localTripleHeight v (fun i => ((s : ℚˣ) : ℚ) * y i) =
        rationalPlaceNorm v ((s : ℚˣ) : ℚ) * localTripleHeight v y := by
    simp only [localTripleHeight, hnorm]
    have hnon := le_of_lt (rationalPlaceNorm_pos v (Units.ne_zero (s : ℚˣ)))
    rw [← mul_max_of_nonneg _ _ hnon, ← mul_max_of_nonneg _ _ hnon]
  unfold tripleHeight
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, rationalPlaceNorm_product, fixed_sunit_product_formula, one_mul]

theorem tripleChoiceFormsProduct_sunit_scale (choice : Fin 3 → Fin 3)
    (s : fixedSUnitGroup) (y : Fin 3 → ℚ) :
    tripleChoiceFormsProduct choice (fun i => ((s : ℚˣ) : ℚ) * y i) =
      tripleChoiceFormsProduct choice y := by
  have hform (v j : Fin 3) :
      threeCoordinateSumForms (choice v) j (fun i => ((s : ℚˣ) : ℚ) * y i) =
        ((s : ℚˣ) : ℚ) * threeCoordinateSumForms (choice v) j y :=
    (threeCoordinateSumForms (choice v) j).map_smul ((s : ℚˣ) : ℚ) y
  have hnorm (v : Fin 3) (q : ℚ) :
      rationalPlaceNorm v (((s : ℚˣ) : ℚ) * q) =
        rationalPlaceNorm v ((s : ℚˣ) : ℚ) * rationalPlaceNorm v q := by
    fin_cases v <;> simp [rationalPlaceNorm, abs_mul]
  unfold tripleChoiceFormsProduct
  simp_rw [hform, hnorm, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow, rationalPlaceNorm_product, fixed_sunit_product_formula]
  simp


theorem four_term_height_one_le {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    1 ≤ tripleHeight (fun i => x i.castSucc) := by
  have hl (v : Fin 3) : 1 ≤ localTripleHeight v (fun i => x i.castSucc) := by
    change 1 ≤ max (rationalPlaceNorm v (x 0))
      (max (rationalPlaceNorm v (x 1)) (rationalPlaceNorm v (x 2)))
    rw [hx.1, rationalPlaceNorm_one]
    exact le_max_left _ _
  unfold tripleHeight
  calc
    1 = ∏ _v : Fin 3, (1 : ℚ) := by simp
    _ ≤ _ := Finset.prod_le_prod (by intro v _; norm_num) (fun v _ => hl v)


abbrev RealTriple := Fin 3 → ℝ

abbrev lattice3 (b : Basis (Fin 3) ℝ RealTriple) : Submodule ℤ RealTriple :=
  Submodule.span ℤ (Set.range b)

def coordinateGauge3 (e : RealTriple ≃ₗ[ℝ] RealTriple) (x : RealTriple) : ℝ :=
  ‖e x‖

def columnMatrix3 (v : Fin 3 → RealTriple) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => v j i

theorem lattice3_gauge_ball_finite (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (r : ℝ) :
    ({x : RealTriple | coordinateGauge3 e x ≤ r} ∩ (lattice3 b : Set RealTriple)).Finite := by
  have hf := ZSpan.setFinite_inter (b.map e) (Metric.isBounded_closedBall (x := 0) (r := r))
  apply (hf.preimage e.injective.injOn).subset
  intro x hx
  refine ⟨?_, ?_⟩
  · simpa [coordinateGauge3, Metric.mem_closedBall, dist_zero_right] using hx.1
  · have hm := Submodule.mem_map_of_mem (f := (e.restrictScalars ℤ).toLinearMap) hx.2
    simpa only [lattice3, Submodule.map_span, Set.range_comp,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Basis.coe_map] using hm

theorem exists_shortest_lattice3_vector_outside (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (W : Submodule ℝ RealTriple) (hW : W ≠ ⊤) :
    ∃ x ∈ lattice3 b, x ∉ W ∧ 0 < coordinateGauge3 e x ∧
      ∀ y ∈ lattice3 b, y ∉ W → coordinateGauge3 e x ≤ coordinateGauge3 e y := by
  classical
  have hex : ∃ i, b i ∉ W := by
    by_contra! h
    apply hW
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  obtain ⟨i, hi⟩ := hex
  let s : Set RealTriple :=
    {x | coordinateGauge3 e x ≤ coordinateGauge3 e (b i)} ∩
      (lattice3 b : Set RealTriple) ∩ {x | x ∉ W}
  have hs : s.Finite := (lattice3_gauge_ball_finite b e _).inter_of_left _
  have hbi : b i ∈ lattice3 b := Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image s (coordinateGauge3 e) hs
    ⟨b i, ⟨⟨show coordinateGauge3 e (b i) ≤ coordinateGauge3 e (b i) from le_rfl, hbi⟩, hi⟩⟩
  refine ⟨x, hx.1.2, hx.2, ?_, ?_⟩
  · apply norm_pos_iff.mpr
    intro h0
    have : x = 0 := e.injective (h0.trans e.map_zero.symm)
    exact hx.2 (this ▸ W.zero_mem)
  · intro y hy hyW
    by_cases hle : coordinateGauge3 e y ≤ coordinateGauge3 e (b i)
    · exact hmin y ⟨⟨hle, hy⟩, hyW⟩
    · exact hx.1.1.trans (le_of_not_ge hle)

noncomputable def successiveRadius3 (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (k : Fin 3) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val + 1) → RealTriple,
    LinearIndependent ℝ u ∧ (∀ i, u i ∈ lattice3 b) ∧
      ∀ i, coordinateGauge3 e (u i) ≤ r}

theorem independent_family_escapes_subspace3 {n : ℕ} (u : Fin n → RealTriple)
    (hu : LinearIndependent ℝ u) (W : Submodule ℝ RealTriple)
    (hW : Module.finrank ℝ W < n) : ∃ i, u i ∉ W := by
  by_contra! h
  have hs : Submodule.span ℝ (Set.range u) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  have hd := Submodule.finrank_mono hs
  rw [finrank_span_eq_card hu, Fintype.card_fin] at hd
  omega

theorem exists_successive_minima3 (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    ∃ v : Fin 3 → RealTriple, LinearIndependent ℝ v ∧
      (∀ i, v i ∈ lattice3 b) ∧
      (∀ i, 0 < successiveRadius3 b e i) ∧
      (successiveRadius3 b e 0 ≤ successiveRadius3 b e 1 ∧
        successiveRadius3 b e 1 ≤ successiveRadius3 b e 2) ∧
      ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i := by
  classical
  obtain ⟨x, hxL, hxW, hxpos, hxmin⟩ :=
    exists_shortest_lattice3_vector_outside b e ⊥ bot_ne_top
  have hx0 : x ≠ 0 := by simpa using hxW
  let ux : Fin 1 → RealTriple := ![x]
  have hxli : LinearIndependent ℝ ux := linearIndependent_unique ux hx0
  let W1 := Submodule.span ℝ (Set.range ux)
  have hdim1 : Module.finrank ℝ W1 = 1 := by
    simpa [W1] using finrank_span_eq_card hxli
  have hW1 : W1 ≠ ⊤ := by
    intro h
    have hd := finrank_le_of_span_eq_top h
    norm_num [RealTriple, Module.finrank_pi] at hd
  obtain ⟨y, hyL, hyW, hypos, hymin⟩ :=
    exists_shortest_lattice3_vector_outside b e W1 hW1
  let uxy : Fin 2 → RealTriple := Fin.snoc ux y
  have hxyli : LinearIndependent ℝ uxy := linearIndependent_fin_snoc.mpr ⟨hxli, hyW⟩
  let W2 := Submodule.span ℝ (Set.range uxy)
  have hdim2 : Module.finrank ℝ W2 = 2 := by
    simpa [W2] using finrank_span_eq_card hxyli
  have hW2 : W2 ≠ ⊤ := by
    intro h
    have hd := finrank_le_of_span_eq_top h
    norm_num [RealTriple, Module.finrank_pi] at hd
  obtain ⟨z, hzL, hzW, hzpos, hzmin⟩ :=
    exists_shortest_lattice3_vector_outside b e W2 hW2
  let v : Fin 3 → RealTriple := Fin.snoc uxy z
  have hvli : LinearIndependent ℝ v := linearIndependent_fin_snoc.mpr ⟨hxyli, hzW⟩
  have hy0 : y ≠ 0 := fun h => hyW (h ▸ W1.zero_mem)
  have hyz : coordinateGauge3 e y ≤ coordinateGauge3 e z := by
    apply hymin z hzL
    intro hz
    apply hzW
    exact (Submodule.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, by simp [uxy]⟩)) hz
  have hxy : coordinateGauge3 e x ≤ coordinateGauge3 e y :=
    hxmin y hyL (by simpa using hy0)
  have hrad0 : successiveRadius3 b e 0 = coordinateGauge3 e x := by
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨ux, hxli, by intro i; fin_cases i; exact hxL,
        by intro i; fin_cases i; exact le_rfl⟩
    · rintro r ⟨u, hu, huL, hur⟩
      exact (hxmin (u 0) (huL 0) (by simpa using hu.ne_zero 0)).trans (hur 0)
  have hrad1 : successiveRadius3 b e 1 = coordinateGauge3 e y := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨uxy, hxyli, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [uxy, ux, Fin.snoc, hxL, hyL]
      · intro i; fin_cases i
        · exact hxy
        · exact le_rfl
    · rintro r ⟨u, hu, huL, hur⟩
      obtain ⟨i, hi⟩ := independent_family_escapes_subspace3 u hu W1 (by omega)
      exact (hymin (u i) (huL i) hi).trans (hur i)
  have hrad2 : successiveRadius3 b e 2 = coordinateGauge3 e z := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨v, hvli, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [v, uxy, ux, Fin.snoc, hxL, hyL, hzL]
      · intro i; fin_cases i
        · exact hxy.trans hyz
        · exact hyz
        · exact le_rfl
    · rintro r ⟨u, hu, huL, hur⟩
      obtain ⟨i, hi⟩ := independent_family_escapes_subspace3 u hu W2 (by omega)
      exact (hzmin (u i) (huL i) hi).trans (hur i)
  refine ⟨v, hvli, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [v, uxy, ux, Fin.snoc, hxL, hyL, hzL]
  · intro i; fin_cases i
    · change 0 < successiveRadius3 b e 0
      rw [hrad0]
      exact hxpos
    · change 0 < successiveRadius3 b e 1
      rw [hrad1]
      exact hypos
    · change 0 < successiveRadius3 b e 2
      rw [hrad2]
      exact hzpos
  · simpa [hrad0, hrad1, hrad2] using And.intro hxy hyz
  · intro i; fin_cases i <;> simp [v, uxy, ux, Fin.snoc, hrad0, hrad1, hrad2]

theorem abs_det3_le_column_bounds (A : Matrix (Fin 3) (Fin 3) ℝ)
    (r : Fin 3 → ℝ) (hA : ∀ i j, |A i j| ≤ r j) :
    |A.det| ≤ 6 * ∏ j, r j := by
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  change abv A.det ≤ _
  calc
    abv A.det = abv (∑ σ : Equiv.Perm (Fin 3),
        Equiv.Perm.sign σ • ∏ j, A (σ j) j) := congrArg abv (Matrix.det_apply A)
    _ ≤ ∑ σ : Equiv.Perm (Fin 3), abv (Equiv.Perm.sign σ • ∏ j, A (σ j) j) :=
      abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin 3), ∏ j, |A (σ j) j| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ _σ : Equiv.Perm (Fin 3), ∏ j, r j := by
      exact Finset.sum_le_sum fun σ _ =>
        Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hA (σ j) j)
    _ = 6 * ∏ j, r j := by simp [Fintype.card_perm, Nat.factorial]

theorem lattice3_independent_det_ge (b : Basis (Fin 3) ℝ RealTriple)
    (v : Fin 3 → RealTriple) (hv : ∀ j, v j ∈ lattice3 b)
    (hli : LinearIndependent ℝ v) :
    |(columnMatrix3 b).det| ≤ |(columnMatrix3 v).det| := by
  classical
  let C : Matrix (Fin 3) (Fin 3) ℤ := fun i j =>
    (b.restrictScalars ℤ).repr ⟨v j, hv j⟩ i
  let R : Matrix (Fin 3) (Fin 3) ℝ := C.map (Int.castRingHom ℝ)
  have hR : R = b.toMatrix v := by
    ext i j
    exact b.restrictScalars_repr_apply ℤ ⟨v j, hv j⟩ i
  have hmul : columnMatrix3 b * R = columnMatrix3 v := by
    ext i j
    rw [hR]
    change (∑ k, b k i * b.repr (v j) k) = v j i
    have h := congrFun (b.sum_repr (v j)) i
    simpa [Finset.sum_apply, smul_eq_mul, mul_comm] using h
  have hdetv : (columnMatrix3 v).det ≠ 0 := by
    apply isUnit_iff_ne_zero.mp
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    exact Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hdetR : R.det ≠ 0 := by
    intro h0
    apply hdetv
    rw [← hmul, Matrix.det_mul, h0, mul_zero]
  have hcast : R.det = (C.det : ℝ) := by
    exact (RingHom.map_det (Int.castRingHom ℝ) C).symm
  have hdetC : C.det ≠ 0 := by
    intro h0
    apply hdetR
    rw [hcast, h0, Int.cast_zero]
  have hOne : (1 : ℝ) ≤ |R.det| := by
    rw [hcast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hdetC
  calc
    |(columnMatrix3 b).det| ≤ |(columnMatrix3 b).det| * |R.det| :=
      le_mul_of_one_le_right (abs_nonneg _) hOne
    _ = |(columnMatrix3 v).det| := by rw [← abs_mul, ← Matrix.det_mul, hmul]

theorem lattice3_parallelepiped_product_lower (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (v : Fin 3 → RealTriple)
    (hv : ∀ j, v j ∈ lattice3 b) (hli : LinearIndependent ℝ v)
    (r : Fin 3 → ℝ) (hr : ∀ i j, |e (v j) i| ≤ r j) :
    |(columnMatrix3 (fun j => e (b j))).det| ≤ 6 * ∏ j, r j := by
  have hv' : ∀ j, e (v j) ∈ lattice3 (b.map e) := by
    intro j
    have hm := Submodule.mem_map_of_mem (f := (e.restrictScalars ℤ).toLinearMap) (hv j)
    simpa only [lattice3, Submodule.map_span, Set.range_comp,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Basis.coe_map] using hm
  have hli' : LinearIndependent ℝ (fun j => e (v j)) :=
    hli.map' e.toLinearMap e.ker
  exact (lattice3_independent_det_ge (b.map e) _ hv' hli').trans
    (abs_det3_le_column_bounds _ r hr)

theorem normalized_lattice3_parallelepiped_product_lower
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hnorm : |(columnMatrix3 (fun j => e (b j))).det| = 1)
    (v : Fin 3 → RealTriple) (hv : ∀ j, v j ∈ lattice3 b)
    (hli : LinearIndependent ℝ v) (r : Fin 3 → ℝ)
    (hr : ∀ i j, |e (v j) i| ≤ r j) :
    (1 : ℝ) / 6 ≤ ∏ j, r j := by
  have h := lattice3_parallelepiped_product_lower b e v hv hli r hr
  rw [hnorm] at h
  linarith

theorem successive_minima3_parallelepiped_lower
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    |(columnMatrix3 (fun j => e (b j))).det| ≤
      6 * ∏ j, successiveRadius3 b e j := by
  obtain ⟨v, hli, hv, _, _, hrad⟩ := exists_successive_minima3 b e
  apply lattice3_parallelepiped_product_lower b e v hv hli
  intro i j
  rw [← hrad j]
  exact norm_le_pi_norm (e (v j)) i

theorem normalized_successive_minima3_lower
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hnorm : |(columnMatrix3 (fun j => e (b j))).det| = 1) :
    (1 : ℝ) / 6 ≤ ∏ j, successiveRadius3 b e j := by
  have h := successive_minima3_parallelepiped_lower b e
  rw [hnorm] at h
  linarith

def parallelepipedBody3 (e : RealTriple ≃ₗ[ℝ] RealTriple) : Set RealTriple :=
  e ⁻¹' Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)

theorem mem_parallelepipedBody3_iff (e : RealTriple ≃ₗ[ℝ] RealTriple) (x : RealTriple) :
    x ∈ parallelepipedBody3 e ↔ coordinateGauge3 e x ≤ 1 := by
  simp [parallelepipedBody3, coordinateGauge3, pi_norm_le_iff_of_nonempty,
    Real.norm_eq_abs, abs_le, Pi.le_def, forall_and]

open scoped Pointwise in
theorem mem_dilate_parallelepipedBody3_iff (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (x : RealTriple) (r : ℝ) (hr : 0 < r) :
    x ∈ r • parallelepipedBody3 e ↔ coordinateGauge3 e x ≤ r := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_parallelepipedBody3_iff]
  simp only [coordinateGauge3, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hr]
  simpa using (inv_mul_le_iff₀ hr : r⁻¹ * ‖e x‖ ≤ 1 ↔ ‖e x‖ ≤ r * 1)

theorem parallelepipedBody3_volume (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    MeasureTheory.volume.real (parallelepipedBody3 e) =
      8 / |LinearMap.det e.toLinearMap| := by
  rw [MeasureTheory.measureReal_def, parallelepipedBody3,
    MeasureTheory.Measure.addHaar_preimage_linearEquiv,
    MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp only [Real.volume_Icc, LinearEquiv.det_coe_symm, abs_inv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal, abs_nonneg, div_eq_mul_inv]
  norm_num
  ring

theorem lattice3_covolume (b : Basis (Fin 3) ℝ RealTriple) :
    ZLattice.covolume (lattice3 b) = |(columnMatrix3 b).det| := by
  rw [ZLattice.covolume_eq_det (lattice3 b) (b.restrictScalars ℤ)]
  have h : Matrix.of (Subtype.val ∘ (b.restrictScalars ℤ)) = (columnMatrix3 b).transpose := by
    ext i j
    simp [columnMatrix3]
  rw [h, Matrix.det_transpose]

theorem columnMatrix3_map_det (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    (columnMatrix3 (fun j => e (b j))).det =
      LinearMap.det e.toLinearMap * (columnMatrix3 b).det := by
  let B := Pi.basisFun ℝ (Fin 3)
  have hm : columnMatrix3 (fun j => e (b j)) =
      LinearMap.toMatrix B B e.toLinearMap * columnMatrix3 b := by
    ext i j
    have h := congrFun (congrArg e (B.sum_repr (b j))) i
    simpa [columnMatrix3, Matrix.mul_apply, LinearMap.toMatrix_apply,
      B, map_sum, map_smul, Finset.sum_apply, smul_eq_mul, mul_comm] using h.symm
  rw [hm, Matrix.det_mul, LinearMap.det_toMatrix]

theorem successive_minima3_parallelepiped_volume_lower
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    (8 / 6 : ℝ) * ZLattice.covolume (lattice3 b) ≤
      (∏ j, successiveRadius3 b e j) *
        MeasureTheory.volume.real (parallelepipedBody3 e) := by
  have h := successive_minima3_parallelepiped_lower b e
  rw [columnMatrix3_map_det, abs_mul, ← lattice3_covolume] at h
  rw [parallelepipedBody3_volume]
  have hd : 0 < |LinearMap.det e.toLinearMap| :=
    abs_pos.mpr (e.isUnit_det'.ne_zero)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem normalized_successive_minima3_volume_lower
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hnorm : MeasureTheory.volume.real (parallelepipedBody3 e) =
      8 * ZLattice.covolume (lattice3 b)) :
    (1 : ℝ) / 6 ≤ ∏ j, successiveRadius3 b e j := by
  have h := successive_minima3_parallelepiped_volume_lower b e
  rw [hnorm] at h
  have hd := ZLattice.covolume_pos (lattice3 b) MeasureTheory.volume
  nlinarith

open scoped Pointwise in
theorem convex_fiber3_dilate_subset_translate (m : Fin 3)
    (C : Set (Fin m.val → ℝ)) (hC : Convex ℝ C)
    (c : Fin m.val → ℝ) (hc : c ∈ C) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    s • C ⊆ (s - t) • c +ᵥ (t • C) := by
  rintro _ ⟨x, hx, rfl⟩
  let z := (s / t) • x + (1 - s / t) • c
  have hz : z ∈ C := by
    apply hC hx hc (div_nonneg hs ht.le) _ (by ring)
    exact sub_nonneg.mpr ((div_le_one ht).mpr hst)
  apply Set.mem_vadd_set.mpr
  refine ⟨t • z, Set.smul_mem_smul_set hz, ?_⟩
  change (s - t) • c + t • ((s / t) • x + (1 - s / t) • c) = s • x
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

open scoped Pointwise in
theorem convex_fiber3_translate_union_volume_mono (m : Fin 3)
    (C Q : Set (Fin m.val → ℝ)) (hC : Convex ℝ C)
    (c : Fin m.val → ℝ) (hc : c ∈ C) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    MeasureTheory.volume (Q + s • C) ≤ MeasureTheory.volume (Q + t • C) := by
  have hsub : Q + s • C ⊆ (s - t) • c +ᵥ (Q + t • C) := by
    rintro _ ⟨q, hq, x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ :=
      Set.mem_vadd_set.mp (convex_fiber3_dilate_subset_translate m C hC c hc s t hs hst ht hx)
    apply Set.mem_vadd_set.mpr
    refine ⟨q + y, Set.mem_add.mpr ⟨q, hq, y, hy, rfl⟩, ?_⟩
    simp [vadd_eq_add, add_left_comm]
  calc
    MeasureTheory.volume (Q + s • C) ≤
        MeasureTheory.volume ((s - t) • c +ᵥ (Q + t • C)) := MeasureTheory.measure_mono hsub
    _ = MeasureTheory.volume (Q + t • C) := MeasureTheory.measure_vadd _ _ _

section

open scoped Pointwise

def minimaFlag3 (v : Fin 3 → RealTriple) (k : Fin 3) : Submodule ℝ RealTriple :=
  Submodule.span ℝ (Set.range (fun i : Fin k.val => v (Fin.castLE (by omega) i)))

theorem minimaFlag3_finrank (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (k : Fin 3) :
    Module.finrank ℝ (minimaFlag3 v k) = k.val := by
  simpa [minimaFlag3] using
    finrank_span_eq_card (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))

theorem successiveRadius3_le_family (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (k : Fin 3)
    (u : Fin (k.val + 1) → RealTriple) (hu : LinearIndependent ℝ u)
    (huL : ∀ i, u i ∈ lattice3 b) (r : ℝ)
    (hr : ∀ i, coordinateGauge3 e (u i) ≤ r) :
    successiveRadius3 b e k ≤ r := by
  unfold successiveRadius3
  apply csInf_le (s := {s : ℝ | ∃ w : Fin (k.val + 1) → RealTriple,
    LinearIndependent ℝ w ∧ (∀ i, w i ∈ lattice3 b) ∧
      ∀ i, coordinateGauge3 e (w i) ≤ s}) _ ⟨u, hu, huL, hr⟩
  refine ⟨0, ?_⟩
  rintro s ⟨w, _, _, hw⟩
  exact (norm_nonneg (e (w 0))).trans (hw 0)

theorem lattice3_short_mem_minimaFlag (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice3 b)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (k : Fin 3) (hgap : ∀ i : Fin 3, i < k →
      successiveRadius3 b e i < successiveRadius3 b e k)
    (x : RealTriple) (hx : x ∈ lattice3 b)
    (hxr : coordinateGauge3 e x < successiveRadius3 b e k) :
    x ∈ minimaFlag3 v k := by
  classical
  by_contra hxW
  let u : Fin k.val → RealTriple := fun i => v (Fin.castLE (by omega) i)
  have hu : LinearIndependent ℝ u := hv.comp _ (Fin.castLE_injective _)
  let w : Fin (k.val + 1) → RealTriple := Fin.snoc u x
  have hux : LinearIndependent ℝ w :=
    linearIndependent_fin_snoc.mpr ⟨hu, hxW⟩
  have hL : ∀ i : Fin (k.val + 1), w i ∈ lattice3 b := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hx
    · simpa [w, u] using hvL (Fin.castLE (by omega) j)
  have hlt : ∀ i : Fin (k.val + 1), coordinateGauge3 e (w i) < successiveRadius3 b e k := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hxr
    · simpa [w, u, hvr] using hgap (Fin.castLE (by omega) j) (by exact j.isLt)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => coordinateGauge3 e (w i)) (Finset.univ_nonempty)
  have hle := successiveRadius3_le_family b e k w hux hL _
    (fun j => hi j (Finset.mem_univ j))
  exact (not_lt_of_ge hle) (hlt i)

theorem exists_minimaFlag3 (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    ∃ v : Fin 3 → RealTriple, LinearIndependent ℝ v ∧
      (∀ i, v i ∈ lattice3 b) ∧
      (∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i) ∧
      (∀ k, Module.finrank ℝ (minimaFlag3 v k) = k.val) ∧
      ∀ k, (∀ i : Fin 3, i < k → successiveRadius3 b e i < successiveRadius3 b e k) →
        ∀ x ∈ lattice3 b, coordinateGauge3 e x < successiveRadius3 b e k →
          x ∈ minimaFlag3 v k := by
  obtain ⟨v, hv, hvL, _, _, hvr⟩ := exists_successive_minima3 b e
  exact ⟨v, hv, hvL, hvr, minimaFlag3_finrank v hv,
    fun k hgap x hx hxr => lattice3_short_mem_minimaFlag b e v hv hvL hvr k hgap x hx hxr⟩

theorem minimaFlag3_mono (v : Fin 3 → RealTriple) (k l : Fin 3) (hkl : k ≤ l) :
    minimaFlag3 v k ≤ minimaFlag3 v l := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨Fin.castLE hkl i, ?_⟩
  rfl

theorem lattice3_halfBody_cosets_disjoint (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (W : Submodule ℝ RealTriple) (mu r : ℝ)
    (hshort : ∀ z ∈ lattice3 b, coordinateGauge3 e z < mu → z ∈ W)
    (hr : 0 < r) (hrmu : r < mu) (x y : RealTriple)
    (hx : x ∈ lattice3 b) (hy : y ∈ lattice3 b) (hxy : x - y ∉ W)
    (Q : Set RealTriple) (hQ : Q ⊆ (lattice3 b : Set RealTriple) ∩ (W : Set RealTriple)) :
    Disjoint (x +ᵥ (Q + (r / 2) • parallelepipedBody3 e))
      (y +ᵥ (Q + (r / 2) • parallelepipedBody3 e)) := by
  apply Set.disjoint_left.mpr
  intro z hxz hyz
  obtain ⟨u, hu, hxu⟩ := Set.mem_vadd_set.mp hxz
  obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_add.mp hu
  obtain ⟨w, hw, hyw⟩ := Set.mem_vadd_set.mp hyz
  obtain ⟨d, hd, f, hf, hdf⟩ := Set.mem_add.mp hw
  have heq : x + a + c = y + d + f := by
    simpa [vadd_eq_add, ← hac, ← hdf, add_assoc] using hxu.trans hyw.symm
  have hz : x + a - (y + d) = f - c := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa [add_comm, add_left_comm, add_assoc] using heq
  have hdiffL : f - c ∈ lattice3 b := by
    rw [← hz]
    exact (lattice3 b).sub_mem
      ((lattice3 b).add_mem hx (hQ ha).1) ((lattice3 b).add_mem hy (hQ hd).1)
  have hcr := (mem_dilate_parallelepipedBody3_iff e c (r / 2) (by linarith)).mp hc
  have hfr := (mem_dilate_parallelepipedBody3_iff e f (r / 2) (by linarith)).mp hf
  have hbound : coordinateGauge3 e (f - c) ≤ r := by
    calc
      coordinateGauge3 e (f - c) = ‖e f - e c‖ := by simp [coordinateGauge3]
      _ ≤ ‖e f‖ + ‖e c‖ := norm_sub_le _ _
      _ ≤ r := by change coordinateGauge3 e f + coordinateGauge3 e c ≤ r; linarith
  have hW := hshort (f - c) hdiffL (hbound.trans_lt hrmu)
  apply hxy
  have hadW : a - d ∈ W := W.sub_mem (hQ ha).2 (hQ hd).2
  have hsub := W.sub_mem hW hadW
  convert hsub using 1
  rw [← hz]
  abel

theorem minimaFlag3_halfBody_cosets_disjoint (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice3 b)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (k : Fin 3) (hgap : ∀ i : Fin 3, i < k →
      successiveRadius3 b e i < successiveRadius3 b e k)
    (r : ℝ) (hr : 0 < r) (hrmu : r < successiveRadius3 b e k)
    (x y : RealTriple) (hx : x ∈ lattice3 b) (hy : y ∈ lattice3 b)
    (hxy : x - y ∉ minimaFlag3 v k)
    (Q : Set RealTriple)
    (hQ : Q ⊆ (lattice3 b : Set RealTriple) ∩ (minimaFlag3 v k : Set RealTriple)) :
    Disjoint (x +ᵥ (Q + (r / 2) • parallelepipedBody3 e))
      (y +ᵥ (Q + (r / 2) • parallelepipedBody3 e)) := by
  exact lattice3_halfBody_cosets_disjoint b e (minimaFlag3 v k) _ r
    (fun z hz hzr => lattice3_short_mem_minimaFlag b e v hv hvL hvr k hgap z hz hzr)
    hr hrmu x y hx hy hxy Q hQ

end

noncomputable section

def latticeFlag3 (b : Basis (Fin 3) ℝ RealTriple) (v : Fin 3 → RealTriple)
    (k : Fin 3) : Submodule ℤ (lattice3 b) :=
  ((minimaFlag3 v k).restrictScalars ℤ).comap (lattice3 b).subtype

def flagLattice3 (b : Basis (Fin 3) ℝ RealTriple) (v : Fin 3 → RealTriple)
    (k : Fin 3) : Submodule ℤ (minimaFlag3 v k) :=
  (lattice3 b).comap ((minimaFlag3 v k).subtype.restrictScalars ℤ)

theorem latticeFlag3_saturated (b : Basis (Fin 3) ℝ RealTriple)
    (v : Fin 3 → RealTriple) (k : Fin 3) (n : ℤ) (hn : n ≠ 0)
    (x : lattice3 b) (hx : n • x ∈ latticeFlag3 b v k) :
    x ∈ latticeFlag3 b v k := by
  change n • (x : RealTriple) ∈ minimaFlag3 v k at hx
  rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  change (x : RealTriple) ∈ minimaFlag3 v k
  exact (Submodule.smul_mem_iff (minimaFlag3 v k) (by exact_mod_cast hn : (n : ℝ) ≠ 0)).mp hx

noncomputable def latticeFlag3_equiv_flagLattice3 (b : Basis (Fin 3) ℝ RealTriple)
    (v : Fin 3 → RealTriple) (k : Fin 3) :
    latticeFlag3 b v k ≃ₗ[ℤ] flagLattice3 b v k where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance flagLattice3_discrete (b : Basis (Fin 3) ℝ RealTriple)
    (v : Fin 3 → RealTriple) (k : Fin 3) : DiscreteTopology (flagLattice3 b v k) := by
  let f : flagLattice3 b v k → lattice3 b := fun x => ⟨x.val.val, x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : lattice3 b => (z : RealTriple)) h

instance flagLattice3_isZLattice (b : Basis (Fin 3) ℝ RealTriple)
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b) (k : Fin 3) :
    IsZLattice ℝ (flagLattice3 b v k) where
  span_top := by
    let u : Fin k.val → RealTriple := fun i => v (Fin.castLE (by omega) i)
    let B : Basis (Fin k.val) ℝ (minimaFlag3 v k) :=
      Basis.span (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    change (B i : RealTriple) ∈ lattice3 b
    have hB : (B i : RealTriple) = u i :=
      Basis.span_apply (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _)) i
    rw [hB]
    exact hvL (Fin.castLE (by omega) i)

theorem latticeFlag3_finrank (b : Basis (Fin 3) ℝ RealTriple)
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b) (k : Fin 3) :
    Module.finrank ℤ (latticeFlag3 b v k) = k.val := by
  letI := flagLattice3_isZLattice b v hv hvL k
  rw [(latticeFlag3_equiv_flagLattice3 b v k).finrank_eq,
    ZLattice.rank ℝ (flagLattice3 b v k), minimaFlag3_finrank v hv k]


theorem saturated_integer_submodule_complement
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M)
    (hN : ∀ n : ℤ, n ≠ 0 → ∀ x : M, n • x ∈ N → x ∈ N) :
    ∃ Q : Submodule ℤ M, IsCompl N Q := by
  letI qModule : Module ℤ (M ⧸ N) :=
    Submodule.Quotient.module N

  letI qSMul : SMul ℤ (M ⧸ N) :=
    SMulZeroClass.toSMul

  letI qTF : NoZeroSMulDivisors ℤ (M ⧸ N) := by
    constructor
    intro n z h
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      obtain ⟨x, rfl⟩ := N.mkQ_surjective z
      apply (Submodule.Quotient.mk_eq_zero N).mpr
      apply hN n hn x
      rw [← int_smul_eq_zsmul (inferInstance : Module ℤ M) n x]
      apply (Submodule.Quotient.mk_eq_zero N).mp
      simpa only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul] using h
  letI qFinite : Module.Finite ℤ (M ⧸ N) :=
    Module.Finite.of_surjective N.mkQ N.mkQ_surjective

  letI qFree : Module.Free ℤ (M ⧸ N) :=
    @Module.free_of_finite_type_torsion_free'
      ℤ _ (M ⧸ N) _ qModule _ _ qFinite qTF
  obtain ⟨g, hg⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  let f : M →ₗ[ℤ] N :=
    (LinearMap.id - g.comp N.mkQ).codRestrict N (by
      intro x
      apply (Submodule.Quotient.mk_eq_zero N).mp
      change N.mkQ (x - g (N.mkQ x)) = 0

      have hgx : N.mkQ (g (N.mkQ x)) = N.mkQ x := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hg (N.mkQ x)

      rw [map_sub, hgx, sub_self])
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj ?_⟩
  intro x
  apply Subtype.ext
  change x.val - g (N.mkQ x.val) = x.val
  have hx : N.mkQ x.val = 0 := (Submodule.Quotient.mk_eq_zero N).mpr x.property
  simp [hx]


theorem saturated_integer_basis_extend
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    [NoZeroSMulDivisors ℤ M] {n : ℕ}
    (N : Submodule ℤ M) (a : @Basis (Fin n) ℤ N _ _ N.module)
    (hM : Module.finrank ℤ M = n + 1)
    (hN : ∀ z : ℤ, z ≠ 0 → ∀ x : M, z • x ∈ N → x ∈ N) :
    ∃ c : Basis (Fin (n + 1)) ℤ M, ∀ i : Fin n, c i.castSucc = (a i : M) := by
  classical
  obtain ⟨Q, hQ⟩ := saturated_integer_submodule_complement N hN
  letI nModule : Module ℤ N := N.module
  letI qModule : Module ℤ Q := Q.module
  letI nFree : Module.Free ℤ N := Module.Free.of_basis a

  letI qSMul : SMul ℤ Q := SMulZeroClass.toSMul

  letI qTF : NoZeroSMulDivisors ℤ Q := by
    constructor
    intro z x hx

    have hxM' :
        @SMul.smul ℤ M
          (inferInstance : Module ℤ M).toSMul
          z (x : M) = 0 := by
      have h := congrArg (Q.subtype) hx
      simpa only [map_smul, map_zero] using h

    have hxM : z • (x : M) = 0 := by
      calc
        z • (x : M) =
            @SMul.smul ℤ M
              (inferInstance : Module ℤ M).toSMul
              z (x : M) :=
                (int_smul_eq_zsmul
                  (inferInstance : Module ℤ M) z (x : M)).symm
        _ = 0 := hxM'

    rcases eq_zero_or_eq_zero_of_smul_eq_zero hxM with hz | hx0
    · exact Or.inl hz
    · exact Or.inr (Subtype.ext hx0)

  letI qFree : Module.Free ℤ Q :=
    Module.free_of_finite_type_torsion_free'

  letI pqModule : Module ℤ (N × Q) := Prod.instModule
  let e := Submodule.prodEquivOfIsCompl N Q hQ
  have hNr : Module.finrank ℤ N = n := by
    simpa using Module.finrank_eq_card_basis a
  have hQr : Module.finrank ℤ Q = 1 := by
    have h := e.finrank_eq
    rw [Module.finrank_prod, hNr, hM] at h
    omega
  let d : Basis (Fin 1) ℤ Q := Module.finBasisOfFinrankEq ℤ Q hQr
  let c : Basis (Fin (n + 1)) ℤ M := ((a.prod d).map e).reindex finSumFinEquiv
  refine ⟨c, ?_⟩
  intro i
  change c (Fin.castAdd 1 i) = _
  simp [c, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl', e]


theorem latticeFlag3_basis_real_span {ι : Type*}
    (b : Basis (Fin 3) ℝ RealTriple) (v : Fin 3 → RealTriple)
    (hvL : ∀ i, v i ∈ lattice3 b) (k : Fin 3)
    (a : @Basis ι ℤ (latticeFlag3 b v k) _ _ (latticeFlag3 b v k).module) :
    Submodule.span ℝ (Set.range (fun i =>
      (((a i : latticeFlag3 b v k) : lattice3 b) : RealTriple))) = minimaFlag3 v k := by
  let N := latticeFlag3 b v k
  letI nModule : Module ℤ N := N.module
  let W := Submodule.span ℝ (Set.range (fun i =>
    (((a i : latticeFlag3 b v k) : lattice3 b) : RealTriple)))
  have hw : ∀ x : N, ((x : lattice3 b) : RealTriple) ∈ W := by
    have h : Submodule.span ℤ (Set.range a) ≤
        ((W.restrictScalars ℤ).comap (lattice3 b).subtype).comap N.subtype := by
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


theorem exists_adapted_integer_basis3
    (b : Basis (Fin 3) ℝ RealTriple) (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice3 b) :
    ∃ c : Basis (Fin 3) ℤ (lattice3 b), ∀ k : Fin 3,
      Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k := by
  classical
  let L := lattice3 b
  let N1 : Submodule ℤ L := latticeFlag3 b v 1
  let N2 : Submodule ℤ L := latticeFlag3 b v 2
  letI lModule : Module ℤ L := (lattice3 b).module
  letI n1Module : Module ℤ N1 := N1.module
  letI n2Module : Module ℤ N2 := N2.module
  have h12 : N1 ≤ N2 := by
    intro x hx
    exact minimaFlag3_mono v 1 2 (by decide) hx
  let S : Submodule ℤ N2 := N1.comap N2.subtype
  letI sModule : Module ℤ S := S.module
  let e : S ≃ₗ[ℤ] N1 := Submodule.comapSubtypeEquivOfLe h12
  have hr1 : Module.finrank ℤ N1 = 1 := latticeFlag3_finrank b v hv hvL 1
  have hr2 : Module.finrank ℤ N2 = 2 := latticeFlag3_finrank b v hv hvL 2
  have hrL : Module.finrank ℤ L = 3 := by
    simpa using Module.finrank_eq_card_basis (b.restrictScalars ℤ)
  let t : @Basis (Fin 1) ℤ N1 _ _ n1Module := Module.finBasisOfFinrankEq ℤ N1 hr1
  let aS : @Basis (Fin 1) ℤ S _ _ sModule := t.map e.symm
  have hS : ∀ z : ℤ, z ≠ 0 → ∀ x : N2, z • x ∈ S → x ∈ S := by
    intro z hz x hx
    exact latticeFlag3_saturated b v 1 z hz (x : L) hx
  obtain ⟨a2, ha⟩ := saturated_integer_basis_extend S aS hr2 hS
  obtain ⟨c, hc⟩ := saturated_integer_basis_extend N2 a2 hrL
    (latticeFlag3_saturated b v 2)
  have ha0 : ((a2 0 : N2) : L) = (t 0 : L) := by
    simpa only [aS, Basis.map_apply, e, Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N2 => (x : L)) (ha 0)
  refine ⟨c, ?_⟩
  intro k
  fin_cases k
  · simp [minimaFlag3]
  · have heq : (fun i : Fin 1 => ((c (Fin.castLE (by omega) i) : L) : RealTriple)) =
        (fun i : Fin 1 => (((t i : N1) : L) : RealTriple)) := by
      funext i
      fin_cases i
      exact congrArg (fun x : L => (x : RealTriple)) ((hc 0).trans ha0)
    rw [heq]
    exact latticeFlag3_basis_real_span b v hvL 1 t
  · have heq : (fun i : Fin 2 => ((c (Fin.castLE (by omega) i) : L) : RealTriple)) =
        (fun i : Fin 2 => (((a2 i : N2) : L) : RealTriple)) := by
      funext i
      exact congrArg (fun x : L => (x : RealTriple)) (hc i)
    rw [heq]
    exact latticeFlag3_basis_real_span b v hvL 2 a2


section

open MeasureTheory
open scoped Pointwise

def flagFiberUnion3 (m : Fin 3) (Q : Finset (Fin m.val → ℝ)) (r : ℝ)
    (C : Set ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ))) :
    Set ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ)) :=
  ⋃ q ∈ Q, (fun z => (q + r • z.1, z.2)) '' C

theorem flagFiberUnion3_fiber (m : Fin 3) (Q : Finset (Fin m.val → ℝ)) (r : ℝ)
    (C : Set ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ)))
    (y : Fin (3 - m.val) → ℝ) :
    (fun x => (x, y)) ⁻¹' flagFiberUnion3 m Q r C =
      (Q : Set (Fin m.val → ℝ)) + r • ((fun x => (x, y)) ⁻¹' C) := by
  ext x
  simp only [flagFiberUnion3, Set.mem_preimage, Set.mem_iUnion, Set.mem_image,
    Set.mem_add, Set.mem_smul_set]
  constructor
  · rintro ⟨q, hq, ⟨u, w⟩, hC, heq⟩
    rcases Prod.mk.inj heq with ⟨hx, hy⟩
    refine ⟨q, hq, r • u, ⟨u, ?_, rfl⟩, hx⟩
    simpa only [← hy] using hC
  · rintro ⟨q, hq, _, ⟨u, hu, rfl⟩, hx⟩
    exact ⟨q, hq, (u, y), hu, Prod.ext hx rfl⟩

theorem convex_flagFiberUnion3_volume_mono (m : Fin 3)
    (Q : Finset (Fin m.val → ℝ))
    (C : Set ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ)))
    (hCc : IsCompact C) (hC : Convex ℝ C)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    volume (flagFiberUnion3 m Q s C) ≤ volume (flagFiberUnion3 m Q t C) := by
  have hm (r : ℝ) : MeasurableSet (flagFiberUnion3 m Q r C) := by
    apply IsCompact.measurableSet
    apply Q.isCompact_biUnion
    intro q _
    exact hCc.image ((continuous_const.add (continuous_const.smul continuous_fst)).prodMk
      continuous_snd)
  change (volume.prod volume) (flagFiberUnion3 m Q s C) ≤
    (volume.prod volume) (flagFiberUnion3 m Q t C)
  rw [Measure.prod_apply_symm (hm s), Measure.prod_apply_symm (hm t)]
  apply lintegral_mono
  intro y
  dsimp only
  rw [flagFiberUnion3_fiber, flagFiberUnion3_fiber]
  let Cy := (fun x : Fin m.val → ℝ => (x, y)) ⁻¹' C
  have hCy : Convex ℝ Cy := by
    intro x hx z hz a b ha hb hab
    have h := hC hx hz ha hb hab
    change (a • x + b • z, a • y + b • y) ∈ C at h
    change (a • x + b • z, y) ∈ C
    simpa only [← add_smul, hab, one_smul] using h
  by_cases hn : Cy.Nonempty
  · obtain ⟨c, hc⟩ := hn
    exact convex_fiber3_translate_union_volume_mono m Cy Q hCy c hc s t hs hst ht
  · have hempty : Cy = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change volume ((Q : Set (Fin m.val → ℝ)) + s • Cy) ≤
      volume ((Q : Set (Fin m.val → ℝ)) + t • Cy)
    simp [hempty]


theorem flagFiberUnion3_transverse_volume (m : Fin 3)
    (Q : Finset (Fin m.val → ℝ)) (r : ℝ)
    (C : Set ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ))) :
    volume (((fun q : Fin m.val → ℝ => (q, (0 : Fin (3 - m.val) → ℝ))) ''
      (Q : Set (Fin m.val → ℝ))) + r • C) =
      ENNReal.ofReal |r ^ (3 - m.val)| * volume (flagFiberUnion3 m Q r C) := by
  letI productHaar : (volume : Measure ((Fin m.val → ℝ) ×
      (Fin (3 - m.val) → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let T : ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ)) →ₗ[ℝ]
      ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ)) :=
    LinearMap.prodMap LinearMap.id (r • LinearMap.id)
  have himage : T '' flagFiberUnion3 m Q r C =
      ((fun q : Fin m.val → ℝ => (q, (0 : Fin (3 - m.val) → ℝ))) ''
        (Q : Set (Fin m.val → ℝ))) + r • C := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases Set.mem_iUnion.mp hw with ⟨q, hw⟩
      rcases Set.mem_iUnion.mp hw with ⟨hq, hw⟩
      rcases hw with ⟨u, hu, rfl⟩
      apply Set.mem_add.mpr
      refine ⟨(q, 0), ⟨q, hq, rfl⟩, r • u, Set.smul_mem_smul_set hu, ?_⟩
      ext <;> simp [T]
    · intro hz
      obtain ⟨q, hq, w, hw, hsum⟩ := Set.mem_add.mp hz
      rcases hq with ⟨q, hq, rfl⟩
      rcases hw with ⟨u, hu, rfl⟩
      refine ⟨(q + r • u.1, u.2), ?_, ?_⟩
      · exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, ⟨u, hu, rfl⟩⟩⟩
      · calc
          T (q + r • u.1, u.2) = (q, 0) + r • u := by ext <;> simp [T]
          _ = z := hsum
  rw [← himage, Measure.addHaar_image_linearMap volume T]
  congr 2
  simp [T, LinearMap.det_prodMap, LinearMap.det_smul, Module.finrank_pi]


theorem convex_flag3_translate_union_volume_growth (m : Fin 3)
    (Q : Finset (Fin m.val → ℝ))
    (C : Set ((Fin m.val → ℝ) × (Fin (3 - m.val) → ℝ)))
    (hCc : IsCompact C) (hC : Convex ℝ C)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    ENNReal.ofReal |t ^ (3 - m.val)| *
      volume (((fun q : Fin m.val → ℝ => (q, (0 : Fin (3 - m.val) → ℝ))) ''
        (Q : Set (Fin m.val → ℝ))) + s • C) ≤
    ENNReal.ofReal |s ^ (3 - m.val)| *
      volume (((fun q : Fin m.val → ℝ => (q, (0 : Fin (3 - m.val) → ℝ))) ''
        (Q : Set (Fin m.val → ℝ))) + t • C) := by
  rw [flagFiberUnion3_transverse_volume, flagFiberUnion3_transverse_volume]
  simpa only [mul_left_comm, mul_assoc] using
    mul_le_mul_left' (convex_flagFiberUnion3_volume_mono m Q C hCc hC s t hs hst ht)
      (ENNReal.ofReal |t ^ (3 - m.val)| * ENNReal.ofReal |s ^ (3 - m.val)|)


theorem exists_adapted_lattice_coordinates3
    (b : Basis (Fin 3) ℝ RealTriple) (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice3 b) :
    ∃ B : Basis (Fin 3) ℝ RealTriple,
      Submodule.span ℤ (Set.range B) = lattice3 b ∧
      (∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        B (Fin.castLE (by omega) i))) = minimaFlag3 v k) ∧
      ∀ S : Set RealTriple,
        volume (B.equivFun '' S) = volume S / ENNReal.ofReal (ZLattice.covolume (lattice3 b)) := by
  obtain ⟨c, hc⟩ := exists_adapted_integer_basis3 b v hv hvL
  refine ⟨c.ofZLatticeBasis ℝ (lattice3 b), c.ofZLatticeBasis_span ℝ (lattice3 b), ?_, ?_⟩
  · intro k
    simpa only [Basis.ofZLatticeBasis_apply] using hc k
  · intro S
    exact ZLattice.volume_image_eq_volume_div_covolume (lattice3 b) c


theorem parallelepipedBody3_compact_convex (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    IsCompact (parallelepipedBody3 e) ∧ Convex ℝ (parallelepipedBody3 e) := by
  have hbody : parallelepipedBody3 e = e ⁻¹' Metric.closedBall (0 : RealTriple) 1 := by
    ext x
    rw [mem_parallelepipedBody3_iff]
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, coordinateGauge3]
  rw [hbody]
  constructor
  · exact e.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  · exact (convex_closedBall (0 : RealTriple) 1).linear_preimage e.toLinearMap


def integerBox3 (N : ℕ) (s : Finset (Fin 3)) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun i => if i ∈ s then Finset.Icc (-(N : ℤ)) N else {0})

theorem mem_integerBox3 (N : ℕ) (s : Finset (Fin 3)) (z : Fin 3 → ℤ) :
    z ∈ integerBox3 N s ↔ ∀ i, if i ∈ s then -(N : ℤ) ≤ z i ∧ z i ≤ N else z i = 0 := by
  simp only [integerBox3, Fintype.mem_piFinset]
  apply forall_congr'
  intro i
  split <;> simp_all

def integerLatticePoint3 (b : Basis (Fin 3) ℝ RealTriple)
    (c : Basis (Fin 3) ℤ (lattice3 b)) (z : Fin 3 → ℤ) : RealTriple :=
  (c.equivFun.symm z : lattice3 b)

theorem integerLatticePoint3_injective (b : Basis (Fin 3) ℝ RealTriple)
    (c : Basis (Fin 3) ℤ (lattice3 b)) : Function.Injective (integerLatticePoint3 b c) := by
  intro z w h
  exact c.equivFun.symm.injective (Subtype.coe_injective h)

theorem integerLatticePoint3_add (b : Basis (Fin 3) ℝ RealTriple)
    (c : Basis (Fin 3) ℤ (lattice3 b)) (z w : Fin 3 → ℤ) :
    integerLatticePoint3 b c (z + w) = integerLatticePoint3 b c z + integerLatticePoint3 b c w := by
  exact congrArg Subtype.val (c.equivFun.symm.map_add z w)

theorem integerLatticePoint3_mem_flag_iff (b : Basis (Fin 3) ℝ RealTriple)
    (c : Basis (Fin 3) ℤ (lattice3 b)) (v : Fin 3 → RealTriple)
    (hc : ∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k)
    (k : Fin 3) (z : Fin 3 → ℤ) :
    integerLatticePoint3 b c z ∈ minimaFlag3 v k ↔ ∀ i, k ≤ i → z i = 0 := by
  classical
  let B := c.ofZLatticeBasis ℝ (lattice3 b)
  have hset : Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple)) =
      B '' {i : Fin 3 | i < k} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.castLE (by omega) i, i.isLt, by simp [B]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, by simp [B]⟩
  have hrepr (i : Fin 3) : B.repr (integerLatticePoint3 b c z) i = (z i : ℝ) := by
    rw [integerLatticePoint3, Basis.ofZLatticeBasis_repr_apply]
    change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = _
    simp only [LinearEquiv.apply_symm_apply]
  rw [← hc k, hset, B.mem_span_image]
  constructor
  · intro h i hi
    by_contra hz
    have hmem : i ∈ (B.repr (integerLatticePoint3 b c z)).support := by
      simp [hrepr, hz]
    have := h hmem
    exact (not_lt_of_ge hi) this
  · intro h i hi
    by_contra hik
    have hz := h i (le_of_not_gt hik)
    have hn : B.repr (integerLatticePoint3 b c z) i ≠ 0 := Finsupp.mem_support_iff.mp hi
    exact hn (by simp [hrepr, hz])

theorem integerBox3_split (N : ℕ) (s : Finset (Fin 3)) :
    (integerBox3 N Finset.univ : Set (Fin 3 → ℤ)) =
      (integerBox3 N s : Set (Fin 3 → ℤ)) + (integerBox3 N sᶜ : Set (Fin 3 → ℤ)) := by
  classical
  ext z
  constructor
  · intro hz
    have hz' := (mem_integerBox3 N Finset.univ z).mp hz
    let x : Fin 3 → ℤ := fun i => if i ∈ s then z i else 0
    let y : Fin 3 → ℤ := fun i => if i ∈ s then 0 else z i
    refine Set.mem_add.mpr ⟨x, ?_, y, ?_, ?_⟩
    · apply (mem_integerBox3 N s x).mpr
      intro i
      have := hz' i
      by_cases hi : i ∈ s <;> simp_all [x]
    · apply (mem_integerBox3 N sᶜ y).mpr
      intro i
      have := hz' i
      by_cases hi : i ∈ s <;> simp_all [y]
    · funext i
      by_cases hi : i ∈ s <;> simp [x, y, hi]
  · rintro ⟨x, hx, y, hy, rfl⟩
    apply (mem_integerBox3 N Finset.univ (x + y)).mpr
    intro i
    have hx' := (mem_integerBox3 N s x).mp hx i
    have hy' := (mem_integerBox3 N sᶜ y).mp hy i
    by_cases hi : i ∈ s <;> simp_all

theorem integerBox3_split_unique (N : ℕ) (s : Finset (Fin 3))
    (x x' y y' : Fin 3 → ℤ)
    (hx : x ∈ integerBox3 N s) (hx' : x' ∈ integerBox3 N s)
    (hy : y ∈ integerBox3 N sᶜ) (hy' : y' ∈ integerBox3 N sᶜ)
    (h : x + y = x' + y') : x = x' ∧ y = y' := by
  classical
  have hcoord (i : Fin 3) : x i = x' i ∧ y i = y' i := by
    have ha := congrFun h i
    have h1 := (mem_integerBox3 N s x).mp hx i
    have h2 := (mem_integerBox3 N s x').mp hx' i
    have h3 := (mem_integerBox3 N sᶜ y).mp hy i
    have h4 := (mem_integerBox3 N sᶜ y').mp hy' i
    by_cases hi : i ∈ s <;> simp_all
  exact ⟨funext (fun i => (hcoord i).1), funext (fun i => (hcoord i).2)⟩

theorem integerLatticePoint3_box_split (b : Basis (Fin 3) ℝ RealTriple)
    (c : Basis (Fin 3) ℤ (lattice3 b)) (N : ℕ) (s : Finset (Fin 3)) :
    integerLatticePoint3 b c '' (integerBox3 N Finset.univ : Set (Fin 3 → ℤ)) =
      integerLatticePoint3 b c '' (integerBox3 N s : Set (Fin 3 → ℤ)) +
      integerLatticePoint3 b c '' (integerBox3 N sᶜ : Set (Fin 3 → ℤ)) := by
  rw [integerBox3_split N s]
  ext p
  constructor
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, (integerLatticePoint3_add b c x y).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, integerLatticePoint3_add b c x y⟩

theorem integerBox3_transverse_not_mem_flag
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (v : Fin 3 → RealTriple)
    (hc : ∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k)
    (N : ℕ) (k : Fin 3) (z w : Fin 3 → ℤ)
    (hz : z ∈ integerBox3 N (Finset.univ.filter (fun i => i < k))ᶜ)
    (hw : w ∈ integerBox3 N (Finset.univ.filter (fun i => i < k))ᶜ)
    (hzw : z ≠ w) :
    integerLatticePoint3 b c z - integerLatticePoint3 b c w ∉ minimaFlag3 v k := by
  classical
  intro h
  have hsub : integerLatticePoint3 b c (z - w) =
      integerLatticePoint3 b c z - integerLatticePoint3 b c w :=
    congrArg Subtype.val (c.equivFun.symm.map_sub z w)
  rw [← hsub, integerLatticePoint3_mem_flag_iff b c v hc] at h
  apply hzw
  funext i
  by_cases hi : i < k
  · have hz' := (mem_integerBox3 N _ z).mp hz i
    have hw' := (mem_integerBox3 N _ w).mp hw i
    simp_all [not_le_of_gt hi]
  · exact sub_eq_zero.mp (h i (le_of_not_gt hi))

theorem integerBox3_strict_gap_disjoint
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b)
    (hc : ∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k)
    (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (N : ℕ) (k : Fin 3)
    (hgap : ∀ i : Fin 3, i < k → successiveRadius3 b e i < successiveRadius3 b e k)
    (r : ℝ) (hr : 0 < r) (hrmu : r < successiveRadius3 b e k) :
    Set.PairwiseDisjoint
      (integerBox3 N (Finset.univ.filter (fun i => i < k))ᶜ : Set (Fin 3 → ℤ))
      (fun z => integerLatticePoint3 b c z +ᵥ
        ((integerLatticePoint3 b c ''
          (integerBox3 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 3 → ℤ))) +
          (r / 2) • parallelepipedBody3 e)) := by
  classical
  let s := Finset.univ.filter (fun i : Fin 3 => i < k)
  let Q := integerLatticePoint3 b c '' (integerBox3 N s : Set (Fin 3 → ℤ))
  let T := integerBox3 N sᶜ
  let A := Q + (r / 2) • parallelepipedBody3 e
  have hQ : Q ⊆ (lattice3 b : Set RealTriple) ∩ (minimaFlag3 v k : Set RealTriple) := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨(c.equivFun.symm z).property, ?_⟩
    apply (integerLatticePoint3_mem_flag_iff b c v hc k z).mpr
    intro i hi
    have hz' := (mem_integerBox3 N s z).mp hz i
    simpa [s, not_lt_of_ge hi] using hz'
  have hdis : Set.PairwiseDisjoint (T : Set (Fin 3 → ℤ))
      (fun z => integerLatticePoint3 b c z +ᵥ A) := by
    intro z hz w hw hzw
    exact minimaFlag3_halfBody_cosets_disjoint b e v hv hvL hvr k hgap r hr hrmu
      _ _ (c.equivFun.symm z).property (c.equivFun.symm w).property
      (integerBox3_transverse_not_mem_flag b c v hc N k z w hz hw hzw) Q hQ
  exact hdis

theorem integerBox3_strict_gap_volume
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b)
    (hc : ∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k)
    (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (N : ℕ) (k : Fin 3)
    (hgap : ∀ i : Fin 3, i < k → successiveRadius3 b e i < successiveRadius3 b e k)
    (r : ℝ) (hr : 0 < r) (hrmu : r < successiveRadius3 b e k) :
    volume ((integerLatticePoint3 b c ''
      (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) + (r / 2) • parallelepipedBody3 e) =
    ((integerBox3 N (Finset.univ.filter (fun i => i < k))ᶜ).card : ENNReal) *
      volume ((integerLatticePoint3 b c ''
        (integerBox3 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 3 → ℤ))) +
        (r / 2) • parallelepipedBody3 e) := by
  classical
  let s := Finset.univ.filter (fun i : Fin 3 => i < k)
  let Q := integerLatticePoint3 b c '' (integerBox3 N s : Set (Fin 3 → ℤ))
  let T := integerBox3 N sᶜ
  let A := Q + (r / 2) • parallelepipedBody3 e
  have hQ : Q ⊆ (lattice3 b : Set RealTriple) ∩ (minimaFlag3 v k : Set RealTriple) := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨(c.equivFun.symm z).property, ?_⟩
    apply (integerLatticePoint3_mem_flag_iff b c v hc k z).mpr
    intro i hi
    have hz' := (mem_integerBox3 N s z).mp hz i
    simpa [s, not_lt_of_ge hi] using hz'
  have hAc : IsCompact A :=
    ((integerBox3 N s).finite_toSet.image _).isCompact.add
      ((parallelepipedBody3_compact_convex e).1.smul (r / 2))
  have hdis : Set.PairwiseDisjoint (T : Set (Fin 3 → ℤ))
      (fun z => integerLatticePoint3 b c z +ᵥ A) := by
    intro z hz w hw hzw
    exact minimaFlag3_halfBody_cosets_disjoint b e v hv hvL hvr k hgap r hr hrmu
      _ _ (c.equivFun.symm z).property (c.equivFun.symm w).property
      (integerBox3_transverse_not_mem_flag b c v hc N k z w hz hw hzw) Q hQ
  have hdecomp : (integerLatticePoint3 b c ''
      (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) + (r / 2) • parallelepipedBody3 e =
      ⋃ z ∈ T, integerLatticePoint3 b c z +ᵥ A := by
    rw [integerLatticePoint3_box_split b c N s]
    ext x
    constructor
    · rintro ⟨_, ⟨q, hq, _, ⟨z, hz, rfl⟩, rfl⟩, u, hu, rfl⟩
      refine Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
      exact Set.mem_vadd_set.mpr ⟨q + u, ⟨q, hq, u, hu, rfl⟩, by
        change integerLatticePoint3 b c z + (q + u) = _
        ac_rfl⟩
    · rintro hx
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hzt, hx⟩ := Set.mem_iUnion.mp hz
      obtain ⟨_, ⟨q, hq, u, hu, rfl⟩, rfl⟩ := Set.mem_vadd_set.mp hx
      exact ⟨q + integerLatticePoint3 b c z, ⟨q, hq, _, ⟨z, hzt, rfl⟩, rfl⟩,
        u, hu, by change _ = integerLatticePoint3 b c z + (q + u); abel⟩
  rw [hdecomp, measure_biUnion_finset hdis (fun z _ => (hAc.vadd _).measurableSet)]
  simp only [measure_vadd, Finset.sum_const, nsmul_eq_mul]
  rfl

def splitIndex3 (k : Fin 3) : Fin k.val ⊕ Fin (3 - k.val) ≃ Fin 3 :=
  finSumFinEquiv.trans (finCongr (by omega))

def splitCoordinates3 (k : Fin 3) : RealTriple ≃ₗ[ℝ]
    ((Fin k.val → ℝ) × (Fin (3 - k.val) → ℝ)) :=
  (LinearEquiv.piCongrLeft ℝ (fun _ : Fin 3 => ℝ) (splitIndex3 k)).symm.trans
    (LinearEquiv.sumPiEquivProdPi ℝ (Fin k.val) (Fin (3 - k.val)) (fun _ => ℝ))

theorem splitCoordinates3_volume_preserving (k : Fin 3) :
    MeasurePreserving (splitCoordinates3 k) := by
  exact (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin k.val ⊕ Fin (3 - k.val) => ℝ)).comp
      ((volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) (splitIndex3 k)).symm
        (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (splitIndex3 k)))

theorem splitCoordinates3_volume (k : Fin 3) (S : Set RealTriple) (hS : IsCompact S) :
    volume (splitCoordinates3 k '' S) = volume S := by
  have h := (splitCoordinates3_volume_preserving k).measure_preimage
    (hS.image (splitCoordinates3 k).toContinuousLinearEquiv.continuous).measurableSet.nullMeasurableSet
  change volume ((splitCoordinates3 k) ⁻¹' ((splitCoordinates3 k) '' S)) =
    volume ((splitCoordinates3 k) '' S) at h
  rw [Set.preimage_image_eq _ (splitCoordinates3 k).injective] at h
  exact h.symm

end

end

theorem splitCoordinates3_integerBox_image
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (N : ℕ) (k : Fin 3) :
    (splitCoordinates3 k).comp (c.ofZLatticeBasis ℝ (lattice3 b)).equivFun.toLinearMap ''
      (integerLatticePoint3 b c ''
        (integerBox3 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 3 → ℤ))) =
    (fun q : Fin k.val → ℝ => (q, (0 : Fin (3 - k.val) → ℝ))) ''
      ((integerBox3 N (Finset.univ.filter (fun i => i < k))).image
        (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)) :
          Set (Fin k.val → ℝ)) := by
  classical
  have hcoord (z : Fin 3 → ℤ) :
      (c.ofZLatticeBasis ℝ (lattice3 b)).equivFun (integerLatticePoint3 b c z) =
        fun i => (z i : ℝ) := by
    funext i
    change (c.ofZLatticeBasis ℝ (lattice3 b)).repr (integerLatticePoint3 b c z) i = _
    rw [integerLatticePoint3, Basis.ofZLatticeBasis_repr_apply]
    change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = _
    simp only [LinearEquiv.apply_symm_apply]
  have hsplit (z : Fin 3 → ℤ)
      (hz : z ∈ integerBox3 N (Finset.univ.filter (fun i => i < k))) :
      splitCoordinates3 k (fun i => (z i : ℝ)) =
        ((fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)), 0) := by
    apply Prod.ext
    · funext i
      change (z (splitIndex3 k (Sum.inl i)) : ℝ) = _
      congr 2
    · funext i
      have hi : ¬ splitIndex3 k (Sum.inr i) < k := by
        change ¬ k.val + i.val < k.val
        omega
      have hz' := (mem_integerBox3 N _ z).mp hz (splitIndex3 k (Sum.inr i))
      have hz0 : z (splitIndex3 k (Sum.inr i)) = 0 := by
        simpa [hi] using hz'
      change (z (splitIndex3 k (Sum.inr i)) : ℝ) = 0
      simp [hz0]
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨_, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoord, hsplit z hz]
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoord, hsplit z hz]


noncomputable section

open MeasureTheory
open scoped Pointwise

def adaptedSplitCoordinates3 (b : Basis (Fin 3) ℝ RealTriple)
    (c : Basis (Fin 3) ℤ (lattice3 b)) (k : Fin 3) :=
  (c.ofZLatticeBasis ℝ (lattice3 b)).equivFun.trans (splitCoordinates3 k)

theorem adaptedSplitCoordinates3_volume
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (k : Fin 3) (S : Set RealTriple) (hS : IsCompact S) :
    volume (adaptedSplitCoordinates3 b c k '' S) =
      volume S / ENNReal.ofReal (ZLattice.covolume (lattice3 b)) := by
  change volume ((fun x => splitCoordinates3 k
    ((c.ofZLatticeBasis ℝ (lattice3 b)).equivFun x)) '' S) = _
  rw [← Set.image_image]
  have hcS : IsCompact ((c.ofZLatticeBasis ℝ (lattice3 b)).equivFun '' S) :=
    hS.image (c.ofZLatticeBasis ℝ (lattice3 b)).equivFun.toContinuousLinearEquiv.continuous
  rw [splitCoordinates3_volume k _ hcS]
  exact ZLattice.volume_image_eq_volume_div_covolume (lattice3 b) c

theorem adaptedSplitCoordinates3_box_body_image
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (N : ℕ) (k : Fin 3) (C : Set RealTriple) (r : ℝ) :
    adaptedSplitCoordinates3 b c k ''
      ((integerLatticePoint3 b c ''
        (integerBox3 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 3 → ℤ))) + r • C) =
    ((fun q : Fin k.val → ℝ => (q, (0 : Fin (3 - k.val) → ℝ))) ''
      ((integerBox3 N (Finset.univ.filter (fun i => i < k))).image
        (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)) :
          Set (Fin k.val → ℝ))) + r • (adaptedSplitCoordinates3 b c k '' C) := by
  have hb := splitCoordinates3_integerBox_image b c N k
  change adaptedSplitCoordinates3 b c k '' _ = _ at hb
  rw [← hb]
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, _, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, _, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, _, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    exact ⟨q + r • u, ⟨q, hq, r • u, ⟨u, hu, rfl⟩, rfl⟩, by simp⟩

theorem adaptedSplitCoordinates3_box_body_volume
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (N : ℕ) (k : Fin 3) (C : Set RealTriple) (hC : IsCompact C) (r : ℝ) :
    volume (((fun q : Fin k.val → ℝ => (q, (0 : Fin (3 - k.val) → ℝ))) ''
      ((integerBox3 N (Finset.univ.filter (fun i => i < k))).image
        (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)) :
          Set (Fin k.val → ℝ))) + r • (adaptedSplitCoordinates3 b c k '' C)) =
    volume ((integerLatticePoint3 b c ''
      (integerBox3 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 3 → ℤ))) + r • C) /
        ENNReal.ofReal (ZLattice.covolume (lattice3 b)) := by
  rw [← adaptedSplitCoordinates3_box_body_image]
  exact adaptedSplitCoordinates3_volume b c k _
    (((integerBox3 N _).finite_toSet.image _).isCompact.add (hC.smul r))

theorem integerBox3_longitudinal_volume_growth
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (N : ℕ) (k : Fin 3) (C : Set RealTriple) (hCc : IsCompact C) (hC : Convex ℝ C)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) :
    ENNReal.ofReal |t ^ (3 - k.val)| *
      volume ((integerLatticePoint3 b c ''
        (integerBox3 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 3 → ℤ))) + s • C) ≤
    ENNReal.ofReal |s ^ (3 - k.val)| *
      volume ((integerLatticePoint3 b c ''
        (integerBox3 N (Finset.univ.filter (fun i => i < k)) : Set (Fin 3 → ℤ))) + t • C) := by
  classical
  have h := convex_flag3_translate_union_volume_growth k
    ((integerBox3 N (Finset.univ.filter (fun i => i < k))).image
      (fun z => fun i : Fin k.val => (z (Fin.castLE (by omega) i) : ℝ)))
    (adaptedSplitCoordinates3 b c k '' C)
    (hCc.image (adaptedSplitCoordinates3 b c k).toContinuousLinearEquiv.continuous)
    (hC.linear_image (adaptedSplitCoordinates3 b c k).toLinearMap) s t hs hst ht
  rw [adaptedSplitCoordinates3_box_body_volume b c N k C hCc s,
    adaptedSplitCoordinates3_box_body_volume b c N k C hCc t] at h
  have hc0 : ENNReal.ofReal (ZLattice.covolume (lattice3 b)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos (lattice3 b) volume))
  have h' := mul_le_mul_right' h (ENNReal.ofReal (ZLattice.covolume (lattice3 b)))
  simpa only [mul_assoc, ENNReal.div_mul_cancel hc0 ENNReal.ofReal_ne_top] using h'

theorem integerBox3_full_volume_growth_step
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b)
    (hc : ∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k)
    (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (N : ℕ) (k : Fin 3) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hpacking : s = t ∨ ((∀ i : Fin 3, i < k →
      successiveRadius3 b e i < successiveRadius3 b e k) ∧ t < successiveRadius3 b e k)) :
    ENNReal.ofReal |(t / 2) ^ (3 - k.val)| *
      volume ((integerLatticePoint3 b c ''
        (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) + (s / 2) • parallelepipedBody3 e) ≤
    ENNReal.ofReal |(s / 2) ^ (3 - k.val)| *
      volume ((integerLatticePoint3 b c ''
        (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) + (t / 2) • parallelepipedBody3 e) := by
  rcases hpacking with heq | ⟨hgap, htmu⟩
  · subst t
    exact le_rfl
  have ht : 0 < t := hs.trans_le hst
  rw [integerBox3_strict_gap_volume b c v hv hvL hc e hvr N k hgap s hs (hst.trans_lt htmu),
    integerBox3_strict_gap_volume b c v hv hvL hc e hvr N k hgap t ht htmu]
  have h := integerBox3_longitudinal_volume_growth b c N k _
    (parallelepipedBody3_compact_convex e).1 (parallelepipedBody3_compact_convex e).2
    (s / 2) (t / 2) (by positivity) (by linarith) (by positivity)
  simpa only [mul_left_comm] using mul_le_mul_left' h
    ((integerBox3 N (Finset.univ.filter (fun i => i < k))ᶜ).card : ENNReal)


theorem integerBox3_full_volume_growth
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b)
    (hc : ∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k)
    (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (successiveRadius3 b e 1 * successiveRadius3 b e 2) *
      volume.real ((integerLatticePoint3 b c ''
        (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) +
        (ρ * successiveRadius3 b e 0 / 2) • parallelepipedBody3 e) ≤
    successiveRadius3 b e 0 ^ 2 *
      volume.real ((integerLatticePoint3 b c ''
        (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) +
        (ρ * successiveRadius3 b e 2 / 2) • parallelepipedBody3 e) := by
  obtain ⟨_, _, _, hpos, h01, _⟩ := exists_successive_minima3 b e
  let μ := successiveRadius3 b e
  let U : ℝ → Set RealTriple := fun r =>
    (integerLatticePoint3 b c '' (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) +
      (r / 2) • parallelepipedBody3 e
  have hUc (r : ℝ) : IsCompact (U r) :=
    ((integerBox3 N Finset.univ).finite_toSet.image _).isCompact.add
      ((parallelepipedBody3_compact_convex e).1.smul (r / 2))
  have hstep (i j k : Fin 3) (hij : μ i ≤ μ j)
      (hgap : μ i = μ j ∨ (∀ l : Fin 3, l < k → μ l < μ k) ∧ j = k) :
      |(ρ * μ j / 2) ^ (3 - k.val)| * volume.real (U (ρ * μ i)) ≤
      |(ρ * μ i / 2) ^ (3 - k.val)| * volume.real (U (ρ * μ j)) := by
    have hp : ρ * μ i = ρ * μ j ∨
        (∀ l : Fin 3, l < k → μ l < μ k) ∧ ρ * μ j < μ k := by
      rcases hgap with heq | ⟨hgap, rfl⟩
      · exact Or.inl (congrArg (ρ * ·) heq)
      · exact Or.inr ⟨hgap, mul_lt_of_lt_one_left (hpos j) hρ1⟩
    have h := integerBox3_full_volume_growth_step b c v hv hvL hc e hvr N k
      (ρ * μ i) (ρ * μ j) (mul_pos hρ (hpos i)) (mul_le_mul_of_nonneg_left hij hρ.le) hp
    have hf : ENNReal.ofReal |(ρ * μ i / 2) ^ (3 - k.val)| * volume (U (ρ * μ j)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hUc _).measure_ne_top
    have ht := ENNReal.toReal_mono hf h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def] using ht
  have hg1 : μ 0 = μ 1 ∨ (∀ l : Fin 3, l < 1 → μ l < μ 1) ∧ (1 : Fin 3) = 1 := by
    by_cases heq : μ 0 = μ 1
    · exact Or.inl heq
    · refine Or.inr ⟨?_, rfl⟩
      intro l hl
      have : l = 0 := by ext; change l.val = 0; change l.val < 1 at hl; omega
      subst l
      exact lt_of_le_of_ne h01.1 heq
  have hg2 : μ 1 = μ 2 ∨ (∀ l : Fin 3, l < 2 → μ l < μ 2) ∧ (2 : Fin 3) = 2 := by
    by_cases heq : μ 1 = μ 2
    · exact Or.inl heq
    · refine Or.inr ⟨?_, rfl⟩
      intro l hl
      have h12 : μ 1 < μ 2 := lt_of_le_of_ne h01.2 heq
      fin_cases l
      · exact h01.1.trans_lt h12
      · exact h12
      · exact False.elim (lt_irrefl _ hl)
  have h1 := hstep 0 1 1 h01.1 hg1
  have h2 := hstep 1 2 2 h01.2 hg2
  norm_num only [Fin.val_one, Fin.val_two, Nat.reduceSub, pow_one] at h1 h2
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)] at h1
  rw [abs_of_pos (div_pos (mul_pos hρ (hpos 2)) (by norm_num)),
    abs_of_pos (div_pos (mul_pos hρ (hpos 1)) (by norm_num))] at h2
  have h1' : μ 1 ^ 2 * volume.real (U (ρ * μ 0)) ≤
      μ 0 ^ 2 * volume.real (U (ρ * μ 1)) := by
    nlinarith [sq_pos_of_pos hρ]
  have h2' : μ 2 * volume.real (U (ρ * μ 1)) ≤
      μ 1 * volume.real (U (ρ * μ 2)) := by
    nlinarith
  have h := (mul_le_mul_of_nonneg_left h1' (hpos 2).le).trans
    (by simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left h2' (sq_nonneg (μ 0)))
  change μ 1 * μ 2 * volume.real (U (ρ * μ 0)) ≤ μ 0 ^ 2 * volume.real (U (ρ * μ 2))
  nlinarith [hpos 1]


theorem volume_smul_realTriple (r : ℝ) (C : Set RealTriple) :
    volume (r • C) = ENNReal.ofReal |r ^ 3| * volume C := by
  let T : RealTriple →ₗ[ℝ] RealTriple := r • LinearMap.id
  change volume (T '' C) = _
  rw [Measure.addHaar_image_linearMap volume T]
  congr 2
  simp [T, LinearMap.det_smul, Module.finrank_pi]

theorem integerBox3_full_volume_product_lower
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b)
    (hc : ∀ k : Fin 3, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : lattice3 b) : RealTriple))) = minimaFlag3 v k)
    (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ((integerBox3 N Finset.univ).card : ℝ) * (ρ / 2) ^ 3 *
      (∏ i, successiveRadius3 b e i) * volume.real (parallelepipedBody3 e) ≤
    volume.real ((integerLatticePoint3 b c ''
      (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) +
      (ρ * successiveRadius3 b e 2 / 2) • parallelepipedBody3 e) := by
  classical
  obtain ⟨_, _, _, hpos, _, _⟩ := exists_successive_minima3 b e
  have hfilter : Finset.univ.filter (fun i : Fin 3 => i < 0) = ∅ := by simp
  have hzero : integerBox3 N ∅ = {0} := by
    ext z
    rw [mem_integerBox3]
    simp only [Finset.not_mem_empty, ite_false, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  have hpoint : integerLatticePoint3 b c 0 = 0 := by
    simp [integerLatticePoint3]
  have hpack := integerBox3_strict_gap_volume b c v hv hvL hc e hvr N 0
    (by intro i hi; exact False.elim (Fin.not_lt_zero i hi))
    (ρ * successiveRadius3 b e 0) (mul_pos hρ (hpos 0))
    (mul_lt_of_lt_one_left (hpos 0) hρ1)
  rw [hfilter, Finset.compl_empty, hzero] at hpack
  simp only [Finset.coe_singleton, Set.image_singleton, hpoint] at hpack
  change volume _ = _ * volume ((0 : Set RealTriple) + _) at hpack
  rw [zero_add] at hpack
  rw [volume_smul_realTriple] at hpack
  have hreal := congrArg ENNReal.toReal hpack
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (abs_nonneg _), ← measureReal_def] at hreal
  rw [abs_of_pos (pow_pos (div_pos (mul_pos hρ (hpos 0)) (by norm_num)) 3)] at hreal
  have hg := integerBox3_full_volume_growth b c v hv hvL hc e hvr N ρ hρ hρ1
  rw [hreal] at hg
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  have hfactor :
      successiveRadius3 b e 1 * successiveRadius3 b e 2 *
        ((integerBox3 N Finset.univ).card *
          ((ρ * successiveRadius3 b e 0 / 2) ^ 3 * volume.real (parallelepipedBody3 e))) =
      successiveRadius3 b e 0 ^ 2 *
        ((integerBox3 N Finset.univ).card * (ρ / 2) ^ 3 *
          (successiveRadius3 b e 0 * (successiveRadius3 b e 1 * successiveRadius3 b e 2)) *
            volume.real (parallelepipedBody3 e)) := by ring
  rw [hfactor] at hg
  exact (mul_le_mul_left (sq_pos_of_pos (hpos 0))).mp hg


theorem integerBox3_full_body_fixed_enlargement
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    ∃ R : ℝ, 0 < R ∧ ∀ (N : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      (c.ofZLatticeBasis ℝ (lattice3 b)).equivFun ''
        ((integerLatticePoint3 b c ''
          (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) +
          (ρ * successiveRadius3 b e 2 / 2) • parallelepipedBody3 e) ⊆
      Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(N : ℝ) - R) ((N : ℝ) + R)) := by
  let B := (c.ofZLatticeBasis ℝ (lattice3 b)).equivFun
  let A := (successiveRadius3 b e 2 / 2) • parallelepipedBody3 e
  have hAc : IsCompact A := (parallelepipedBody3_compact_convex e).1.smul _
  have hBc : IsCompact (B '' A) := hAc.image B.toContinuousLinearEquiv.continuous
  obtain ⟨R, hR, hbound⟩ := hBc.isBounded.subset_closedBall_lt 0 (0 : RealTriple)
  refine ⟨R, hR, ?_⟩
  intro N ρ hρ hρ1 x hx
  obtain ⟨_, ⟨_, ⟨z, hz, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩ := hx
  have hcoord : B (integerLatticePoint3 b c z) = fun i => (z i : ℝ) := by
    funext i
    change (c.ofZLatticeBasis ℝ (lattice3 b)).repr (integerLatticePoint3 b c z) i = _
    rw [integerLatticePoint3, Basis.ofZLatticeBasis_repr_apply]
    change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = _
    simp only [LinearEquiv.apply_symm_apply]
  have hzero : (0 : RealTriple) ∈ A := by
    refine ⟨0, ?_, by simp⟩
    rw [mem_parallelepipedBody3_iff]
    simp [coordinateGauge3]
  have hsmall : (ρ * successiveRadius3 b e 2 / 2) • u ∈ A := by
    have h := ((parallelepipedBody3_compact_convex e).2.smul
      (successiveRadius3 b e 2 / 2)).smul_mem_of_zero_mem hzero
        (show (successiveRadius3 b e 2 / 2) • u ∈ A from ⟨u, hu, rfl⟩) ⟨hρ, hρ1⟩
    simpa only [smul_smul, mul_div_assoc] using h
  have hnorm : ‖B ((ρ * successiveRadius3 b e 2 / 2) • u)‖ ≤ R := by
    have h := hbound (Set.mem_image_of_mem B hsmall)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  rw [Set.mem_pi]
  intro i _
  change B (integerLatticePoint3 b c z + (ρ * successiveRadius3 b e 2 / 2) • u) i ∈ _
  rw [map_add, Pi.add_apply, hcoord]
  have hz' := (mem_integerBox3 N Finset.univ z).mp hz i
  simp only [Finset.mem_univ, ite_true] at hz'
  have hzR : -(N : ℝ) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ N := by exact_mod_cast hz'
  have hi : |B ((ρ * successiveRadius3 b e 2 / 2) • u) i| ≤ R :=
    le_trans (by simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (B ((ρ * successiveRadius3 b e 2 / 2) • u)) i) hnorm
  exact ⟨by linarith [(abs_le.mp hi).1], by linarith [(abs_le.mp hi).2]⟩

theorem integerBox3_full_body_volume_upper
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    ∃ R : ℝ, 0 < R ∧ ∀ (N : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      volume.real ((integerLatticePoint3 b c ''
        (integerBox3 N Finset.univ : Set (Fin 3 → ℤ))) +
        (ρ * successiveRadius3 b e 2 / 2) • parallelepipedBody3 e) ≤
      (2 * ((N : ℝ) + R)) ^ 3 * ZLattice.covolume (lattice3 b) := by
  obtain ⟨R, hR, hsub⟩ := integerBox3_full_body_fixed_enlargement b c e
  refine ⟨R, hR, ?_⟩
  intro N ρ hρ hρ1
  have hbox : volume (Set.pi Set.univ
      (fun _ : Fin 3 => Set.Icc (-(N : ℝ) - R) ((N : ℝ) + R))) =
      ENNReal.ofReal ((2 * ((N : ℝ) + R)) ^ 3) := by
    rw [volume_pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by linarith [Nat.cast_nonneg (α := ℝ) N])]
    congr 1
    ring
  have h := measure_mono (μ := volume) (hsub N ρ hρ hρ1)
  rw [ZLattice.volume_image_eq_volume_div_covolume (lattice3 b) c, hbox] at h
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have hcov := ZLattice.covolume_pos (lattice3 b) volume
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hcov.le,
    ENNReal.toReal_ofReal (by positivity)] at h'
  exact (div_le_iff₀ hcov).mp h'

theorem integerBox3_full_card (N : ℕ) :
    (integerBox3 N Finset.univ).card = (2 * N + 1) ^ 3 := by
  simp [integerBox3, Fintype.card_piFinset, Int.card_Icc]
  omega


open Filter Topology

theorem cubic_box_leading_coefficient (A B R : ℝ)
    (h : ∀ N : ℕ, (2 * (N : ℝ) + 1) ^ 3 * A ≤ (2 * ((N : ℝ) + R)) ^ 3 * B) :
    A ≤ B := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hn (n : ℕ) :
      (2 + ((n : ℝ) + 1)⁻¹) ^ 3 * A ≤
        (2 + 2 * R * ((n : ℝ) + 1)⁻¹) ^ 3 * B := by
    have hne : (n : ℝ) + 1 ≠ 0 := by positivity
    have h' := mul_le_mul_of_nonneg_right (h (n + 1))
      (show 0 ≤ (((n : ℝ) + 1) ^ 3)⁻¹ by positivity)
    push_cast at h'
    have hleft : (2 + ((n : ℝ) + 1)⁻¹) ^ 3 * A =
        (2 * ((n : ℝ) + 1) + 1) ^ 3 * A * (((n : ℝ) + 1) ^ 3)⁻¹ := by
      field_simp [hne]
    have hright : (2 + 2 * R * ((n : ℝ) + 1)⁻¹) ^ 3 * B =
        (2 * ((n : ℝ) + 1 + R)) ^ 3 * B * (((n : ℝ) + 1) ^ 3)⁻¹ := by
      field_simp [hne]
      ring_nf
      simp
    rw [hleft, hright]
    exact h'
  have hL : Tendsto (fun n : ℕ => (2 + ((n : ℝ) + 1)⁻¹) ^ 3 * A) atTop (𝓝 (2 ^ 3 * A)) := by
    simpa using ((tendsto_const_nhds.add hinv).pow 3).mul_const A
  have hR : Tendsto (fun n : ℕ => (2 + 2 * R * ((n : ℝ) + 1)⁻¹) ^ 3 * B)
      atTop (𝓝 (2 ^ 3 * B)) := by
    simpa using ((tendsto_const_nhds.add (hinv.const_mul (2 * R))).pow 3).mul_const B
  have hlim := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hn)
  norm_num at hlim
  linarith

open MeasureTheory

theorem successive_minima3_parallelepiped_volume_upper_contracted
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (ρ / 2) ^ 3 * (∏ j, successiveRadius3 b e j) *
      volume.real (parallelepipedBody3 e) ≤ ZLattice.covolume (lattice3 b) := by
  obtain ⟨v, hv, hvL, _, _, hvr⟩ := exists_successive_minima3 b e
  obtain ⟨c, hc⟩ := exists_adapted_integer_basis3 b v hv hvL
  obtain ⟨R, _, hupper⟩ := integerBox3_full_body_volume_upper b c e
  apply cubic_box_leading_coefficient _ _ R
  intro N
  have h := (integerBox3_full_volume_product_lower b c v hv hvL hc e hvr N ρ hρ hρ1).trans
    (hupper N ρ hρ.le hρ1.le)
  rw [integerBox3_full_card] at h
  push_cast at h
  simpa only [mul_assoc] using h

theorem successive_minima3_parallelepiped_volume_upper
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    (∏ j, successiveRadius3 b e j) * volume.real (parallelepipedBody3 e) ≤
      8 * ZLattice.covolume (lattice3 b) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ =>
      ((1 - ((n : ℝ) + 2)⁻¹) / 2) ^ 3 * (∏ j, successiveRadius3 b e j) *
        volume.real (parallelepipedBody3 e)) atTop
      (𝓝 (((1 : ℝ) / 2) ^ 3 * (∏ j, successiveRadius3 b e j) *
        volume.real (parallelepipedBody3 e))) := by
    simpa using (((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).div_const 2).pow 3).mul_const
      (∏ j, successiveRadius3 b e j)).mul_const (volume.real (parallelepipedBody3 e))
  have hbound : ∀ n : ℕ,
      ((1 - ((n : ℝ) + 2)⁻¹) / 2) ^ 3 * (∏ j, successiveRadius3 b e j) *
        volume.real (parallelepipedBody3 e) ≤ ZLattice.covolume (lattice3 b) := by
    intro n
    have hpos : 0 < (n : ℝ) + 2 := by positivity
    have hi : ((n : ℝ) + 2)⁻¹ < 1 := (inv_lt_one₀ hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact successive_minima3_parallelepiped_volume_upper_contracted b e _
      (by linarith) (by linarith [inv_pos.mpr hpos])
  have h := le_of_tendsto hlim (Eventually.of_forall hbound)
  norm_num at h
  nlinarith


set_option maxHeartbeats 800000 in
theorem integer_span3_index_det
    {M : Type*} [AddCommGroup M]
    (c : Basis (Fin 3) ℤ M) (u : Fin 3 → M) (hu : LinearIndependent ℤ u) :
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
        (Subtype.val ∘ (Basis.span hu : Fin 3 → N)) = u := by
      funext i
      exact Basis.span_apply hu i

    have hmat :
        c.toMatrix (Subtype.val ∘ (Basis.span hu : Fin 3 → N)) =
          c.toMatrix u :=
      congrArg (fun w : Fin 3 → M => c.toMatrix w) hspan

    calc
      Nat.card (M ⧸ N) =
          (c.toMatrix (Subtype.val ∘ (Basis.span hu : Fin 3 → N))).det.natAbs := by
            simpa only [Basis.det_apply] using h
      _ = (c.toMatrix u).det.natAbs := by
            rw [hmat]
  refine ⟨hfinite, hcard, ?_⟩
  letI := hfinite
  have hpos := Nat.card_pos (α := M ⧸ N)
  rw [hcard] at hpos
  exact Int.natAbs_ne_zero.mp (ne_of_gt hpos)


theorem lattice3_coordinate_det_covolume
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (u : Fin 3 → lattice3 b) :
    |(columnMatrix3 (fun i => (u i : RealTriple))).det| =
      ZLattice.covolume (lattice3 b) * |((c.toMatrix u).det : ℝ)| := by
  let B := c.ofZLatticeBasis ℝ (lattice3 b)
  let C := (c.toMatrix u).map (Int.castRingHom ℝ)
  have hC : C = B.toMatrix (fun i => (u i : RealTriple)) := by
    ext i j
    exact (Basis.ofZLatticeBasis_repr_apply ℝ (lattice3 b) c (u j) i).symm
  have hmul : columnMatrix3 B * C = columnMatrix3 (fun i => (u i : RealTriple)) := by
    ext i j
    rw [hC]
    change (∑ k, B k i * B.repr (u j : RealTriple) k) = (u j : RealTriple) i
    have h := congrFun (B.sum_repr (u j : RealTriple)) i
    simpa [Finset.sum_apply, smul_eq_mul, mul_comm] using h
  have hcov : ZLattice.covolume (lattice3 b) = |(columnMatrix3 B).det| := by
    rw [ZLattice.covolume_eq_det (lattice3 b) c]
    have hm : Matrix.of (Subtype.val ∘ c) = (columnMatrix3 B).transpose := by
      ext i j
      simp [B, columnMatrix3, Basis.ofZLatticeBasis_apply]
    rw [hm, Matrix.det_transpose]
  have hcast : C.det = ((c.toMatrix u).det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) (c.toMatrix u)).symm
  rw [← hmul, Matrix.det_mul, abs_mul, ← hcov, hcast]


theorem lattice3_generated_index_det
    (b : Basis (Fin 3) ℝ RealTriple) (c : Basis (Fin 3) ℤ (lattice3 b))
    (u : Fin 3 → lattice3 b)
    (hu : LinearIndependent ℝ (fun i => (u i : RealTriple))) :
    Finite (lattice3 b ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index = (c.toMatrix u).det.natAbs ∧
      (c.toMatrix u).det ≠ 0 ∧
      ((Submodule.span ℤ (Set.range u)).toAddSubgroup.index : ℝ) *
        ZLattice.covolume (lattice3 b) = |(columnMatrix3 (fun i => (u i : RealTriple))).det| := by
  have huZ : LinearIndependent ℤ u :=
    LinearIndependent.of_comp (lattice3 b).subtype (hu.restrict_scalars' ℤ)
  obtain ⟨hf, hi, hd⟩ := integer_span3_index_det c u huZ
  refine ⟨hf, hi, hd, ?_⟩
  rw [hi, Int.cast_natAbs, Int.cast_abs]
  exact (mul_comm _ _).trans (lattice3_coordinate_det_covolume b c u).symm

theorem successive_minima3_attaining_det_upper
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (v : Fin 3 → RealTriple)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i) :
    |(columnMatrix3 (fun i => e (v i))).det| ≤ 6 * ∏ i, successiveRadius3 b e i := by
  apply abs_det3_le_column_bounds
  intro i j
  rw [← hvr j]
  simpa only [coordinateGauge3, Real.norm_eq_abs] using norm_le_pi_norm (e (v j)) i

theorem successive_minima3_attaining_index_le_six
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (u : Fin 3 → lattice3 b)
    (hu : LinearIndependent ℝ (fun i => (u i : RealTriple)))
    (hvr : ∀ i, coordinateGauge3 e (u i : RealTriple) = successiveRadius3 b e i) :
    (Submodule.span ℤ (Set.range u)).toAddSubgroup.index ≤ 6 := by
  classical
  let c := b.restrictScalars ℤ
  obtain ⟨_, _, _, hindex⟩ := lattice3_generated_index_det b c u hu
  let V := basisOfPiSpaceOfLinearIndependent hu
  have hmap : |(columnMatrix3 (fun i => e (u i : RealTriple))).det| =
      |LinearMap.det e.toLinearMap| * |(columnMatrix3 (fun i => (u i : RealTriple))).det| := by
    simpa only [V, coe_basisOfPiSpaceOfLinearIndependent, abs_mul] using
      congrArg abs (columnMatrix3_map_det V e)
  have hbound := successive_minima3_attaining_det_upper b e (fun i => (u i : RealTriple)) hvr
  rw [hmap, ← hindex] at hbound
  have hup := successive_minima3_parallelepiped_volume_upper b e
  rw [parallelepipedBody3_volume, ← mul_div_assoc] at hup
  have hepos : 0 < |LinearMap.det e.toLinearMap| := abs_pos.mpr e.isUnit_det'.ne_zero
  have hcpos := ZLattice.covolume_pos (lattice3 b) MeasureTheory.volume
  have hprod : (∏ i, successiveRadius3 b e i) ≤
      |LinearMap.det e.toLinearMap| * ZLattice.covolume (lattice3 b) := by
    have h := (div_le_iff₀ hepos).mp hup
    nlinarith
  have hcomb := hbound.trans (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 6))
  have hreal : ((Submodule.span ℤ (Set.range u)).toAddSubgroup.index : ℝ) ≤ 6 := by
    apply (mul_le_mul_left (mul_pos hepos hcpos)).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcomb
  exact_mod_cast hreal

theorem exists_successive_minima3_bounded_index
    (b : Basis (Fin 3) ℝ RealTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    ∃ u : Fin 3 → lattice3 b,
      LinearIndependent ℝ (fun i => (u i : RealTriple)) ∧
      (∀ i, coordinateGauge3 e (u i : RealTriple) = successiveRadius3 b e i) ∧
      Finite (lattice3 b ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index ≤ 6 ∧
      ∀ c : Basis (Fin 3) ℤ (lattice3 b),
        (Submodule.span ℤ (Set.range u)).toAddSubgroup.index = (c.toMatrix u).det.natAbs ∧
        (c.toMatrix u).det ≠ 0 ∧
        ((Submodule.span ℤ (Set.range u)).toAddSubgroup.index : ℝ) *
          ZLattice.covolume (lattice3 b) =
            |(columnMatrix3 (fun i => (u i : RealTriple))).det| := by
  obtain ⟨v, hv, hvL, _, _, hvr⟩ := exists_successive_minima3 b e
  let u : Fin 3 → lattice3 b := fun i => ⟨v i, hvL i⟩
  have hu : LinearIndependent ℝ (fun i => (u i : RealTriple)) := hv
  refine ⟨u, hu, hvr, (lattice3_generated_index_det b (b.restrictScalars ℤ) u hu).1,
    successive_minima3_attaining_index_le_six b e u hu hvr, ?_⟩
  intro c
  exact (lattice3_generated_index_det b c u hu).2


open scoped Matrix

abbrev IntegerTriple := Fin 3 → ℤ

def primaryResidue3 (A : Matrix (Fin 3) (Fin 3) ℤ) (p : ℕ) (a : Fin 3 → ℕ) :
    IntegerTriple →+ (∀ i : Fin 3, ZMod (p ^ a i)) where
  toFun x i := ((A *ᵥ x) i : ZMod (p ^ a i))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [Matrix.mulVec_add]

def mixedCongruence3 (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℕ) :
    AddSubgroup IntegerTriple :=
  (primaryResidue3 A₂ 2 a).ker ⊓ (primaryResidue3 A₃ 3 b).ker

theorem mem_mixedCongruence3
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℕ) (x : IntegerTriple) :
    x ∈ mixedCongruence3 A₂ A₃ a b ↔
      (∀ i, (2 : ℤ) ^ a i ∣ (A₂ *ᵥ x) i) ∧
      (∀ i, (3 : ℤ) ^ b i ∣ (A₃ *ᵥ x) i) := by
  simp only [mixedCongruence3, AddSubgroup.mem_inf, AddMonoidHom.mem_ker,
    primaryResidue3, AddMonoidHom.coe_mk, ZeroHom.coe_mk, funext_iff,
    Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, Nat.cast_ofNat]

theorem primaryResidue3_surjective
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : IsUnit A) (p : ℕ) (a : Fin 3 → ℕ) :
    Function.Surjective (primaryResidue3 A p a) := by
  intro y
  choose z hz using fun i => ZMod.intCast_surjective (y i)
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA z
  refine ⟨x, ?_⟩
  funext i
  change ((A *ᵥ x) i : ZMod (p ^ a i)) = y i
  rw [hx]
  exact hz i

theorem primaryResidue3_index
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : IsUnit A) (p : ℕ) (a : Fin 3 → ℕ) :
    (primaryResidue3 A p a).ker.index = p ^ (∑ i, a i) := by
  rw [← AddMonoidHom.comap_bot,
    AddSubgroup.index_comap_of_surjective ⊥ (primaryResidue3_surjective A hA p a),
    AddSubgroup.index_bot]
  simp only [Nat.card_pi, Nat.card_zmod]
  exact Finset.prod_pow_eq_pow_sum Finset.univ a p

theorem mixedCongruence3_index
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) :
    (mixedCongruence3 A₂ A₃ a b).index = 2 ^ (∑ i, a i) * 3 ^ (∑ i, b i) := by
  let H := (primaryResidue3 A₂ 2 a).ker
  let K := (primaryResidue3 A₃ 3 b).ker
  have hH : H.index = 2 ^ (∑ i, a i) := primaryResidue3_index A₂ h₂ 2 a
  have hK : K.index = 3 ^ (∑ i, b i) := primaryResidue3_index A₃ h₃ 3 b
  have hc : Nat.Coprime H.index K.index := by
    rw [hH, hK]
    exact (by norm_num : Nat.Coprime 2 3).pow _ _
  have hne : (H ⊓ K).index ≠ 0 := AddSubgroup.index_inf_ne_zero
    (by rw [hH]; positivity) (by rw [hK]; positivity)
  have hd : H.index * K.index ∣ (H ⊓ K).index := hc.mul_dvd_of_dvd_of_dvd
    (AddSubgroup.index_dvd_of_le inf_le_left) (AddSubgroup.index_dvd_of_le inf_le_right)
  have heq : (H ⊓ K).index = H.index * K.index :=
    le_antisymm AddSubgroup.index_inf_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd)
  exact heq.trans (congrArg₂ (· * ·) hH hK)

theorem mixedCongruence3_finite
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) : Finite (IntegerTriple ⧸ mixedCongruence3 A₂ A₃ a b) := by
  apply Nat.finite_of_card_ne_zero
  change (mixedCongruence3 A₂ A₃ a b).index ≠ 0
  rw [mixedCongruence3_index A₂ A₃ h₂ h₃ a b]
  positivity


def retainedIntegerMatrix3 (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ :=
  ![Pi.single (k.succAbove 0) 1, Pi.single (k.succAbove 1) 1, fun _ => 1]

theorem retainedIntegerMatrix3_det (k : Fin 3) :
    (retainedIntegerMatrix3 k).det = if k = 1 then -1 else 1 := by
  rw [Matrix.det_fin_three]
  fin_cases k <;> decide

theorem retainedIntegerMatrix3_isUnit (k : Fin 3) : IsUnit (retainedIntegerMatrix3 k) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [retainedIntegerMatrix3_det]
  split <;> norm_num

theorem retainedIntegerMatrix3_apply (k i : Fin 3) (x : Fin 3 → ℤ) :
    (((retainedIntegerMatrix3 k *ᵥ x) i : ℤ) : ℚ) =
      threeCoordinateSumForms k i (fun j => (x j : ℚ)) := by
  fin_cases i <;> simp [retainedIntegerMatrix3, threeCoordinateSumForms, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Pi.single_apply, add_assoc]


theorem mixedCongruence3_multiple
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℕ) (x : IntegerTriple) :
    ((2 : ℤ) ^ (∑ i, a i) * 3 ^ (∑ i, b i)) • x ∈ mixedCongruence3 A₂ A₃ a b := by
  rw [mem_mixedCongruence3]
  constructor
  · intro i
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i))) _) _
  · intro i
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (pow_dvd_pow _ (Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i))) _) _

theorem mixedCongruence3_finrank
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℕ) :
    Module.finrank ℤ (mixedCongruence3 A₂ A₃ a b) = 3 := by
  let G := mixedCongruence3 A₂ A₃ a b
  let D : ℤ := 2 ^ (∑ i, a i) * 3 ^ (∑ i, b i)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  let f : IntegerTriple →ₗ[ℤ] IntegerTriple := D • LinearMap.id
  have hf : Function.Injective f := by
    intro x y h
    funext i
    have hi := congrFun h i
    change D * x i = D * y i at hi
    exact mul_left_cancel₀ hD hi
  let u : Fin 3 → G := fun i => ⟨D • Pi.basisFun ℤ (Fin 3) i,
    mixedCongruence3_multiple A₂ A₃ a b _⟩
  have hu : LinearIndependent ℤ u := by
    apply LinearIndependent.of_comp G.toIntSubmodule.subtype
    exact (Pi.basisFun ℤ (Fin 3)).linearIndependent.map' f
      (LinearMap.ker_eq_bot_of_injective hf)
  letI : Module.Finite ℤ G := Module.Finite.of_injective G.subtype.toIntLinearMap Subtype.val_injective
  have hl := hu.fintype_card_le_finrank
  have hh := G.toIntSubmodule.finrank_le
  have hd : Module.finrank ℤ IntegerTriple = 3 := by simp [IntegerTriple, Module.finrank_pi]
  rw [hd] at hh
  simpa using le_antisymm hh hl

theorem mixedCongruence3_has_basis
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℕ) :
    Nonempty (Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) := by
  let G := mixedCongruence3 A₂ A₃ a b
  letI : Module.Finite ℤ G := Module.Finite.of_injective G.subtype.toIntLinearMap Subtype.val_injective
  letI : NoZeroSMulDivisors ℤ G := Function.Injective.noZeroSMulDivisors
    (fun x : G => (x : IntegerTriple)) Subtype.val_injective rfl (fun _ _ => rfl)
  exact ⟨Module.finBasisOfFinrankEq ℤ G (mixedCongruence3_finrank A₂ A₃ a b)⟩

def integerTripleReal3 : IntegerTriple →ₗ[ℤ] RealTriple where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp [Int.cast_mul]


theorem mixedCongruence3_basis_det
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) :
    |(columnMatrix3 (fun i => integerTripleReal3 (c i))).det| =
      (2 : ℝ) ^ (∑ i, a i) * 3 ^ (∑ i, b i) := by
  have hi := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 3))
    (mixedCongruence3 A₂ A₃ a b) c
  rw [mixedCongruence3_index A₂ A₃ h₂ h₃ a b] at hi
  have hmat : columnMatrix3 (fun i => integerTripleReal3 (c i)) =
      ((Pi.basisFun ℤ (Fin 3)).toMatrix (fun i => (c i : IntegerTriple))).map (Int.castRingHom ℝ) := by
    ext i j
    rfl
  have hdet : (columnMatrix3 (fun i => integerTripleReal3 (c i))).det =
      (((Pi.basisFun ℤ (Fin 3)).toMatrix (fun i => (c i : IntegerTriple))).det : ℝ) := by
    rw [hmat]
    exact (RingHom.map_det (Int.castRingHom ℝ) _).symm
  rw [hdet]
  have hstd : (Pi.basisFun ℤ (Fin 3)).det (fun i => (c i : IntegerTriple)) =
      ((Pi.basisFun ℤ (Fin 3)).toMatrix (fun i => (c i : IntegerTriple))).det :=
    Basis.det_apply _ _
  rw [hstd] at hi
  have hh := congrArg (fun n : ℕ => (n : ℝ)) hi
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_natAbs, Int.cast_abs] using hh.symm

theorem mixedCongruence3_basis_det_ne_zero
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) :
    (columnMatrix3 (fun i => integerTripleReal3 (c i))).det ≠ 0 := by
  apply abs_pos.mp
  rw [mixedCongruence3_basis_det A₂ A₃ h₂ h₃ a b c]
  positivity

theorem mixedCongruence3_basis_real_independent
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) :
    LinearIndependent ℝ (fun i => integerTripleReal3 (c i)) := by
  exact Matrix.linearIndependent_cols_of_det_ne_zero
    (mixedCongruence3_basis_det_ne_zero A₂ A₃ h₂ h₃ a b c)

def mixedCongruence3_realBasis
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) :
    Basis (Fin 3) ℝ RealTriple := by
  classical
  exact basisOfPiSpaceOfLinearIndependent
    (mixedCongruence3_basis_real_independent A₂ A₃ h₂ h₃ a b c)

theorem mixedCongruence3_realBasis_apply
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) (i : Fin 3) :
    mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c i = integerTripleReal3 (c i) := by
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent
    (mixedCongruence3_basis_real_independent A₂ A₃ h₂ h₃ a b c)) i

def mixedCongruence3_realImage
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℕ) : Submodule ℤ RealTriple :=
  (mixedCongruence3 A₂ A₃ a b).toIntSubmodule.map integerTripleReal3

theorem mixedCongruence3_realImage_eq_lattice3
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) :
    mixedCongruence3_realImage A₂ A₃ a b =
      lattice3 (mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c) := by
  let G := mixedCongruence3 A₂ A₃ a b
  let B := mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c
  let f : G →ₗ[ℤ] RealTriple := integerTripleReal3.comp G.subtype.toIntLinearMap
  apply le_antisymm
  · have hspan : Submodule.span ℤ (Set.range c) ≤ (lattice3 B).comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change integerTripleReal3 (c i) ∈ lattice3 B
      rw [← mixedCongruence3_realBasis_apply A₂ A₃ h₂ h₃ a b c i]
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [c.span_eq] at hspan
    rintro y ⟨x, hx, rfl⟩
    exact hspan (Submodule.mem_top : (⟨x, hx⟩ : G) ∈ ⊤)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [mixedCongruence3_realBasis_apply]
    exact ⟨(c i : IntegerTriple), (c i).property, rfl⟩

theorem mixedCongruence3_covolume
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b)) :
    ZLattice.covolume (mixedCongruence3_realImage A₂ A₃ a b) =
      (2 : ℝ) ^ (∑ i, a i) * 3 ^ (∑ i, b i) := by
  rw [mixedCongruence3_realImage_eq_lattice3 A₂ A₃ h₂ h₃ a b c, lattice3_covolume]
  have he : (mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c : Fin 3 → RealTriple) =
      fun i => integerTripleReal3 (c i) :=
    funext (mixedCongruence3_realBasis_apply A₂ A₃ h₂ h₃ a b c)
  rw [he]
  exact mixedCongruence3_basis_det A₂ A₃ h₂ h₃ a b c


theorem mixedCongruence3_real_lattice
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) :
    DiscreteTopology (mixedCongruence3_realImage A₂ A₃ a b) ∧
      Submodule.span ℝ (mixedCongruence3_realImage A₂ A₃ a b : Set RealTriple) = ⊤ := by
  obtain ⟨c⟩ := mixedCongruence3_has_basis A₂ A₃ a b
  rw [mixedCongruence3_realImage_eq_lattice3 A₂ A₃ h₂ h₃ a b c]
  exact ⟨inferInstance, ZSpan.span_top _⟩

theorem mixedCongruence3_covolume_eq_index
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) :
    ZLattice.covolume (mixedCongruence3_realImage A₂ A₃ a b) =
      ((mixedCongruence3 A₂ A₃ a b).index : ℝ) := by
  obtain ⟨c⟩ := mixedCongruence3_has_basis A₂ A₃ a b
  rw [mixedCongruence3_covolume A₂ A₃ h₂ h₃ a b c,
    mixedCongruence3_index A₂ A₃ h₂ h₃ a b]
  push_cast
  rfl

theorem mixedCongruence3_minima_volume_upper
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b))
    (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    (∏ i, successiveRadius3 (mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c) e i) *
      volume.real (parallelepipedBody3 e) ≤
        8 * ((2 : ℝ) ^ (∑ i, a i) * 3 ^ (∑ i, b i)) := by
  have h := successive_minima3_parallelepiped_volume_upper
    (mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c) e
  rw [← mixedCongruence3_realImage_eq_lattice3 A₂ A₃ h₂ h₃ a b c,
    mixedCongruence3_covolume A₂ A₃ h₂ h₃ a b c] at h
  exact h

theorem exists_mixedCongruence3_minima_bounded_index
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (a b : Fin 3 → ℕ) (c : Basis (Fin 3) ℤ (mixedCongruence3 A₂ A₃ a b))
    (e : RealTriple ≃ₗ[ℝ] RealTriple) :
    ∃ u : Fin 3 → mixedCongruence3_realImage A₂ A₃ a b,
      LinearIndependent ℝ (fun i => (u i : RealTriple)) ∧
      (∀ i, coordinateGauge3 e (u i : RealTriple) =
        successiveRadius3 (mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c) e i) ∧
      Finite (mixedCongruence3_realImage A₂ A₃ a b ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index ≤ 6 ∧
      ∀ d : Basis (Fin 3) ℤ (mixedCongruence3_realImage A₂ A₃ a b),
        (Submodule.span ℤ (Set.range u)).toAddSubgroup.index = (d.toMatrix u).det.natAbs ∧
        (d.toMatrix u).det ≠ 0 ∧
        ((Submodule.span ℤ (Set.range u)).toAddSubgroup.index : ℝ) *
          ((2 : ℝ) ^ (∑ i, a i) * 3 ^ (∑ i, b i)) =
            |(columnMatrix3 (fun i => (u i : RealTriple))).det| := by
  have h := exists_successive_minima3_bounded_index
    (mixedCongruence3_realBasis A₂ A₃ h₂ h₃ a b c) e
  rw [← mixedCongruence3_realImage_eq_lattice3 A₂ A₃ h₂ h₃ a b c,
    mixedCongruence3_covolume A₂ A₃ h₂ h₃ a b c] at h
  exact h


theorem padicNorm_int_le_rpow_iff_dvd_ceil
    (p : ℕ) [hp : Fact p.Prime] (Q c : ℝ) (hQ : 1 < Q) (_hc : c ≤ 0) (m : ℤ) :
    (padicNorm p (m : ℚ) : ℝ) ≤ Real.rpow Q c ↔
      (p : ℤ) ^ Nat.ceil (-c * Real.log Q / Real.log p) ∣ m := by
  have hQpos : 0 < Q := lt_trans zero_lt_one hQ
  have hpone : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hppos : (0 : ℝ) < p := lt_trans zero_lt_one hpone
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hpone
  by_cases hm : m = 0
  · subst m
    simpa only [Int.cast_zero, padicNorm.zero, Rat.cast_zero, dvd_zero, iff_true]
      using (Real.rpow_pos_of_pos hQpos c).le
  have hnorm : (padicNorm p (m : ℚ) : ℝ) =
      (p : ℝ) ^ (-(padicValInt p m : ℤ)) := by
    have h := padicNorm.eq_zpow_of_nonzero (p := p) (by exact_mod_cast hm : (m : ℚ) ≠ 0)
    rw [padicValRat.of_int] at h
    simpa only [Rat.cast_zpow, Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) h
  have hdiv (n : ℕ) : (p : ℤ) ^ n ∣ m ↔ n ≤ padicValInt p m := by
    rw [← Nat.cast_pow, Int.natCast_dvd,
      padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hm)]
    rfl
  rw [hdiv, Nat.ceil_le, hnorm, Real.rpow_eq_pow,
    Real.le_rpow_iff_log_le (zpow_pos hppos _) hQpos, Real.log_zpow,
    div_le_iff₀ hlp]
  push_cast
  constructor <;> intro h <;> nlinarith


theorem mem_mixedCongruence3_Q_iff
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (c₂ c₃ : Fin 3 → ℝ) (Q : ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) (x : IntegerTriple) :
    x ∈ mixedCongruence3 A₂ A₃
      (fun i => Nat.ceil (-c₂ i * Real.log Q / Real.log 2))
      (fun i => Nat.ceil (-c₃ i * Real.log Q / Real.log 3)) ↔
      (∀ i, (padicNorm 2 ((A₂ *ᵥ x) i : ℚ) : ℝ) ≤ Real.rpow Q (c₂ i)) ∧
      (∀ i, (padicNorm 3 ((A₃ *ᵥ x) i : ℚ) : ℝ) ≤ Real.rpow Q (c₃ i)) := by
  rw [mem_mixedCongruence3]
  constructor
  · rintro ⟨h2, h3⟩
    exact ⟨fun i => (padicNorm_int_le_rpow_iff_dvd_ceil 2 Q (c₂ i) hQ (hc₂ i) _).mpr (h2 i),
      fun i => (padicNorm_int_le_rpow_iff_dvd_ceil 3 Q (c₃ i) hQ (hc₃ i) _).mpr (h3 i)⟩
  · rintro ⟨h2, h3⟩
    exact ⟨fun i => (padicNorm_int_le_rpow_iff_dvd_ceil 2 Q (c₂ i) hQ (hc₂ i) _).mp (h2 i),
      fun i => (padicNorm_int_le_rpow_iff_dvd_ceil 3 Q (c₃ i) hQ (hc₃ i) _).mp (h3 i)⟩

theorem exists_mixedCongruence3_Q_lattice
    (A₂ A₃ : Matrix (Fin 3) (Fin 3) ℤ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃)
    (c₂ c₃ : Fin 3 → ℝ) (Q : ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    let a := fun i => Nat.ceil (-c₂ i * Real.log Q / Real.log 2)
    let b := fun i => Nat.ceil (-c₃ i * Real.log Q / Real.log 3)
    ∃ G : AddSubgroup IntegerTriple,
      (∀ x, x ∈ G ↔
        (∀ i, (padicNorm 2 ((A₂ *ᵥ x) i : ℚ) : ℝ) ≤ Real.rpow Q (c₂ i)) ∧
        (∀ i, (padicNorm 3 ((A₃ *ᵥ x) i : ℚ) : ℝ) ≤ Real.rpow Q (c₃ i))) ∧
      G = mixedCongruence3 A₂ A₃ a b ∧
      Finite (IntegerTriple ⧸ G) ∧
      G.index = 2 ^ (∑ i, a i) * 3 ^ (∑ i, b i) ∧
      ZLattice.covolume (G.toIntSubmodule.map integerTripleReal3) =
        (2 : ℝ) ^ (∑ i, a i) * 3 ^ (∑ i, b i) := by
  dsimp only
  let a := fun i => Nat.ceil (-c₂ i * Real.log Q / Real.log 2)
  let b := fun i => Nat.ceil (-c₃ i * Real.log Q / Real.log 3)
  refine ⟨mixedCongruence3 A₂ A₃ a b,
    mem_mixedCongruence3_Q_iff A₂ A₃ c₂ c₃ Q hQ hc₂ hc₃, rfl,
    mixedCongruence3_finite A₂ A₃ h₂ h₃ a b,
    mixedCongruence3_index A₂ A₃ h₂ h₃ a b, ?_⟩
  change ZLattice.covolume (mixedCongruence3_realImage A₂ A₃ a b) = _
  rw [mixedCongruence3_covolume_eq_index A₂ A₃ h₂ h₃ a b,
    mixedCongruence3_index A₂ A₃ h₂ h₃ a b]
  push_cast
  rfl

theorem exists_retained_mixedCongruence3_Q_lattice
    (k₂ k₃ : Fin 3) (c₂ c₃ : Fin 3 → ℝ) (Q : ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    let a := fun i => Nat.ceil (-c₂ i * Real.log Q / Real.log 2)
    let b := fun i => Nat.ceil (-c₃ i * Real.log Q / Real.log 3)
    ∃ G : AddSubgroup IntegerTriple,
      (∀ x, x ∈ G ↔
        (∀ i, (padicNorm 2 (threeCoordinateSumForms k₂ i (fun j => (x j : ℚ))) : ℝ) ≤
          Real.rpow Q (c₂ i)) ∧
        (∀ i, (padicNorm 3 (threeCoordinateSumForms k₃ i (fun j => (x j : ℚ))) : ℝ) ≤
          Real.rpow Q (c₃ i))) ∧
      G = mixedCongruence3 (retainedIntegerMatrix3 k₂) (retainedIntegerMatrix3 k₃) a b ∧
      Finite (IntegerTriple ⧸ G) ∧
      G.index = 2 ^ (∑ i, a i) * 3 ^ (∑ i, b i) ∧
      ZLattice.covolume (G.toIntSubmodule.map integerTripleReal3) =
        (2 : ℝ) ^ (∑ i, a i) * 3 ^ (∑ i, b i) := by
  obtain ⟨G, hmem, heq, hf, hi, hv⟩ := exists_mixedCongruence3_Q_lattice
    (retainedIntegerMatrix3 k₂) (retainedIntegerMatrix3 k₃)
    (retainedIntegerMatrix3_isUnit k₂) (retainedIntegerMatrix3_isUnit k₃)
    c₂ c₃ Q hQ hc₂ hc₃
  refine ⟨G, ?_, heq, hf, hi, hv⟩
  intro x
  simpa only [retainedIntegerMatrix3_apply] using hmem x


def qThreshold (p : ℕ) (Q c : ℝ) : ℝ := -c * Real.log Q / Real.log p

def ceilingFactor (p t : ℝ) : ℝ := p ^ ((Nat.ceil t : ℝ) - t)

def qRoundingFactor3 (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) : ℝ :=
  ∏ i, ceilingFactor 2 (qThreshold 2 Q (c₂ i)) * ceilingFactor 3 (qThreshold 3 Q (c₃ i))

def qCongruenceIndex3 (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) : ℕ :=
  2 ^ (∑ i, Nat.ceil (qThreshold 2 Q (c₂ i))) *
    3 ^ (∑ i, Nat.ceil (qThreshold 3 Q (c₃ i)))

theorem qThreshold_nonneg (p : ℕ) (hp : 1 < p) (Q c : ℝ) (hQ : 1 < Q) (hc : c ≤ 0) :
    0 ≤ qThreshold p Q c := by
  unfold qThreshold
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  exact div_nonneg (mul_nonneg (neg_nonneg.mpr hc) (Real.log_pos hQ).le)
    (Real.log_pos hpR).le

theorem ceil_sub_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (Nat.ceil t : ℝ) - t ∧ (Nat.ceil t : ℝ) - t < 1 := by
  exact ⟨sub_nonneg.mpr (Nat.le_ceil t), by linarith [Nat.ceil_lt_add_one ht]⟩

theorem ceilingFactor_bounds (p t : ℝ) (hp : 1 < p) (ht : 0 ≤ t) :
    1 ≤ ceilingFactor p t ∧ ceilingFactor p t < p := by
  obtain ⟨h0, h1⟩ := ceil_sub_bounds t ht
  refine ⟨Real.one_le_rpow hp.le h0, ?_⟩
  have h := (Real.rpow_lt_rpow_left_iff hp).mpr h1
  simpa [ceilingFactor] using h

theorem qRoundingFactor3_bounds (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    1 ≤ qRoundingFactor3 Q c₂ c₃ ∧ qRoundingFactor3 Q c₂ c₃ < 216 := by
  let f := fun i => ceilingFactor 2 (qThreshold 2 Q (c₂ i)) *
    ceilingFactor 3 (qThreshold 3 Q (c₃ i))
  have hf (i : Fin 3) : 1 ≤ f i ∧ f i < 6 := by
    have h2 := ceilingFactor_bounds 2 _ (by norm_num)
      (qThreshold_nonneg 2 (by decide) Q (c₂ i) hQ (hc₂ i))
    have h3 := ceilingFactor_bounds 3 _ (by norm_num)
      (qThreshold_nonneg 3 (by decide) Q (c₃ i) hQ (hc₃ i))
    constructor
    · simpa [f] using (mul_le_mul h2.1 h3.1 (by norm_num) (by linarith))
    · have h := mul_lt_mul h2.2 h3.2.le (by linarith : 0 < ceilingFactor 3 (qThreshold 3 Q (c₃ i))) (by norm_num : (0 : ℝ) ≤ 2)
      norm_num [f] at h ⊢
      exact h
  constructor
  · have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin 3 => (1 : ℝ))
      (fun _ _ => by norm_num) (fun i _ => (hf i).1)
    simpa [qRoundingFactor3, f] using h
  · change (∏ i : Fin 3, f i) < 216
    have heq : (∏ i : Fin 3, f i) = f 0 * f 1 * f 2 := by
      simp [Fin.prod_univ_succ]
      ring
    rw [heq]
    have h01 : f 0 * f 1 < 6 * 6 :=
      mul_lt_mul (hf 0).2 (hf 1).2.le (by linarith [(hf 1).1]) (by norm_num)
    have h012 := mul_lt_mul h01 (hf 2).2.le (by linarith [(hf 2).1]) (by norm_num : (0 : ℝ) ≤ 6 * 6)
    norm_num at h012
    exact h012

theorem qRoundingFactor3_eq_one_of_integral (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (h₂ : ∀ i, ∃ n : ℕ, qThreshold 2 Q (c₂ i) = n)
    (h₃ : ∀ i, ∃ n : ℕ, qThreshold 3 Q (c₃ i) = n) :
    qRoundingFactor3 Q c₂ c₃ = 1 := by
  apply Finset.prod_eq_one
  intro i _
  obtain ⟨n, hn⟩ := h₂ i
  obtain ⟨m, hm⟩ := h₃ i
  simp [ceilingFactor, hn, hm]

theorem qThreshold_rpow (p : ℕ) (hp : 1 < p) (Q c : ℝ) (hQ : 1 < Q) :
    (p : ℝ) ^ qThreshold p Q c = Q ^ (-c) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hpR)
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hpR), Real.rpow_def_of_pos (lt_trans zero_lt_one hQ)]
  congr 1
  unfold qThreshold
  field_simp
  ring

theorem pow_ceil_factorization (p t : ℝ) (hp : 0 < p) :
    p ^ Nat.ceil t = p ^ t * ceilingFactor p t := by
  unfold ceilingFactor
  rw [← Real.rpow_add hp]
  have heq : t + ((Nat.ceil t : ℝ) - t) = Nat.ceil t := by ring
  rw [heq, Real.rpow_natCast]

theorem qCongruenceIndex3_factorization (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q) :
    (qCongruenceIndex3 Q c₂ c₃ : ℝ) =
      (∏ i, Q ^ (-c₂ i) * Q ^ (-c₃ i)) * qRoundingFactor3 Q c₂ c₃ := by
  simp only [qCongruenceIndex3, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.prod_pow_eq_pow_sum Finset.univ _ (2 : ℝ),
    ← Finset.prod_pow_eq_pow_sum Finset.univ _ (3 : ℝ), ← Finset.prod_mul_distrib]
  calc
    _ = ∏ i : Fin 3, (Q ^ (-c₂ i) * Q ^ (-c₃ i)) *
        (ceilingFactor 2 (qThreshold 2 Q (c₂ i)) * ceilingFactor 3 (qThreshold 3 Q (c₃ i))) := by
      apply Finset.prod_congr rfl
      intro i _
      have h2 : (2 : ℝ) ^ qThreshold 2 Q (c₂ i) = Q ^ (-c₂ i) := by
        simpa only [Nat.cast_ofNat] using qThreshold_rpow 2 (by decide) Q (c₂ i) hQ
      have h3 : (3 : ℝ) ^ qThreshold 3 Q (c₃ i) = Q ^ (-c₃ i) := by
        simpa only [Nat.cast_ofNat] using qThreshold_rpow 3 (by decide) Q (c₃ i) hQ
      rw [pow_ceil_factorization 2 _ (by norm_num), pow_ceil_factorization 3 _ (by norm_num), h2, h3]
      ring
    _ = _ := Finset.prod_mul_distrib

def archCoordinates3 (A : RealTriple ≃ₗ[ℝ] RealTriple) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 < w i) : RealTriple ≃ₗ[ℝ] RealTriple where
  toFun x i := A x i / w i
  invFun y := A.symm (fun i => y i * w i)
  map_add' x y := by ext i; simp [add_div]
  map_smul' r x := by ext i; simp [smul_eq_mul, mul_div_assoc]
  left_inv x := by
    change A.symm (fun i => (A x i / w i) * w i) = x
    have h : (fun i => (A x i / w i) * w i) = A x :=
      funext (fun i => div_mul_cancel₀ _ (hw i).ne')
    rw [h, A.symm_apply_apply]
  right_inv y := by
    change (fun i => A (A.symm (fun j => y j * w j)) i / w i) = y
    rw [A.apply_symm_apply]
    exact funext (fun i => mul_div_cancel_right₀ _ (hw i).ne')

def archBody3 (A : RealTriple ≃ₗ[ℝ] RealTriple) (w : Fin 3 → ℝ) : Set RealTriple :=
  {x | ∀ i, |A x i| ≤ w i}

theorem archBody3_eq_parallelepiped (A : RealTriple ≃ₗ[ℝ] RealTriple) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 < w i) : archBody3 A w = parallelepipedBody3 (archCoordinates3 A w hw) := by
  ext x
  simp only [archBody3, Set.mem_setOf_eq, parallelepipedBody3, Set.mem_preimage,
    Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h i
    change -1 ≤ A x i / w i ∧ A x i / w i ≤ 1
    rw [← abs_le, abs_div, abs_of_pos (hw i), div_le_iff₀ (hw i), one_mul]
    exact h i
  · intro h i
    have hi := h i
    change -1 ≤ A x i / w i ∧ A x i / w i ≤ 1 at hi
    rwa [← abs_le, abs_div, abs_of_pos (hw i), div_le_iff₀ (hw i), one_mul] at hi

theorem archCoordinates3_det (A : RealTriple ≃ₗ[ℝ] RealTriple) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 < w i) :
    LinearMap.det (archCoordinates3 A w hw).toLinearMap = LinearMap.det A.toLinearMap / ∏ i, w i := by
  let B := Pi.basisFun ℝ (Fin 3)
  have hm : LinearMap.toMatrix B B (archCoordinates3 A w hw).toLinearMap =
      Matrix.diagonal (fun i => (w i)⁻¹) * LinearMap.toMatrix B B A.toLinearMap := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, Pi.basisFun_repr, Matrix.diagonal_mul,
      archCoordinates3, div_eq_mul_inv, mul_comm]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_mul, Matrix.det_diagonal,
    Finset.prod_inv_distrib, LinearMap.det_toMatrix]
  ring

theorem archBody3_volume (A : RealTriple ≃ₗ[ℝ] RealTriple) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 < w i) :
    volume.real (archBody3 A w) = 8 * (∏ i, w i) / |LinearMap.det A.toLinearMap| := by
  have hwprod : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  rw [archBody3_eq_parallelepiped A w hw, parallelepipedBody3_volume,
    archCoordinates3_det, abs_div, abs_of_pos hwprod]
  field_simp

def retainedRealMatrix3 (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (retainedIntegerMatrix3 k).map (Int.castRingHom ℝ)

theorem retainedRealMatrix3_det (k : Fin 3) :
    (retainedRealMatrix3 k).det = if k = 1 then -1 else 1 := by
  have hcast : (retainedRealMatrix3 k).det = ((retainedIntegerMatrix3 k).det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) _).symm
  rw [hcast, retainedIntegerMatrix3_det]
  split <;> norm_num

def retainedRealCoordinates3 (k : Fin 3) : RealTriple ≃ₗ[ℝ] RealTriple :=
  LinearEquiv.ofBijective (Matrix.toLin' (retainedRealMatrix3 k)) (by
    have hu : IsUnit (retainedRealMatrix3 k) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [retainedRealMatrix3_det]
      split <;> norm_num
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem retainedRealCoordinates3_apply (k : Fin 3) (x : RealTriple) :
    retainedRealCoordinates3 k x = ![x (k.succAbove 0), x (k.succAbove 1), ∑ j, x j] := by
  ext i
  fin_cases i <;> simp [retainedRealCoordinates3, retainedRealMatrix3, retainedIntegerMatrix3,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply, add_assoc]

theorem retainedRealCoordinates3_abs_det (k : Fin 3) :
    |LinearMap.det (retainedRealCoordinates3 k).toLinearMap| = 1 := by
  change |LinearMap.det (Matrix.toLin' (retainedRealMatrix3 k))| = 1
  rw [LinearMap.det_toLin', retainedRealMatrix3_det]
  split <;> norm_num

theorem retainedRealBody3_volume (k : Fin 3) (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) :
    volume.real (archBody3 (retainedRealCoordinates3 k) w) = 8 * ∏ i, w i := by
  rw [archBody3_volume _ _ hw, retainedRealCoordinates3_abs_det, div_one]

def qSourceBody3 (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) : Set RealTriple :=
  {x | ∀ i, |(retainedRealMatrix3 k *ᵥ x) i| ≤ Q ^ c₀ i}

def qSourceCoordinates3 (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) (hQ : 1 < Q) :
    RealTriple ≃ₗ[ℝ] RealTriple :=
  archCoordinates3 (retainedRealCoordinates3 k) (fun i => Q ^ c₀ i)
    (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (c₀ i))

def qSourceLattice3 (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) : AddSubgroup IntegerTriple :=
  mixedCongruence3 (retainedIntegerMatrix3 k₂) (retainedIntegerMatrix3 k₃)
    (fun i => Nat.ceil (qThreshold 2 Q (c₂ i)))
    (fun i => Nat.ceil (qThreshold 3 Q (c₃ i)))

theorem qSourceBody3_eq_parallelepiped (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) (hQ : 1 < Q) :
    qSourceBody3 k Q c₀ = parallelepipedBody3 (qSourceCoordinates3 k Q c₀ hQ) := by
  change archBody3 (retainedRealCoordinates3 k) (fun i => Q ^ c₀ i) = _
  exact archBody3_eq_parallelepiped _ _ _

theorem qSourceBody3_volume (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ) (hQ : 1 < Q) :
    volume.real (qSourceBody3 k Q c₀) = 8 * ∏ i, Q ^ c₀ i := by
  change volume.real (archBody3 (retainedRealCoordinates3 k) (fun i => Q ^ c₀ i)) = _
  exact retainedRealBody3_volume _ _ (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) (c₀ i))

theorem qSourceLattice3_spec (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    (∀ x, x ∈ qSourceLattice3 k₂ k₃ Q c₂ c₃ ↔
      (∀ i, (padicNorm 2 (threeCoordinateSumForms k₂ i (fun j => (x j : ℚ))) : ℝ) ≤ Q ^ c₂ i) ∧
      (∀ i, (padicNorm 3 (threeCoordinateSumForms k₃ i (fun j => (x j : ℚ))) : ℝ) ≤ Q ^ c₃ i)) ∧
    Finite (IntegerTriple ⧸ qSourceLattice3 k₂ k₃ Q c₂ c₃) ∧
    (qSourceLattice3 k₂ k₃ Q c₂ c₃).index = qCongruenceIndex3 Q c₂ c₃ ∧
    ZLattice.covolume ((qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3) =
      (qCongruenceIndex3 Q c₂ c₃ : ℝ) := by
  obtain ⟨G, hm, heq, hf, hi, hv⟩ :=
    exists_retained_mixedCongruence3_Q_lattice k₂ k₃ c₂ c₃ Q hQ hc₂ hc₃
  have heq' : G = qSourceLattice3 k₂ k₃ Q c₂ c₃ := heq
  subst G
  refine ⟨hm, hf, hi, ?_⟩
  simpa only [qCongruenceIndex3, qThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hv

theorem qBalanced_width_product (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (∏ i, Q ^ (-c₂ i) * Q ^ (-c₃ i)) = ∏ i, Q ^ c₀ i := by
  have hQpos : 0 < Q := lt_trans zero_lt_one hQ
  simp_rw [← Real.rpow_add hQpos]
  rw [← Real.rpow_sum_of_pos hQpos _ Finset.univ, ← Real.rpow_sum_of_pos hQpos _ Finset.univ]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [Finset.sum_add_distrib] at hb
  linarith

theorem qCongruenceIndex3_balanced (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    (qCongruenceIndex3 Q c₂ c₃ : ℝ) = (∏ i, Q ^ c₀ i) * qRoundingFactor3 Q c₂ c₃ := by
  rw [qCongruenceIndex3_factorization Q c₂ c₃ hQ, qBalanced_width_product Q c₀ c₂ c₃ hQ hb]

theorem qSourceBody3_volume_ratio (k : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    volume.real (qSourceBody3 k Q c₀) / (8 * (qCongruenceIndex3 Q c₂ c₃ : ℝ)) =
      1 / qRoundingFactor3 Q c₂ c₃ := by
  have hW : 0 < ∏ i, Q ^ c₀ i :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  have hR : 0 < qRoundingFactor3 Q c₂ c₃ :=
    lt_of_lt_of_le zero_lt_one (qRoundingFactor3_bounds Q c₂ c₃ hQ hc₂ hc₃).1
  rw [qSourceBody3_volume k Q c₀ hQ, qCongruenceIndex3_balanced Q c₀ c₂ c₃ hQ hb]
  field_simp
  ring

theorem exists_qSource_minima_upper
    (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∃ B : Basis (Fin 3) ℝ RealTriple,
      lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 ∧
      (∏ i, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) i) ≤ qRoundingFactor3 Q c₂ c₃ ∧
      qRoundingFactor3 Q c₂ c₃ < 216 := by
  let a := fun i => Nat.ceil (qThreshold 2 Q (c₂ i))
  let b := fun i => Nat.ceil (qThreshold 3 Q (c₃ i))
  obtain ⟨c⟩ := mixedCongruence3_has_basis (retainedIntegerMatrix3 k₂) (retainedIntegerMatrix3 k₃) a b
  let B := mixedCongruence3_realBasis _ _ (retainedIntegerMatrix3_isUnit k₂)
    (retainedIntegerMatrix3_isUnit k₃) a b c
  have hL : lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 :=
    (mixedCongruence3_realImage_eq_lattice3 _ _ (retainedIntegerMatrix3_isUnit k₂)
      (retainedIntegerMatrix3_isUnit k₃) a b c).symm
  refine ⟨B, hL, ?_, (qRoundingFactor3_bounds Q c₂ c₃ hQ hc₂ hc₃).2⟩
  have h := successive_minima3_parallelepiped_volume_upper B (qSourceCoordinates3 k₀ Q c₀ hQ)
  have hvol : volume.real (parallelepipedBody3 (qSourceCoordinates3 k₀ Q c₀ hQ)) =
      8 * ∏ i, Q ^ c₀ i := by
    rw [← qSourceBody3_eq_parallelepiped k₀ Q c₀ hQ]
    exact qSourceBody3_volume k₀ Q c₀ hQ
  have hcov : ZLattice.covolume (lattice3 B) = (qCongruenceIndex3 Q c₂ c₃ : ℝ) := by
    rw [hL]
    exact (qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).2.2.2
  rw [hvol, hcov, qCongruenceIndex3_balanced Q c₀ c₂ c₃ hQ hb] at h
  have hW : 0 < ∏ i, Q ^ c₀ i :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  apply (mul_le_mul_right (mul_pos (by norm_num : (0 : ℝ) < 8) hW)).mp
  nlinarith
theorem qRoundingFactor3_eq_one_of_integer (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (h₂ : ∀ i, ∃ n : ℤ, qThreshold 2 Q (c₂ i) = n)
    (h₃ : ∀ i, ∃ n : ℤ, qThreshold 3 Q (c₃ i) = n) :
    qRoundingFactor3 Q c₂ c₃ = 1 := by
  have hnat (t : ℝ) (ht : 0 ≤ t) (hi : ∃ n : ℤ, t = n) : ∃ n : ℕ, t = n := by
    obtain ⟨n, rfl⟩ := hi
    have hn : 0 ≤ n := by exact_mod_cast ht
    refine ⟨n.toNat, ?_⟩
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hn)
    simpa only [Int.cast_natCast] using h.symm
  exact qRoundingFactor3_eq_one_of_integral Q c₂ c₃
    (fun i => hnat _ (qThreshold_nonneg 2 (by decide) Q (c₂ i) hQ (hc₂ i)) (h₂ i))
    (fun i => hnat _ (qThreshold_nonneg 3 (by decide) Q (c₃ i) hQ (hc₃ i)) (h₃ i))


theorem integerTripleReal3_injective : Function.Injective integerTripleReal3 := by
  intro x y h
  funext i
  exact Int.cast_injective (congrFun h i)

def integerTripleRealEquiv3 (G : AddSubgroup IntegerTriple) :
    G ≃ₗ[ℤ] G.toIntSubmodule.map integerTripleReal3 :=
  LinearEquiv.ofBijective
    { toFun := fun x => ⟨integerTripleReal3 (x : IntegerTriple), ⟨x, x.property, rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; exact integerTripleReal3.map_add _ _
      map_smul' := by intro r x; apply Subtype.ext; exact integerTripleReal3.map_smul r _ }
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        exact integerTripleReal3_injective (congrArg Subtype.val h)
      · rintro ⟨y, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)

theorem integerTripleRealEquiv3_apply (G : AddSubgroup IntegerTriple) (x : G) :
    ((integerTripleRealEquiv3 G x : G.toIntSubmodule.map integerTripleReal3) : RealTriple) =
      integerTripleReal3 (x : IntegerTriple) := by
  rfl

theorem integerTripleRealEquiv3_symm_apply (G : AddSubgroup IntegerTriple)
    (y : G.toIntSubmodule.map integerTripleReal3) :
    integerTripleReal3 ((integerTripleRealEquiv3 G).symm y : IntegerTriple) = (y : RealTriple) := by
  exact congrArg Subtype.val ((integerTripleRealEquiv3 G).apply_symm_apply y)

theorem integerTripleRealEquiv3_symm_apply_apply (G : AddSubgroup IntegerTriple) (x : G) :
    (integerTripleRealEquiv3 G).symm (integerTripleRealEquiv3 G x) = x := by
  exact (integerTripleRealEquiv3 G).symm_apply_apply x

theorem integerTripleRealEquiv3_map_span (G : AddSubgroup IntegerTriple) (u : Fin 3 → G) :
    (Submodule.span ℤ (Set.range u)).map (integerTripleRealEquiv3 G).toLinearMap =
      Submodule.span ℤ (Set.range (fun i => integerTripleRealEquiv3 G (u i))) := by
  simpa only [Set.range_comp'] using
    Submodule.map_span (integerTripleRealEquiv3 G).toLinearMap (Set.range u)

def integerTripleRealQuotientEquiv3 (G : AddSubgroup IntegerTriple) (u : Fin 3 → G) :
    (G ⧸ Submodule.span ℤ (Set.range u)) ≃ₗ[ℤ]
      ((G.toIntSubmodule.map integerTripleReal3) ⧸
        Submodule.span ℤ (Set.range (fun i => integerTripleRealEquiv3 G (u i)))) :=
  Submodule.Quotient.equiv _ _ (integerTripleRealEquiv3 G) (integerTripleRealEquiv3_map_span G u)

theorem integerTripleRealEquiv3_finite_iff (G : AddSubgroup IntegerTriple) (u : Fin 3 → G) :
    Finite (G ⧸ Submodule.span ℤ (Set.range u)) ↔
      Finite ((G.toIntSubmodule.map integerTripleReal3) ⧸
        Submodule.span ℤ (Set.range (fun i => integerTripleRealEquiv3 G (u i)))) :=
  (integerTripleRealQuotientEquiv3 G u).toEquiv.finite_iff

theorem integerTripleRealEquiv3_index (G : AddSubgroup IntegerTriple) (u : Fin 3 → G) :
    (Submodule.span ℤ (Set.range u)).toAddSubgroup.index =
      (Submodule.span ℤ (Set.range (fun i => integerTripleRealEquiv3 G (u i)))).toAddSubgroup.index := by
  change Nat.card (G ⧸ Submodule.span ℤ (Set.range u)) =
    Nat.card ((G.toIntSubmodule.map integerTripleReal3) ⧸
      Submodule.span ℤ (Set.range (fun i => integerTripleRealEquiv3 G (u i))))
  exact Nat.card_congr (integerTripleRealQuotientEquiv3 G u).toEquiv


theorem qSource_arch_bound (k : Fin 3) (Q : ℝ) (c₀ : Fin 3 → ℝ)
    (hQ : 1 < Q) (x : RealTriple) (i : Fin 3) :
    |retainedRealCoordinates3 k x i| ≤
      coordinateGauge3 (qSourceCoordinates3 k Q c₀ hQ) x * Q ^ c₀ i := by
  have h : |qSourceCoordinates3 k Q c₀ hQ x i| ≤
      coordinateGauge3 (qSourceCoordinates3 k Q c₀ hQ) x := by
    simpa only [coordinateGauge3, Real.norm_eq_abs] using
      norm_le_pi_norm (qSourceCoordinates3 k Q c₀ hQ x) i
  change |retainedRealCoordinates3 k x i / Q ^ c₀ i| ≤ _ at h
  have hw : 0 < Q ^ c₀ i := Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _
  rwa [abs_div, abs_of_pos hw, div_le_iff₀ hw] at h

theorem exists_qSource_integer_attaining_frame
    (k₀ k₂ k₃ : Fin 3) (Q : ℝ) (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hQ : 1 < Q) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∃ (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → qSourceLattice3 k₂ k₃ Q c₂ c₃),
      lattice3 B = (qSourceLattice3 k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3 ∧
      LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) ∧
      (∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
        (integerTripleReal3 (u j : IntegerTriple)) =
          successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) ∧
      Finite ((qSourceLattice3 k₂ k₃ Q c₂ c₃) ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index ≤ 6 ∧
      (∀ i j, |retainedRealCoordinates3 k₀ (integerTripleReal3 (u j : IntegerTriple)) i| ≤
        successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j * Q ^ c₀ i) ∧
      (∀ i j, (padicNorm 2 (threeCoordinateSumForms k₂ i
        (fun l => ((u j : IntegerTriple) l : ℚ))) : ℝ) ≤ Q ^ c₂ i) ∧
      (∀ i j, (padicNorm 3 (threeCoordinateSumForms k₃ i
        (fun l => ((u j : IntegerTriple) l : ℚ))) : ℝ) ≤ Q ^ c₃ i) ∧
      (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) ≤
        qRoundingFactor3 Q c₂ c₃ ∧ qRoundingFactor3 Q c₂ c₃ < 216 ∧
      (∏ j, successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j) < 216 := by
  obtain ⟨B, hL, hp, hR⟩ := exists_qSource_minima_upper k₀ k₂ k₃ Q c₀ c₂ c₃ hQ hc₂ hc₃ hb
  have hv := exists_successive_minima3_bounded_index B (qSourceCoordinates3 k₀ Q c₀ hQ)
  rw [hL] at hv
  obtain ⟨v, hvLI, hvAtt, hvFin, hvIndex, _⟩ := hv
  let G := qSourceLattice3 k₂ k₃ Q c₂ c₃
  let u : Fin 3 → G := fun j => (integerTripleRealEquiv3 G).symm (v j)
  have huv : (fun j => integerTripleRealEquiv3 G (u j)) = v :=
    funext (fun j => (integerTripleRealEquiv3 G).apply_symm_apply (v j))
  have hcast (j : Fin 3) : integerTripleReal3 (u j : IntegerTriple) = (v j : RealTriple) :=
    integerTripleRealEquiv3_symm_apply G (v j)
  have huLI : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)) := by
    simpa only [hcast] using hvLI
  have huAtt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) =
        successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j := by
    simpa only [hcast] using hvAtt
  have huFin : Finite (G ⧸ Submodule.span ℤ (Set.range u)) := by
    apply (integerTripleRealEquiv3_finite_iff G u).mpr
    rw [huv]
    exact hvFin
  have huIndex : (Submodule.span ℤ (Set.range u)).toAddSubgroup.index ≤ 6 := by
    rw [integerTripleRealEquiv3_index G u, huv]
    exact hvIndex
  refine ⟨B, u, hL, huLI, huAtt, huFin, huIndex, ?_, ?_, ?_, hp, hR, hp.trans_lt hR⟩
  · intro i j
    have h := qSource_arch_bound k₀ Q c₀ hQ (integerTripleReal3 (u j : IntegerTriple)) i
    rwa [huAtt j] at h
  · intro i j
    exact ((qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).1
      (u j : IntegerTriple) |>.mp (u j).property).1 i
  · intro i j
    exact ((qSourceLattice3_spec k₂ k₃ Q c₂ c₃ hQ hc₂ hc₃).1
      (u j : IntegerTriple) |>.mp (u j).property).2 i


end

end JSP000334


namespace JSP000334

noncomputable def rothOmega (m : ℕ) (theta : ℝ) : ℝ :=
  24 / (2 : ℝ) ^ m * (theta / 12) ^ (2 * m - 1)

theorem rothOmega_eq_source (m : ℕ) (theta : ℝ) :
    rothOmega m theta =
      24 * Real.rpow 2 (-(m : ℝ)) * (theta / 12) ^ (2 * m - 1) := by
  rw [Real.rpow_eq_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp only [rothOmega, div_eq_mul_inv]

theorem rothOmega_induction_ratio (m : ℕ) (theta : ℝ) :
    rothOmega (m + 2) (theta ^ 2 / 12) =
      (theta / 12) ^ (2 * m + 1) * (2 * rothOmega (m + 3) theta) := by
  have hsq : theta ^ 2 / 12 / 12 = (theta / 12) ^ 2 := by ring
  have hexp : 2 * (2 * (m + 2) - 1) = (2 * m + 1) + (2 * (m + 3) - 1) := by omega
  have hden : (2 : ℝ) ^ (m + 3) = (2 : ℝ) ^ (m + 2) * 2 := by
    simpa [Nat.add_assoc] using (pow_succ (2 : ℝ) (m + 2))
  unfold rothOmega
  rw [hsq, ← pow_mul, hexp, pow_add, hden]
  ring

theorem rothOmega_induction_transfer_fails (m : ℕ) (theta : ℝ)
    (htheta : 0 < theta) (hthetaUpper : theta < 1 / 12) :
    rothOmega (m + 2) (theta ^ 2 / 12) < 2 * rothOmega (m + 3) theta := by
  rw [rothOmega_induction_ratio]
  have hbase : 0 ≤ theta / 12 := by positivity
  have hlt : theta / 12 < 1 := by linarith
  have hpow : (theta / 12) ^ (2 * m + 1) < 1 := by
    exact pow_lt_one₀ hbase hlt (by omega)
  have hpos : 0 < 2 * rothOmega (m + 3) theta := by
    unfold rothOmega
    positivity
  nlinarith [mul_pos hpos (sub_pos.mpr hpow)]

end JSP000334


namespace JSP000334

noncomputable abbrev omega89 (m : ℕ) (t : ℝ) : ℝ := rothOmega m t

noncomputable def omega65 (m : ℕ) (t : ℝ) : ℝ :=
  24 / (2 : ℝ) ^ m * (t / 12) ^ (2 ^ m - 1)

theorem omega65_eq_source (m : ℕ) (t : ℝ) :
    omega65 m t = 24 * Real.rpow 2 (-(m : ℝ)) * (t / 12) ^ (2 ^ m - 1) := by
  rw [Real.rpow_eq_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp only [omega65, div_eq_mul_inv]

theorem omega65_pos (m : ℕ) (t : ℝ) (ht : 0 < t) : 0 < omega65 m t := by
  unfold omega65
  positivity

noncomputable def rothInductionOmega (m : ℕ) (t : ℝ) : ℝ :=
  24 / (2 : ℝ) ^ m * (t / 12) ^ (2 ^ (m - 1))

theorem rothInductionOmega_eq_formula (m : ℕ) (t : ℝ) :
    rothInductionOmega m t = 24 * Real.rpow 2 (-(m : ℝ)) * (t / 12) ^ (2 ^ (m - 1)) := by
  rw [Real.rpow_eq_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp only [rothInductionOmega, div_eq_mul_inv]

theorem rothInductionOmega_pos (m : ℕ) (t : ℝ) (ht : 0 < t) : 0 < rothInductionOmega m t := by
  unfold rothInductionOmega
  positivity

theorem omega65_induction (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    rothInductionOmega m (t ^ 2 / 12) = 2 * rothInductionOmega (m + 1) t := by
  have hsq : t ^ 2 / 12 / 12 = (t / 12) ^ 2 := by ring
  have hexp : 2 * 2 ^ (m - 1) = 2 ^ ((m + 1) - 1) := by
    have hh : m = (m - 1) + 1 := by omega
    simp only [Nat.add_sub_cancel]
    conv_rhs => rw [hh, pow_succ]
    omega
  unfold rothInductionOmega
  rw [hsq, ← pow_mul, hexp, pow_succ]
  ring

theorem roth_exponent65_gt89 (m : ℕ) (hm : 4 ≤ m) : 2 * m - 1 < 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hp : 2 ^ ((m + 1) - 1) = 2 ^ (m - 1) * 2 := by
      have he : (m + 1) - 1 = (m - 1) + 1 := by omega
      rw [he, pow_succ]
    rw [hp]
    omega

theorem omega65_eq89_one (t : ℝ) : rothInductionOmega 1 t = omega89 1 t := by
  norm_num [rothInductionOmega, omega89, rothOmega]

theorem omega89_lt65_small (m : ℕ) (hm : 2 ≤ m) (hm' : m ≤ 3)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1 / 12) : omega89 m t < rothInductionOmega m t := by
  unfold omega89 rothOmega rothInductionOmega
  apply mul_lt_mul_of_pos_left ?_ (by positivity)
  apply pow_lt_pow_right_of_lt_one₀ (by positivity : 0 < t / 12) (by linarith : t / 12 < 1)
  have hh : m = 2 ∨ m = 3 := by omega
  rcases hh with rfl | rfl <;> norm_num

theorem omega65_lt89_large (m : ℕ) (hm : 4 ≤ m)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1 / 12) : rothInductionOmega m t < omega89 m t := by
  unfold omega89 rothOmega rothInductionOmega
  exact mul_lt_mul_of_pos_left
    (pow_lt_pow_right_of_lt_one₀ (by positivity : 0 < t / 12)
      (by linarith : t / 12 < 1) (roth_exponent65_gt89 m hm)) (by positivity)

end JSP000334


namespace JSP000334

theorem roth_binomial_det_ne_zero {ell : ℕ} (n : Fin ell → ℕ)
    (hn : Function.Injective n) :
    Matrix.det (fun i j : Fin ell => (Nat.choose (n j) i.val : ℚ)) ≠ 0 := by
  have hv : Matrix.det (Matrix.vandermonde (fun j => (n j : ℚ))) ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr (fun i j h => hn (Nat.cast_injective h))
  have he := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun j => (n j : ℚ)) (fun i : Fin ell => descPochhammer ℚ i.val)
    (fun i => descPochhammer_natDegree ℚ i.val)
    (fun i => monic_descPochhammer ℚ i.val)
  have hscaled :
      (fun i j : Fin ell => (i.val.factorial : ℚ) * (Nat.choose (n j) i.val : ℚ)) =
        (fun i j : Fin ell => (descPochhammer ℚ i.val).eval (n j : ℚ)) := by
    funext i j
    rw [descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have he' : Matrix.det (fun i j : Fin ell =>
      (descPochhammer ℚ i.val).eval (n j : ℚ)) ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact he ▸ hv
  rw [← hscaled] at he'
  change (Matrix.of (fun i j : Fin ell =>
    (i.val.factorial : ℚ) * (Nat.choose (n j) i.val : ℚ))).det ≠ 0 at he'
  rw [Matrix.det_mul_column] at he'
  exact (mul_ne_zero_iff.mp he').2

theorem roth_monomial_hasseWronskian_ne_zero {ell : ℕ}
    (n : Fin ell → ℕ)
    (hn : Function.Injective n) :
    Matrix.det (fun i j : Fin ell =>
      Polynomial.hasseDeriv i.val
        (Polynomial.monomial (n j) (1 : ℚ))) ≠ 0 := by
  intro hz
  have he := congrArg (Polynomial.evalRingHom (1 : ℚ)) hz

  have hentry (i j : Fin ell) :
      Polynomial.eval (1 : ℚ)
        (Polynomial.hasseDeriv i.val
          (Polynomial.monomial (n j) (1 : ℚ))) =
      (Nat.choose (n j) i.val : ℚ) := by
    simp [Polynomial.hasseDeriv_monomial,
      Polynomial.eval_monomial]

  have heMap :
      (Matrix.map
        (fun i j : Fin ell =>
          Polynomial.hasseDeriv i.val
            (Polynomial.monomial (n j) (1 : ℚ)))
        (Polynomial.eval (1 : ℚ))).det = 0 := by
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply,
      Polynomial.coe_evalRingHom, map_zero] using he

  have hmatrix :
      Matrix.map
        (fun i j : Fin ell =>
          Polynomial.hasseDeriv i.val
            (Polynomial.monomial (n j) (1 : ℚ)))
        (Polynomial.eval (1 : ℚ)) =
      (fun i j : Fin ell =>
        (Nat.choose (n j) i.val : ℚ)) := by
    ext i j
    exact hentry i j

  rw [hmatrix] at heMap
  exact roth_binomial_det_ne_zero n hn heMap

end JSP000334


namespace JSP000334

open scoped BigOperators
open Polynomial

private theorem roth_uniform_det_coeff {ell : ℕ}
    (A : Matrix (Fin ell) (Fin ell) (Polynomial ℚ)) (M : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ M) :
    A.det.coeff (ell * M) = Matrix.det (fun i j => (A i j).coeff M) := by
  rw [Matrix.det_apply, Polynomial.finset_sum_coeff, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.coeff_smul]
  congr 1
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Polynomial.coeff_prod_of_natDegree_le Finset.univ (fun i => A (σ i) i) M
      (fun i _ => hA (σ i) i)

private theorem roth_padded_hasse_entry (p : Polynomial ℚ) (M i : ℕ)
    (hM : p.natDegree ≤ M) :
    let H := X ^ (M - p.natDegree) * (X ^ i * hasseDeriv i p)
    H.natDegree ≤ M ∧
      H.coeff M = (Nat.choose p.natDegree i : ℚ) * p.leadingCoeff := by
  dsimp only
  by_cases hi : i ≤ p.natDegree
  · constructor
    · calc
        _ ≤ (X ^ (M - p.natDegree) : Polynomial ℚ).natDegree +
            (X ^ i * hasseDeriv i p).natDegree := natDegree_mul_le
        _ ≤ (M - p.natDegree) + (i + (p.natDegree - i)) := by
          simp only [natDegree_X_pow]
          gcongr
          calc
            (X ^ i * hasseDeriv i p).natDegree ≤
                (X ^ i : Polynomial ℚ).natDegree + (hasseDeriv i p).natDegree :=
              natDegree_mul_le
            _ ≤ i + (p.natDegree - i) := by
              rw [natDegree_X_pow]
              exact Nat.add_le_add_left (natDegree_hasseDeriv_le p i) i
        _ = M := by omega
    · have he : (p.natDegree - i) + (M - p.natDegree + i) = M := by omega
      have hc : (X ^ (M - p.natDegree) * (X ^ i * hasseDeriv i p)).coeff
          ((p.natDegree - i) + (M - p.natDegree + i)) =
          (Nat.choose p.natDegree i : ℚ) * p.leadingCoeff := by
        rw [← mul_assoc, ← pow_add, coeff_X_pow_mul, hasseDeriv_coeff]
        simp only [Nat.sub_add_cancel hi, coeff_natDegree]
      simpa only [he] using hc
  · have hz := hasseDeriv_eq_zero_of_lt_natDegree p i (lt_of_not_ge hi)
    simp [hz, Nat.choose_eq_zero_of_lt (lt_of_not_ge hi)]

private theorem roth_hasse_wronskian_distinct {ell : ℕ}
    (g : Fin ell → Polynomial ℚ) (h0 : ∀ j, g j ≠ 0)
    (hn : Function.Injective (fun j => (g j).natDegree)) :
    Matrix.det (fun i j : Fin ell => hasseDeriv i.val (g j)) ≠ 0 := by
  let M := ∑ j : Fin ell, (g j).natDegree
  have hM (j : Fin ell) : (g j).natDegree ≤ M :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (g k).natDegree) (Finset.mem_univ j)
  let A : Matrix (Fin ell) (Fin ell) (Polynomial ℚ) :=
    fun i j => X ^ (M - (g j).natDegree) * (X ^ i.val * hasseDeriv i.val (g j))
  have ha (i j : Fin ell) : (A i j).natDegree ≤ M :=
    (roth_padded_hasse_entry (g j) M i.val (hM j)).1
  have hc (i j : Fin ell) :
      (A i j).coeff M = (g j).leadingCoeff * (Nat.choose (g j).natDegree i.val : ℚ) := by
    simpa only [mul_comm] using (roth_padded_hasse_entry (g j) M i.val (hM j)).2
  have ht : A.det.coeff (ell * M) ≠ 0 := by
    rw [roth_uniform_det_coeff A M ha]
    have he : (fun i j : Fin ell => (A i j).coeff M) =
        Matrix.of (fun i j : Fin ell =>
          (g j).leadingCoeff * (Nat.choose (g j).natDegree i.val : ℚ)) := by
      funext i j
      exact hc i j
    rw [he, Matrix.det_mul_row]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
      leadingCoeff_ne_zero.mpr (h0 j)) (roth_binomial_det_ne_zero _ hn)
  intro hz
  have hzA : A.det = 0 := by
    change (Matrix.of fun i j : Fin ell => X ^ (M - (g j).natDegree) *
      (Matrix.of fun i j : Fin ell => X ^ i.val * hasseDeriv i.val (g j)) i j).det = 0
    rw [Matrix.det_mul_row, Matrix.det_mul_column, hz, mul_zero, mul_zero]
  exact ht (by rw [hzA, coeff_zero])

theorem roth_univariate_hasse_wronskian_ne_zero {ell : ℕ}
    (g : Fin ell → Polynomial ℚ) (hg : LinearIndependent ℚ g) :
    Matrix.det (fun i j : Fin ell => hasseDeriv i.val (g j)) ≠ 0 := by
  classical
  revert hg
  refine (measure (fun f : Fin ell → Polynomial ℚ => ∑ j, (f j).natDegree)).wf.induction
    (C := fun f => LinearIndependent ℚ f →
      Matrix.det (fun i j : Fin ell => hasseDeriv i.val (f j)) ≠ 0) g ?_
  intro g ih hg
  by_cases hd : Function.Injective (fun j => (g j).natDegree)
  · exact roth_hasse_wronskian_distinct g (fun j => hg.ne_zero j) hd
  obtain ⟨i, j, hijdeg, hij⟩ := Function.not_injective_iff.mp hd
  let q : ℚ := (g j).leadingCoeff / (g i).leadingCoeff
  let h := Function.update g j (g j - q • g i)
  have hh : LinearIndependent ℚ h := by
    have he : h = g + fun k => (if k = j then -q else 0) • g i := by
      funext k
      by_cases hk : k = j
      · simp [h, Function.update_apply, hk, sub_eq_add_neg]
      · simp [h, Function.update_apply, hk]
    rw [he]
    exact (linearIndependent_add_smul_iff (by simp [hij])).mpr hg
  have hnz : g j - q • g i ≠ 0 := by simpa [h] using hh.ne_zero j
  have hle : (g j - q • g i).natDegree ≤ (g j).natDegree := by
    exact ((g j).natDegree_sub_le (q • g i)).trans
      (max_le le_rfl ((natDegree_smul_le q (g i)).trans hijdeg.le))
  have hc : (g j - q • g i).coeff (g j).natDegree = 0 := by
    rw [coeff_sub, coeff_smul, coeff_natDegree,
      show (g i).coeff (g j).natDegree = (g i).leadingCoeff by
        rw [← hijdeg, coeff_natDegree], smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr (hg.ne_zero i))).symm
  have hlt : (g j - q • g i).natDegree < (g j).natDegree := by
    have hne : (g j - q • g i).natDegree ≠ (g j).natDegree := by
      intro he
      exact (leadingCoeff_ne_zero.mpr hnz) (by rw [← coeff_natDegree, he, hc])
    omega
  have hm : (∑ k : Fin ell, (h k).natDegree) < ∑ k : Fin ell, (g k).natDegree := by
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : k = j
      · simpa [h, hk] using hle
      · simp [h, Function.update_apply, hk]
    · exact ⟨j, Finset.mem_univ j, by simpa [h] using hlt⟩
  have hih := ih h hm hh
  have heW : (fun r k : Fin ell => hasseDeriv r.val (h k)) =
      Matrix.updateCol (fun r k : Fin ell => hasseDeriv r.val (g k)) j
        (fun r => hasseDeriv r.val (g j) +
          C (-q) • hasseDeriv r.val (g i)) := by
    ext r k
    by_cases hk : k = j
    · subst k
      simp [h, map_sub, map_smul, Polynomial.smul_eq_C_mul,
        smul_eq_mul, sub_eq_add_neg]
      rw [← Polynomial.smul_eq_C_mul, map_smul,
        coeff_smul, smul_eq_mul]
    · simp [h, Function.update_apply, hk, Matrix.updateCol_ne hk]
  rw [heW, Matrix.det_updateCol_add_smul_self _ hij.symm] at hih
  exact hih

end JSP000334

namespace JSP000334


noncomputable def rothDividedDerivative {d : ℕ}
    (a : Fin d →₀ ℕ) (P : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin d) ℚ :=
  P.sum fun s z => MvPolynomial.monomial (s - a)
    (z * ∏ k : Fin d, (Nat.choose (s k) (a k) : ℚ))

theorem rothDividedDerivative_monomial {d : ℕ} (a b : Fin d →₀ ℕ) (z : ℚ) :
    rothDividedDerivative a (MvPolynomial.monomial b z) =
      MvPolynomial.monomial (b - a) (z * ∏ k : Fin d, (Nat.choose (b k) (a k) : ℚ)) := by
  simp [rothDividedDerivative]

noncomputable def rothDividedDerivativeLinear {d : ℕ} (a : Fin d →₀ ℕ) :
    MvPolynomial (Fin d) ℚ →ₗ[ℚ] MvPolynomial (Fin d) ℚ where
  toFun := rothDividedDerivative a
  map_add' P Q := by
    apply Finsupp.sum_add_index'
    · intro b
      simp
    · intro b x y
      simp [add_mul, map_add]
  map_smul' q P := by
    change rothDividedDerivative a (q • P) = q • rothDividedDerivative a P
    unfold rothDividedDerivative
    rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
    · apply Finset.sum_congr rfl
      intro b hb
      simp [MvPolynomial.smul_monomial, mul_assoc]
    · intro b
      simp

theorem rothDividedDerivative_zero {d : ℕ} (P : MvPolynomial (Fin d) ℚ) :
    rothDividedDerivative 0 P = P := by
  simpa [rothDividedDerivative, MvPolynomial.sum_def] using
    (MvPolynomial.support_sum_monomial_coeff P)

def rothExponentCode {d : ℕ} (K : ℕ) (b : Fin d → ℕ) : ℕ :=
  ∑ k : Fin d, b k * K ^ k.val

private theorem rothExponentCode_succ {d : ℕ} (K : ℕ) (b : Fin (d+1) → ℕ) :
    rothExponentCode K b = b 0 + K * rothExponentCode K (fun k => b k.succ) := by
  simp [rothExponentCode, Fin.sum_univ_succ, pow_succ, Finset.mul_sum]
  congr 1
  funext i
  ring

theorem rothExponentCode_injOn {d : ℕ} (K : ℕ) (hK : 1 < K)
    (b c : Fin d → ℕ) (hb : ∀ k, b k < K) (hc : ∀ k, c k < K)
    (he : rothExponentCode K b = rothExponentCode K c) : b = c := by
  induction d with
  | zero => exact funext fun k => Fin.elim0 k
  | succ d ih =>
    rw [rothExponentCode_succ, rothExponentCode_succ] at he
    have hh : b 0 = c 0 := by
      have hm := congrArg (fun x => x % K) he
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (hb 0), Nat.mod_eq_of_lt (hc 0)] using hm
    have ht : rothExponentCode K (fun k : Fin d => b k.succ) =
        rothExponentCode K (fun k : Fin d => c k.succ) := by
      rw [hh] at he
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < K) (Nat.add_left_cancel he)
    have hit := ih (fun k => b k.succ) (fun k => c k.succ)
      (fun k => hb k.succ) (fun k => hc k.succ) ht
    funext k
    exact Fin.cases hh (fun j => congrFun hit j) k

noncomputable def rothPowerSpecialization {d : ℕ} (K : ℕ) :
    MvPolynomial (Fin d) ℚ →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval (fun k : Fin d => Polynomial.X ^ (K ^ k.val))

theorem rothPowerSpecialization_monomial {d : ℕ} (K : ℕ)
    (b : Fin d →₀ ℕ) (z : ℚ) :
    rothPowerSpecialization K (MvPolynomial.monomial b z) =
      Polynomial.monomial (rothExponentCode K b) z := by
  rw [rothPowerSpecialization, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp_rw [← pow_mul, Nat.mul_comm (K ^ _) (b _)]
  rw [Finset.prod_pow_eq_pow_sum]
  simp [rothExponentCode, Polynomial.C_mul_X_pow_eq_monomial]

theorem rothPowerSpecialization_toFinsupp {d : ℕ} (K : ℕ)
    (P : MvPolynomial (Fin d) ℚ) :
    (rothPowerSpecialization K P).toFinsupp =
      Finsupp.mapDomain (fun b : Fin d →₀ ℕ => rothExponentCode K b) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial b z =>
    rw [rothPowerSpecialization_monomial, Polynomial.toFinsupp_monomial]
    change Finsupp.single (rothExponentCode K b) z =
      Finsupp.mapDomain (fun c : Fin d →₀ ℕ => rothExponentCode K c) (Finsupp.single b z)
    rw [Finsupp.mapDomain_single]
  | add P Q hp hq =>
    rw [map_add, Polynomial.toFinsupp_add, Finsupp.mapDomain_add, hp, hq]

theorem rothPowerSpecialization_injOn {d : ℕ} (K : ℕ) (hK : 1 < K) :
    Set.InjOn (rothPowerSpecialization (d := d) K)
      {P | ∀ b ∈ P.support, ∀ k, b k < K} := by
  intro P hP Q hQ he
  have he' := congrArg Polynomial.toFinsupp he
  rw [rothPowerSpecialization_toFinsupp, rothPowerSpecialization_toFinsupp] at he'
  apply Finsupp.mapDomain_injOn {b : Fin d →₀ ℕ | ∀ k, b k < K} ?_ hP hQ he'
  intro b hb c hc hcode
  apply Finsupp.ext
  exact congrFun (rothExponentCode_injOn K hK b c hb hc hcode)

theorem rothPowerSpecialization_linearIndependent {d ell : ℕ}
    (K : ℕ) (hK : 1 < K) (f : Fin ell → MvPolynomial (Fin d) ℚ)
    (hf : LinearIndependent ℚ f)
    (hbound : ∀ j b, b ∈ (f j).support → ∀ k, b k < K) :
    LinearIndependent ℚ (fun j => rothPowerSpecialization K (f j)) := by
  have hs : Submodule.span ℚ (Set.range f) ≤
      Finsupp.supported ℚ ℚ {b : Fin d →₀ ℕ | ∀ k, b k < K} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hbound j
  apply hf.map_injOn (rothPowerSpecialization K).toLinearMap
  intro P hP Q hQ he
  exact rothPowerSpecialization_injOn K hK (hs hP) (hs hQ) he

theorem exists_rothPowerSpecialization_linearIndependent {d ell : ℕ}
    (f : Fin ell → MvPolynomial (Fin d) ℚ) (hf : LinearIndependent ℚ f) :
    ∃ K : ℕ, 1 < K ∧
      (∀ j b, b ∈ (f j).support → ∀ k, b k < K) ∧
      LinearIndependent ℚ (fun j => rothPowerSpecialization K (f j)) := by
  classical
  let N := ∑ j : Fin ell, ∑ b ∈ (f j).support, ∑ k : Fin d, b k
  have hb : ∀ j b, b ∈ (f j).support → ∀ k, b k < N + 2 := by
    intro j b hbj k
    have h1 : b k ≤ ∑ t : Fin d, b t :=
      Finset.single_le_sum (fun t _ => Nat.zero_le (b t)) (Finset.mem_univ k)
    have h2 : (∑ t : Fin d, b t) ≤ ∑ c ∈ (f j).support, ∑ t : Fin d, c t :=
      Finset.single_le_sum (fun c _ => Nat.zero_le (∑ t : Fin d, c t)) hbj
    have h3 : (∑ c ∈ (f j).support, ∑ t : Fin d, c t) ≤ N :=
      Finset.single_le_sum (fun z _ => Nat.zero_le (∑ c ∈ (f z).support, ∑ t : Fin d, c t))
        (Finset.mem_univ j)
    omega
  exact ⟨N + 2, by omega, hb, rothPowerSpecialization_linearIndependent _ (by omega) f hf hb⟩

theorem exists_rothPower_hasseWronskian_ne_zero {d ell : ℕ}
    (f : Fin ell → MvPolynomial (Fin d) ℚ) (hf : LinearIndependent ℚ f) :
    ∃ K : ℕ, 1 < K ∧
      (∀ j b, b ∈ (f j).support → ∀ k, b k < K) ∧
      Matrix.det (fun i j : Fin ell =>
        Polynomial.hasseDeriv i.val (rothPowerSpecialization K (f j))) ≠ 0 := by
  obtain ⟨K, hK, hb, hi⟩ := exists_rothPowerSpecialization_linearIndependent f hf
  exact ⟨K, hK, hb, roth_univariate_hasse_wronskian_ne_zero _ hi⟩

theorem rothDividedDerivative_support {d : ℕ} (a : Fin d →₀ ℕ)
    (P : MvPolynomial (Fin d) ℚ) :
    (rothDividedDerivative a P).support ⊆ P.support.image (fun b => b - a) := by
  classical
  intro c hc
  rw [MvPolynomial.mem_support_iff] at hc
  by_contra hn
  apply hc
  rw [rothDividedDerivative, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro b hb
  have hne : b - a ≠ c := by
    intro he
    exact hn (Finset.mem_image.mpr ⟨b, hb, he⟩)
  simp [MvPolynomial.coeff_monomial, hne]

noncomputable def rothBoxMultiIndex {d K : ℕ} (a : Fin d → Fin K) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (a k).val)

@[simp] theorem rothBoxMultiIndex_apply {d K : ℕ} (a : Fin d → Fin K) (k : Fin d) :
    rothBoxMultiIndex a k = (a k).val := rfl

private theorem roth_binomial_box {R : Type*} [CommRing R]
    (x y : R) (n K : ℕ) (hn : n < K) :
    ∑ a : Fin K, (Nat.choose n a.val : R) * x ^ (n - a.val) * y ^ a.val =
      (x + y) ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
    (Nat.choose n a : R) * x ^ (n - a) * y ^ a) K]
  symm
  calc
    (x + y) ^ n = ∑ a ∈ Finset.range (n + 1),
        (Nat.choose n a : R) * x ^ (n - a) * y ^ a := by
      rw [add_comm x y, add_pow]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ a ∈ Finset.range K, (Nat.choose n a : R) * x ^ (n - a) * y ^ a := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro a ha hna
      have hlt : n < a := by
        rw [Finset.mem_range] at ha
        rw [Finset.mem_range] at hna
        omega
      simp [Nat.choose_eq_zero_of_lt hlt]

private theorem roth_taylor_box_monomial {R : Type*} [CommRing R] [Algebra ℚ R]
    {d K : ℕ} (x y : Fin d → R) (b : Fin d →₀ ℕ) (z : ℚ)
    (hb : ∀ k, b k < K) :
    MvPolynomial.aeval (fun k => x k + y k) (MvPolynomial.monomial b z) =
      ∑ a : Fin d → Fin K,
        MvPolynomial.aeval x (rothDividedDerivative (rothBoxMultiIndex a)
          (MvPolynomial.monomial b z)) * ∏ k : Fin d, y k ^ (a k).val := by
  classical
  have he (a : Fin d → Fin K) :
      MvPolynomial.aeval x (rothDividedDerivative (rothBoxMultiIndex a)
        (MvPolynomial.monomial b z)) * (∏ k : Fin d, y k ^ (a k).val) =
      algebraMap ℚ R z * ∏ k : Fin d,
        ((Nat.choose (b k) (a k).val : R) * x k ^ (b k - (a k).val) * y k ^ (a k).val) := by
    rw [rothDividedDerivative_monomial, MvPolynomial.aeval_monomial]
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    simp only [map_mul, map_prod, map_natCast, rothBoxMultiIndex_apply, Finsupp.tsub_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (k : Fin d) (a : Fin K) =>
    (Nat.choose (b k) a.val : R) * x k ^ (b k - a.val) * y k ^ a.val)]
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact (roth_binomial_box (x k) (y k) (b k) K (hb k)).symm

theorem roth_taylor_box {R : Type*} [CommRing R] [Algebra ℚ R]
    {d K : ℕ} (x y : Fin d → R) (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ b ∈ P.support, ∀ k, b k < K) :
    MvPolynomial.aeval (fun k => x k + y k) P =
      ∑ a : Fin d → Fin K,
        MvPolynomial.aeval x (rothDividedDerivative (rothBoxMultiIndex a) P) *
          ∏ k : Fin d, y k ^ (a k).val := by
  classical
  have hs (a : Fin d → Fin K) :
      MvPolynomial.aeval x (rothDividedDerivative (rothBoxMultiIndex a) P) =
        ∑ b ∈ P.support, MvPolynomial.aeval x
          (rothDividedDerivative (rothBoxMultiIndex a) (MvPolynomial.monomial b (P.coeff b))) := by
    let L := (MvPolynomial.aeval x).toLinearMap.comp
      (rothDividedDerivativeLinear (rothBoxMultiIndex a))
    change L P = ∑ b ∈ P.support, L (MvPolynomial.monomial b (P.coeff b))
    rw [← map_sum, ← MvPolynomial.as_sum P]
  calc
    MvPolynomial.aeval (fun k => x k + y k) P =
        ∑ b ∈ P.support, MvPolynomial.aeval (fun k => x k + y k)
          (MvPolynomial.monomial b (P.coeff b)) := by
      rw [← map_sum, ← MvPolynomial.as_sum P]
    _ = ∑ b ∈ P.support, ∑ a : Fin d → Fin K,
        MvPolynomial.aeval x (rothDividedDerivative (rothBoxMultiIndex a)
          (MvPolynomial.monomial b (P.coeff b))) * ∏ k : Fin d, y k ^ (a k).val := by
      apply Finset.sum_congr rfl
      intro b hb
      exact roth_taylor_box_monomial x y b (P.coeff b) (hP b hb)
    _ = ∑ a : Fin d → Fin K, ∑ b ∈ P.support,
        MvPolynomial.aeval x (rothDividedDerivative (rothBoxMultiIndex a)
          (MvPolynomial.monomial b (P.coeff b))) * ∏ k : Fin d, y k ^ (a k).val :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul, ← hs a]

noncomputable def rothTaylorLift : Polynomial ℚ →ₐ[ℚ] Polynomial (Polynomial ℚ) :=
  Polynomial.aeval (Polynomial.X + Polynomial.C Polynomial.X)

private theorem roth_hasse_map_C (p : Polynomial ℚ) (i : ℕ) :
    Polynomial.hasseDeriv i (p.map Polynomial.C) =
      (Polynomial.hasseDeriv i p).map Polynomial.C := by
  ext n
  simp [Polynomial.hasseDeriv_coeff, Polynomial.coeff_map]

theorem rothTaylorLift_coeff (p : Polynomial ℚ) (i : ℕ) :
    (rothTaylorLift p).coeff i = Polynomial.hasseDeriv i p := by
  have he : rothTaylorLift p = Polynomial.taylor Polynomial.X (p.map Polynomial.C) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
    | monomial n z =>
      simp [rothTaylorLift, Polynomial.aeval_monomial, Polynomial.taylor_monomial]
  rw [he, Polynomial.taylor_coeff, roth_hasse_map_C, Polynomial.eval_map,
    Polynomial.eval₂_C_X]

noncomputable def rothTaylorDelta {d : ℕ} (K : ℕ) (k : Fin d) :
    Polynomial (Polynomial ℚ) :=
  rothTaylorLift (Polynomial.X ^ (K ^ k.val)) - Polynomial.C ((Polynomial.X : Polynomial ℚ) ^ (K ^ k.val))

noncomputable def rothChainCoefficient {d K : ℕ} (i : ℕ) (a : Fin d → Fin K) : Polynomial ℚ :=
  (∏ k : Fin d, rothTaylorDelta K k ^ (a k).val).coeff i

theorem rothPowerSpecialization_hasse_chain {d K : ℕ}
    (P : MvPolynomial (Fin d) ℚ) (hP : ∀ b ∈ P.support, ∀ k, b k < K) (i : ℕ) :
    Polynomial.hasseDeriv i (rothPowerSpecialization K P) =
      ∑ a : Fin d → Fin K, rothChainCoefficient i a *
        rothPowerSpecialization K (rothDividedDerivative (rothBoxMultiIndex a) P) := by
  classical
  let c : Polynomial ℚ →ₐ[ℚ] Polynomial (Polynomial ℚ) := Polynomial.CAlgHom
  have hc : MvPolynomial.aeval (fun k : Fin d => Polynomial.C ((Polynomial.X : Polynomial ℚ) ^ (K ^ k.val))) =
      c.comp (rothPowerSpecialization K) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [rothPowerSpecialization, c]
  have hl : MvPolynomial.aeval (fun k : Fin d => rothTaylorLift (Polynomial.X ^ (K ^ k.val))) =
      rothTaylorLift.comp (rothPowerSpecialization K) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [rothPowerSpecialization]
  have ht := roth_taylor_box
    (fun k : Fin d => Polynomial.C ((Polynomial.X : Polynomial ℚ) ^ (K ^ k.val)))
    (rothTaylorDelta K) P hP
  have hx : (fun k : Fin d => Polynomial.C ((Polynomial.X : Polynomial ℚ) ^ (K ^ k.val)) + rothTaylorDelta K k) =
      (fun k : Fin d => rothTaylorLift (Polynomial.X ^ (K ^ k.val))) := by
    funext k
    simp [rothTaylorDelta]
  rw [hx, hl] at ht
  simp_rw [hc, AlgHom.comp_apply] at ht
  have he := congrArg (fun p : Polynomial (Polynomial ℚ) => p.coeff i) ht
  change (rothTaylorLift (rothPowerSpecialization K P)).coeff i =
    (∑ a : Fin d → Fin K,
      Polynomial.C (rothPowerSpecialization K
        (rothDividedDerivative (rothBoxMultiIndex a) P)) *
        ∏ k : Fin d, rothTaylorDelta K k ^ (a k).val).coeff i at he
  rw [rothTaylorLift_coeff] at he
  calc
    Polynomial.hasseDeriv i (rothPowerSpecialization K P) =
        ∑ a : Fin d → Fin K,
          (Polynomial.C (rothPowerSpecialization K
            (rothDividedDerivative (rothBoxMultiIndex a) P)) *
            ∏ k : Fin d, rothTaylorDelta K k ^ (a k).val).coeff i := by
      simpa only [Polynomial.finset_sum_coeff] using he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Polynomial.coeff_C_mul]
      unfold rothChainCoefficient
      exact mul_comm _ _

theorem rothChainCoefficient_eq_zero_of_order {d K : ℕ}
    (i : ℕ) (a : Fin d → Fin K) (hi : i < ∑ k : Fin d, (a k).val) :
    rothChainCoefficient i a = 0 := by
  classical
  have hd (k : Fin d) : Polynomial.X ∣ rothTaylorDelta K k := by
    apply Polynomial.X_dvd_iff.mpr
    simp only [rothTaylorDelta, Polynomial.coeff_sub, rothTaylorLift_coeff,
      Polynomial.hasseDeriv_zero, LinearMap.id_apply, Polynomial.coeff_C, ite_true, sub_self]
  choose q hq using hd
  have he : (∏ k : Fin d, rothTaylorDelta K k ^ (a k).val) =
      Polynomial.X ^ (∑ k : Fin d, (a k).val) * ∏ k : Fin d, q k ^ (a k).val := by
    simp_rw [hq, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [rothChainCoefficient, he, Polynomial.coeff_X_pow_mul', if_neg (by omega)]

theorem roth_generalized_wronskian_ne_zero
    (d ell : ℕ) (hd : 1 ≤ d) (hell : 1 ≤ ell)
    (f : Fin ell → MvPolynomial (Fin d) ℚ)
    (hf : LinearIndependent ℚ f) :
    ∃ alpha : Fin ell → (Fin d →₀ ℕ),
      (∀ i, (∑ k : Fin d, alpha i k) ≤ i.val) ∧
      Matrix.det (fun i j => rothDividedDerivative (alpha i) (f j)) ≠ 0 := by
  classical
  obtain ⟨K, hK, hb, hw⟩ := exists_rothPower_hasseWronskian_ne_zero f hf
  let u : Fin ell → (Fin d → Fin K) → (Fin ell → Polynomial ℚ) :=
    fun i a j => rothChainCoefficient i.val a *
      rothPowerSpecialization K (rothDividedDerivative (rothBoxMultiIndex a) (f j))
  have hrow : (fun i : Fin ell => ∑ a : Fin d → Fin K, u i a) =
      (fun i j : Fin ell => Polynomial.hasseDeriv i.val (rothPowerSpecialization K (f j))) := by
    funext i j
    simpa only [u, Finset.sum_apply] using
      (rothPowerSpecialization_hasse_chain (f j) (hb j) i.val).symm
  have hexp := (Matrix.detRowAlternating
    (R := Polynomial ℚ) (n := Fin ell)).toMultilinearMap.map_sum u
  change Matrix.det (fun i : Fin ell => ∑ a : Fin d → Fin K, u i a) =
    ∑ r : Fin ell → (Fin d → Fin K), Matrix.det (fun i => u i (r i)) at hexp
  rw [hrow] at hexp
  have hs : Matrix.det (fun i j : Fin ell =>
      Polynomial.hasseDeriv i.val (rothPowerSpecialization K (f j))) =
      ∑ r : Fin ell → (Fin d → Fin K),
        (∏ i : Fin ell, rothChainCoefficient i.val (r i)) *
          Matrix.det (fun i j : Fin ell => rothPowerSpecialization K
            (rothDividedDerivative (rothBoxMultiIndex (r i)) (f j))) := by
    refine hexp.trans ?_
    apply Finset.sum_congr rfl
    intro r _
    exact Matrix.det_mul_column (fun i : Fin ell => rothChainCoefficient i.val (r i))
      (fun i j : Fin ell => rothPowerSpecialization K
        (rothDividedDerivative (rothBoxMultiIndex (r i)) (f j)))
  rw [hs] at hw
  obtain ⟨r, hrmem, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  have hcprod := (mul_ne_zero_iff.mp hr).1
  have hdet := (mul_ne_zero_iff.mp hr).2
  have hbudget (i : Fin ell) : ∑ k : Fin d, (r i k).val ≤ i.val := by
    by_contra hn
    have hc := Finset.prod_ne_zero_iff.mp hcprod i (Finset.mem_univ i)
    exact hc (rothChainCoefficient_eq_zero_of_order i.val (r i) (by omega))
  refine ⟨fun i => rothBoxMultiIndex (r i), ?_, ?_⟩
  · intro i
    simpa only [rothBoxMultiIndex_apply] using hbudget i
  · have hm := (rothPowerSpecialization (d := d) K).map_det
      (fun i j : Fin ell => rothDividedDerivative (rothBoxMultiIndex (r i)) (f j))
    change rothPowerSpecialization K
      (Matrix.det (fun i j : Fin ell =>
        rothDividedDerivative (rothBoxMultiIndex (r i)) (f j))) =
      Matrix.det (fun i j : Fin ell => rothPowerSpecialization K
        (rothDividedDerivative (rothBoxMultiIndex (r i)) (f j))) at hm
    intro hz
    apply hdet
    rw [← hm, hz, map_zero]


end JSP000334

namespace JSP000334


private theorem roth_minimum_separated_left_independent
    {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]
    (F : V →ₗ[ℚ] W →ₗ[ℚ] Z) {ell : ℕ}
    (A : Fin ell → V) (B : Fin ell → W) (x : Z)
    (hsum : (∑ s, F (A s) (B s)) = x)
    (hmin : ∀ (k : ℕ) (a : Fin k → V) (b : Fin k → W),
      (∑ s, F (a s) (b s)) = x → ell ≤ k) :
    LinearIndependent ℚ A := by
  classical
  cases ell with
  | zero => exact linearIndependent_empty_type
  | succ n =>
    by_contra hn
    obtain ⟨c, hc, i, hci⟩ := Fintype.not_linearIndependent_iff.mp hn
    rw [Fin.sum_univ_succAbove _ i] at hc
    have he := congrArg (fun v : V => (c i)⁻¹ • v) hc
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hci, one_smul, smul_zero] at he
    let q : Fin n → ℚ := fun j => -((c i)⁻¹ * c (i.succAbove j))
    have hAi : A i = ∑ j : Fin n, q j • A (i.succAbove j) := by
      calc
        A i = -((c i)⁻¹ • ∑ j : Fin n, c (i.succAbove j) • A (i.succAbove j)) :=
          eq_neg_iff_add_eq_zero.mpr he
        _ = _ := by simp [q, Finset.smul_sum, smul_smul, neg_smul]
    have hr : (∑ j : Fin n, F (A (i.succAbove j))
        (B (i.succAbove j) + q j • B i)) = x := by
      calc
        _ = (∑ j : Fin n, F (A (i.succAbove j)) (B (i.succAbove j))) +
            F (∑ j : Fin n, q j • A (i.succAbove j)) (B i) := by
          simp [map_add, map_smul, map_sum, Finset.sum_add_distrib,
            LinearMap.sum_apply, LinearMap.smul_apply]
        _ = (∑ j : Fin n, F (A (i.succAbove j)) (B (i.succAbove j))) +
            F (A i) (B i) := by rw [← hAi]
        _ = x := by
          rw [add_comm, ← Fin.sum_univ_succAbove (fun s => F (A s) (B s)) i]
          exact hsum
    have hm := hmin n (fun j => A (i.succAbove j))
      (fun j => B (i.succAbove j) + q j • B i) hr
    omega

private theorem roth_exists_minimum_bilinear_sum
    {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]
    (F : V →ₗ[ℚ] W →ₗ[ℚ] Z) (x : Z) (hx : x ≠ 0)
    (N : ℕ) (a : Fin N → V) (b : Fin N → W)
    (hab : (∑ s, F (a s) (b s)) = x) :
    ∃ (ell : ℕ) (A : Fin ell → V) (B : Fin ell → W),
      1 ≤ ell ∧ ell ≤ N ∧ (∑ s, F (A s) (B s)) = x ∧
      LinearIndependent ℚ A ∧ LinearIndependent ℚ B ∧
      (∀ (k : ℕ) (a' : Fin k → V) (b' : Fin k → W),
        (∑ s, F (a' s) (b' s)) = x → ell ≤ k) := by
  classical
  let h : ∃ k : ℕ, ∃ (A : Fin k → V) (B : Fin k → W),
      (∑ s, F (A s) (B s)) = x := ⟨N, a, b, hab⟩
  obtain ⟨A, B, hs⟩ := Nat.find_spec h
  have hm (k : ℕ) (a' : Fin k → V) (b' : Fin k → W)
      (he : (∑ s, F (a' s) (b' s)) = x) : Nat.find h ≤ k :=
    Nat.find_min' h ⟨a', b', he⟩
  have hp : 1 ≤ Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    haveI : IsEmpty (Fin (Nat.find h)) := by rw [hz]; infer_instance
    apply hx
    simpa using hs.symm
  refine ⟨Nat.find h, A, B, hp, hm N a b hab, hs, ?_, ?_, hm⟩
  · exact roth_minimum_separated_left_independent F A B x hs hm
  · apply roth_minimum_separated_left_independent F.flip B A x hs
    intro k b' a' he
    exact hm k a' b' he

noncomputable def rothSeparatedProduct {d : ℕ} :
    MvPolynomial (Fin d) ℚ →ₗ[ℚ] Polynomial ℚ →ₗ[ℚ]
      Polynomial (MvPolynomial (Fin d) ℚ) :=
  (LinearMap.mul ℚ (Polynomial (MvPolynomial (Fin d) ℚ))).compl₁₂
    (Polynomial.CAlgHom : MvPolynomial (Fin d) ℚ →ₐ[ℚ]
      Polynomial (MvPolynomial (Fin d) ℚ)).toLinearMap
    (Polynomial.mapAlgHom (Algebra.ofId ℚ (MvPolynomial (Fin d) ℚ))).toLinearMap

theorem rothSeparatedProduct_apply {d : ℕ}
    (A : MvPolynomial (Fin d) ℚ) (B : Polynomial ℚ) :
    rothSeparatedProduct A B = Polynomial.C A * B.map MvPolynomial.C := rfl

theorem roth_exists_minimum_separated_polynomial {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℚ)) (hP : P ≠ 0) :
    ∃ (ell : ℕ) (A : Fin ell → MvPolynomial (Fin d) ℚ)
        (B : Fin ell → Polynomial ℚ),
      1 ≤ ell ∧ ell ≤ P.natDegree + 1 ∧
      (∑ s, Polynomial.C (A s) * (B s).map MvPolynomial.C) = P ∧
      LinearIndependent ℚ A ∧ LinearIndependent ℚ B ∧
      (∀ (k : ℕ) (a : Fin k → MvPolynomial (Fin d) ℚ)
          (b : Fin k → Polynomial ℚ),
        (∑ s, Polynomial.C (a s) * (b s).map MvPolynomial.C) = P → ell ≤ k) := by
  classical
  have hs : (∑ s : Fin (P.natDegree + 1),
      rothSeparatedProduct (P.coeff s.val) ((Polynomial.X : Polynomial ℚ) ^ s.val)) = P := by
    simp only [rothSeparatedProduct_apply, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.C_mul_X_pow_eq_monomial]
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Polynomial.monomial n (P.coeff n))
      (P.natDegree + 1)]
    exact P.as_sum_range.symm
  obtain ⟨ell, A, B, hp, hb, he, hA, hB, hm⟩ :=
    roth_exists_minimum_bilinear_sum (rothSeparatedProduct (d := d)) P hP
      (P.natDegree + 1) (fun s => P.coeff s.val)
      (fun s => (Polynomial.X : Polynomial ℚ) ^ s.val) hs
  exact ⟨ell, A, B, hp, hb, he, hA, hB, hm⟩

noncomputable def rothCoefficientDividedDerivative {d : ℕ} (a : Fin d →₀ ℕ) :
    Polynomial (MvPolynomial (Fin d) ℚ) →ₗ[ℚ] Polynomial (MvPolynomial (Fin d) ℚ) :=
  let e := (Polynomial.toFinsuppIsoLinear (MvPolynomial (Fin d) ℚ) :
    Polynomial (MvPolynomial (Fin d) ℚ) ≃ₗ[MvPolynomial (Fin d) ℚ]
      (ℕ →₀ MvPolynomial (Fin d) ℚ)).restrictScalars ℚ
  e.symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (rothDividedDerivativeLinear a)).comp e.toLinearMap)

theorem rothCoefficientDividedDerivative_coeff {d : ℕ} (a : Fin d →₀ ℕ)
    (P : Polynomial (MvPolynomial (Fin d) ℚ)) (n : ℕ) :
    (rothCoefficientDividedDerivative a P).coeff n =
      rothDividedDerivative a (P.coeff n) := rfl

noncomputable def rothMixedDividedDerivative {d : ℕ} (a : Fin d →₀ ℕ) (j : ℕ) :
    Polynomial (MvPolynomial (Fin d) ℚ) →ₗ[ℚ] Polynomial (MvPolynomial (Fin d) ℚ) :=
  ((Polynomial.hasseDeriv j).restrictScalars ℚ).comp (rothCoefficientDividedDerivative a)

theorem rothMixedDividedDerivative_separated {d : ℕ} (a : Fin d →₀ ℕ) (j : ℕ)
    (A : MvPolynomial (Fin d) ℚ) (B : Polynomial ℚ) :
    rothMixedDividedDerivative a j (Polynomial.C A * B.map MvPolynomial.C) =
      Polynomial.C (rothDividedDerivative a A) *
        (Polynomial.hasseDeriv j B).map MvPolynomial.C := by
  have hc : rothCoefficientDividedDerivative a (Polynomial.C A * B.map MvPolynomial.C) =
      Polynomial.C (rothDividedDerivative a A) * B.map MvPolynomial.C := by
    apply Polynomial.ext
    intro n
    rw [rothCoefficientDividedDerivative_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    have he (q : ℚ) : rothDividedDerivative a (A * MvPolynomial.C q) =
        rothDividedDerivative a A * MvPolynomial.C q := by
      calc
        _ = rothDividedDerivative a (q • A) := by
          congr 1
          simp [Algebra.smul_def, mul_comm]
        _ = q • rothDividedDerivative a A := (rothDividedDerivativeLinear a).map_smul q A
        _ = _ := by simp [Algebra.smul_def, mul_comm]
    exact he (B.coeff n)
  change Polynomial.hasseDeriv j
    (rothCoefficientDividedDerivative a (Polynomial.C A * B.map MvPolynomial.C)) = _
  rw [hc, ← Polynomial.smul_eq_C_mul, map_smul, Polynomial.smul_eq_C_mul]
  congr 1
  ext n
  simp [Polynomial.hasseDeriv_coeff, Polynomial.coeff_map]

theorem roth_exists_separated_mixed_wronskian
    (d : ℕ) (hd : 1 ≤ d)
    (P : Polynomial (MvPolynomial (Fin d) ℚ)) (hP : P ≠ 0) :
    ∃ (ell : ℕ) (A : Fin ell → MvPolynomial (Fin d) ℚ)
        (B : Fin ell → Polynomial ℚ) (alpha : Fin ell → (Fin d →₀ ℕ)),
      1 ≤ ell ∧ ell ≤ P.natDegree + 1 ∧
      (∑ s, Polynomial.C (A s) * (B s).map MvPolynomial.C) = P ∧
      LinearIndependent ℚ A ∧ LinearIndependent ℚ B ∧
      (∀ (k : ℕ) (a : Fin k → MvPolynomial (Fin d) ℚ)
          (b : Fin k → Polynomial ℚ),
        (∑ s, Polynomial.C (a s) * (b s).map MvPolynomial.C) = P → ell ≤ k) ∧
      (∀ i, (∑ k : Fin d, alpha i k) ≤ i.val) ∧
      Matrix.det (fun i j : Fin ell => rothMixedDividedDerivative (alpha i) j.val P) =
        Polynomial.C (Matrix.det (fun i s : Fin ell => rothDividedDerivative (alpha i) (A s))) *
          (Matrix.det (fun s j : Fin ell => Polynomial.hasseDeriv j.val (B s))).map MvPolynomial.C ∧
      Matrix.det (fun i s : Fin ell => rothDividedDerivative (alpha i) (A s)) ≠ 0 ∧
      Matrix.det (fun s j : Fin ell => Polynomial.hasseDeriv j.val (B s)) ≠ 0 ∧
      Matrix.det (fun i j : Fin ell => rothMixedDividedDerivative (alpha i) j.val P) ≠ 0 := by
  classical
  obtain ⟨ell, A, B, hp, hb, hs, hA, hB, hm⟩ :=
    roth_exists_minimum_separated_polynomial P hP
  obtain ⟨alpha, hbudget, hv⟩ := roth_generalized_wronskian_ne_zero d ell hd hp A hA
  have hu : Matrix.det (fun s j : Fin ell => Polynomial.hasseDeriv j.val (B s)) ≠ 0 := by
    have h := roth_univariate_hasse_wronskian_ne_zero B hB
    rw [← Matrix.det_transpose] at h
    exact h
  let L : Matrix (Fin ell) (Fin ell) (Polynomial (MvPolynomial (Fin d) ℚ)) :=
    fun i s => Polynomial.C (rothDividedDerivative (alpha i) (A s))
  let T : Matrix (Fin ell) (Fin ell) (Polynomial (MvPolynomial (Fin d) ℚ)) :=
    fun s j => (Polynomial.hasseDeriv j.val (B s)).map MvPolynomial.C
  have hentry (i j : Fin ell) : rothMixedDividedDerivative (alpha i) j.val P =
      ∑ s : Fin ell, Polynomial.C (rothDividedDerivative (alpha i) (A s)) *
        (Polynomial.hasseDeriv j.val (B s)).map MvPolynomial.C := by
    rw [← hs, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    exact rothMixedDividedDerivative_separated (alpha i) j.val (A s) (B s)
  have hmat : (fun i j : Fin ell => rothMixedDividedDerivative (alpha i) j.val P) = L * T := by
    apply Matrix.ext
    intro i j
    exact hentry i j
  have hl := (Polynomial.C : MvPolynomial (Fin d) ℚ →+*
    Polynomial (MvPolynomial (Fin d) ℚ)).map_det
      (fun i s : Fin ell => rothDividedDerivative (alpha i) (A s))
  change Polynomial.C (Matrix.det (fun i s : Fin ell =>
    rothDividedDerivative (alpha i) (A s))) = L.det at hl
  have ht := (Polynomial.mapRingHom (MvPolynomial.C : ℚ →+* MvPolynomial (Fin d) ℚ)).map_det
    (fun s j : Fin ell => Polynomial.hasseDeriv j.val (B s))
  change (Matrix.det (fun s j : Fin ell => Polynomial.hasseDeriv j.val (B s))).map
    MvPolynomial.C = T.det at ht
  have hf : Matrix.det (fun i j : Fin ell => rothMixedDividedDerivative (alpha i) j.val P) =
      Polynomial.C (Matrix.det (fun i s : Fin ell => rothDividedDerivative (alpha i) (A s))) *
        (Matrix.det (fun s j : Fin ell => Polynomial.hasseDeriv j.val (B s))).map MvPolynomial.C := by
    rw [hmat, Matrix.det_mul, ← hl, ← ht]
  refine ⟨ell, A, B, alpha, hp, hb, hs, hA, hB, hm, hbudget, hf, hv, hu, ?_⟩
  rw [hf]
  apply mul_ne_zero
  · intro hz
    apply hv
    apply Polynomial.C_injective
    simpa using hz
  · intro hz
    apply hu
    apply Polynomial.map_injective (MvPolynomial.C : ℚ →+* MvPolynomial (Fin d) ℚ)
      (MvPolynomial.C_injective (Fin d) ℚ)
    simpa using hz

theorem roth_primitive_rational_scalar_integral
    (U W : Polynomial ℤ) (hU : U.IsPrimitive) (q : ℚ)
    (he : Polynomial.C q * U.map (Int.castRingHom ℚ) = W.map (Int.castRingHom ℚ)) :
    ∃ z : ℤ, (z : ℚ) = q := by
  have hcop : IsCoprime (q.den : ℤ) q.num :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using q.reduced.symm)
  have hc (n : ℕ) : (q.den : ℤ) ∣ U.coeff n := by
    have hcoef := congrArg (fun p : Polynomial ℚ => p.coeff n) he
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, Int.coe_castRingHom] at hcoef
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hnum : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hd).mp q.num_div_den
    have heq : (q.den : ℚ) * (W.coeff n : ℚ) =
        (q.num : ℚ) * (U.coeff n : ℚ) := by
      rw [← hcoef, hnum]
      ring
    have hez : (q.den : ℤ) * W.coeff n = q.num * U.coeff n := by exact_mod_cast heq
    apply hcop.dvd_of_dvd_mul_left
    exact ⟨W.coeff n, hez.symm⟩
  have hunit : IsUnit (q.den : ℤ) :=
    hU (q.den : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hc)
  have hden : q.den = 1 := by simpa using Int.isUnit_iff_natAbs_eq.mp hunit
  exact ⟨q.num, Rat.coe_int_num_of_den_eq_one hden⟩

theorem roth_exists_primitive_integer_factor
    (U : Polynomial ℚ) (hU : U ≠ 0) :
    ∃ (u : Polynomial ℤ) (q : ℚ),
      u.IsPrimitive ∧ q ≠ 0 ∧ U = Polynomial.C q * u.map (Int.castRingHom ℚ) := by
  classical
  let N : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) U
  obtain ⟨⟨b, hb⟩, he⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) U
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have he' : N.map (Int.castRingHom ℚ) = Polynomial.C (b : ℚ) * U := by
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using he
  have hbC : (Polynomial.C (b : ℚ) : Polynomial ℚ) ≠ 0 := by
    intro hz
    apply hbQ
    exact Polynomial.C_injective (by simpa using hz)
  have hN : N ≠ 0 := by
    intro hz
    apply mul_ne_zero hbC hU
    rw [← he', hz, Polynomial.map_zero]
  have hc : N.content ≠ 0 := fun h => hN (Polynomial.content_eq_zero_iff.mp h)
  refine ⟨N.primPart, (N.content : ℚ) / (b : ℚ), N.isPrimitive_primPart,
    div_ne_zero (by exact_mod_cast hc) hbQ, ?_⟩
  apply mul_left_cancel₀ hbC
  calc
    Polynomial.C (b : ℚ) * U = N.map (Int.castRingHom ℚ) := he'.symm
    _ = Polynomial.C (N.content : ℚ) * N.primPart.map (Int.castRingHom ℚ) := by
      have hn := congrArg (Polynomial.map (Int.castRingHom ℚ)) N.eq_C_content_mul_primPart
      simpa only [Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom] using hn
    _ = Polynomial.C (b : ℚ) *
        (Polynomial.C ((N.content : ℚ) / (b : ℚ)) * N.primPart.map (Int.castRingHom ℚ)) := by
      rw [← mul_assoc, ← Polynomial.C_mul]
      congr 1
      congr 1
      field_simp

theorem roth_separated_integral_rescaling {d : ℕ}
    (W : Polynomial (MvPolynomial (Fin d) ℤ))
    (V : MvPolynomial (Fin d) ℚ) (U : Polynomial ℚ) (hU : U ≠ 0)
    (he : Polynomial.C V * U.map MvPolynomial.C =
      W.map (MvPolynomial.map (Int.castRingHom ℚ))) :
    ∃ (u : Polynomial ℤ) (v : MvPolynomial (Fin d) ℤ) (q : ℚ),
      u.IsPrimitive ∧ q ≠ 0 ∧ U = Polynomial.C q * u.map (Int.castRingHom ℚ) ∧
      MvPolynomial.map (Int.castRingHom ℚ) v = q • V ∧
      W.map (MvPolynomial.map (Int.castRingHom ℚ)) =
        Polynomial.C (MvPolynomial.map (Int.castRingHom ℚ) v) *
          (u.map (Int.castRingHom ℚ)).map MvPolynomial.C := by
  classical
  obtain ⟨u, q, hu, hq, hqu⟩ := roth_exists_primitive_integer_factor U hU
  let V' : MvPolynomial (Fin d) ℚ := q • V
  have he' : Polynomial.C V' * (u.map (Int.castRingHom ℚ)).map MvPolynomial.C =
      W.map (MvPolynomial.map (Int.castRingHom ℚ)) := by
    calc
      _ = Polynomial.C V * U.map MvPolynomial.C := by
        rw [hqu, Polynomial.map_mul, Polynomial.map_C]
        simp only [V', Algebra.smul_def, MvPolynomial.algebraMap_eq, Polynomial.C_mul]
        ring
      _ = _ := he
  have hvcoeff (beta : Fin d →₀ ℕ) : ∃ z : ℤ, (z : ℚ) = V'.coeff beta := by
    let Wb : Polynomial ℤ := Polynomial.ofFinsupp
      (Finsupp.mapRange (MvPolynomial.coeff beta) rfl W.toFinsupp)
    apply roth_primitive_rational_scalar_integral u Wb hu (V'.coeff beta)
    apply Polynomial.ext
    intro n
    have hn := congrArg (fun P : Polynomial (MvPolynomial (Fin d) ℚ) =>
      MvPolynomial.coeff beta (P.coeff n)) he'
    have hc (a : ℚ) : MvPolynomial.coeff beta (V' * MvPolynomial.C a) =
        V'.coeff beta * a := by
      rw [mul_comm, MvPolynomial.coeff_C_mul, mul_comm]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
      MvPolynomial.coeff_map, Int.coe_castRingHom, hc] at hn
    simpa only [Polynomial.coeff_C_mul, Polynomial.coeff_map, Int.coe_castRingHom] using hn
  let v : MvPolynomial (Fin d) ℤ := Finsupp.mapRange
    (fun r : ℚ => ⌊r⌋) (by simp) V'
  have hv : MvPolynomial.map (Int.castRingHom ℚ) v = V' := by
    apply MvPolynomial.ext
    intro beta
    simp only [MvPolynomial.coeff_map, Int.coe_castRingHom]
    change (⌊V'.coeff beta⌋ : ℚ) = V'.coeff beta
    obtain ⟨z, hz⟩ := hvcoeff beta
    rw [← hz]
    simp
  refine ⟨u, v, q, hu, hq, hqu, hv, ?_⟩
  rw [hv]
  exact he'.symm

noncomputable def rothIntegerDividedDerivative {d : ℕ}
    (a : Fin d →₀ ℕ) (P : MvPolynomial (Fin d) ℤ) : MvPolynomial (Fin d) ℤ :=
  P.sum fun b z => MvPolynomial.monomial (b - a)
    (z * ∏ k : Fin d, (Nat.choose (b k) (a k) : ℤ))

theorem rothIntegerDividedDerivative_map {d : ℕ}
    (a : Fin d →₀ ℕ) (P : MvPolynomial (Fin d) ℤ) :
    rothDividedDerivative a (MvPolynomial.map (Int.castRingHom ℚ) P) =
      MvPolynomial.map (Int.castRingHom ℚ) (rothIntegerDividedDerivative a P) := by
  classical
  calc
    _ = rothDividedDerivative a (MvPolynomial.map (Int.castRingHom ℚ)
        (∑ b ∈ P.support, MvPolynomial.monomial b (P.coeff b))) :=
      congrArg (fun Q => rothDividedDerivative a (MvPolynomial.map (Int.castRingHom ℚ) Q)) P.as_sum
    _ = ∑ b ∈ P.support, rothDividedDerivative a
        (MvPolynomial.map (Int.castRingHom ℚ) (MvPolynomial.monomial b (P.coeff b))) := by
      rw [map_sum]
      exact map_sum (rothDividedDerivativeLinear a) _ _
    _ = _ := by
      simp [rothIntegerDividedDerivative, MvPolynomial.sum_def,
        rothDividedDerivative_monomial, MvPolynomial.map_monomial, map_sum, map_mul, map_prod]

noncomputable def rothIntegerMixedDividedDerivative {d : ℕ}
    (a : Fin d →₀ ℕ) (j : ℕ) (P : Polynomial (MvPolynomial (Fin d) ℤ)) :
    Polynomial (MvPolynomial (Fin d) ℤ) :=
  Polynomial.hasseDeriv j (Polynomial.ofFinsupp
    (Finsupp.mapRange (rothIntegerDividedDerivative a)
      (by simp [rothIntegerDividedDerivative]) P.toFinsupp))

theorem rothIntegerMixedDividedDerivative_map {d : ℕ}
    (a : Fin d →₀ ℕ) (j : ℕ) (P : Polynomial (MvPolynomial (Fin d) ℤ)) :
    (rothIntegerMixedDividedDerivative a j P).map
        (MvPolynomial.map (Int.castRingHom ℚ)) =
      rothMixedDividedDerivative a j (P.map (MvPolynomial.map (Int.castRingHom ℚ))) := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map]
  change MvPolynomial.map (Int.castRingHom ℚ)
      ((Polynomial.hasseDeriv j (Polynomial.ofFinsupp
        (Finsupp.mapRange (rothIntegerDividedDerivative a)
          (by simp [rothIntegerDividedDerivative]) P.toFinsupp))).coeff n) =
    (Polynomial.hasseDeriv j (rothCoefficientDividedDerivative a
      (P.map (MvPolynomial.map (Int.castRingHom ℚ))))).coeff n
  rw [Polynomial.hasseDeriv_coeff, Polynomial.hasseDeriv_coeff,
    rothCoefficientDividedDerivative_coeff, Polynomial.coeff_map]
  change MvPolynomial.map (Int.castRingHom ℚ)
      ((Nat.choose (n + j) j : MvPolynomial (Fin d) ℤ) *
        rothIntegerDividedDerivative a (P.coeff (n + j))) = _
  rw [map_mul, map_natCast, ← rothIntegerDividedDerivative_map]

theorem roth_exists_integral_separated_wronskian
    (d : ℕ) (hd : 1 ≤ d)
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (hP : P ≠ 0) :
    ∃ (ell : ℕ) (alpha : Fin ell → (Fin d →₀ ℕ))
        (u : Polynomial ℤ) (v : MvPolynomial (Fin d) ℤ),
      1 ≤ ell ∧ ell ≤ P.natDegree + 1 ∧
      (∀ i, (∑ k : Fin d, alpha i k) ≤ i.val) ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) =
        Polynomial.C v * u.map MvPolynomial.C ∧
      u ≠ 0 ∧ v ≠ 0 ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) ≠ 0 := by
  classical
  let c : MvPolynomial (Fin d) ℤ →+* MvPolynomial (Fin d) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hc : Function.Injective c :=
    MvPolynomial.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  have hpc : P.map c ≠ 0 := by
    intro hz
    apply hP
    apply Polynomial.map_injective c hc
    simpa using hz
  obtain ⟨ell, A, B, alpha, hp, hb, hs, hA, hB, hm, hbudget, hf, hv, hu, hw⟩ :=
    roth_exists_separated_mixed_wronskian d hd (P.map c) hpc
  let W : Polynomial (MvPolynomial (Fin d) ℤ) := Matrix.det
    (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)
  have hmap : W.map c = Matrix.det
      (fun i j : Fin ell => rothMixedDividedDerivative (alpha i) j.val (P.map c)) := by
    have ht := (Polynomial.mapRingHom c).map_det
      (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)
    change W.map c = Matrix.det (fun i j : Fin ell =>
      (rothIntegerMixedDividedDerivative (alpha i) j.val P).map c) at ht
    refine ht.trans (congrArg Matrix.det ?_)
    apply Matrix.ext
    intro i j
    exact rothIntegerMixedDividedDerivative_map (alpha i) j.val P
  obtain ⟨u, v, q, huprim, hq, hqu, hqv, hfact⟩ :=
    roth_separated_integral_rescaling W
      (Matrix.det (fun i s : Fin ell => rothDividedDerivative (alpha i) (A s)))
      (Matrix.det (fun s j : Fin ell => Polynomial.hasseDeriv j.val (B s))) hu
      (hf.symm.trans hmap.symm)
  have hmaps : (u.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin d) ℤ)).map c =
      (u.map (Int.castRingHom ℚ)).map MvPolynomial.C := by
    apply Polynomial.ext
    intro n
    simp [Polynomial.coeff_map, c, MvPolynomial.map_C]
  have he : W = Polynomial.C v * u.map MvPolynomial.C := by
    apply Polynomial.map_injective c hc
    rw [Polynomial.map_mul, Polynomial.map_C, hmaps]
    exact hfact
  refine ⟨ell, alpha, u, v, hp,
    hb.trans (Nat.add_le_add_right (Polynomial.natDegree_map_le (p := P) (f := c)) 1),
    hbudget, he, huprim.ne_zero, ?_, ?_⟩
  · intro hz
    have hvzero : q • Matrix.det
        (fun i s : Fin ell => rothDividedDerivative (alpha i) (A s)) = 0 := by
      rw [← hqv, hz, map_zero]
    have hqC : (MvPolynomial.C q : MvPolynomial (Fin d) ℚ) ≠ 0 := by
      intro hzq
      apply hq
      exact MvPolynomial.C_injective (Fin d) ℚ (by simpa using hzq)
    apply mul_ne_zero hqC hv
    simpa only [Algebra.smul_def, MvPolynomial.algebraMap_eq] using hvzero
  · intro hz
    apply hw
    change W = 0 at hz
    rw [← hmap, hz, Polynomial.map_zero]

theorem rothIntegerDividedDerivative_coeff {d : ℕ}
    (a gamma : Fin d →₀ ℕ) (P : MvPolynomial (Fin d) ℤ) :
    (rothIntegerDividedDerivative a P).coeff gamma =
      P.coeff (gamma + a) *
        ∏ k : Fin d, (Nat.choose ((gamma + a) k) (a k) : ℤ) := by
  classical
  rw [rothIntegerDividedDerivative, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  calc
    _ = (MvPolynomial.monomial ((gamma + a) - a)
        (P.coeff (gamma + a) * ∏ k : Fin d,
          (Nat.choose ((gamma + a) k) (a k) : ℤ))).coeff gamma := by
      apply Finset.sum_eq_single (gamma + a)
      · intro b hb hne
        by_cases hab : a ≤ b
        · have hd : b - a ≠ gamma := by
            intro hz
            apply hne
            calc
              b = (b - a) + a := (tsub_add_cancel_of_le hab).symm
              _ = gamma + a := by rw [hz]
          simp [MvPolynomial.coeff_monomial, hd]
        · change ¬ ∀ k, a k ≤ b k at hab
          push_neg at hab
          obtain ⟨k, hk⟩ := hab
          have hz : (∏ k : Fin d, (Nat.choose (b k) (a k) : ℤ)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            simp [Nat.choose_eq_zero_of_lt hk]
          simp [hz]
      · intro hn
        have hz : P.coeff (gamma + a) = 0 := MvPolynomial.not_mem_support_iff.mp hn
        simp [hz]
    _ = _ := by simp

noncomputable def rothIntegerHeight {d : ℕ} (P : MvPolynomial (Fin d) ℤ) : ℕ :=
  P.support.sup fun b => (P.coeff b).natAbs

theorem rothIntegerHeight_coeff_le {d : ℕ}
    (P : MvPolynomial (Fin d) ℤ) (b : Fin d →₀ ℕ) :
    (P.coeff b).natAbs ≤ rothIntegerHeight P := by
  classical
  by_cases hb : b ∈ P.support
  · exact Finset.le_sup (f := fun b => (P.coeff b).natAbs) hb
  · simp [MvPolynomial.not_mem_support_iff.mp hb]

theorem rothIntegerHeight_dividedDerivative_le {d : ℕ}
    (P : MvPolynomial (Fin d) ℤ) (a : Fin d →₀ ℕ) (r : Fin d → ℕ)
    (hP : ∀ b ∈ P.support, ∀ k, b k ≤ r k) :
    rothIntegerHeight (rothIntegerDividedDerivative a P) ≤
      rothIntegerHeight P * 2 ^ (∑ k : Fin d, r k) := by
  classical
  apply Finset.sup_le
  intro gamma _
  rw [rothIntegerDividedDerivative_coeff]
  by_cases hz : P.coeff (gamma + a) = 0
  · simp [hz]
  · have hb := hP (gamma + a) (MvPolynomial.mem_support_iff.mpr hz)
    have hchoose (k : Fin d) : Nat.choose ((gamma + a) k) (a k) ≤ 2 ^ r k := by
      have h : Nat.choose ((gamma + a) k) (a k) ≤ 2 ^ ((gamma + a) k) := by
        by_cases hn : (gamma + a) k = 0
        · have ha : a k = 0 := by
            have hn' : gamma k + a k = 0 := hn
            omega
          simp [hn, ha]
        · exact (Nat.choose_le_two_pow _ _ (Nat.pos_of_ne_zero hn)).le
      exact h.trans (Nat.pow_le_pow_right (by decide) (hb k))
    have hp : (∏ k : Fin d, (Nat.choose ((gamma + a) k) (a k) : ℤ)).natAbs =
        ∏ k : Fin d, Nat.choose ((gamma + a) k) (a k) := by
      rw [← Nat.cast_prod]
      rfl
    rw [Int.natAbs_mul, hp]
    apply Nat.mul_le_mul (rothIntegerHeight_coeff_le P (gamma + a))
    calc
      _ ≤ ∏ k : Fin d, 2 ^ r k := Finset.prod_le_prod' (fun k _ => hchoose k)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

end JSP000334

open scoped BigOperators
namespace JSP000334

noncomputable def rothUnivariateIntegerHeight (u : Polynomial ℤ) : ℕ :=
  u.support.sup fun n => (u.coeff n).natAbs

noncomputable def rothNestedIntegerHeight {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) : ℕ :=
  P.support.sup fun n => rothIntegerHeight (P.coeff n)

theorem rothUnivariateIntegerHeight_coeff_le (u : Polynomial ℤ) (n : ℕ) :
    (u.coeff n).natAbs ≤ rothUnivariateIntegerHeight u := by
  classical
  by_cases hn : n ∈ u.support
  · exact Finset.le_sup (f := fun n => (u.coeff n).natAbs) hn
  · simp [Polynomial.not_mem_support_iff.mp hn]

theorem rothNestedIntegerHeight_coeff_le {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (n : ℕ) (b : Fin d →₀ ℕ) :
    ((P.coeff n).coeff b).natAbs ≤ rothNestedIntegerHeight P := by
  classical
  apply (rothIntegerHeight_coeff_le (P.coeff n) b).trans
  by_cases hn : n ∈ P.support
  · exact Finset.le_sup (f := fun n => rothIntegerHeight (P.coeff n)) hn
  · simp [Polynomial.not_mem_support_iff.mp hn, rothIntegerHeight]

theorem rothNestedIntegerHeight_le_iff {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (H : ℕ) :
    rothNestedIntegerHeight P ≤ H ↔ ∀ n b, ((P.coeff n).coeff b).natAbs ≤ H := by
  classical
  constructor
  · intro h n b
    exact (rothNestedIntegerHeight_coeff_le P n b).trans h
  · intro h
    apply Finset.sup_le
    intro n _
    apply Finset.sup_le
    intro b _
    exact h n b

theorem rothSeparatedInteger_coeff {d : ℕ} (v : MvPolynomial (Fin d) ℤ)
    (u : Polynomial ℤ) (n : ℕ) (b : Fin d →₀ ℕ) :
    ((Polynomial.C v * u.map MvPolynomial.C).coeff n).coeff b =
      v.coeff b * u.coeff n := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map, mul_comm,
    MvPolynomial.coeff_C_mul, mul_comm]

theorem rothNestedIntegerHeight_separated {d : ℕ}
    (v : MvPolynomial (Fin d) ℤ) (u : Polynomial ℤ) :
    rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) =
      rothIntegerHeight v * rothUnivariateIntegerHeight u := by
  classical
  apply Nat.le_antisymm
  · apply (rothNestedIntegerHeight_le_iff _ _).mpr
    intro n b
    rw [rothSeparatedInteger_coeff, Int.natAbs_mul]
    exact Nat.mul_le_mul (rothIntegerHeight_coeff_le v b)
      (rothUnivariateIntegerHeight_coeff_le u n)
  · by_cases hv : v = 0
    · simp [hv, rothIntegerHeight]
    by_cases hu : u = 0
    · simp [hu, rothUnivariateIntegerHeight]
    obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_sup v.support
      (MvPolynomial.support_nonempty.mpr hv) (fun b => (v.coeff b).natAbs)
    obtain ⟨n, hn, hf⟩ := Finset.exists_mem_eq_sup u.support
      (Polynomial.support_nonempty.mpr hu) (fun n => (u.coeff n).natAbs)
    change (v.support.sup _) * (u.support.sup _) ≤ _
    rw [he, hf]
    have h := rothNestedIntegerHeight_coeff_le (Polynomial.C v * u.map MvPolynomial.C) n b
    rw [rothSeparatedInteger_coeff v u n b, Int.natAbs_mul] at h
    exact h

theorem rothIntegerHeight_pos {d : ℕ} (v : MvPolynomial (Fin d) ℤ) (hv : v ≠ 0) :
    1 ≤ rothIntegerHeight v := by
  obtain ⟨b, hb⟩ := MvPolynomial.exists_coeff_ne_zero hv
  exact (Nat.one_le_iff_ne_zero.mpr (by simpa using hb)).trans
    (rothIntegerHeight_coeff_le v b)

theorem rothUnivariateIntegerHeight_pos (u : Polynomial ℤ) (hu : u ≠ 0) :
    1 ≤ rothUnivariateIntegerHeight u := by
  have he : ∃ n, u.coeff n ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (Polynomial.ext (by simpa using h))
  obtain ⟨n, hn⟩ := he
  exact (Nat.one_le_iff_ne_zero.mpr (by simpa using hn)).trans
    (rothUnivariateIntegerHeight_coeff_le u n)

theorem rothSeparatedIntegerHeight_bounds {d : ℕ}
    (v : MvPolynomial (Fin d) ℤ) (u : Polynomial ℤ) (hv : v ≠ 0) (hu : u ≠ 0) :
    rothIntegerHeight v ≤ rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) ∧
    rothUnivariateIntegerHeight u ≤
      rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) := by
  rw [rothNestedIntegerHeight_separated]
  constructor
  · exact Nat.le_mul_of_pos_right _ (rothUnivariateIntegerHeight_pos u hu)
  · exact Nat.le_mul_of_pos_left _ (rothIntegerHeight_pos v hv)

end JSP000334

open scoped BigOperators
namespace JSP000334

def rothNestedSupportBound {d : ℕ} (P : Polynomial (MvPolynomial (Fin d) ℤ))
    (r : Fin d → ℕ) (s : ℕ) : Prop :=
  ∀ n b, (P.coeff n).coeff b ≠ 0 → n ≤ s ∧ ∀ k, b k ≤ r k

theorem rothIntegerMixedDividedDerivative_coeff {d : ℕ}
    (a b : Fin d →₀ ℕ) (j n : ℕ) (P : Polynomial (MvPolynomial (Fin d) ℤ)) :
    ((rothIntegerMixedDividedDerivative a j P).coeff n).coeff b =
      (Nat.choose (n + j) j : ℤ) * (P.coeff (n + j)).coeff (b + a) *
        ∏ k : Fin d, (Nat.choose ((b + a) k) (a k) : ℤ) := by
  rw [rothIntegerMixedDividedDerivative, Polynomial.hasseDeriv_coeff]
  change ((Nat.choose (n + j) j : MvPolynomial (Fin d) ℤ) *
    rothIntegerDividedDerivative a (P.coeff (n + j))).coeff b = _
  rw [show (Nat.choose (n + j) j : MvPolynomial (Fin d) ℤ) =
    MvPolynomial.C (Nat.choose (n + j) j : ℤ) by simp,
    MvPolynomial.coeff_C_mul, rothIntegerDividedDerivative_coeff]
  ring

theorem rothNestedSupportBound_mixed {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (r : Fin d → ℕ) (s : ℕ)
    (hP : rothNestedSupportBound P r s) (a : Fin d →₀ ℕ) (j : ℕ) :
    rothNestedSupportBound (rothIntegerMixedDividedDerivative a j P) r s := by
  intro n b hn
  rw [rothIntegerMixedDividedDerivative_coeff] at hn
  have hc : (P.coeff (n + j)).coeff (b + a) ≠ 0 := by
    intro hz
    simp [hz] at hn
  obtain ⟨hs, hr⟩ := hP (n + j) (b + a) hc
  refine ⟨by omega, fun k => ?_⟩
  have hk := hr k
  change b k + a k ≤ r k at hk
  omega

private theorem rothNestedSupportBound_sum {d : ℕ} {ι : Type*}
    (t : Finset ι) (f : ι → Polynomial (MvPolynomial (Fin d) ℤ))
    (r : Fin d → ℕ) (s : ℕ) (hf : ∀ i ∈ t, rothNestedSupportBound (f i) r s) :
    rothNestedSupportBound (∑ i ∈ t, f i) r s := by
  classical
  intro n b hn
  simp only [Polynomial.finset_sum_coeff, MvPolynomial.coeff_sum] at hn
  obtain ⟨i, hi, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact hf i hi n b hc

private theorem rothNestedSupportBound_mul {d : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin d) ℤ))
    (r t : Fin d → ℕ) (s u : ℕ)
    (hP : rothNestedSupportBound P r s) (hQ : rothNestedSupportBound Q t u) :
    rothNestedSupportBound (P * Q) (fun k => r k + t k) (s + u) := by
  classical
  intro n b hn
  rw [Polynomial.coeff_mul, MvPolynomial.coeff_sum] at hn
  obtain ⟨⟨i,j⟩, hij, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨a, ha, c, hc', he⟩ := Finset.mem_add.mp
    (MvPolynomial.support_mul (P.coeff i) (Q.coeff j) (MvPolynomial.mem_support_iff.mpr hc))
  obtain ⟨hi, hr⟩ := hP i a (MvPolynomial.mem_support_iff.mp ha)
  obtain ⟨hj, ht⟩ := hQ j c (MvPolynomial.mem_support_iff.mp hc')
  have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
  refine ⟨by omega, fun k => ?_⟩
  rw [← he, Finsupp.add_apply]
  exact Nat.add_le_add (hr k) (ht k)

private theorem rothNestedSupportBound_one {d : ℕ} :
    rothNestedSupportBound (1 : Polynomial (MvPolynomial (Fin d) ℤ)) (fun _ => 0) 0 := by
  classical
  intro n b hn
  by_cases hn0 : n = 0
  · subst n
    by_cases hb0 : b = 0
    · subst b; simp
    · simp [MvPolynomial.coeff_one, hb0, Ne.symm hb0] at hn
  · simp [Polynomial.coeff_one, hn0] at hn

private theorem rothNestedSupportBound_prod {d : ℕ} {ι : Type*}
    (t : Finset ι) (f : ι → Polynomial (MvPolynomial (Fin d) ℤ))
    (r : Fin d → ℕ) (s : ℕ) (hf : ∀ i ∈ t, rothNestedSupportBound (f i) r s) :
    rothNestedSupportBound (∏ i ∈ t, f i) (fun k => t.card * r k) (t.card * s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using rothNestedSupportBound_one (d := d)
  | @insert i t hit ih =>
    rw [Finset.prod_insert hit, Finset.card_insert_of_not_mem hit]
    have hm := rothNestedSupportBound_mul (f i) (∏ a ∈ t, f a) r
      (fun k => t.card * r k) s (t.card * s) (hf i (Finset.mem_insert_self i t))
      (ih (fun a ha => hf a (Finset.mem_insert_of_mem ha)))
    simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm] using hm

theorem rothNestedSupportBound_det {d ell : ℕ}
    (M : Matrix (Fin ell) (Fin ell) (Polynomial (MvPolynomial (Fin d) ℤ)))
    (r : Fin d → ℕ) (s : ℕ) (hM : ∀ i j, rothNestedSupportBound (M i j) r s) :
    rothNestedSupportBound M.det (fun k => ell * r k) (ell * s) := by
  classical
  rw [Matrix.det_apply]
  apply rothNestedSupportBound_sum
  intro p _
  have hp := rothNestedSupportBound_prod Finset.univ (fun i => M (p i) i) r s
    (fun i _ => hM (p i) i)
  simp only [Finset.card_univ, Fintype.card_fin] at hp
  intro n b hn
  apply hp n b
  intro hz
  simp only [Polynomial.coeff_smul, MvPolynomial.coeff_smul, hz, smul_zero] at hn
  exact hn rfl

theorem rothMixedWronskian_support {d ell : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (r : Fin d → ℕ) (s : ℕ)
    (hP : rothNestedSupportBound P r s) (alpha : Fin ell → (Fin d →₀ ℕ)) :
    rothNestedSupportBound
      (Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P))
      (fun k => ell * r k) (ell * s) :=
  rothNestedSupportBound_det _ r s (fun i j => rothNestedSupportBound_mixed P r s hP (alpha i) j.val)

end JSP000334

namespace JSP000334

theorem rothSeparatedInteger_degree_bounds {d : ℕ}
    (v : MvPolynomial (Fin d) ℤ) (u : Polynomial ℤ)
    (hv : v ≠ 0) (hu : u ≠ 0) (r : Fin d → ℕ) (s : ℕ)
    (h : rothNestedSupportBound (Polynomial.C v * u.map MvPolynomial.C) r s) :
    u.natDegree ≤ s ∧ ∀ k, v.degreeOf k ≤ r k := by
  classical
  obtain ⟨b, hb⟩ := MvPolynomial.exists_coeff_ne_zero hv
  have hn : u.coeff u.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hu
  have hh := h u.natDegree b (by rw [rothSeparatedInteger_coeff]; exact mul_ne_zero hb hn)
  refine ⟨hh.1, fun k => MvPolynomial.degreeOf_le_iff.mpr ?_⟩
  intro c hc
  exact (h u.natDegree c (by
    rw [rothSeparatedInteger_coeff]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hc) hn)).2 k

theorem roth_exists_integral_separated_wronskian_bounds
    (d : ℕ) (hd : 1 ≤ d)
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (hP : P ≠ 0)
    (r : Fin d → ℕ) (s : ℕ) (hb : rothNestedSupportBound P r s) :
    ∃ (ell : ℕ) (alpha : Fin ell → (Fin d →₀ ℕ))
        (u : Polynomial ℤ) (v : MvPolynomial (Fin d) ℤ),
      1 ≤ ell ∧ ell ≤ P.natDegree + 1 ∧
      (∀ i, (∑ k : Fin d, alpha i k) ≤ i.val) ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) =
        Polynomial.C v * u.map MvPolynomial.C ∧
      u ≠ 0 ∧ v ≠ 0 ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) ≠ 0 ∧
      rothNestedSupportBound (Polynomial.C v * u.map MvPolynomial.C)
        (fun k => ell * r k) (ell * s) ∧
      u.natDegree ≤ ell * s ∧ (∀ k, v.degreeOf k ≤ ell * r k) ∧
      rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) =
        rothIntegerHeight v * rothUnivariateIntegerHeight u ∧
      rothIntegerHeight v ≤ rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) ∧
      rothUnivariateIntegerHeight u ≤
        rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) := by
  obtain ⟨ell, alpha, u, v, hl, he, ha, hw, hu, hv, hn⟩ :=
    roth_exists_integral_separated_wronskian d hd P hP
  have hs := rothMixedWronskian_support P r s hb alpha
  rw [hw] at hs
  obtain ⟨hdu, hdv⟩ := rothSeparatedInteger_degree_bounds v u hv hu _ _ hs
  obtain ⟨hHv, hHu⟩ := rothSeparatedIntegerHeight_bounds v u hv hu
  exact ⟨ell, alpha, u, v, hl, he, ha, hw, hu, hv, hn, hs, hdu, hdv,
    rothNestedIntegerHeight_separated v u, hHv, hHu⟩

end JSP000334

namespace JSP000334

private theorem rothNestedIntegerHeight_sum {d : ℕ} {ι : Type*}
    (t : Finset ι) (f : ι → Polynomial (MvPolynomial (Fin d) ℤ)) :
    rothNestedIntegerHeight (∑ i ∈ t, f i) ≤ ∑ i ∈ t, rothNestedIntegerHeight (f i) := by
  classical
  apply (rothNestedIntegerHeight_le_iff _ _).mpr
  intro n b
  simp only [Polynomial.finset_sum_coeff, MvPolynomial.coeff_sum]
  exact (nat_abs_sum_le t _).trans (Finset.sum_le_sum (fun i _ =>
    rothNestedIntegerHeight_coeff_le (f i) n b))

private theorem rothNestedIntegerHeight_monomial_mul {d : ℕ}
    (Q : Polynomial (MvPolynomial (Fin d) ℤ)) (i : ℕ) (a : Fin d →₀ ℕ) (c : ℤ) :
    rothNestedIntegerHeight (Polynomial.monomial i (MvPolynomial.monomial a c) * Q) ≤
      c.natAbs * rothNestedIntegerHeight Q := by
  classical
  apply (rothNestedIntegerHeight_le_iff _ _).mpr
  intro n b
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  split_ifs with hi
  · rw [MvPolynomial.coeff_monomial_mul']
    split_ifs with ha
    · rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (rothNestedIntegerHeight_coeff_le Q (n - i) (b - a))
    · simp
  · simp

noncomputable def rothNestedIntegerMass {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) : ℕ :=
  ∑ n ∈ P.support, ∑ b ∈ (P.coeff n).support, ((P.coeff n).coeff b).natAbs

private theorem rothNestedIntegerHeight_mul_mass {d : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin d) ℤ)) :
    rothNestedIntegerHeight (P * Q) ≤ rothNestedIntegerMass P * rothNestedIntegerHeight Q := by
  classical
  have he : P = ∑ n ∈ P.support, ∑ b ∈ (P.coeff n).support,
      Polynomial.monomial n (MvPolynomial.monomial b ((P.coeff n).coeff b)) := by
    calc
      P = ∑ n ∈ P.support, Polynomial.monomial n (P.coeff n) := by
        simpa only [Polynomial.sum_def] using (Polynomial.sum_monomial_eq P).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← map_sum, ← MvPolynomial.as_sum (P.coeff n)]
  calc
    rothNestedIntegerHeight (P * Q) = rothNestedIntegerHeight
        (∑ n ∈ P.support, ∑ b ∈ (P.coeff n).support,
          Polynomial.monomial n (MvPolynomial.monomial b ((P.coeff n).coeff b)) * Q) := by
      conv_lhs => rw [he]
      simp only [Finset.sum_mul]
    _ ≤ ∑ n ∈ P.support, rothNestedIntegerHeight
        (∑ b ∈ (P.coeff n).support,
          Polynomial.monomial n (MvPolynomial.monomial b ((P.coeff n).coeff b)) * Q) :=
      rothNestedIntegerHeight_sum _ _
    _ ≤ ∑ n ∈ P.support, ∑ b ∈ (P.coeff n).support,
        ((P.coeff n).coeff b).natAbs * rothNestedIntegerHeight Q := by
      apply Finset.sum_le_sum
      intro n _
      exact (rothNestedIntegerHeight_sum _ _).trans (Finset.sum_le_sum
        (fun b _ => rothNestedIntegerHeight_monomial_mul Q n b _))
    _ = _ := by simp only [rothNestedIntegerMass, Finset.sum_mul]

private theorem rothNestedIntegerHeight_prod_mass {d : ℕ} {ι : Type*}
    (t : Finset ι) (f : ι → Polynomial (MvPolynomial (Fin d) ℤ)) :
    rothNestedIntegerHeight (∏ i ∈ t, f i) ≤ ∏ i ∈ t, rothNestedIntegerMass (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    apply (rothNestedIntegerHeight_le_iff _ _).mpr
    intro n b
    by_cases hn : n = 0
    · subst n
      by_cases hb : b = 0
      · subst b; simp [Polynomial.coeff_one, MvPolynomial.coeff_one]
      · simp [Polynomial.coeff_one, MvPolynomial.coeff_one, hb, Ne.symm hb]
    · simp [Polynomial.coeff_one, hn]
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (rothNestedIntegerHeight_mul_mass _ _).trans (Nat.mul_le_mul_left _ ih)

end JSP000334

namespace JSP000334

private theorem rothInteger_support_card {d : ℕ}
    (v : MvPolynomial (Fin d) ℤ) (r : Fin d → ℕ)
    (hv : ∀ b ∈ v.support, ∀ k, b k ≤ r k) :
    v.support.card ≤ ∏ k : Fin d, (r k + 1) := by
  classical
  let f : {b // b ∈ v.support} → (∀ k : Fin d, Fin (r k + 1)) :=
    fun b k => ⟨b.val k, Nat.lt_succ_of_le (hv b.val b.property k)⟩
  have hf : Function.Injective f := by
    intro b c he
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    exact congrArg Fin.val (congrFun he k)
  simpa [Fintype.card_pi] using Fintype.card_le_of_injective f hf

private theorem rothNestedIntegerMass_le {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (r : Fin d → ℕ) (s : ℕ)
    (hP : rothNestedSupportBound P r s) :
    rothNestedIntegerMass P ≤
      ((s + 1) * ∏ k : Fin d, (r k + 1)) * rothNestedIntegerHeight P := by
  classical
  have hc (n : ℕ) : (P.coeff n).support.card ≤ ∏ k : Fin d, (r k + 1) :=
    rothInteger_support_card _ r (fun b hb => (hP n b (MvPolynomial.mem_support_iff.mp hb)).2)
  have hs : P.support.card ≤ s + 1 := by
    apply (Finset.card_le_card (t := Finset.range (s + 1)) ?_).trans_eq (Finset.card_range _)
    intro n hn
    obtain ⟨b, hb⟩ := MvPolynomial.exists_coeff_ne_zero (Polynomial.mem_support_iff.mp hn)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hP n b hb).1)
  calc
    rothNestedIntegerMass P ≤ ∑ n ∈ P.support,
        (P.coeff n).support.card * rothNestedIntegerHeight P := by
      apply Finset.sum_le_sum
      intro n _
      exact (Finset.sum_le_sum (fun b _ => rothNestedIntegerHeight_coeff_le P n b)).trans_eq
        (by simp)
    _ ≤ ∑ n ∈ P.support, (∏ k : Fin d, (r k + 1)) * rothNestedIntegerHeight P := by
      exact Finset.sum_le_sum (fun n _ => Nat.mul_le_mul_right _ (hc n))
    _ = P.support.card * ((∏ k : Fin d, (r k + 1)) * rothNestedIntegerHeight P) := by simp
    _ ≤ _ := by exact (Nat.mul_le_mul_right _ hs).trans_eq (by ring)

theorem rothNestedIntegerHeight_mixed_le {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (r : Fin d → ℕ) (s : ℕ)
    (hP : rothNestedSupportBound P r s) (a : Fin d →₀ ℕ) (j : ℕ) :
    rothNestedIntegerHeight (rothIntegerMixedDividedDerivative a j P) ≤
      2 ^ (s + ∑ k : Fin d, r k) * rothNestedIntegerHeight P := by
  classical
  apply (rothNestedIntegerHeight_le_iff _ _).mpr
  intro n b
  have he : (rothIntegerMixedDividedDerivative a j P).coeff n =
      (Nat.choose (n + j) j : MvPolynomial (Fin d) ℤ) *
        rothIntegerDividedDerivative a (P.coeff (n + j)) := by
    rw [rothIntegerMixedDividedDerivative, Polynomial.hasseDeriv_coeff]
    rfl
  rw [he, show (Nat.choose (n + j) j : MvPolynomial (Fin d) ℤ) =
    MvPolynomial.C (Nat.choose (n + j) j : ℤ) by simp, MvPolynomial.coeff_C_mul,
    Int.natAbs_mul, Int.natAbs_natCast]
  by_cases hz : P.coeff (n + j) = 0
  · simp [hz, rothIntegerDividedDerivative]
  obtain ⟨c, hc⟩ := MvPolynomial.exists_coeff_ne_zero hz
  have hs := (hP (n + j) c hc).1
  have hch : Nat.choose (n + j) j ≤ 2 ^ s := by
    apply le_trans (b := 2 ^ (n + j))
    · by_cases hn : n + j = 0
      · have hj : j = 0 := by omega
        have hn0 : n = 0 := by omega
        simp [hn0, hj]
      · exact (Nat.choose_le_two_pow _ _ (Nat.pos_of_ne_zero hn)).le
    · exact Nat.pow_le_pow_right (by decide) hs
  have hd := rothIntegerHeight_dividedDerivative_le (P.coeff (n + j)) a r
    (fun c hc => (hP (n + j) c (MvPolynomial.mem_support_iff.mp hc)).2)
  have hh : rothIntegerHeight (P.coeff (n + j)) ≤ rothNestedIntegerHeight P := by
    apply Finset.sup_le
    intro c _
    exact rothNestedIntegerHeight_coeff_le P (n + j) c
  calc
    _ ≤ 2 ^ s * rothIntegerHeight (rothIntegerDividedDerivative a (P.coeff (n + j))) :=
      Nat.mul_le_mul hch (rothIntegerHeight_coeff_le _ b)
    _ ≤ 2 ^ s * (rothNestedIntegerHeight P * 2 ^ (∑ k : Fin d, r k)) :=
      Nat.mul_le_mul_left _ (hd.trans (Nat.mul_le_mul_right _ hh))
    _ = _ := by rw [pow_add]; ring

theorem rothMixedWronskian_height_le {d ell : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (r : Fin d → ℕ) (s : ℕ)
    (hP : rothNestedSupportBound P r s) (alpha : Fin ell → (Fin d →₀ ℕ)) :
    rothNestedIntegerHeight
      (Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)) ≤
      ((s + 1) * ∏ k : Fin d, (r k + 1)) ^ ell * Nat.factorial ell *
        2 ^ (ell * (s + ∑ k : Fin d, r k)) * rothNestedIntegerHeight P ^ ell := by
  classical
  let B := ((s + 1) * ∏ k : Fin d, (r k + 1)) *
    (2 ^ (s + ∑ k : Fin d, r k) * rothNestedIntegerHeight P)
  have hm (i j : Fin ell) :
      rothNestedIntegerMass (rothIntegerMixedDividedDerivative (alpha i) j.val P) ≤ B :=
    (rothNestedIntegerMass_le _ r s (rothNestedSupportBound_mixed P r s hP _ _)).trans
      (Nat.mul_le_mul_left _ (rothNestedIntegerHeight_mixed_le P r s hP _ _))
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ p : Equiv.Perm (Fin ell), rothNestedIntegerHeight
        (p.sign • ∏ i, rothIntegerMixedDividedDerivative (alpha (p i)) i.val P) :=
      rothNestedIntegerHeight_sum _ _
    _ ≤ ∑ p : Equiv.Perm (Fin ell), B ^ ell := by
      apply Finset.sum_le_sum
      intro p _
      have hsign (Q : Polynomial (MvPolynomial (Fin d) ℤ)) :
          rothNestedIntegerHeight (p.sign • Q) ≤ rothNestedIntegerHeight Q := by
        apply (rothNestedIntegerHeight_le_iff _ _).mpr
        intro n b
        rcases Int.units_eq_one_or p.sign with hs | hs
        · simpa [hs] using rothNestedIntegerHeight_coeff_le Q n b
        · simpa [hs, Polynomial.coeff_neg, MvPolynomial.coeff_neg] using
            rothNestedIntegerHeight_coeff_le Q n b
      apply (hsign _).trans
      apply (rothNestedIntegerHeight_prod_mass _ _).trans
      exact (Finset.prod_le_prod' (fun i _ => hm (p i) i)).trans_eq (by simp)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        smul_eq_mul]
      dsimp [B]
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm (s + ∑ k : Fin d, r k) ell]
      ring

end JSP000334

namespace JSP000334

theorem rothMixedWronskian_height_le_ordered {d ell : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (r : Fin d → ℕ) (s R : ℕ)
    (hP : rothNestedSupportBound P r s) (hs : s ≤ R) (hr : ∀ k, r k ≤ R)
    (he : ell ≤ s + 1) (alpha : Fin ell → (Fin d →₀ ℕ)) :
    rothNestedIntegerHeight
      (Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)) ≤
      2 ^ (3 * (d + 1) * R * ell) * rothNestedIntegerHeight P ^ ell := by
  classical
  let S := s + ∑ k : Fin d, r k
  have hN : ((s + 1) * ∏ k : Fin d, (r k + 1)) ≤ 2 ^ S := by
    calc
      _ ≤ 2 ^ s * ∏ k : Fin d, 2 ^ r k :=
        Nat.mul_le_mul ((Nat.lt_two_pow_self (n := s))) (Finset.prod_le_prod'
          (fun k _ => (Nat.lt_two_pow_self (n := r k))))
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
  have hS : S ≤ (d + 1) * R := by
    have hsum : (∑ k : Fin d, r k) ≤ d * R := by
      simpa using Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) => hr k)
    dsimp [S]
    nlinarith
  have hfact : Nat.factorial ell ≤ 2 ^ (R * ell) := by
    calc
      _ ≤ ell ^ ell := Nat.factorial_le_pow ell
      _ ≤ (2 ^ R) ^ ell := Nat.pow_le_pow_left (he.trans (hs.trans_lt (Nat.lt_two_pow_self (n := R)))) ell
      _ = _ := (pow_mul _ _ _).symm
  have hpow : 2 ^ (ell * S + R * ell + ell * S) ≤ 2 ^ (3 * (d + 1) * R * ell) := by
    apply Nat.pow_le_pow_right (by decide)
    have hSE := Nat.mul_le_mul_left ell hS
    have hRE : R ≤ (d + 1) * R := by nlinarith
    have hREl := Nat.mul_le_mul_right ell hRE
    nlinarith
  apply (rothMixedWronskian_height_le P r s hP alpha).trans
  apply Nat.mul_le_mul_right
  calc
    _ ≤ (2 ^ S) ^ ell * 2 ^ (R * ell) * 2 ^ (ell * S) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left hN ell) hfact)
    _ = 2 ^ (ell * S + R * ell + ell * S) := by
      rw [← pow_mul, ← pow_add, ← pow_add, Nat.mul_comm S ell]
    _ ≤ _ := hpow

end JSP000334

namespace JSP000334
noncomputable def rothLastVariableEquiv (d : ℕ) :
    MvPolynomial (Fin (d + 1)) ℤ ≃ₐ[ℤ] Polynomial (MvPolynomial (Fin d) ℤ) :=
  (MvPolynomial.renameEquiv ℤ (finRotate (d + 1))).trans (MvPolynomial.finSuccEquiv ℤ d)

theorem rothLastVariableEquiv_X_last (d : ℕ) :
    rothLastVariableEquiv d (MvPolynomial.X (Fin.last d)) = Polynomial.X := by
  simp [rothLastVariableEquiv, finRotate_last, MvPolynomial.finSuccEquiv_X_zero]

theorem rothLastVariableEquiv_X_castSucc {d : ℕ} (k : Fin d) :
    rothLastVariableEquiv d (MvPolynomial.X k.castSucc) = Polynomial.C (MvPolynomial.X k) := by
  have hr : finRotate (d + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
  simp [rothLastVariableEquiv, hr, MvPolynomial.finSuccEquiv_X_succ]
end JSP000334
namespace JSP000334

noncomputable def rothLastExponent {d : ℕ} (n : ℕ) (b : Fin d →₀ ℕ) : Fin (d + 1) →₀ ℕ :=
  (b.cons n).mapDomain (finRotate (d + 1)).symm

theorem rothLastExponent_last {d : ℕ} (n : ℕ) (b : Fin d →₀ ℕ) :
    rothLastExponent n b (Fin.last d) = n := by
  simp [rothLastExponent, Finsupp.mapDomain_equiv_apply, finRotate_last]

theorem rothLastExponent_castSucc {d : ℕ} (n : ℕ) (b : Fin d →₀ ℕ) (k : Fin d) :
    rothLastExponent n b k.castSucc = b k := by
  have hr : finRotate (d + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
  simp [rothLastExponent, Finsupp.mapDomain_equiv_apply, hr]

theorem rothLastVariableEquiv_coeff {d : ℕ}
    (P : MvPolynomial (Fin (d + 1)) ℤ) (n : ℕ) (b : Fin d →₀ ℕ) :
    ((rothLastVariableEquiv d P).coeff n).coeff b = P.coeff (rothLastExponent n b) := by
  change (((MvPolynomial.finSuccEquiv ℤ d)
    (MvPolynomial.rename (finRotate (d + 1)) P)).coeff n).coeff b = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  have he : (rothLastExponent n b).mapDomain (finRotate (d + 1)) = b.cons n := by
    ext k
    simp [rothLastExponent, Finsupp.mapDomain_equiv_apply]
  rw [← he, MvPolynomial.coeff_rename_mapDomain _ (finRotate (d + 1)).injective]

end JSP000334

namespace JSP000334

theorem rothWronskian_height_absorption
    (m R ell H W : ℕ) (Q rho C : ℝ) (hQ : 0 < Q)
    (hden : (2 : ℝ) ^ (3 * m) ≤ Q ^ (rho * C))
    (hH : (H : ℝ) ≤ Q ^ (rho * R * C))
    (hW : W ≤ 2 ^ (3 * m * R * ell) * H ^ ell) :
    (W : ℝ) ≤ Q ^ (2 * rho * R * C * ell) := by
  have hden' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ (3 * m)) hden (R * ell)
  have hH' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ H) hH ell
  have he1 : (Q ^ (rho * C)) ^ (R * ell) = Q ^ (rho * R * C * ell) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 1
    push_cast
    ring
  have he2 : (Q ^ (rho * R * C)) ^ ell = Q ^ (rho * R * C * ell) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
  have he3 : ((2 : ℝ) ^ (3 * m)) ^ (R * ell) = 2 ^ (3 * m * R * ell) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [he1, he3] at hden'
  rw [he2] at hH'
  calc
    (W : ℝ) ≤ 2 ^ (3 * m * R * ell) * (H : ℝ) ^ ell := by exact_mod_cast hW
    _ ≤ Q ^ (rho * R * C * ell) * Q ^ (rho * R * C * ell) :=
      mul_le_mul hden' hH' (by positivity) (Real.rpow_nonneg hQ.le _)
    _ = Q ^ (2 * rho * R * C * ell) := by
      rw [← Real.rpow_add hQ]
      congr 1
      ring

end JSP000334

namespace JSP000334

theorem rothSeparated_height_absorption
    (R s ell U W : ℕ) (Q T rho C : ℝ)
    (hQ : 0 < Q) (hT : 0 < T) (hrho : 0 ≤ rho)
    (hgrowth : Q ^ ((R : ℝ) * C) ≤ T ^ (s : ℝ))
    (hW : (W : ℝ) ≤ Q ^ (2 * rho * R * C * ell)) (hU : U ≤ W) :
    (U : ℝ) ≤ T ^ (2 * rho * s * ell) := by
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hQ.le _) hgrowth
    (show 0 ≤ 2 * rho * (ell : ℝ) by positivity)
  rw [← Real.rpow_mul hQ.le, ← Real.rpow_mul hT.le] at hp
  have he1 : (R : ℝ) * C * (2 * rho * ell) = 2 * rho * R * C * ell := by ring
  have he2 : (s : ℝ) * (2 * rho * ell) = 2 * rho * s * ell := by ring
  rw [he1, he2] at hp
  exact (show (U : ℝ) ≤ W by exact_mod_cast hU).trans (hW.trans hp)

end JSP000334

open scoped BigOperators
namespace JSP000334

noncomputable def rothTaylorPolynomial {d : ℕ} (z : Fin d → ℚ)
    (P : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin d) ℚ :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (z k) + MvPolynomial.X k) P

theorem rothTaylorPolynomial_eq_divided_sum {d K : ℕ}
    (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ b ∈ P.support, ∀ k, b k < K) :
    rothTaylorPolynomial z P = ∑ a : Fin d → Fin K,
      MvPolynomial.monomial (rothBoxMultiIndex a)
        (MvPolynomial.aeval z (rothDividedDerivative (rothBoxMultiIndex a) P)) := by
  classical
  have hc (Q : MvPolynomial (Fin d) ℚ) :
      (MvPolynomial.aeval (fun k => MvPolynomial.C (z k)) Q : MvPolynomial (Fin d) ℚ) =
        MvPolynomial.C (MvPolynomial.aeval z Q) := by
    have he := MvPolynomial.comp_aeval_apply (f := z)
      (Algebra.ofId ℚ (MvPolynomial (Fin d) ℚ)) Q
    simpa only [Algebra.ofId_apply, MvPolynomial.algebraMap_eq] using he.symm
  have ht := roth_taylor_box (fun k => MvPolynomial.C (z k))
    (fun k => MvPolynomial.X k) P hP
  change rothTaylorPolynomial z P = _ at ht
  rw [ht]
  apply Finset.sum_congr rfl
  intro a _
  rw [hc, MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [rothBoxMultiIndex_apply]

noncomputable def rothTaylorWeight {d : ℕ} (r : Fin d → ℕ) (b : Fin d →₀ ℕ) : ℝ :=
  ∑ k : Fin d, (b k : ℝ) / (r k : ℝ)

noncomputable def rothWeightedTaylorIndex {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ) : WithTop ℝ :=
  (rothTaylorPolynomial z P).support.inf fun b => (rothTaylorWeight r b : WithTop ℝ)

theorem rothTaylorWeight_add {d : ℕ} (r : Fin d → ℕ) (a b : Fin d →₀ ℕ) :
    rothTaylorWeight r (a + b) = rothTaylorWeight r a + rothTaylorWeight r b := by
  simp [rothTaylorWeight, Nat.cast_add, add_div, Finset.sum_add_distrib]

theorem rothWeightedTaylorIndex_lower_iff {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ) (t : ℝ) :
    (t : WithTop ℝ) ≤ rothWeightedTaylorIndex r z P ↔
      ∀ b ∈ (rothTaylorPolynomial z P).support, t ≤ rothTaylorWeight r b := by
  classical
  simp [rothWeightedTaylorIndex, Finset.le_inf_iff]

theorem rothWeightedTaylorIndex_mul_lower {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P Q : MvPolynomial (Fin d) ℚ) (a b : ℝ)
    (hP : (a : WithTop ℝ) ≤ rothWeightedTaylorIndex r z P)
    (hQ : (b : WithTop ℝ) ≤ rothWeightedTaylorIndex r z Q) :
    ((a + b : ℝ) : WithTop ℝ) ≤ rothWeightedTaylorIndex r z (P * Q) := by
  classical
  apply (rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
  intro c hc
  simp only [rothTaylorPolynomial, map_mul] at hc
  obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hc)
  rw [← he, rothTaylorWeight_add]
  exact add_le_add ((rothWeightedTaylorIndex_lower_iff _ _ _ _).mp hP u hu)
    ((rothWeightedTaylorIndex_lower_iff _ _ _ _).mp hQ v hv)

theorem rothWeightedTaylorIndex_add_lower {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P Q : MvPolynomial (Fin d) ℚ) (a : ℝ)
    (hP : (a : WithTop ℝ) ≤ rothWeightedTaylorIndex r z P)
    (hQ : (a : WithTop ℝ) ≤ rothWeightedTaylorIndex r z Q) :
    (a : WithTop ℝ) ≤ rothWeightedTaylorIndex r z (P + Q) := by
  classical
  apply (rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
  intro c hc
  simp only [rothTaylorPolynomial, map_add] at hc
  rcases Finset.mem_union.mp (MvPolynomial.support_add hc) with hc | hc
  · exact (rothWeightedTaylorIndex_lower_iff _ _ _ _).mp hP c hc
  · exact (rothWeightedTaylorIndex_lower_iff _ _ _ _).mp hQ c hc

end JSP000334
namespace JSP000334

theorem rothTaylorPolynomial_coeff {d : ℕ} (z : Fin d → ℚ)
    (P : MvPolynomial (Fin d) ℚ) (a : Fin d →₀ ℕ) :
    (rothTaylorPolynomial z P).coeff a = MvPolynomial.aeval z (rothDividedDerivative a P) := by
  classical
  let B := P.support.sup (fun b => (Finset.univ : Finset (Fin d)).sup (fun k => b k))
  let A := (Finset.univ : Finset (Fin d)).sup (fun k => a k)
  let K := max A B + 1
  have ha (k : Fin d) : a k < K := by
    have hk := Finset.le_sup (f := fun k => a k) (Finset.mem_univ k)
    have hA : A ≤ max A B := le_max_left _ _
    exact Nat.lt_succ_of_le (hk.trans hA)
  have hP : ∀ b ∈ P.support, ∀ k, b k < K := by
    intro b hb k
    have hk := Finset.le_sup (f := fun k => b k) (Finset.mem_univ k)
    have hb' := Finset.le_sup (f := fun b => (Finset.univ : Finset (Fin d)).sup (fun k => b k)) hb
    have hB : B ≤ max A B := le_max_right _ _
    exact Nat.lt_succ_of_le ((hk.trans hb').trans hB)
  let v : Fin d → Fin K := fun k => ⟨a k, ha k⟩
  have hv : rothBoxMultiIndex v = a := by ext k; rfl
  have hinj : Function.Injective (rothBoxMultiIndex (d := d) (K := K)) := by
    intro u v he
    funext k
    apply Fin.ext
    exact congrArg (fun b => b k) he
  rw [rothTaylorPolynomial_eq_divided_sum z P hP, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single v]
  · simp [hv, MvPolynomial.coeff_monomial]
  · intro u _ hne
    have h : rothBoxMultiIndex u ≠ a := by
      intro he
      apply hne
      exact hinj (he.trans hv.symm)
    simp [MvPolynomial.coeff_monomial, h, Ne.symm h]
  · simp

theorem rothWeightedTaylorIndex_zero {d : ℕ} (r : Fin d → ℕ) (z : Fin d → ℚ) :
    rothWeightedTaylorIndex r z 0 = ⊤ := by
  simp [rothWeightedTaylorIndex, rothTaylorPolynomial]

theorem rothWeightedTaylorIndex_nonneg {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ) :
    (0 : WithTop ℝ) ≤ rothWeightedTaylorIndex r z P := by
  apply (rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
  intro b _
  unfold rothTaylorWeight
  exact Finset.sum_nonneg (fun k _ => by positivity)

end JSP000334

namespace JSP000334

theorem rothDividedDerivative_coeff {d : ℕ}
    (a gamma : Fin d →₀ ℕ) (P : MvPolynomial (Fin d) ℚ) :
    (rothDividedDerivative a P).coeff gamma =
      P.coeff (gamma + a) *
        ∏ k : Fin d, (Nat.choose ((gamma + a) k) (a k) : ℚ) := by
  classical
  rw [rothDividedDerivative, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  calc
    _ = (MvPolynomial.monomial ((gamma + a) - a)
        (P.coeff (gamma + a) * ∏ k : Fin d,
          (Nat.choose ((gamma + a) k) (a k) : ℚ))).coeff gamma := by
      apply Finset.sum_eq_single (gamma + a)
      · intro b hb hne
        by_cases hab : a ≤ b
        · have hd : b - a ≠ gamma := by
            intro hz
            apply hne
            calc
              b = (b - a) + a := (tsub_add_cancel_of_le hab).symm
              _ = gamma + a := by rw [hz]
          simp [MvPolynomial.coeff_monomial, hd]
        · change ¬ ∀ k, a k ≤ b k at hab
          push_neg at hab
          obtain ⟨k, hk⟩ := hab
          have hz : (∏ k : Fin d, (Nat.choose (b k) (a k) : ℚ)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            simp [Nat.choose_eq_zero_of_lt hk]
          simp [hz]
      · intro hn
        have hz : P.coeff (gamma + a) = 0 := MvPolynomial.not_mem_support_iff.mp hn
        simp [hz]
    _ = _ := by simp


end JSP000334

namespace JSP000334

theorem rothDividedDerivative_comp {d : ℕ} (a b : Fin d →₀ ℕ)
    (P : MvPolynomial (Fin d) ℚ) :
    rothDividedDerivative a (rothDividedDerivative b P) =
      (∏ k : Fin d, (Nat.choose ((a + b) k) (a k) : ℚ)) •
        rothDividedDerivative (a + b) P := by
  classical
  apply MvPolynomial.ext
  intro c
  simp only [rothDividedDerivative_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  have hch (k : Fin d) :
      Nat.choose ((c + a + b) k) (b k) * Nat.choose ((c + a) k) (a k) =
        Nat.choose ((a + b) k) (a k) * Nat.choose ((c + a + b) k) ((a + b) k) := by
    simp only [Finsupp.add_apply]
    have h := Nat.choose_mul (n := c k + a k + b k) (k := a k + b k) (s := b k)
      (by omega) (by omega)
    have hn : c k + a k + b k - b k = c k + a k := by omega
    have ha : a k + b k - b k = a k := by omega
    rw [hn, ha] at h
    have hs : Nat.choose (a k + b k) (b k) = Nat.choose (a k + b k) (a k) :=
      Nat.choose_symm_add.symm
    rw [hs] at h
    nlinarith
  calc
    _ = P.coeff (c + (a + b)) *
        ∏ k : Fin d, ((Nat.choose ((c + a + b) k) (b k) : ℚ) *
          (Nat.choose ((c + a) k) (a k) : ℚ)) := by
      rw [Finset.prod_mul_distrib]
      simp only [add_assoc]
      ring
    _ = P.coeff (c + (a + b)) *
        ∏ k : Fin d, ((Nat.choose ((a + b) k) (a k) : ℚ) *
          (Nat.choose ((c + a + b) k) ((a + b) k) : ℚ)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      exact_mod_cast hch k
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [add_assoc]; ring

theorem rothWeightedTaylorIndex_derivative_lower {d : ℕ}
    (r : Fin d → ℕ) (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ)
    (a : Fin d →₀ ℕ) (t : ℝ)
    (hP : (t : WithTop ℝ) ≤ rothWeightedTaylorIndex r z P) :
    ((max 0 (t - rothTaylorWeight r a) : ℝ) : WithTop ℝ) ≤
      rothWeightedTaylorIndex r z (rothDividedDerivative a P) := by
  classical
  apply (rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
  intro b hb
  have hc : (rothTaylorPolynomial z P).coeff (b + a) ≠ 0 := by
    rw [MvPolynomial.mem_support_iff, rothTaylorPolynomial_coeff,
      rothDividedDerivative_comp, map_smul] at hb
    rw [rothTaylorPolynomial_coeff]
    intro hz
    simp [hz] at hb
  have ht := (rothWeightedTaylorIndex_lower_iff _ _ _ _).mp hP (b + a)
    (MvPolynomial.mem_support_iff.mpr hc)
  rw [rothTaylorWeight_add] at ht
  apply max_le
  · unfold rothTaylorWeight
    exact Finset.sum_nonneg (fun k _ => by positivity)
  · linarith

end JSP000334

namespace JSP000334

private theorem rothWeightedTaylorIndex_sum_lower {d : ℕ} {ι : Type*}
    (r : Fin d → ℕ) (z : Fin d → ℚ) (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℚ) (t : ℝ)
    (hf : ∀ i ∈ s, (t : WithTop ℝ) ≤ rothWeightedTaylorIndex r z (f i)) :
    (t : WithTop ℝ) ≤ rothWeightedTaylorIndex r z (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothWeightedTaylorIndex_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact rothWeightedTaylorIndex_add_lower r z _ _ t (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem rothWeightedTaylorIndex_prod_lower {d : ℕ} {ι : Type*}
    (r : Fin d → ℕ) (z : Fin d → ℚ) (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℚ) (t : ι → ℝ)
    (hf : ∀ i ∈ s, (t i : WithTop ℝ) ≤ rothWeightedTaylorIndex r z (f i)) :
    ((∑ i ∈ s, t i : ℝ) : WithTop ℝ) ≤ rothWeightedTaylorIndex r z (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact rothWeightedTaylorIndex_nonneg r z 1
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact rothWeightedTaylorIndex_mul_lower r z _ _ _ _ (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem rothDerivativeDeterminant_index_lower {d ell : ℕ}
    (r : Fin d → ℕ) (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ)
    (alpha : Fin ell → Fin ell → (Fin d →₀ ℕ)) (t rho : ℝ) (s : ℕ)
    (hP : (t : WithTop ℝ) ≤ rothWeightedTaylorIndex r z P)
    (hloss : ∀ i j, rothTaylorWeight r (alpha i j) ≤ rho + (j.val : ℝ) / s) :
    ((∑ j : Fin ell, max 0 (t - rho - (j.val : ℝ) / s) : ℝ) : WithTop ℝ) ≤
      rothWeightedTaylorIndex r z
        (Matrix.det (fun i j : Fin ell => rothDividedDerivative (alpha i j) P)) := by
  classical
  have hentry (i j : Fin ell) :
      ((max 0 (t - rho - (j.val : ℝ) / s) : ℝ) : WithTop ℝ) ≤
        rothWeightedTaylorIndex r z (rothDividedDerivative (alpha i j) P) := by
    apply le_trans (b := ((max 0 (t - rothTaylorWeight r (alpha i j)) : ℝ) : WithTop ℝ))
    · exact_mod_cast (max_le_max (le_refl (0 : ℝ)) (by linarith [hloss i j]))
    · exact rothWeightedTaylorIndex_derivative_lower r z P _ t hP
  rw [Matrix.det_apply]
  apply rothWeightedTaylorIndex_sum_lower
  intro p _
  have hp := rothWeightedTaylorIndex_prod_lower r z Finset.univ
    (fun i => rothDividedDerivative (alpha (p i) i) P)
    (fun j => max 0 (t - rho - (j.val : ℝ) / s)) (fun j _ => hentry (p j) j)
  rcases Int.units_eq_one_or p.sign with hs | hs
  · simpa [hs] using hp
  · simpa [hs, rothWeightedTaylorIndex, rothTaylorPolynomial] using hp

end JSP000334

namespace JSP000334

noncomputable def rothFlattenRational {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) : MvPolynomial (Fin (d + 1)) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) ((rothLastVariableEquiv d).symm P)

theorem rothFlattenRational_coeff {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (n : ℕ) (b : Fin d →₀ ℕ) :
    (rothFlattenRational P).coeff (rothLastExponent n b) = (((P.coeff n).coeff b : ℤ) : ℚ) := by
  rw [rothFlattenRational, MvPolynomial.coeff_map]
  have he := rothLastVariableEquiv_coeff ((rothLastVariableEquiv d).symm P) n b
  rw [AlgEquiv.apply_symm_apply] at he
  exact congrArg (fun x : ℤ => (x : ℚ)) he.symm

theorem rothLastExponent_add {d : ℕ} (n j : ℕ) (b a : Fin d →₀ ℕ) :
    rothLastExponent n b + rothLastExponent j a = rothLastExponent (n + j) (b + a) := by
  apply Finsupp.ext
  intro k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [Finsupp.add_apply, rothLastExponent_last]
  · simp [Finsupp.add_apply, rothLastExponent_castSucc]

theorem rothLastExponent_surjective {d : ℕ} (c : Fin (d + 1) →₀ ℕ) :
    ∃ n b, rothLastExponent n b = c := by
  let b : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun k => c k.castSucc)
  refine ⟨c (Fin.last d), b, ?_⟩
  apply Finsupp.ext
  intro k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [rothLastExponent_last]
  · simp [rothLastExponent_castSucc, b]

theorem rothFlattenRational_mixed {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (a : Fin d →₀ ℕ) (j : ℕ) :
    rothFlattenRational (rothIntegerMixedDividedDerivative a j P) =
      rothDividedDerivative (rothLastExponent j a) (rothFlattenRational P) := by
  classical
  apply MvPolynomial.ext
  intro c
  obtain ⟨n, b, rfl⟩ := rothLastExponent_surjective c
  rw [rothFlattenRational_coeff, rothIntegerMixedDividedDerivative_coeff,
    rothDividedDerivative_coeff, rothLastExponent_add, rothFlattenRational_coeff]
  rw [Fin.prod_univ_castSucc]
  simp only [rothLastExponent_castSucc, rothLastExponent_last, Int.cast_mul,
    Int.cast_prod, Int.cast_natCast]
  ring

end JSP000334

namespace JSP000334

theorem rothLastExponent_weight {d : ℕ} (r : Fin d → ℕ) (s j : ℕ) (a : Fin d →₀ ℕ) :
    rothTaylorWeight (Fin.snoc r s) (rothLastExponent j a) =
      rothTaylorWeight r a + (j : ℝ) / s := by
  simp [rothTaylorWeight, Fin.sum_univ_castSucc,
    rothLastExponent_last, rothLastExponent_castSucc]

theorem rothTaylorWeight_le_separation {d : ℕ}
    (r : Fin d → ℕ) (s R : ℕ) (rho : ℝ) (a : Fin d →₀ ℕ)
    (hR : 0 < R) (hr : ∀ k, R ≤ r k)
    (ha : (∑ k : Fin d, a k) ≤ s) (hs : (s : ℝ) ≤ rho * R) :
    rothTaylorWeight r a ≤ rho := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  calc
    rothTaylorWeight r a ≤ ∑ k : Fin d, (a k : ℝ) / R := by
      apply Finset.sum_le_sum
      intro k _
      exact div_le_div_of_nonneg_left (by positivity) hR' (by exact_mod_cast hr k)
    _ = (∑ k : Fin d, (a k : ℝ)) / R := (Finset.sum_div _ _ _).symm
    _ ≤ rho := by
      apply (div_le_iff₀ hR').mpr
      exact (show (∑ k : Fin d, (a k : ℝ)) ≤ s by exact_mod_cast ha).trans hs

noncomputable def rothNestedWeightedTaylorIndex {d : ℕ} (r : Fin (d + 1) → ℕ)
    (z : Fin (d + 1) → ℚ) (P : Polynomial (MvPolynomial (Fin d) ℤ)) : WithTop ℝ :=
  rothWeightedTaylorIndex r z (rothFlattenRational P)

theorem rothMixedWronskian_index_lower {d ell : ℕ}
    (r : Fin d → ℕ) (s R : ℕ) (z : Fin (d + 1) → ℚ)
    (P : Polynomial (MvPolynomial (Fin d) ℤ))
    (alpha : Fin ell → (Fin d →₀ ℕ)) (t rho : ℝ)
    (hP : (t : WithTop ℝ) ≤ rothNestedWeightedTaylorIndex (Fin.snoc r s) z P)
    (hR : 0 < R) (hr : ∀ k, R ≤ r k) (hs : (s : ℝ) ≤ rho * R)
    (he : ell ≤ s + 1) (ha : ∀ i, (∑ k : Fin d, alpha i k) ≤ i.val) :
    ((∑ j : Fin ell, max 0 (t - rho - (j.val : ℝ) / s) : ℝ) : WithTop ℝ) ≤
      rothNestedWeightedTaylorIndex (Fin.snoc r s) z
        (Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)) := by
  classical
  let f : Polynomial (MvPolynomial (Fin d) ℤ) →+* MvPolynomial (Fin (d + 1)) ℚ :=
    (MvPolynomial.map (Int.castRingHom ℚ)).comp (rothLastVariableEquiv d).symm.toRingHom
  have hmap := f.map_det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)
  change rothFlattenRational (Matrix.det
    (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)) =
    Matrix.det (fun i j : Fin ell => rothFlattenRational
      (rothIntegerMixedDividedDerivative (alpha i) j.val P)) at hmap
  simp_rw [rothFlattenRational_mixed] at hmap
  change _ ≤ rothWeightedTaylorIndex _ _ _
  rw [hmap]
  apply rothDerivativeDeterminant_index_lower _ _ _ _ t rho s hP
  intro i j
  rw [rothLastExponent_weight]
  apply add_le_add_right
  apply rothTaylorWeight_le_separation r s R rho (alpha i) hR hr ?_ hs
  have hi := i.isLt
  exact (ha i).trans (by omega)

end JSP000334

namespace JSP000334

theorem roth_exists_integral_separated_wronskian_all
    (d : ℕ) (P : Polynomial (MvPolynomial (Fin d) ℤ)) (hP : P ≠ 0) :
    ∃ (ell : ℕ) (alpha : Fin ell → (Fin d →₀ ℕ))
        (u : Polynomial ℤ) (v : MvPolynomial (Fin d) ℤ),
      1 ≤ ell ∧ ell ≤ P.natDegree + 1 ∧
      (∀ i, (∑ k : Fin d, alpha i k) ≤ i.val) ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) =
        Polynomial.C v * u.map MvPolynomial.C ∧
      u ≠ 0 ∧ v ≠ 0 ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) ≠ 0 := by
  cases d with
  | succ d => exact roth_exists_integral_separated_wronskian (d + 1) (by omega) P hP
  | zero =>
    let e := MvPolynomial.isEmptyRingEquiv ℤ (Fin 0)
    let u := P.map e.toRingHom
    have hmap : u.map MvPolynomial.C = P := by
      apply Polynomial.ext
      intro n
      simp only [u, Polynomial.coeff_map, RingEquiv.toRingHom_eq_coe]
      exact e.symm_apply_apply (P.coeff n)
    have hm : rothIntegerMixedDividedDerivative (0 : Fin 0 →₀ ℕ) 0 P = P := by
      apply Polynomial.ext
      intro n
      apply MvPolynomial.ext
      intro b
      rw [rothIntegerMixedDividedDerivative_coeff]
      simp
    have hd : Matrix.det (fun i j : Fin 1 =>
        rothIntegerMixedDividedDerivative (0 : Fin 0 →₀ ℕ) j.val P) = P := by
      simpa [Matrix.det_unique] using hm
    refine ⟨1, fun _ => 0, u, 1, by omega, by omega, ?_, ?_, ?_, one_ne_zero, ?_⟩
    · intro i; simp
    · rw [hd, hmap, Polynomial.C_1, one_mul]
    · intro hz
      rw [hz, Polynomial.map_zero] at hmap
      exact hP hmap.symm
    · rw [hd]; exact hP

end JSP000334

namespace JSP000334

theorem rothTaylorPolynomial_inverse {d : ℕ} (z : Fin d → ℚ)
    (P : MvPolynomial (Fin d) ℚ) :
    rothTaylorPolynomial (fun k => -z k) (rothTaylorPolynomial z P) = P := by
  let f : MvPolynomial (Fin d) ℚ →ₐ[ℚ] MvPolynomial (Fin d) ℚ := MvPolynomial.aeval (fun k => MvPolynomial.C (-z k) + MvPolynomial.X k)
  let g : MvPolynomial (Fin d) ℚ →ₐ[ℚ] MvPolynomial (Fin d) ℚ := MvPolynomial.aeval (fun k => MvPolynomial.C (z k) + MvPolynomial.X k)
  have he : f.comp g = AlgHom.id ℚ (MvPolynomial (Fin d) ℚ) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [f, g, AlgHom.comp_apply, MvPolynomial.algebraMap_eq]
  exact congrArg (fun h : MvPolynomial (Fin d) ℚ →ₐ[ℚ] MvPolynomial (Fin d) ℚ => h P) he

theorem rothWeightedTaylorIndex_finite {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ) (hP : P ≠ 0) :
    ∃ t : ℝ, rothWeightedTaylorIndex r z P = (t : WithTop ℝ) := by
  classical
  have ht : rothTaylorPolynomial z P ≠ 0 := by
    intro hz
    have he := rothTaylorPolynomial_inverse z P
    rw [hz] at he
    simp only [rothTaylorPolynomial, map_zero] at he
    exact hP he.symm
  obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_inf (rothTaylorPolynomial z P).support
    (MvPolynomial.support_nonempty.mpr ht) (fun b => (rothTaylorWeight r b : WithTop ℝ))
  exact ⟨rothTaylorWeight r b, he⟩

theorem rothInductionOmega_le_t (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : 0 < t) (ht' : t < 1 / 12) :
    rothInductionOmega m t ≤ t := by
  have hbase : 0 ≤ t / 12 := by positivity
  have hbase' : t / 12 ≤ 1 := by linarith
  have hpow : (t / 12) ^ (2 ^ (m - 1)) ≤ t / 12 := by
    simpa using pow_le_pow_of_le_one hbase hbase' (Nat.one_le_two_pow (n := m - 1))
  have htwo : (2 : ℝ) ≤ 2 ^ m := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  have hfactor : 24 / (2 : ℝ) ^ m ≤ 12 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  unfold rothInductionOmega
  exact (mul_le_mul hfactor hpow (by positivity) (by norm_num)).trans_eq (by ring)

theorem rothDegrees_antitone {d : ℕ} (r : Fin (d + 1) → ℕ) (rho : ℝ)
    (hrho : rho ≤ 1)
    (hsep : ∀ i : Fin d, (r i.succ : ℝ) ≤ rho * (r i.castSucc : ℝ)) :
    Antitone r := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  have hi := hsep i
  have hr : (0 : ℝ) ≤ r i.castSucc := by positivity
  have hh : (r i.succ : ℝ) ≤ r i.castSucc := by nlinarith
  exact_mod_cast hh

end JSP000334

namespace JSP000334

theorem roth_exists_quantitative_separated_wronskian
    (d : ℕ) (r : Fin (d + 1) → ℕ) (p q : Fin (d + 1) → ℤ)
    (t C : ℝ) (ht : 0 < t) (ht' : t < 1 / 12) (hC : 0 < C) (hC' : C ≤ 1)
    (hr : ∀ k, 0 < r k) (hq : ∀ k, q k ≠ 0)
    (hred : ∀ k, Int.gcd (p k) (q k) = 1)
    (hsep : ∀ i : Fin d, (r i.succ : ℝ) ≤ rothInductionOmega (d + 1) t * (r i.castSucc : ℝ))
    (hgrowth : ∀ k : Fin (d + 1), 1 ≤ k.val →
      |(q 0 : ℝ)| ^ ((r 0 : ℝ) * C) ≤ |(q k : ℝ)| ^ (r k : ℝ))
    (hden : ∀ k, (2 : ℝ) ^ (3 * (d + 1)) ≤ |(q k : ℝ)| ^ (rothInductionOmega (d + 1) t * C))
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (hP : P ≠ 0)
    (hb : rothNestedSupportBound P (fun k => r k.castSucc) (r (Fin.last d)))
    (hheight : (rothNestedIntegerHeight P : ℝ) ≤
      |(q 0 : ℝ)| ^ (rothInductionOmega (d + 1) t * r 0 * C)) :
    ∃ (ell : ℕ) (alpha : Fin ell → (Fin d →₀ ℕ))
        (u : Polynomial ℤ) (v : MvPolynomial (Fin d) ℤ) (I : ℝ),
      1 ≤ ell ∧ ell ≤ r (Fin.last d) + 1 ∧
      (∀ i, (∑ k : Fin d, alpha i k) ≤ i.val) ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) =
        Polynomial.C v * u.map MvPolynomial.C ∧
      u ≠ 0 ∧ v ≠ 0 ∧
      Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P) ≠ 0 ∧
      rothNestedSupportBound (Polynomial.C v * u.map MvPolynomial.C)
        (fun k => ell * r k.castSucc) (ell * r (Fin.last d)) ∧
      u.natDegree ≤ ell * r (Fin.last d) ∧ (∀ k, v.degreeOf k ≤ ell * r k.castSucc) ∧
      rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) ≤
        ((r (Fin.last d) + 1) * ∏ k : Fin d, (r k.castSucc + 1)) ^ ell * ell.factorial *
          2 ^ (ell * (r (Fin.last d) + ∑ k : Fin d, r k.castSucc)) * rothNestedIntegerHeight P ^ ell ∧
      rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) ≤
        2 ^ (3 * (d + 1) * r 0 * ell) * rothNestedIntegerHeight P ^ ell ∧
      rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) =
        rothIntegerHeight v * rothUnivariateIntegerHeight u ∧
      rothIntegerHeight v ≤ rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) ∧
      rothUnivariateIntegerHeight u ≤ rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) ∧
      rothNestedWeightedTaylorIndex r (fun k => (p k : ℚ) / (q k : ℚ)) P = (I : WithTop ℝ) ∧
      ((∑ j : Fin ell, max 0 (I - rothInductionOmega (d + 1) t - (j.val : ℝ) / r (Fin.last d)) : ℝ) : WithTop ℝ) ≤
        rothNestedWeightedTaylorIndex r (fun k => (p k : ℚ) / (q k : ℚ))
          (Polynomial.C v * u.map MvPolynomial.C) ∧
      (rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C) : ℝ) ≤
        |(q 0 : ℝ)| ^ (2 * rothInductionOmega (d + 1) t * r 0 * C * ell) ∧
      (rothUnivariateIntegerHeight u : ℝ) ≤
        |(q (Fin.last d) : ℝ)| ^ (2 * rothInductionOmega (d + 1) t * r (Fin.last d) * ell) := by
  classical
  let rho := rothInductionOmega (d + 1) t
  let z : Fin (d + 1) → ℚ := fun k => (p k : ℚ) / (q k : ℚ)
  have hrho : 0 < rho := rothInductionOmega_pos _ _ ht
  have hrho' : rho ≤ 1 := (rothInductionOmega_le_t _ (by omega) t ht ht').trans (by linarith)
  have hanti := rothDegrees_antitone r rho hrho' hsep
  obtain ⟨ell, alpha, u, v, hl, he, ha, hw, hu, hv, hn⟩ :=
    roth_exists_integral_separated_wronskian_all d P hP
  have hdeg : P.natDegree ≤ r (Fin.last d) := by
    obtain ⟨b, hb'⟩ := MvPolynomial.exists_coeff_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP)
    exact (hb P.natDegree b hb').1
  have hell : ell ≤ r (Fin.last d) + 1 := he.trans (Nat.add_le_add_right hdeg 1)
  have hsupport := rothMixedWronskian_support P _ _ hb alpha
  rw [hw] at hsupport
  obtain ⟨hdu, hdv⟩ := rothSeparatedInteger_degree_bounds v u hv hu _ _ hsupport
  have hgeneral := rothMixedWronskian_height_le P _ _ hb alpha
  rw [hw] at hgeneral
  have hsimp := rothMixedWronskian_height_le_ordered P _ _ (r 0) hb
    (hanti (Fin.zero_le _)) (fun k => hanti (Fin.zero_le _)) hell alpha
  rw [hw] at hsimp
  obtain ⟨hHv, hHu⟩ := rothSeparatedIntegerHeight_bounds v u hv hu
  have hflat : rothFlattenRational P ≠ 0 := by
    intro hz
    have hi := MvPolynomial.map_injective (σ := Fin (d + 1)) (f := Int.castRingHom ℚ) Int.cast_injective
    have hh : (rothLastVariableEquiv d).symm P = 0 := hi (by simpa [rothFlattenRational] using hz)
    exact hP ((rothLastVariableEquiv d).symm.injective (by simpa using hh))
  obtain ⟨I, hI⟩ := rothWeightedTaylorIndex_finite r z (rothFlattenRational P) hflat
  have hsnoc : Fin.snoc (fun k : Fin d => r k.castSucc) (r (Fin.last d)) = r := by
    funext k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp
  have hindex : ((∑ j : Fin ell, max 0 (I - rho - (j.val : ℝ) / r (Fin.last d)) : ℝ) : WithTop ℝ) ≤
      rothNestedWeightedTaylorIndex r z
        (Matrix.det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)) := by
    cases d with
    | zero =>
      let f : Polynomial (MvPolynomial (Fin 0) ℤ) →+* MvPolynomial (Fin 1) ℚ :=
        (MvPolynomial.map (Int.castRingHom ℚ)).comp (rothLastVariableEquiv 0).symm.toRingHom
      have hm := f.map_det (fun i j : Fin ell => rothIntegerMixedDividedDerivative (alpha i) j.val P)
      change rothFlattenRational (Matrix.det _) = Matrix.det
        (fun i j : Fin ell => rothFlattenRational (rothIntegerMixedDividedDerivative (alpha i) j.val P)) at hm
      simp_rw [rothFlattenRational_mixed] at hm
      change _ ≤ rothWeightedTaylorIndex _ _ _
      rw [hm]
      apply rothDerivativeDeterminant_index_lower _ _ _ _ I rho (r (Fin.last 0)) hI.ge
      intro i j
      rw [← hsnoc, rothLastExponent_weight]
      simp only [rothTaylorWeight, Finset.univ_eq_empty, Finset.sum_empty, zero_add, Fin.snoc_last]
      linarith
    | succ d =>
      have hmin : ∀ k : Fin (d + 1), r (Fin.last d).castSucc ≤ r k.castSucc := by
        intro k
        exact hanti (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last k))
      have hs := hsep (Fin.last d)
      simp only [Fin.succ_last] at hs
      have hh := rothMixedWronskian_index_lower (fun k : Fin (d + 1) => r k.castSucc)
        (r (Fin.last (d + 1))) (r (Fin.last d).castSucc) z P alpha I rho
        (by simpa only [hsnoc] using hI.ge) (hr _) hmin hs hell ha
      simpa only [hsnoc] using hh
  rw [hw] at hindex
  have hQ : ∀ k, 0 < |(q k : ℝ)| := by
    intro k
    exact abs_pos.mpr (by exact_mod_cast hq k)
  have hWabs := rothWronskian_height_absorption (d + 1) (r 0) ell
    (rothNestedIntegerHeight P) (rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C))
    |(q 0 : ℝ)| rho C (hQ 0) (hden 0) hheight hsimp
  have hg : |(q 0 : ℝ)| ^ ((r 0 : ℝ) * C) ≤ |(q (Fin.last d) : ℝ)| ^ (r (Fin.last d) : ℝ) := by
    cases d with
    | zero =>
      have hlast : Fin.last 0 = (0 : Fin 1) := Fin.ext rfl
      rw [hlast]
      have hQ1 : (1 : ℝ) ≤ |(q 0 : ℝ)| := by
        exact_mod_cast (Int.one_le_abs (hq 0))
      apply Real.rpow_le_rpow_of_exponent_le hQ1
      nlinarith [show (0 : ℝ) ≤ r 0 by positivity]
    | succ d => exact hgrowth (Fin.last (d + 1)) (by simp)
  have hUabs := rothSeparated_height_absorption (r 0) (r (Fin.last d)) ell
    (rothUnivariateIntegerHeight u) (rothNestedIntegerHeight (Polynomial.C v * u.map MvPolynomial.C))
    |(q 0 : ℝ)| |(q (Fin.last d) : ℝ)| rho C (hQ 0) (hQ _) hrho.le hg hWabs hHu
  exact ⟨ell, alpha, u, v, I, hl, hell, ha, hw, hu, hv, hn, hsupport, hdu, hdv,
    hgeneral, hsimp, rothNestedIntegerHeight_separated v u, hHv, hHu, hI, hindex, hWabs, hUabs⟩

end JSP000334

namespace JSP000334

theorem rothLastVariableEquiv_supportBound {d : ℕ}
    (P : MvPolynomial (Fin (d + 1)) ℤ) (r : Fin (d + 1) → ℕ)
    (hP : ∀ c ∈ P.support, ∀ k, c k ≤ r k) :
    rothNestedSupportBound (rothLastVariableEquiv d P)
      (fun k => r k.castSucc) (r (Fin.last d)) := by
  intro n b hn
  rw [rothLastVariableEquiv_coeff] at hn
  have hc := hP (rothLastExponent n b) (MvPolynomial.mem_support_iff.mpr hn)
  constructor
  · simpa only [rothLastExponent_last] using hc (Fin.last d)
  · intro k
    simpa only [rothLastExponent_castSucc] using hc k.castSucc

theorem rothLastVariableEquiv_height {d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℤ) :
    rothNestedIntegerHeight (rothLastVariableEquiv d P) = rothIntegerHeight P := by
  classical
  apply Nat.le_antisymm
  · apply (rothNestedIntegerHeight_le_iff _ _).mpr
    intro n b
    rw [rothLastVariableEquiv_coeff]
    exact rothIntegerHeight_coeff_le _ _
  · apply Finset.sup_le
    intro c _
    obtain ⟨n, b, rfl⟩ := rothLastExponent_surjective c
    rw [← rothLastVariableEquiv_coeff P n b]
    exact rothNestedIntegerHeight_coeff_le _ _ _

end JSP000334

namespace JSP000334

private noncomputable def rothMinimumWeightPart {d : ℕ} (r : Fin d → ℕ)
    (t : ℝ) (P : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin d) ℚ :=
  Finsupp.filter (fun b => rothTaylorWeight r b = t) P

private theorem rothMinimumWeightPart_coeff {d : ℕ} (r : Fin d → ℕ)
    (t : ℝ) (P : MvPolynomial (Fin d) ℚ) (b : Fin d →₀ ℕ) :
    (rothMinimumWeightPart r t P).coeff b =
      if rothTaylorWeight r b = t then P.coeff b else 0 := by
  classical
  exact Finsupp.filter_apply _ _ _

private theorem rothMinimumWeightPart_ne_zero {d : ℕ} (r : Fin d → ℕ)
    (P : MvPolynomial (Fin d) ℚ) (a : Fin d →₀ ℕ) (ha : a ∈ P.support) :
    rothMinimumWeightPart r (rothTaylorWeight r a) P ≠ 0 := by
  intro hz
  have he := congrArg (fun Q : MvPolynomial (Fin d) ℚ => Q.coeff a) hz
  change (rothMinimumWeightPart r (rothTaylorWeight r a) P).coeff a = 0 at he
  rw [rothMinimumWeightPart_coeff, if_pos rfl] at he
  exact (MvPolynomial.mem_support_iff.mp ha) he

private theorem rothMinimumWeightPart_product {d : ℕ} (r : Fin d → ℕ)
    (P Q : MvPolynomial (Fin d) ℚ) (a b : ℝ)
    (hP : ∀ c ∈ P.support, a ≤ rothTaylorWeight r c)
    (hQ : ∀ c ∈ Q.support, b ≤ rothTaylorWeight r c)
    (c : Fin d →₀ ℕ) (hc : rothTaylorWeight r c = a + b) :
    ((rothMinimumWeightPart r a P) * (rothMinimumWeightPart r b Q)).coeff c = (P * Q).coeff c := by
  classical
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [rothMinimumWeightPart_coeff, rothMinimumWeightPart_coeff]
  by_cases hp : P.coeff u.1 = 0
  · simp [hp]
  by_cases hq : Q.coeff u.2 = 0
  · simp [hq]
  have h1 := hP u.1 (MvPolynomial.mem_support_iff.mpr hp)
  have h2 := hQ u.2 (MvPolynomial.mem_support_iff.mpr hq)
  have he : rothTaylorWeight r u.1 + rothTaylorWeight r u.2 = a + b := by
    rw [← rothTaylorWeight_add, Finset.mem_antidiagonal.mp hu, hc]
  have hp' : rothTaylorWeight r u.1 = a := by linarith
  have hq' : rothTaylorWeight r u.2 = b := by linarith
  simp [hp', hq']

theorem rothWeightedTaylorIndex_mul {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P Q : MvPolynomial (Fin d) ℚ) :
    rothWeightedTaylorIndex r z (P * Q) =
      rothWeightedTaylorIndex r z P + rothWeightedTaylorIndex r z Q := by
  classical
  by_cases hP : P = 0
  · simp [hP, rothWeightedTaylorIndex_zero]
  by_cases hQ : Q = 0
  · simp [hQ, rothWeightedTaylorIndex_zero]
  have hp : rothTaylorPolynomial z P ≠ 0 := by
    intro hz
    have he := rothTaylorPolynomial_inverse z P
    rw [hz] at he
    simp only [rothTaylorPolynomial, map_zero] at he
    exact hP he.symm
  have hq : rothTaylorPolynomial z Q ≠ 0 := by
    intro hz
    have he := rothTaylorPolynomial_inverse z Q
    rw [hz] at he
    simp only [rothTaylorPolynomial, map_zero] at he
    exact hQ he.symm
  obtain ⟨a, ha, hea⟩ := Finset.exists_mem_eq_inf (rothTaylorPolynomial z P).support
    (MvPolynomial.support_nonempty.mpr hp) (fun b => (rothTaylorWeight r b : WithTop ℝ))
  obtain ⟨b, hb, heb⟩ := Finset.exists_mem_eq_inf (rothTaylorPolynomial z Q).support
    (MvPolynomial.support_nonempty.mpr hq) (fun b => (rothTaylorWeight r b : WithTop ℝ))
  change rothWeightedTaylorIndex r z P = _ at hea
  change rothWeightedTaylorIndex r z Q = _ at heb
  have hap := (rothWeightedTaylorIndex_lower_iff _ _ _ _).mp hea.ge
  have hbq := (rothWeightedTaylorIndex_lower_iff _ _ _ _).mp heb.ge
  have hprod : rothMinimumWeightPart r (rothTaylorWeight r a) (rothTaylorPolynomial z P) *
      rothMinimumWeightPart r (rothTaylorWeight r b) (rothTaylorPolynomial z Q) ≠ 0 :=
    mul_ne_zero (rothMinimumWeightPart_ne_zero r _ a ha) (rothMinimumWeightPart_ne_zero r _ b hb)
  obtain ⟨c, hc⟩ := MvPolynomial.exists_coeff_ne_zero hprod
  have hmem := MvPolynomial.support_mul _ _ (MvPolynomial.mem_support_iff.mpr hc)
  obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_add.mp hmem
  have hw (t : ℝ) (F : MvPolynomial (Fin d) ℚ) (w : Fin d →₀ ℕ)
      (hw : w ∈ (rothMinimumWeightPart r t F).support) : rothTaylorWeight r w = t := by
    rw [MvPolynomial.mem_support_iff, rothMinimumWeightPart_coeff] at hw
    by_contra hn
    simp [hn] at hw
  have hwc : rothTaylorWeight r c = rothTaylorWeight r a + rothTaylorWeight r b := by
    rw [← he, rothTaylorWeight_add, hw _ _ _ hu, hw _ _ _ hv]
  rw [rothMinimumWeightPart_product r _ _ _ _ hap hbq c hwc] at hc
  have hc' : c ∈ (rothTaylorPolynomial z (P * Q)).support := by
    simpa only [rothTaylorPolynomial, map_mul, MvPolynomial.mem_support_iff] using hc
  apply le_antisymm
  · have hh := Finset.inf_le (f := fun b => (rothTaylorWeight r b : WithTop ℝ)) hc'
    change rothWeightedTaylorIndex r z (P * Q) ≤ _ at hh
    simpa only [hea, heb, hwc, WithTop.coe_add] using hh
  · rw [hea, heb, ← WithTop.coe_add]
    exact rothWeightedTaylorIndex_mul_lower r z P Q _ _ hea.ge heb.ge

end JSP000334

namespace JSP000334
open Polynomial

theorem rothPrimitive_integer_dvd_of_rational_dvd
    (A B : Polynomial ℤ) (hA : A.IsPrimitive) (hB : B ≠ 0)
    (hd : A.map (Int.castRingHom ℚ) ∣ B.map (Int.castRingHom ℚ)) : A ∣ B := by
  obtain ⟨Q, hQ⟩ := hd
  have hBQ : B.map (Int.castRingHom ℚ) ≠ 0 := by
    exact fun h => hB (Polynomial.map_injective _ Int.cast_injective (by simpa using h))
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ; exact hBQ hQ
  obtain ⟨U, c, hU, hc, he⟩ := roth_exists_primitive_integer_factor Q hQ0
  have hprod : Polynomial.C c * (A * U).map (Int.castRingHom ℚ) =
      B.map (Int.castRingHom ℚ) := by
    rw [hQ, he, Polynomial.map_mul]
    ring
  obtain ⟨z, hz⟩ := roth_primitive_rational_scalar_integral (A * U) B (hA.mul hU) c hprod
  refine ⟨Polynomial.C z * U, ?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
  rw [← hprod, ← hz]
  simp only [Polynomial.map_mul, Int.coe_castRingHom]
  ring

theorem rothReducedLinear_isPrimitive (p q : ℤ) (hred : Int.gcd p q = 1) :
    (Polynomial.C q * Polynomial.X - Polynomial.C p).IsPrimitive := by
  intro a ha
  have hh := (Polynomial.C_dvd_iff_dvd_coeff a _).mp ha
  have hq : a ∣ q := by
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      mul_one, Polynomial.coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0), sub_zero] using hh 1
  have hp : a ∣ p := by simpa using (dvd_neg.mp (show a ∣ -p by simpa using hh 0))
  exact (Int.isCoprime_iff_gcd_eq_one.mpr hred).isUnit_of_dvd' hp hq

theorem rothReducedLinear_pow_isPrimitive (p q : ℤ) (hred : Int.gcd p q = 1) (k : ℕ) :
    ((Polynomial.C q * Polynomial.X - Polynomial.C p) ^ k).IsPrimitive := by
  induction k with
  | zero => simpa using (Polynomial.isPrimitive_one : (1 : Polynomial ℤ).IsPrimitive)
  | succ k ih => simpa [pow_succ] using ih.mul (rothReducedLinear_isPrimitive p q hred)

theorem rothRationalMultiplicity_denominator_dvd
    (f : Polynomial ℤ) (hf : f ≠ 0) (p q : ℤ) (hq : q ≠ 0)
    (hred : Int.gcd p q = 1) (k : ℕ)
    (hd : (Polynomial.X - Polynomial.C ((p : ℚ) / (q : ℚ))) ^ k ∣
      f.map (Int.castRingHom ℚ)) : q ^ k ∣ f.leadingCoeff := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have he : (Polynomial.C q * Polynomial.X - Polynomial.C p).map (Int.castRingHom ℚ) =
      Polynomial.C (q : ℚ) * (Polynomial.X - Polynomial.C ((p : ℚ) / (q : ℚ))) := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Int.coe_castRingHom, mul_sub, ← Polynomial.C_mul]
    congr 1
    field_simp
  have hdQ : ((Polynomial.C q * Polynomial.X - Polynomial.C p) ^ k).map
      (Int.castRingHom ℚ) ∣ f.map (Int.castRingHom ℚ) := by
    rw [Polynomial.map_pow, he, mul_pow]
    obtain ⟨g, hg⟩ := hd
    refine ⟨Polynomial.C (((q : ℚ) ^ k)⁻¹) * g, ?_⟩
    have hc : Polynomial.C (q : ℚ) ^ k * Polynomial.C (((q : ℚ) ^ k)⁻¹) =
        (1 : Polynomial ℚ) := by
      rw [← Polynomial.C_pow, ← Polynomial.C_mul,
        mul_inv_cancel₀ (pow_ne_zero k hqQ), Polynomial.C_1]
    rw [hg]
    calc
      (Polynomial.X - Polynomial.C ((p : ℚ) / (q : ℚ))) ^ k * g =
          (Polynomial.C (q : ℚ) ^ k * Polynomial.C (((q : ℚ) ^ k)⁻¹)) *
          ((Polynomial.X - Polynomial.C ((p : ℚ) / (q : ℚ))) ^ k * g) := by
            rw [hc, one_mul]
      _ = _ := by ring
  have hdZ := rothPrimitive_integer_dvd_of_rational_dvd _ f
    (rothReducedLinear_pow_isPrimitive p q hred k) hf hdQ
  have hlead : (Polynomial.C q * Polynomial.X - Polynomial.C p).leadingCoeff = q := by
    rw [Polynomial.leadingCoeff_sub_of_degree_lt]
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, mul_one]
    · rw [Polynomial.degree_C_mul_X hq]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by decide : (0 : WithBot ℕ) < 1)
  have h := Polynomial.leadingCoeff_dvd_leadingCoeff hdZ
  rw [Polynomial.leadingCoeff_pow, hlead] at h
  exact h

theorem rothRationalMultiplicity_height_le
    (f : Polynomial ℤ) (hf : f ≠ 0) (p q : ℤ) (hq : q ≠ 0)
    (hred : Int.gcd p q = 1) :
    |(q : ℝ)| ^ (f.map (Int.castRingHom ℚ)).rootMultiplicity ((p : ℚ) / (q : ℚ)) ≤
      (rothUnivariateIntegerHeight f : ℝ) := by
  have hd := rothRationalMultiplicity_denominator_dvd f hf p q hq hred _
    (Polynomial.pow_rootMultiplicity_dvd (f.map (Int.castRingHom ℚ)) ((p : ℚ) / (q : ℚ)))
  have hn := Int.natAbs_le_of_dvd_ne_zero hd (Polynomial.leadingCoeff_ne_zero.mpr hf)
  have hh := le_trans hn (rothUnivariateIntegerHeight_coeff_le f f.natDegree)
  have hhR : ((q ^ (f.map (Int.castRingHom ℚ)).rootMultiplicity
      ((p : ℚ) / (q : ℚ))).natAbs : ℝ) ≤ (rothUnivariateIntegerHeight f : ℝ) := by
    exact_mod_cast hh
  simpa only [Int.natAbs_pow, Nat.cast_pow, Int.cast_natAbs, Int.cast_abs] using hhR

theorem rothRationalMultiplicity_hasse_ne_zero
    (f : Polynomial ℤ) (hf : f ≠ 0) (a : ℚ) :
    (Polynomial.hasseDeriv ((f.map (Int.castRingHom ℚ)).rootMultiplicity a)
      (f.map (Int.castRingHom ℚ))).eval a ≠ 0 := by
  have hfQ : f.map (Int.castRingHom ℚ) ≠ 0 := by
    exact fun h => hf (Polynomial.map_injective _ Int.cast_injective (by simpa using h))
  have ht : Polynomial.taylor a (f.map (Int.castRingHom ℚ)) ≠ 0 := by
    intro h
    apply hfQ
    exact Polynomial.taylor_injective a (by simpa using h)
  have hc := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr ht
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  rw [← Polynomial.taylor_coeff]
  exact hc

theorem rothRationalDenominator_hasse_witness
    (f : Polynomial ℤ) (hf : f ≠ 0) (p q : ℤ) (hq : q ≠ 0)
    (hred : Int.gcd p q = 1) (hq1 : 1 < |(q : ℝ)|) (r : ℕ) (hr : 0 < r)
    (A : ℝ) (hH : (rothUnivariateIntegerHeight f : ℝ) ≤
      Real.rpow |(q : ℝ)| (A * (r : ℝ))) :
    ∃ k : ℕ, (k : ℝ) / (r : ℝ) ≤ A ∧
      (Polynomial.hasseDeriv k (f.map (Int.castRingHom ℚ))).eval
        ((p : ℚ) / (q : ℚ)) ≠ 0 := by
  let k := (f.map (Int.castRingHom ℚ)).rootMultiplicity ((p : ℚ) / (q : ℚ))
  refine ⟨k, ?_, rothRationalMultiplicity_hasse_ne_zero f hf _⟩
  have hh : Real.rpow |(q : ℝ)| (k : ℝ) ≤ Real.rpow |(q : ℝ)| (A * (r : ℝ)) := by
    change |(q : ℝ)| ^ (k : ℝ) ≤ |(q : ℝ)| ^ (A * (r : ℝ))
    rw [Real.rpow_natCast]
    exact le_trans (rothRationalMultiplicity_height_le f hf p q hq hred) hH
  have hk : (k : ℝ) ≤ A * (r : ℝ) := (Real.rpow_le_rpow_left_iff hq1).mp hh
  exact (div_le_iff₀ (by exact_mod_cast hr)).mpr hk

theorem rothFlattenRational_eval {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℤ)) (z : Fin (d + 1) → ℚ) :
    MvPolynomial.aeval z (rothFlattenRational P) =
      Polynomial.eval₂ (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun k => z k.castSucc))
        (z (Fin.last d)) P := by
  have he : (Polynomial.eval₂RingHom
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun k => z k.castSucc)) (z (Fin.last d))).comp
        (rothLastVariableEquiv d).toRingHom = MvPolynomial.eval₂Hom (Int.castRingHom ℚ) z := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rothLastVariableEquiv]
    · intro k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [RingHom.comp_apply, rothLastVariableEquiv_X_last]
      · simp [RingHom.comp_apply, rothLastVariableEquiv_X_castSucc]
  have h := RingHom.congr_fun he ((rothLastVariableEquiv d).symm P)
  simpa [rothFlattenRational, MvPolynomial.aeval_def, MvPolynomial.eval₂_map] using h.symm

theorem rothIntegerMixed_separated {d : ℕ}
    (v : MvPolynomial (Fin d) ℤ) (u : Polynomial ℤ) (a : Fin d →₀ ℕ) (j : ℕ) :
    rothIntegerMixedDividedDerivative a j (Polynomial.C v * u.map MvPolynomial.C) =
      Polynomial.C (rothIntegerDividedDerivative a v) *
        (Polynomial.hasseDeriv j u).map MvPolynomial.C := by
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro b
  rw [rothIntegerMixedDividedDerivative_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, Polynomial.hasseDeriv_coeff,
    map_mul, map_natCast]
  rw [mul_comm v (MvPolynomial.C (u.coeff (n + j))), MvPolynomial.coeff_C_mul]
  rw [show ((n + j).choose j : MvPolynomial (Fin d) ℤ) =
    MvPolynomial.C ((n + j).choose j : ℤ) by simp]
  rw [show rothIntegerDividedDerivative a v *
      (MvPolynomial.C ((n + j).choose j : ℤ) * MvPolynomial.C (u.coeff (n + j))) =
      MvPolynomial.C (u.coeff (n + j)) *
        (MvPolynomial.C ((n + j).choose j : ℤ) * rothIntegerDividedDerivative a v) by ring]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
    rothIntegerDividedDerivative_coeff]
  ring

theorem rothSeparated_hasse_eval {d : ℕ}
    (v : MvPolynomial (Fin d) ℤ) (u : Polynomial ℤ) (a : Fin d →₀ ℕ) (j : ℕ)
    (z : Fin (d + 1) → ℚ) :
    MvPolynomial.aeval z (rothDividedDerivative (rothLastExponent j a)
      (rothFlattenRational (Polynomial.C v * u.map MvPolynomial.C))) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun k => z k.castSucc)
        (rothIntegerDividedDerivative a v) *
      (Polynomial.hasseDeriv j (u.map (Int.castRingHom ℚ))).eval (z (Fin.last d)) := by
  rw [← rothFlattenRational_mixed, rothIntegerMixed_separated, rothFlattenRational_eval]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_map]
  congr 1
  have hm : ((Polynomial.hasseDeriv j u).map (Int.castRingHom ℚ)) =
      Polynomial.hasseDeriv j (u.map (Int.castRingHom ℚ)) := by
    apply Polynomial.ext
    intro n
    simp [Polynomial.coeff_map, Polynomial.hasseDeriv_coeff]
  rw [← hm, Polynomial.eval_map]
  congr 1
  ext x
  simp

theorem rothWeightedTaylorIndex_le_iff {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ) (t : ℝ) :
    rothWeightedTaylorIndex r z P ≤ (t : WithTop ℝ) ↔
      ∃ a : Fin d →₀ ℕ, rothTaylorWeight r a ≤ t ∧
        MvPolynomial.aeval z (rothDividedDerivative a P) ≠ 0 := by
  classical
  rw [rothWeightedTaylorIndex, Finset.inf_le_iff (WithTop.coe_lt_top t)]
  simp only [MvPolynomial.mem_support_iff, rothTaylorPolynomial_coeff, WithTop.coe_le_coe]
  aesop

theorem rothTaylorWeight_scale {d : ℕ} (r : Fin d → ℕ) (a : Fin d →₀ ℕ)
    (ell : ℕ) (he : 0 < ell) :
    (ell : ℝ) * rothTaylorWeight (fun k => ell * r k) a = rothTaylorWeight r a := by
  have heR : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
  simp only [rothTaylorWeight, Finset.mul_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hr : r k = 0
  · simp [hr]
  · have hrR : (r k : ℝ) ≠ 0 := by exact_mod_cast hr
    field_simp
    ring


noncomputable def rothOneVariablePolynomial (P : MvPolynomial (Fin 1) ℤ) : Polynomial ℤ :=
  (rothLastVariableEquiv 0 P).map (MvPolynomial.isEmptyRingEquiv ℤ (Fin 0)).toRingHom

theorem rothOneVariablePolynomial_coeff (P : MvPolynomial (Fin 1) ℤ) (n : ℕ) :
    (rothOneVariablePolynomial P).coeff n = P.coeff (rothLastExponent n (0 : Fin 0 →₀ ℕ)) := by
  rw [rothOneVariablePolynomial, Polynomial.coeff_map]
  change MvPolynomial.isEmptyRingEquiv ℤ (Fin 0) _ = _
  rw [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero, rothLastVariableEquiv_coeff]

theorem rothOneVariablePolynomial_restore (P : MvPolynomial (Fin 1) ℤ) :
    (rothOneVariablePolynomial P).map MvPolynomial.C = rothLastVariableEquiv 0 P := by
  apply Polynomial.ext
  intro n
  simp only [rothOneVariablePolynomial, Polynomial.coeff_map]
  exact (MvPolynomial.isEmptyRingEquiv ℤ (Fin 0)).symm_apply_apply _

theorem rothOneVariablePolynomial_ne_zero (P : MvPolynomial (Fin 1) ℤ) (hP : P ≠ 0) :
    rothOneVariablePolynomial P ≠ 0 := by
  intro h
  have he := rothOneVariablePolynomial_restore P
  rw [h, Polynomial.map_zero] at he
  apply hP
  exact (rothLastVariableEquiv 0).injective (by simpa using he.symm)

theorem rothOneVariablePolynomial_height_le (P : MvPolynomial (Fin 1) ℤ) :
    rothUnivariateIntegerHeight (rothOneVariablePolynomial P) ≤ rothIntegerHeight P := by
  classical
  apply Finset.sup_le
  intro n _
  rw [rothOneVariablePolynomial_coeff]
  exact rothIntegerHeight_coeff_le P _

theorem rothIntegerDividedDerivative_zero_order {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    rothIntegerDividedDerivative 0 P = P := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← rothIntegerDividedDerivative_map, rothDividedDerivative_zero]

theorem rothScalarOne_index_bound
    (P : MvPolynomial (Fin 1) ℤ) (hP : P ≠ 0) (r : Fin 1 → ℕ) (hr : 0 < r 0)
    (p q : Fin 1 → ℤ) (hq : q 0 ≠ 0) (hred : Int.gcd (p 0) (q 0) = 1)
    (hq1 : 1 < |(q 0 : ℝ)|) (A : ℝ)
    (hH : (rothIntegerHeight P : ℝ) ≤ Real.rpow |(q 0 : ℝ)| (A * (r 0 : ℝ))) :
    rothWeightedTaylorIndex r (fun k => (p k : ℚ) / (q k : ℚ))
      (MvPolynomial.map (Int.castRingHom ℚ) P) ≤ (A : WithTop ℝ) := by
  let u := rothOneVariablePolynomial P
  obtain ⟨j, hj, hne⟩ := rothRationalDenominator_hasse_witness u
    (rothOneVariablePolynomial_ne_zero P hP) (p 0) (q 0) hq hred hq1 (r 0) hr A
    ((show (rothUnivariateIntegerHeight u : ℝ) ≤ rothIntegerHeight P by
      exact_mod_cast rothOneVariablePolynomial_height_le P).trans hH)
  apply (rothWeightedTaylorIndex_le_iff _ _ _ A).mpr
  refine ⟨rothLastExponent j (0 : Fin 0 →₀ ℕ), ?_, ?_⟩
  · simp only [rothTaylorWeight, Fin.sum_univ_one]
    change ((rothLastExponent j (0 : Fin 0 →₀ ℕ)) (Fin.last 0) : ℝ) / (r 0 : ℝ) ≤ A
    simpa only [rothLastExponent_last] using hj
  · have he : MvPolynomial.map (Int.castRingHom ℚ) P =
        rothFlattenRational (Polynomial.C (1 : MvPolynomial (Fin 0) ℤ) * u.map MvPolynomial.C) := by
      simp only [Polynomial.C_1, one_mul, rothFlattenRational]
      rw [show u.map MvPolynomial.C = rothLastVariableEquiv 0 P from
        rothOneVariablePolynomial_restore P, AlgEquiv.symm_apply_apply]
    rw [he, rothSeparated_hasse_eval]
    simpa [rothIntegerDividedDerivative_zero_order] using hne


theorem rothClippedSum_arithmetic (s n : ℕ) (hs : 0 < s) (x : ℝ) :
    ∑ j ∈ Finset.range n, (x - (j : ℝ) / s) =
      (n : ℝ) * x - (n : ℝ) * ((n : ℝ) - 1) / (2 * (s : ℝ)) := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

theorem rothClippedSum_prefix_lower (ell s n : ℕ) (hs : 0 < s) (hn : n ≤ ell)
    (x : ℝ) (hcut : (n : ℝ) - 1 ≤ (s : ℝ) * x) :
    (n : ℝ) * x / 2 ≤ ∑ j ∈ Finset.range ell, max 0 (x - (j : ℝ) / s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum : ∑ j ∈ Finset.range n, (x - (j : ℝ) / s) ≤
      ∑ j ∈ Finset.range ell, max 0 (x - (j : ℝ) / s) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, max 0 (x - (j : ℝ) / s) :=
        Finset.sum_le_sum (fun _ _ => le_max_right _ _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun _ _ _ => le_max_left _ _)
  rw [rothClippedSum_arithmetic s n hs x] at hsum
  have hfrac : (n : ℝ) * ((n : ℝ) - 1) / (2 * (s : ℝ)) ≤ (n : ℝ) * x / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (s : ℝ))).mpr
    have h := mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  linarith

theorem rothClippedSum_contradiction (ell s : ℕ) (hl : 0 < ell) (hs : 0 < s)
    (hell : ell ≤ s + 1) (t x : ℝ) (ht : 0 < t) (ht' : t < 1 / 12)
    (hx : 5 * t / 6 < x) :
    (ell : ℝ) * t ^ 2 / 6 < ∑ j : Fin ell, max 0 (x - (j.val : ℝ) / s) := by
  have hlR : (0 : ℝ) < ell := by exact_mod_cast hl
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hx0 : 0 < x := by linarith
  rw [show (∑ j : Fin ell, max 0 (x - (j.val : ℝ) / s)) = ∑ j ∈ Finset.range ell, max 0 (x - (j : ℝ) / s) from (Fin.sum_univ_eq_sum_range (fun j : ℕ => max 0 (x - (j : ℝ) / s)) ell)]
  by_cases hcut : (ell : ℝ) - 1 ≤ (s : ℝ) * x
  · have hb := rothClippedSum_prefix_lower ell s ell hs le_rfl x hcut
    have ht2 : t ^ 2 / 6 < x / 2 := by nlinarith
    nlinarith [mul_pos hlR (sub_pos.mpr ht2)]
  · let n := Nat.ceil ((s : ℝ) * x)
    have hn0 : 0 < n := Nat.one_le_ceil_iff.mpr (mul_pos hsR hx0)
    have hn : n ≤ ell := Nat.ceil_le.mpr (by linarith)
    have hnR : (s : ℝ) * x ≤ n := Nat.le_ceil _
    have hcutn : (n : ℝ) - 1 ≤ (s : ℝ) * x := by
      have hpred : n - 1 < n := Nat.sub_lt hn0 (by decide)
      have hh : ((n - 1 : ℕ) : ℝ) < (s : ℝ) * x := Nat.lt_ceil.mp hpred
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hh
      exact hh.le
    have hb := rothClippedSum_prefix_lower ell s n hs hn x hcutn
    have heR : (ell : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast (show ell ≤ 2 * s by omega)
    have hsquare : t ^ 2 / 6 < x ^ 2 / 4 := by nlinarith [sq_nonneg (x - 5 * t / 6)]
    have hnx : (s : ℝ) * x ^ 2 / 2 ≤ (n : ℝ) * x / 2 := by nlinarith
    have helx : (ell : ℝ) * x ^ 2 / 4 ≤ (s : ℝ) * x ^ 2 / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr heR) (sq_nonneg x)]
    have htstrict : (ell : ℝ) * t ^ 2 / 6 < (ell : ℝ) * x ^ 2 / 4 := by
      nlinarith [mul_pos hlR (sub_pos.mpr hsquare)]
    exact htstrict.trans_le (helx.trans (hnx.trans hb))

theorem rothDenominatorSize_one_lt (m : ℕ) (hm : 0 < m) (t C : ℝ)
    (ht : 0 < t) (hC : 0 < C) (q : ℤ)
    (hden : (2 : ℝ) ^ (3 * m) ≤ Real.rpow |(q : ℝ)| (rothInductionOmega m t * C)) :
    1 < |(q : ℝ)| := by
  by_contra h
  have hqle : |(q : ℝ)| ≤ 1 := le_of_not_gt h
  have hh : Real.rpow |(q : ℝ)| (rothInductionOmega m t * C) ≤ 1 :=
    Real.rpow_le_one (abs_nonneg _) hqle (mul_pos (rothInductionOmega_pos m t ht) hC).le
  have htwo : (1 : ℝ) < 2 ^ (3 * m) := one_lt_pow₀ (by norm_num) (by omega)
  linarith

theorem rothIntegerDividedDerivative_eval {d : ℕ} (P : MvPolynomial (Fin d) ℤ)
    (a : Fin d →₀ ℕ) (z : Fin d → ℚ) :
    MvPolynomial.aeval z (rothDividedDerivative a (MvPolynomial.map (Int.castRingHom ℚ) P)) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) z (rothIntegerDividedDerivative a P) := by
  rw [rothIntegerDividedDerivative_map]
  simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]

theorem rothScalarOne_omega65
    (r : Fin 1 → ℕ) (p q : Fin 1 → ℤ) (t C : ℝ)
    (ht : 0 < t) (hC : 0 < C) (hC' : C ≤ 1)
    (hr : ∀ k, 0 < r k) (hq : ∀ k, q k ≠ 0) (hred : ∀ k, Int.gcd (p k) (q k) = 1)
    (hden : ∀ k, (2 : ℝ) ^ (3 * 1) ≤ |(q k : ℝ)| ^ (rothInductionOmega 1 t * C))
    (P : MvPolynomial (Fin 1) ℤ) (hP : P ≠ 0)
    (hH : (rothIntegerHeight P : ℝ) ≤ |(q 0 : ℝ)| ^ (rothInductionOmega 1 t * r 0 * C)) :
    rothWeightedTaylorIndex r (fun k => (p k : ℚ) / (q k : ℚ))
      (MvPolynomial.map (Int.castRingHom ℚ) P) ≤ (t : WithTop ℝ) := by
  have ho : rothInductionOmega 1 t = t := by simp [rothInductionOmega]; ring
  have hheight : (rothIntegerHeight P : ℝ) ≤ Real.rpow |(q 0 : ℝ)| ((t * C) * (r 0 : ℝ)) := by
    convert hH using 1 <;> rw [ho] <;> congr 1 <;> ring
  have hh := rothScalarOne_index_bound P hP r (hr 0) p q (hq 0) (hred 0)
    (rothDenominatorSize_one_lt 1 (by omega) t C ht hC (q 0) (hden 0)) (t * C) hheight
  exact hh.trans (by exact_mod_cast (mul_le_of_le_one_right ht.le hC'))
theorem rothWeightedTaylorIndex_scale_finite {d : ℕ} (r : Fin d → ℕ)
    (z : Fin d → ℚ) (P : MvPolynomial (Fin d) ℚ) (ell : ℕ) (he : 0 < ell)
    (I : ℝ) (hI : rothWeightedTaylorIndex (fun k => ell * r k) z P = (I : WithTop ℝ)) :
    rothWeightedTaylorIndex r z P = ((ell * I : ℝ) : WithTop ℝ) := by
  have heR : (0 : ℝ) < ell := by exact_mod_cast he
  apply le_antisymm
  · obtain ⟨a, ha, hne⟩ := (rothWeightedTaylorIndex_le_iff _ _ _ I).mp hI.le
    apply (rothWeightedTaylorIndex_le_iff _ _ _ _).mpr
    refine ⟨a, ?_, hne⟩
    rw [← rothTaylorWeight_scale r a ell he]
    exact mul_le_mul_of_nonneg_left ha heR.le
  · apply (rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
    intro a ha
    have hh := (rothWeightedTaylorIndex_lower_iff _ _ _ I).mp hI.ge a ha
    rw [← rothTaylorWeight_scale r a ell he]
    exact mul_le_mul_of_nonneg_left hh heR.le

theorem rothNestedWeightedTaylorIndex_mul {d : ℕ} (r : Fin (d + 1) → ℕ)
    (z : Fin (d + 1) → ℚ) (P Q : Polynomial (MvPolynomial (Fin d) ℤ)) :
    rothNestedWeightedTaylorIndex r z (P * Q) =
      rothNestedWeightedTaylorIndex r z P + rothNestedWeightedTaylorIndex r z Q := by
  unfold rothNestedWeightedTaylorIndex rothFlattenRational
  rw [map_mul, map_mul, rothWeightedTaylorIndex_mul]

theorem rothHasse_order_ge_rootMultiplicity (f : Polynomial ℚ) (a : ℚ) (j : ℕ)
    (hne : (Polynomial.hasseDeriv j f).eval a ≠ 0) : f.rootMultiplicity a ≤ j := by
  by_contra h
  have hj : j < f.rootMultiplicity a := Nat.lt_of_not_ge h
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree] at hj
  have hz : (Polynomial.taylor a f).coeff j = 0 := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
  exact hne (by simpa only [Polynomial.taylor_coeff] using hz)

theorem rothSeparated_index_eq {d : ℕ} (r : Fin d → ℕ) (s : ℕ) (hs : 0 < s)
    (z : Fin d → ℚ) (a : ℚ) (u : Polynomial ℤ) (hu : u ≠ 0)
    (v : MvPolynomial (Fin d) ℤ) (I : ℝ)
    (hI : rothWeightedTaylorIndex r z (MvPolynomial.map (Int.castRingHom ℚ) v) = (I : WithTop ℝ)) :
    rothNestedWeightedTaylorIndex (Fin.snoc r s) (Fin.snoc z a)
      (Polynomial.C v * u.map MvPolynomial.C) =
      ((I + ((u.map (Int.castRingHom ℚ)).rootMultiplicity a : ℝ) / s : ℝ) : WithTop ℝ) := by
  let k := (u.map (Int.castRingHom ℚ)).rootMultiplicity a
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  apply le_antisymm
  · apply (rothWeightedTaylorIndex_le_iff _ _ _ _).mpr
    obtain ⟨b, hb, hvb⟩ := (rothWeightedTaylorIndex_le_iff _ _ _ I).mp hI.le
    rw [rothIntegerDividedDerivative_eval] at hvb
    refine ⟨rothLastExponent k b, ?_, ?_⟩
    · rw [rothLastExponent_weight]
      exact add_le_add_right hb _
    · rw [rothSeparated_hasse_eval]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact mul_ne_zero hvb (rothRationalMultiplicity_hasse_ne_zero u hu a)
  · apply (rothWeightedTaylorIndex_lower_iff _ _ _ _).mpr
    intro c hc
    obtain ⟨j, b, rfl⟩ := rothLastExponent_surjective c
    have hne := MvPolynomial.mem_support_iff.mp hc
    rw [rothTaylorPolynomial_coeff, rothSeparated_hasse_eval] at hne
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hne
    have hparts := mul_ne_zero_iff.mp hne
    have hvb : MvPolynomial.aeval z
        (rothDividedDerivative b (MvPolynomial.map (Int.castRingHom ℚ) v)) ≠ 0 := by
      rw [rothIntegerDividedDerivative_eval]
      exact hparts.1
    have hbmem : b ∈ (rothTaylorPolynomial z (MvPolynomial.map (Int.castRingHom ℚ) v)).support := by
      rw [MvPolynomial.mem_support_iff, rothTaylorPolynomial_coeff]
      exact hvb
    have hb := (rothWeightedTaylorIndex_lower_iff _ _ _ I).mp hI.ge b hbmem
    have hj : k ≤ j := rothHasse_order_ge_rootMultiplicity _ a j hparts.2
    rw [rothLastExponent_weight]
    exact add_le_add hb (div_le_div_of_nonneg_right (by exact_mod_cast hj) hsR.le)


set_option maxHeartbeats 1600000 in
theorem rothScalar_index_omega65 (d : ℕ) :
    ∀ (r : Fin (d + 1) → ℕ) (p q : Fin (d + 1) → ℤ) (t C : ℝ),
    0 < t → t < 1 / 12 → 0 < C → C ≤ 1 →
    (∀ k, 0 < r k) → (∀ k, q k ≠ 0) → (∀ k, Int.gcd (p k) (q k) = 1) →
    (∀ i : Fin d, (r i.succ : ℝ) ≤ rothInductionOmega (d + 1) t * (r i.castSucc : ℝ)) →
    (∀ k : Fin (d + 1), 1 ≤ k.val →
      |(q 0 : ℝ)| ^ ((r 0 : ℝ) * C) ≤ |(q k : ℝ)| ^ (r k : ℝ)) →
    (∀ k, (2 : ℝ) ^ (3 * (d + 1)) ≤ |(q k : ℝ)| ^ (rothInductionOmega (d + 1) t * C)) →
    ∀ (P : MvPolynomial (Fin (d + 1)) ℤ), P ≠ 0 →
    (∀ b ∈ P.support, ∀ k, b k ≤ r k) →
    (rothIntegerHeight P : ℝ) ≤ |(q 0 : ℝ)| ^ (rothInductionOmega (d + 1) t * r 0 * C) →
    rothWeightedTaylorIndex r (fun k => (p k : ℚ) / (q k : ℚ))
      (MvPolynomial.map (Int.castRingHom ℚ) P) ≤ (t : WithTop ℝ) := by
  induction d with
  | zero =>
    intro r p q t C ht ht' hC hC' hr hq hred hsep hgrowth hden P hP hb hH
    exact rothScalarOne_omega65 r p q t C ht hC hC' hr hq hred hden P hP hH
  | succ d ih =>
    intro r p q t C ht ht' hC hC' hr hq hred hsep hgrowth hden P hP hb hH
    let sigma := t ^ 2 / 12
    let rho := rothInductionOmega (d + 2) t
    have hsig : 0 < sigma := by dsimp [sigma]; positivity
    have hsig' : sigma < 1 / 12 := by dsimp [sigma]; nlinarith
    have hrec : rothInductionOmega (d + 1) sigma = 2 * rho := omega65_induction (d + 1) (by omega) t
    have hrho : 0 < rho := rothInductionOmega_pos _ _ ht
    have hsmall : 2 * rho ≤ sigma := by
      rw [← hrec]
      exact rothInductionOmega_le_t (d + 1) (by omega) sigma hsig hsig'
    have hq1 (k) : 1 < |(q k : ℝ)| :=
      rothDenominatorSize_one_lt (d + 2) (by omega) t C ht hC (q k) (hden k)
    let Q := rothLastVariableEquiv (d + 1) P
    have hQ : Q ≠ 0 := fun h => hP ((rothLastVariableEquiv (d + 1)).injective (by simpa [Q] using h))
    have hbQ := rothLastVariableEquiv_supportBound P r hb
    have hHQ : (rothNestedIntegerHeight Q : ℝ) ≤
        |(q 0 : ℝ)| ^ (rho * r 0 * C) := by simpa [Q, rothLastVariableEquiv_height, rho] using hH
    obtain ⟨ell, alpha, u, v, I, hl, hell, ha, hw, hu, hv, hW, hbs, hdu, hdv,
      hgeneral, hsimp, hmulH, hHv, hHu, hI, hlow, hHW, hHU⟩ :=
      roth_exists_quantitative_separated_wronskian (d + 1) r p q t C ht ht' hC hC'
        hr hq hred hsep hgrowth hden Q hQ hbQ hHQ
    have hl0 : 0 < ell := by omega
    have hlR : (0 : ℝ) < ell := by exact_mod_cast hl0
    have hdegV : ∀ b ∈ v.support, ∀ k, b k ≤ ell * r k.castSucc := by
      intro b hb k
      exact (MvPolynomial.monomial_le_degreeOf k hb).trans (hdv k)
    have hsepV : ∀ i : Fin d, ((ell * r i.succ.castSucc : ℕ) : ℝ) ≤
        rothInductionOmega (d + 1) sigma * ((ell * r i.castSucc.castSucc : ℕ) : ℝ) := by
      intro i
      have hh := hsep i.castSucc
      have hh' : (r i.succ.castSucc : ℝ) ≤ rho * (r i.castSucc.castSucc : ℝ) := hh
      rw [hrec]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hh' hlR.le]
    have hgV : ∀ k : Fin (d + 1), 1 ≤ k.val →
        |(q 0 : ℝ)| ^ (((ell * r 0 : ℕ) : ℝ) * C) ≤
          |(q k.castSucc : ℝ)| ^ ((ell * r k.castSucc : ℕ) : ℝ) := by
      intro k hk
      have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ |(q 0 : ℝ)| ^ ((r 0 : ℝ) * C))
        (hgrowth k.castSucc hk) hlR.le
      rw [← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _)] at hh
      convert hh using 1 <;> push_cast <;> congr 1 <;> ring
    have hdV : ∀ k : Fin (d + 1), (2 : ℝ) ^ (3 * (d + 1)) ≤
        |(q k.castSucc : ℝ)| ^ (rothInductionOmega (d + 1) sigma * C) := by
      intro k
      calc
        _ ≤ (2 : ℝ) ^ (3 * (d + 2)) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ |(q k.castSucc : ℝ)| ^ (rho * C) := hden k.castSucc
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le (hq1 k.castSucc).le
          rw [hrec]
          nlinarith
    have hHV : (rothIntegerHeight v : ℝ) ≤
        |(q 0 : ℝ)| ^ (rothInductionOmega (d + 1) sigma * (ell * r 0 : ℕ) * C) := by
      have hh : (rothIntegerHeight v : ℝ) ≤ rothNestedIntegerHeight
          (Polynomial.C v * u.map MvPolynomial.C) := by exact_mod_cast hHv
      apply (hh.trans hHW).trans_eq
      congr 1
      rw [hrec]
      push_cast
      ring
    have hV := ih (fun k => ell * r k.castSucc) (fun k => p k.castSucc) (fun k => q k.castSucc)
      sigma C hsig hsig' hC hC' (fun k => Nat.mul_pos hl0 (hr _))
      (fun k => hq _) (fun k => hred _) hsepV hgV hdV v hv hdegV hHV
    obtain ⟨a, hwa, hva⟩ := (rothWeightedTaylorIndex_le_iff _ _ _ sigma).mp hV
    rw [rothIntegerDividedDerivative_eval] at hva
    have hwa' : rothTaylorWeight (fun k => r k.castSucc) a ≤ (ell : ℝ) * sigma := by
      rw [← rothTaylorWeight_scale _ _ ell hl0]
      exact mul_le_mul_of_nonneg_left hwa hlR.le
    obtain ⟨j, hwj, huj⟩ := rothRationalDenominator_hasse_witness u hu (p (Fin.last (d + 1)))
      (q (Fin.last (d + 1))) (hq _) (hred _) (hq1 _) (r (Fin.last (d + 1))) (hr _)
      (2 * rho * ell) (by convert hHU using 1 <;> congr 1 <;> ring)
    have hsnoc : Fin.snoc (fun k : Fin (d + 1) => r k.castSucc) (r (Fin.last (d + 1))) = r := by
      funext k
      refine Fin.lastCases ?_ (fun i => ?_) k <;> simp
    let z : Fin (d + 2) → ℚ := fun k => (p k : ℚ) / (q k : ℚ)
    have hCv : rothNestedWeightedTaylorIndex r z (Polynomial.C v) ≤
        (((ell : ℝ) * sigma : ℝ) : WithTop ℝ) := by
      apply (rothWeightedTaylorIndex_le_iff _ _ _ _).mpr
      refine ⟨rothLastExponent 0 a, ?_, ?_⟩
      · rw [← hsnoc, rothLastExponent_weight]
        simpa using hwa'
      · have hh := rothSeparated_hasse_eval v (1 : Polynomial ℤ) a 0 z
        simp only [Polynomial.map_one, mul_one, Polynomial.hasseDeriv_zero,
          LinearMap.id_apply, Polynomial.eval_one] at hh
        rw [hh]
        exact hva
    have hU : rothNestedWeightedTaylorIndex r z (u.map MvPolynomial.C) ≤
        ((2 * rho * ell : ℝ) : WithTop ℝ) := by
      apply (rothWeightedTaylorIndex_le_iff _ _ _ _).mpr
      refine ⟨rothLastExponent j (0 : Fin (d + 1) →₀ ℕ), ?_, ?_⟩
      · rw [← hsnoc, rothLastExponent_weight]
        simpa [rothTaylorWeight] using hwj
      · have hh := rothSeparated_hasse_eval (1 : MvPolynomial (Fin (d + 1)) ℤ) u 0 j z
        simp only [Polynomial.C_1, one_mul, rothIntegerDividedDerivative_zero_order,
          MvPolynomial.eval₂_one] at hh
        rw [hh]
        exact huj
    have hWupper : rothNestedWeightedTaylorIndex r (fun k => (p k : ℚ) / (q k : ℚ))
        (Polynomial.C v * u.map MvPolynomial.C) ≤ ((2 * ell * sigma : ℝ) : WithTop ℝ) := by
      rw [rothNestedWeightedTaylorIndex_mul]
      apply (add_le_add hCv hU).trans
      rw [← WithTop.coe_add]
      exact_mod_cast (show (ell : ℝ) * sigma + 2 * rho * ell ≤ 2 * ell * sigma by
        nlinarith only [mul_le_mul_of_nonneg_right hsmall hlR.le])
    have hIeq : rothWeightedTaylorIndex r (fun k => (p k : ℚ) / (q k : ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) P) = (I : WithTop ℝ) := by
      simpa [rothNestedWeightedTaylorIndex, rothFlattenRational, Q] using hI
    rw [hIeq]
    by_cases hle : I ≤ t
    · exact_mod_cast hle
    · exfalso
      have hIt' : t < I := lt_of_not_ge hle
      have hrhot : rho ≤ t / 6 := by dsimp [sigma] at hsmall; nlinarith only [hsmall, ht, ht']
      have hx : 5 * t / 6 < I - rho := by linarith only [hIt', hrhot]
      have hnumeric := rothClippedSum_contradiction ell (r (Fin.last (d + 1))) hl0 (hr _) hell
        t (I - rho) ht ht' hx
      have hbound : (∑ j : Fin ell, max 0 (I - rho - (j.val : ℝ) / r (Fin.last (d + 1)))) ≤
          2 * ell * sigma := by exact_mod_cast hlow.trans hWupper
      dsimp [sigma] at hbound
      nlinarith only [hbound, hnumeric]

theorem roth_scalar_omega65_nonvanishing
    (m : ℕ) (hm : 0 < m) (theta C : ℝ)
    (ht : 0 < theta) (ht' : theta < 1 / 12) (hC : 0 < C) (hC' : C ≤ 1)
    (r : Fin m → ℕ) (p q : Fin m → ℤ) (P : MvPolynomial (Fin m) ℤ)
    (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val + 1 < m),
      (r ⟨h.val + 1, hh⟩ : ℝ) ≤ rothInductionOmega m theta * (r h : ℝ))
    (hq : ∀ h, q h ≠ 0 ∧ Int.gcd (p h) (q h) = 1)
    (hgrowth : ∀ h : Fin m, h.val ≠ 0 →
      Real.rpow |(q ⟨0, hm⟩ : ℝ)| ((r ⟨0, hm⟩ : ℝ) * C) ≤ |(q h : ℝ)| ^ r h)
    (hden : ∀ h, (2 : ℝ) ^ (3 * m) ≤ Real.rpow |(q h : ℝ)| (rothInductionOmega m theta * C))
    (hP : P ≠ 0) (hb : ∀ b ∈ P.support, ∀ h, b h ≤ r h)
    (hH : (rothIntegerHeight P : ℝ) ≤ Real.rpow |(q ⟨0, hm⟩ : ℝ)|
      (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * C)) :
    ∃ J : Fin m →₀ ℕ, (∑ h : Fin m, (J h : ℝ) / (r h : ℝ)) ≤ theta ∧
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun h => (p h : ℚ) / (q h : ℚ))
        (rothIntegerDividedDerivative J P) ≠ 0 := by
  cases m with
  | zero => omega
  | succ d =>
    have hs : ∀ i : Fin d, (r i.succ : ℝ) ≤ rothInductionOmega (d + 1) theta * (r i.castSucc : ℝ) := by
      intro i
      exact hsep i.castSucc (Nat.succ_lt_succ i.isLt)
    have hg : ∀ k : Fin (d + 1), 1 ≤ k.val →
        |(q 0 : ℝ)| ^ ((r 0 : ℝ) * C) ≤ |(q k : ℝ)| ^ (r k : ℝ) := by
      intro k hk
      convert hgrowth k (by omega) using 1
      rw [Real.rpow_natCast]
    have hi := rothScalar_index_omega65 d r p q theta C ht ht' hC hC' hr
      (fun k => (hq k).1) (fun k => (hq k).2) hs hg hden P hP hb hH
    obtain ⟨J, hJ, hne⟩ := (rothWeightedTaylorIndex_le_iff _ _ _ theta).mp hi
    rw [rothIntegerDividedDerivative_eval] at hne
    exact ⟨J, hJ, hne⟩

end JSP000334

namespace JSP000334
open scoped BigOperators

theorem rothPrimitiveTriple_common_divisor
    (V : Fin 3 → ℤ) (hV : Ideal.span (Set.range V) = ⊤)
    (d : ℕ) (hd : ∀ i, d ∣ (V i).natAbs) : d = 1 := by
  have hspan : Ideal.span (Set.range V) ≤ Ideal.span ({(d : ℤ)} : Set ℤ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    exact Int.natCast_dvd.mpr (hd i)
  have hone : (1 : ℤ) ∈ Ideal.span ({(d : ℤ)} : Set ℤ) := by
    apply hspan
    rw [hV]
    trivial
  have hunit : IsUnit (d : ℤ) := isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hone)
  simpa using Int.isUnit_iff_natAbs_eq.mp hunit

theorem rothPrimitiveTriple_pair_gcd_product
    (V : Fin 3 → ℤ) (hV : Ideal.span (Set.range V) = ⊤) (hV0 : V 0 ≠ 0) :
    Nat.gcd (V 0).natAbs (V 1).natAbs * Nat.gcd (V 0).natAbs (V 2).natAbs ≤ (V 0).natAbs := by
  let a := Nat.gcd (V 0).natAbs (V 1).natAbs
  let b := Nat.gcd (V 0).natAbs (V 2).natAbs
  have hcop : Nat.Coprime a b := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    apply rothPrimitiveTriple_common_divisor V hV
    intro i
    fin_cases i
    · exact dvd_trans (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right _ _)
    · exact dvd_trans (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_right _ _)
  have hab : a * b ∣ (V 0).natAbs := hcop.mul_dvd_of_dvd_of_dvd
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hV0) hab

theorem rothPrimitiveTriple_select_pair
    (V : Fin 3 → ℤ) (hV : Ideal.span (Set.range V) = ⊤) (hnz : ∃ i, V i ≠ 0) :
    ∃ i j : Fin 3, i ≠ j ∧ V i ≠ 0 ∧
      (∀ k, (V k).natAbs ≤ (V i).natAbs) ∧ Int.gcd (V i) (V j) ^ 2 ≤ (V i).natAbs := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun k : Fin 3 => (V k).natAbs)
  have hmax (k) : (V k).natAbs ≤ (V i).natAbs := by
    rw [← he]
    exact Finset.le_sup (f := fun k : Fin 3 => (V k).natAbs) (Finset.mem_univ k)
  have hi0 : V i ≠ 0 := by
    obtain ⟨k, hk⟩ := hnz
    intro hz
    have hh := hmax k
    rw [hz, Int.natAbs_zero] at hh
    exact hk (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hh))
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  let W : Fin 3 → ℤ := fun k => V (e k)
  have he0 : e 0 = i := Equiv.swap_apply_left 0 i
  have hrange : Set.range W = Set.range V := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e.symm k, by simp [W]⟩
  have hW : Ideal.span (Set.range W) = ⊤ := by rw [hrange]; exact hV
  have hW0 : W 0 ≠ 0 := by simpa only [W, he0] using hi0
  have hprod := rothPrimitiveTriple_pair_gcd_product W hW hW0
  let a := Int.gcd (W 0) (W 1)
  let b := Int.gcd (W 0) (W 2)
  change a * b ≤ (W 0).natAbs at hprod
  by_cases hab : a ≤ b
  · refine ⟨i, e 1, ?_, hi0, hmax, ?_⟩
    · rw [← he0]
      exact e.injective.ne (by decide : (0 : Fin 3) ≠ 1)
    · have hs : a ^ 2 ≤ (W 0).natAbs := by nlinarith
      simpa only [a, W, he0] using hs
  · refine ⟨i, e 2, ?_, hi0, hmax, ?_⟩
    · rw [← he0]
      exact e.injective.ne (by decide : (0 : Fin 3) ≠ 2)
    · have hs : b ^ 2 ≤ (W 0).natAbs := by nlinarith
      simpa only [b, W, he0] using hs


theorem rothReducedPair_denominator_bounds (a b : ℤ) (ha : a ≠ 0)
    (hsmall : Int.gcd a b ^ 2 ≤ a.natAbs) :
    ∃ p q : ℤ, q ≠ 0 ∧ Int.gcd p q = 1 ∧
      (p : ℚ) / (q : ℚ) = -(b : ℚ) / (a : ℚ) ∧
      q.natAbs ≤ a.natAbs ∧ a.natAbs ≤ q.natAbs ^ 2 := by
  let g := Int.gcd a b
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left b ha
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hga : (g : ℤ) ∣ a := Int.gcd_dvd_left
  have hgb : (g : ℤ) ∣ b := Int.gcd_dvd_right
  let q := a / (g : ℤ)
  let p := -(b / (g : ℤ))
  have hqg : q * (g : ℤ) = a := Int.ediv_mul_cancel hga
  have hq : q ≠ 0 := by intro hz; rw [hz, zero_mul] at hqg; exact ha hqg.symm
  have hmul : q.natAbs * g = a.natAbs := by
    have hh := congrArg Int.natAbs hqg
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hh
  have hcop : Int.gcd p q = 1 := by
    dsimp [p, q]
    rw [Int.gcd_comm, Int.gcd_neg]
    exact Int.gcd_div_gcd_div_gcd hg
  refine ⟨p, q, hq, hcop, ?_, ?_, ?_⟩
  · dsimp [p, q]
    rw [Int.cast_div hgb hgQ, Int.cast_div hga hgQ]
    field_simp
    ring
  · nlinarith
  · change g ^ 2 ≤ a.natAbs at hsmall
    have hgle : g ≤ q.natAbs := by nlinarith
    nlinarith

theorem rothPrimitiveTriple_rational_parameters
    (V : Fin 3 → ℤ) (hV : Ideal.span (Set.range V) = ⊤) (hnz : ∃ i, V i ≠ 0) :
    ∃ (i j : Fin 3) (p q : ℤ), i ≠ j ∧ V i ≠ 0 ∧
      (∀ k, (V k).natAbs ≤ (V i).natAbs) ∧ q ≠ 0 ∧ Int.gcd p q = 1 ∧
      (p : ℚ) / (q : ℚ) = -(V j : ℚ) / (V i : ℚ) ∧
      q.natAbs ≤ (V i).natAbs ∧ (V i).natAbs ≤ q.natAbs ^ 2 := by
  obtain ⟨i, j, hij, hi, hmax, hsmall⟩ := rothPrimitiveTriple_select_pair V hV hnz
  obtain ⟨p, q, hq, hcop, he, hupper, hlower⟩ := rothReducedPair_denominator_bounds (V i) (V j) hi hsmall
  exact ⟨i, j, p, q, hij, hi, hmax, hq, hcop, he, hupper, hlower⟩
theorem rothKernel_square_rpow (H Q a : ℝ) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hHQ : H ≤ Q ^ 2) (ha : 0 ≤ a) : H ^ (a / 2) ≤ Q ^ a := by
  have hh := Real.rpow_le_rpow hH hHQ (show 0 ≤ a / 2 by positivity)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hQ] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem rothKernel_scalar_budgets
    (m : ℕ) (hm : 0 < m) (theta Gamma : ℝ) (ht : 0 < theta)
    (hG : 0 < Gamma) (hG' : Gamma ≤ 2) (r : Fin m → ℕ)
    (H Q : Fin m → ℝ) (K : ℝ)
    (hH : ∀ h, 1 ≤ H h) (hQ : ∀ h, 0 ≤ Q h)
    (hupper : ∀ h, Q h ≤ H h) (hlower : ∀ h, H h ≤ Q h ^ 2)
    (hgrowth : ∀ h : Fin m, h.val ≠ 0 →
      (H ⟨0, hm⟩) ^ ((r ⟨0, hm⟩ : ℝ) * Gamma) ≤ (H h) ^ (r h : ℝ))
    (hden : ∀ h, (2 : ℝ) ^ (12 * m) ≤ (H h) ^ (rothInductionOmega m theta * Gamma))
    (hK : 0 ≤ K) (hheight : K ^ 4 ≤ (H ⟨0, hm⟩) ^
      (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * Gamma)) :
    0 < Gamma / 2 ∧ Gamma / 2 ≤ 1 ∧
    (∀ h : Fin m, h.val ≠ 0 →
      (Q ⟨0, hm⟩) ^ ((r ⟨0, hm⟩ : ℝ) * (Gamma / 2)) ≤ (Q h) ^ (r h : ℝ)) ∧
    (∀ h, (2 : ℝ) ^ (3 * m) ≤ (Q h) ^ (rothInductionOmega m theta * (Gamma / 2))) ∧
    K ≤ (Q ⟨0, hm⟩) ^ (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * (Gamma / 2)) := by
  have hrho : 0 < rothInductionOmega m theta := rothInductionOmega_pos m theta ht
  refine ⟨by positivity, by linarith, ?_, ?_, ?_⟩
  · intro h hh
    have hg := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith [hH ⟨0, hm⟩]) _) (hgrowth h hh) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul (by linarith [hH ⟨0, hm⟩]),
      ← Real.rpow_mul (by linarith [hH h])] at hg
    have hfirst := Real.rpow_le_rpow (hQ ⟨0, hm⟩) (hupper ⟨0, hm⟩)
      (show 0 ≤ (r ⟨0, hm⟩ : ℝ) * (Gamma / 2) by positivity)
    have hlast := rothKernel_square_rpow (H h) (Q h) (r h) (by linarith [hH h]) (hQ h)
      (hlower h) (by positivity)
    have hg' : (H ⟨0, hm⟩) ^ ((r ⟨0, hm⟩ : ℝ) * (Gamma / 2)) ≤
        (H h) ^ ((r h : ℝ) / 2) := by
      convert hg using 1 <;> congr 1 <;> ring
    exact hfirst.trans (hg'.trans hlast)
  · intro h
    have hd := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (12 * m)) (hden h)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by linarith [hH h])] at hd
    have hs := rothKernel_square_rpow (H h) (Q h) (rothInductionOmega m theta * Gamma / 2)
      (by linarith [hH h]) (hQ h) (hlower h) (by positivity)
    have hs' : (H h) ^ (rothInductionOmega m theta * Gamma * (1 / 4)) ≤
        (Q h) ^ (rothInductionOmega m theta * (Gamma / 2)) := by
      convert hs using 1 <;> congr 1 <;> ring
    have hleft : ((12 * m : ℕ) : ℝ) * (1 / 4) = ((3 * m : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hleft, Real.rpow_natCast] at hd
    exact hd.trans hs'
  · have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ K ^ 4) hheight
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK,
      ← Real.rpow_mul (by linarith [hH ⟨0, hm⟩])] at hh
    norm_num at hh
    have hs := rothKernel_square_rpow (H ⟨0, hm⟩) (Q ⟨0, hm⟩)
      (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * Gamma / 2)
      (by linarith [hH ⟨0, hm⟩]) (hQ ⟨0, hm⟩) (hlower ⟨0, hm⟩) (by positivity)
    have hs' : (H ⟨0, hm⟩) ^ (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * Gamma * (1 / 4)) ≤
        (Q ⟨0, hm⟩) ^ (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * (Gamma / 2)) := by
      convert hs using 1 <;> congr 1 <;> ring
    exact hh.trans hs'

abbrev RothBlockVars (m : ℕ) := Fin m × Fin 3

noncomputable def rothBlockIntegerDividedDerivative {m : ℕ}
    (J : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial (RothBlockVars m) ℤ :=
  P.sum fun b c => MvPolynomial.monomial (b - J)
    (c * ∏ u : RothBlockVars m, (Nat.choose (b u) (J u) : ℤ))

theorem rothBlockIntegerDividedDerivative_coeff {m : ℕ}
    (a gamma : RothBlockVars m →₀ ℕ) (P : MvPolynomial (RothBlockVars m) ℤ) :
    (rothBlockIntegerDividedDerivative a P).coeff gamma =
      P.coeff (gamma + a) *
        ∏ k : RothBlockVars m, (Nat.choose ((gamma + a) k) (a k) : ℤ) := by
  classical
  rw [rothBlockIntegerDividedDerivative, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  calc
    _ = (MvPolynomial.monomial ((gamma + a) - a)
        (P.coeff (gamma + a) * ∏ k : RothBlockVars m,
          (Nat.choose ((gamma + a) k) (a k) : ℤ))).coeff gamma := by
      apply Finset.sum_eq_single (gamma + a)
      · intro b hb hne
        by_cases hab : a ≤ b
        · have hd : b - a ≠ gamma := by
            intro hz
            apply hne
            calc
              b = (b - a) + a := (tsub_add_cancel_of_le hab).symm
              _ = gamma + a := by rw [hz]
          simp [MvPolynomial.coeff_monomial, hd]
        · change ¬ ∀ k, a k ≤ b k at hab
          push_neg at hab
          obtain ⟨k, hk⟩ := hab
          have hz : (∏ k : RothBlockVars m, (Nat.choose (b k) (a k) : ℤ)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            simp [Nat.choose_eq_zero_of_lt hk]
          simp [hz]
      · intro hn
        have hz : P.coeff (gamma + a) = 0 := MvPolynomial.not_mem_support_iff.mp hn
        simp [hz]
    _ = _ := by simp

noncomputable def rothKernelChart {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (u : RothBlockVars m) : MvPolynomial (RothBlockVars m) ℚ :=
  if u.2 = k u.1 then
    -(∑ i ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C ((V u.1 i : ℚ) / (V u.1 (k u.1) : ℚ)) * MvPolynomial.X (u.1, i))
  else MvPolynomial.X u

noncomputable def rothKernelRestriction {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial (RothBlockVars m) ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom _) (rothKernelChart V k) P

theorem rothBlockIntegerDividedDerivative_free_monomial {m : ℕ}
    (P : MvPolynomial (RothBlockVars m) ℤ) (J : RothBlockVars m →₀ ℕ)
    (z : RothBlockVars m) (a : ℕ) (hJ : J z = 0) :
    rothBlockIntegerDividedDerivative J (MvPolynomial.monomial (Finsupp.single z a) 1 * P) =
      MvPolynomial.monomial (Finsupp.single z a) 1 * rothBlockIntegerDividedDerivative J P := by
  classical
  apply MvPolynomial.ext
  intro b
  rw [rothBlockIntegerDividedDerivative_coeff, MvPolynomial.coeff_monomial_mul',
    MvPolynomial.coeff_monomial_mul']
  have hle : Finsupp.single z a ≤ b + J ↔ Finsupp.single z a ≤ b := by
    simp only [Finsupp.single_le_iff, Finsupp.add_apply, hJ, add_zero]
  simp only [hle]
  split_ifs with hb
  · rw [one_mul, one_mul, rothBlockIntegerDividedDerivative_coeff]
    have hexp : b + J - Finsupp.single z a = (b - Finsupp.single z a) + J := by
      ext u
      by_cases hu : u = z
      · subst u
        simp [Finsupp.sub_apply, Finsupp.add_apply, hJ]
      · simp [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply, hu, Ne.symm hu]
    rw [hexp]
    congr 1
    apply Finset.prod_congr rfl
    intro u _
    by_cases hu : u = z
    · subst u
      simp [Finsupp.add_apply, hJ]
    · simp [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply, hu, Ne.symm hu]
  · simp

theorem rothKernelRestriction_free_monomial_ne_zero {m : ℕ}
    (V : Fin m → Fin 3 → ℤ) (k : Fin m → Fin 3)
    (P : MvPolynomial (RothBlockVars m) ℤ) (z : RothBlockVars m) (a : ℕ)
    (hz : z.2 ≠ k z.1) :
    rothKernelRestriction V k (MvPolynomial.monomial (Finsupp.single z a) 1 * P) ≠ 0 ↔
      rothKernelRestriction V k P ≠ 0 := by
  have hX : (MvPolynomial.X z : MvPolynomial (RothBlockVars m) ℚ) ≠ 0 := MvPolynomial.X_ne_zero z
  simp only [rothKernelRestriction, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_monomial,
    map_one, one_mul, Finsupp.prod_single_index, pow_zero, rothKernelChart, if_neg hz]
  exact mul_ne_zero_iff.trans (and_iff_right (pow_ne_zero a hX))

theorem rothKernelRestriction_derivative_strip {m : ℕ}
    (V : Fin m → Fin 3 → ℤ) (k : Fin m → Fin 3)
    (P : MvPolynomial (RothBlockVars m) ℤ) (J : RothBlockVars m →₀ ℕ)
    (z : RothBlockVars m) (a : ℕ) (hz : z.2 ≠ k z.1) (hJ : J z = 0) :
    rothKernelRestriction V k
      (rothBlockIntegerDividedDerivative J (MvPolynomial.monomial (Finsupp.single z a) 1 * P)) ≠ 0 ↔
      rothKernelRestriction V k (rothBlockIntegerDividedDerivative J P) ≠ 0 := by
  rw [rothBlockIntegerDividedDerivative_free_monomial P J z a hJ]
  exact rothKernelRestriction_free_monomial_ne_zero V k _ z a hz
noncomputable def rothKernelSetZero {m : ℕ} (z : RothBlockVars m) :
    MvPolynomial (RothBlockVars m) ℤ →ₐ[ℤ] MvPolynomial (RothBlockVars m) ℤ :=
  MvPolynomial.aeval (fun u => if u = z then 0 else MvPolynomial.X u)

theorem rothKernelSetZero_monomial {m : ℕ} (z : RothBlockVars m)
    (b : RothBlockVars m →₀ ℕ) (c : ℤ) :
    rothKernelSetZero z (MvPolynomial.monomial b c) =
      if b z = 0 then MvPolynomial.monomial b c else 0 := by
  classical
  rw [rothKernelSetZero, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  by_cases hb : b z = 0
  · rw [if_pos hb, MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    apply Finset.prod_congr rfl
    intro u _
    by_cases hu : u = z
    · simp [hu, hb]
    · simp [hu]
  · rw [if_neg hb]
    have hz : ∏ u : RothBlockVars m, (if u = z then 0 else MvPolynomial.X u) ^ b u =
        (0 : MvPolynomial (RothBlockVars m) ℤ) := by
      apply Finset.prod_eq_zero (Finset.mem_univ z)
      simp [hb]
    rw [hz, mul_zero]

theorem rothKernelSetZero_coeff {m : ℕ} (z : RothBlockVars m)
    (P : MvPolynomial (RothBlockVars m) ℤ) (b : RothBlockVars m →₀ ℕ) :
    (rothKernelSetZero z P).coeff b = if b z = 0 then P.coeff b else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [rothKernelSetZero_monomial]
    by_cases ha : a z = 0
    · rw [if_pos ha]
      by_cases hb : b z = 0
      · simp [hb]
      · have hab : a ≠ b := by intro h; subst a; exact hb ha
        simp [hb, hab]
    · rw [if_neg ha]
      by_cases hb : b z = 0
      · have hab : a ≠ b := by intro h; subst a; exact ha hb
        simp [hb, hab]
      · simp [hb]
  | add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, hP, hQ, MvPolynomial.coeff_add]
    split_ifs <;> simp

theorem rothKernel_exists_strip_specialize {m : ℕ}
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : P ≠ 0) (z : RothBlockVars m) :
    ∃ (a : ℕ) (Q : MvPolynomial (RothBlockVars m) ℤ),
      P = MvPolynomial.monomial (Finsupp.single z a) 1 * Q ∧
      rothKernelSetZero z Q ≠ 0 ∧
      (∀ b, (Q.coeff b).natAbs ≤ P.support.sup (fun c => (P.coeff c).natAbs)) ∧
      (∀ b, ((rothKernelSetZero z Q).coeff b).natAbs ≤ P.support.sup (fun c => (P.coeff c).natAbs)) := by
  classical
  have hs : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨b, hb, hmin⟩ := Finset.exists_mem_eq_inf' hs (fun b => b z)
  let a := b z
  let s : RothBlockVars m →₀ ℕ := Finsupp.single z a
  let Q := MvPolynomial.divMonomial P s
  have hle (c) (hc : c ∈ P.support) : s ≤ c := by
    rw [Finsupp.single_le_iff]
    change b z ≤ c z
    rw [← hmin]
    exact Finset.inf'_le (fun b => b z) hc
  have he : P = MvPolynomial.monomial s 1 * Q := by
    apply MvPolynomial.ext
    intro c
    rw [MvPolynomial.coeff_monomial_mul']
    by_cases hsc : s ≤ c
    · rw [if_pos hsc, one_mul, MvPolynomial.coeff_divMonomial,
        add_tsub_cancel_of_le hsc]
    · rw [if_neg hsc]
      exact MvPolynomial.not_mem_support_iff.mp (fun hc => hsc (hle c hc))
  have hQ : (rothKernelSetZero z Q).coeff (b - s) ≠ 0 := by
    rw [rothKernelSetZero_coeff]
    have hz : (b - s) z = 0 := by simp [s, a, Finsupp.sub_apply]
    rw [if_pos hz, MvPolynomial.coeff_divMonomial, add_tsub_cancel_of_le (hle b hb)]
    exact MvPolynomial.mem_support_iff.mp hb
  have hcoef (c : RothBlockVars m →₀ ℕ) :
      (Q.coeff c).natAbs ≤ P.support.sup (fun c => (P.coeff c).natAbs) := by
    rw [MvPolynomial.coeff_divMonomial]
    by_cases hc : s + c ∈ P.support
    · exact Finset.le_sup (f := fun c => (P.coeff c).natAbs) hc
    · simp [MvPolynomial.not_mem_support_iff.mp hc]
  refine ⟨a, Q, he, ?_, hcoef, ?_⟩
  · intro hz
    exact hQ (by rw [hz, MvPolynomial.coeff_zero])
  · intro c
    rw [rothKernelSetZero_coeff]
    split_ifs
    · exact hcoef c
    · simp

def rothBlockHomogeneous {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars m) ℤ) : Prop :=
  ∀ b ∈ P.support, ∀ h, ∑ i : Fin 3, b (h, i) = r h

theorem rothBlock_single_sum {m : ℕ} (z : RothBlockVars m) (a : ℕ) (h : Fin m) :
    ∑ i : Fin 3, (Finsupp.single z a : RothBlockVars m →₀ ℕ) (h, i) =
      if h = z.1 then a else 0 := by
  rcases z with ⟨g, j⟩
  by_cases hh : h = g
  · subst h
    simp [Finsupp.single_apply, Prod.mk.injEq]
  · simp [Finsupp.single_apply, Prod.mk.injEq, hh, Ne.symm hh]

theorem rothBlockHomogeneous_divMonomial {m : ℕ}
    (P : MvPolynomial (RothBlockVars m) ℤ) (r : Fin m → ℕ)
    (hP : rothBlockHomogeneous r P) (z : RothBlockVars m) (a : ℕ) :
    rothBlockHomogeneous (fun h => r h - if h = z.1 then a else 0)
      (MvPolynomial.divMonomial P (Finsupp.single z a)) := by
  intro b hb h
  have hbP : Finsupp.single z a + b ∈ P.support := by
    rw [MvPolynomial.mem_support_iff] at hb ⊢
    exact hb
  have hh := hP _ hbP h
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, rothBlock_single_sum] at hh
  change (∑ i : Fin 3, b (h, i)) = r h - (if h = z.1 then a else 0)
  by_cases hz : h = z.1 <;> simp only [hz, if_true, if_false] at hh ⊢ <;> omega

theorem rothBlockHomogeneous_setZero {m : ℕ}
    (P : MvPolynomial (RothBlockVars m) ℤ) (r : Fin m → ℕ)
    (hP : rothBlockHomogeneous r P) (z : RothBlockVars m) :
    rothBlockHomogeneous r (rothKernelSetZero z P) := by
  intro b hb h
  have hb' : b ∈ P.support := by
    rw [MvPolynomial.mem_support_iff] at hb ⊢
    rw [rothKernelSetZero_coeff] at hb
    split_ifs at hb
    · exact hb
    · contradiction
  exact hP b hb' h

theorem rothKernelSetZero_derivative {m : ℕ}
    (P : MvPolynomial (RothBlockVars m) ℤ) (J : RothBlockVars m →₀ ℕ)
    (z : RothBlockVars m) (hJ : J z = 0) :
    rothKernelSetZero z (rothBlockIntegerDividedDerivative J P) =
      rothBlockIntegerDividedDerivative J (rothKernelSetZero z P) := by
  apply MvPolynomial.ext
  intro b
  rw [rothKernelSetZero_coeff, rothBlockIntegerDividedDerivative_coeff,
    rothBlockIntegerDividedDerivative_coeff, rothKernelSetZero_coeff]
  simp only [Finsupp.add_apply, hJ, add_zero]
  split_ifs <;> simp

noncomputable def rothKernelZeroRow {m : ℕ} (V : Fin m → Fin 3 → ℤ) (z : RothBlockVars m) :
    Fin m → Fin 3 → ℤ := fun h i => if (h, i) = z then 0 else V h i

noncomputable def rothKernelSetZeroRat {m : ℕ} (z : RothBlockVars m) :
    MvPolynomial (RothBlockVars m) ℚ →ₐ[ℚ] MvPolynomial (RothBlockVars m) ℚ :=
  MvPolynomial.aeval (fun u => if u = z then 0 else MvPolynomial.X u)

theorem rothKernelChart_specialize {m : ℕ}
    (V : Fin m → Fin 3 → ℤ) (k : Fin m → Fin 3) (z u : RothBlockVars m)
    (hz : z.2 ≠ k z.1) :
    rothKernelSetZeroRat z (rothKernelChart V k u) =
      if u = z then 0 else rothKernelChart (rothKernelZeroRow V z) k u := by
  classical
  by_cases hu : u = z
  · subst u
    simp [rothKernelChart, hz, rothKernelSetZeroRat]
  · rw [if_neg hu]
    by_cases hp : u.2 = k u.1
    · have hpz : (u.1, k u.1) ≠ z := by
        intro he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        exact hz (by simpa only [← h1] using h2.symm)
      simp only [rothKernelChart, hp, if_true, map_neg, map_sum, map_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [rothKernelSetZeroRat, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        rothKernelZeroRow, if_neg hpz]
      by_cases hiZ : (u.1, i) = z
      · simp [hiZ]
      · simp [hiZ]
    · simp [rothKernelChart, hp, hu, rothKernelSetZeroRat]

theorem rothKernelRestriction_specialize {m : ℕ}
    (V : Fin m → Fin 3 → ℤ) (k : Fin m → Fin 3) (z : RothBlockVars m)
    (hz : z.2 ≠ k z.1) (P : MvPolynomial (RothBlockVars m) ℤ) :
    rothKernelSetZeroRat z (rothKernelRestriction V k P) =
      rothKernelRestriction (rothKernelZeroRow V z) k (rothKernelSetZero z P) := by
  have he : (rothKernelSetZeroRat z).toRingHom.comp
      (MvPolynomial.eval₂Hom (Int.castRingHom _) (rothKernelChart V k)) =
      (MvPolynomial.eval₂Hom (Int.castRingHom _) (rothKernelChart (rothKernelZeroRow V z) k)).comp
        (rothKernelSetZero z).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rothKernelSetZeroRat, rothKernelSetZero]
    · intro u
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change rothKernelSetZeroRat z (rothKernelChart V k u) = _
      rw [rothKernelChart_specialize V k z u hz]
      by_cases hu : u = z <;> simp [rothKernelSetZero, hu]
  exact RingHom.congr_fun he P

theorem rothKernelRestriction_lift_elimination {m : ℕ}
    (V : Fin m → Fin 3 → ℤ) (k : Fin m → Fin 3)
    (Q : MvPolynomial (RothBlockVars m) ℤ) (J : RothBlockVars m →₀ ℕ)
    (z : RothBlockVars m) (a : ℕ) (hz : z.2 ≠ k z.1) (hJ : J z = 0)
    (hne : rothKernelRestriction (rothKernelZeroRow V z) k
      (rothBlockIntegerDividedDerivative J (rothKernelSetZero z Q)) ≠ 0) :
    rothKernelRestriction V k (rothBlockIntegerDividedDerivative J
      (MvPolynomial.monomial (Finsupp.single z a) 1 * Q)) ≠ 0 := by
  apply (rothKernelRestriction_derivative_strip V k Q J z a hz hJ).mpr
  intro he
  apply hne
  rw [← rothKernelSetZero_derivative Q J z hJ, ← rothKernelRestriction_specialize V k z hz]
  rw [he, map_zero]

noncomputable def rothKernelZeroRows {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (S : Finset (RothBlockVars m)) : Fin m → Fin 3 → ℤ :=
  fun h i => if (h, i) ∈ S then 0 else V h i

set_option maxHeartbeats 1600000 in
theorem rothKernel_eliminate_discarded {m : ℕ} (S : Finset (RothBlockVars m)) :
    ∀ (V : Fin m → Fin 3 → ℤ) (k : Fin m → Fin 3),
    (∀ z ∈ S, z.2 ≠ k z.1) →
    ∀ (P : MvPolynomial (RothBlockVars m) ℤ) (r : Fin m → ℕ),
    P ≠ 0 → rothBlockHomogeneous r P →
    ∃ (R : MvPolynomial (RothBlockVars m) ℤ) (d : Fin m → ℕ),
      R ≠ 0 ∧ rothBlockHomogeneous d R ∧ (∀ h, d h ≤ r h) ∧
      (∀ b ∈ R.support, ∃ c ∈ P.support, b ≤ c ∧ R.coeff b = P.coeff c) ∧
      (∀ b ∈ R.support, ∀ z ∈ S, b z = 0) ∧
      (∀ J : RothBlockVars m →₀ ℕ, (∀ z ∈ S, J z = 0) →
        rothKernelRestriction (rothKernelZeroRows V S) k (rothBlockIntegerDividedDerivative J R) ≠ 0 →
          rothKernelRestriction V k (rothBlockIntegerDividedDerivative J P) ≠ 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro V k hfree P r hP hhom
    refine ⟨P, r, hP, hhom, fun _ => le_rfl, ?_, ?_, ?_⟩
    · intro b hb
      exact ⟨b, hb, le_rfl, rfl⟩
    · simp
    · intro J hJ hne
      simpa [rothKernelZeroRows] using hne
  | @insert z S hzS ih =>
    intro V k hfree P r hP hhom
    obtain ⟨a, Q, he, hR0, hcoefQ, hcoefR0⟩ := rothKernel_exists_strip_specialize P hP z
    let s : RothBlockVars m →₀ ℕ := Finsupp.single z a
    have hQdiv : Q = MvPolynomial.divMonomial P s := by
      rw [he, MvPolynomial.divMonomial_monomial_mul]
    have hqcoef (b) : Q.coeff b = P.coeff (s + b) := by
      rw [he, MvPolynomial.coeff_monomial_mul, one_mul]
    let r0 : Fin m → ℕ := fun h => r h - if h = z.1 then a else 0
    have hhom0 : rothBlockHomogeneous r0 (rothKernelSetZero z Q) := by
      apply rothBlockHomogeneous_setZero
      rw [hQdiv]
      exact rothBlockHomogeneous_divMonomial P r hhom z a
    obtain ⟨R, d, hR, hhomR, hdr, htrack, hzero, hlift⟩ := ih (rothKernelZeroRow V z) k
      (fun w hw => hfree w (Finset.mem_insert_of_mem hw)) (rothKernelSetZero z Q) r0 hR0 hhom0
    have hv : rothKernelZeroRows (rothKernelZeroRow V z) S = rothKernelZeroRows V (insert z S) := by
      funext h i
      by_cases hmem : (h, i) ∈ S <;> by_cases heq : (h, i) = z <;>
        simp [rothKernelZeroRows, rothKernelZeroRow, hmem, heq]
    have hsource (b) (hb : b ∈ (rothKernelSetZero z Q).support) :
        b z = 0 ∧ s + b ∈ P.support ∧ (rothKernelSetZero z Q).coeff b = P.coeff (s + b) := by
      have hne := MvPolynomial.mem_support_iff.mp hb
      rw [rothKernelSetZero_coeff] at hne
      by_cases hbz : b z = 0
      · refine ⟨hbz, ?_, ?_⟩
        · rw [MvPolynomial.mem_support_iff]
          simpa only [if_pos hbz, hqcoef] using hne
        · rw [rothKernelSetZero_coeff, if_pos hbz, hqcoef]
      · simp [hbz] at hne
    refine ⟨R, d, hR, hhomR, ?_, ?_, ?_, ?_⟩
    · intro h
      exact (hdr h).trans (Nat.sub_le _ _)
    · intro b hb
      obtain ⟨c, hc, hbc, hec⟩ := htrack b hb
      obtain ⟨hcz, hcP, hcEq⟩ := hsource c hc
      refine ⟨s + c, hcP, hbc.trans ?_, hec.trans hcEq⟩
      exact le_add_left le_rfl
    · intro b hb w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · obtain ⟨c, hc, hbc, hec⟩ := htrack b hb
        have hcz := (hsource c hc).1
        exact Nat.eq_zero_of_le_zero (by simpa [hcz] using hbc w)
      · exact hzero b hb w hw
    · intro J hJ hne
      rw [← hv] at hne
      have hh := hlift J (fun w hw => hJ w (Finset.mem_insert_of_mem hw)) hne
      rw [he]
      exact rothKernelRestriction_lift_elimination V k Q J z a
        (hfree z (Finset.mem_insert_self _ _)) (hJ z (Finset.mem_insert_self _ _)) hh

noncomputable def rothKernelPivotExponent {m : ℕ} (k : Fin m → Fin 3)
    (b : RothBlockVars m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun h => b (h, k h))

noncomputable def rothKernelDehom {m : ℕ} (k : Fin m → Fin 3)
    (P : MvPolynomial (RothBlockVars m) ℤ) : MvPolynomial (Fin m) ℤ :=
  P.sum fun b c => MvPolynomial.monomial (rothKernelPivotExponent k b) c

theorem rothKernel_binary_sum (B : Fin 3 → ℕ) (i j : Fin 3) (hij : i ≠ j)
    (hz : ∀ u, u ≠ i → u ≠ j → B u = 0) : ∑ u : Fin 3, B u = B i + B j := by
  calc
    _ = ∑ u : Fin 3, ((if u = i then B i else 0) + (if u = j then B j else 0)) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hi : u = i <;> by_cases hj : u = j <;> simp_all
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem rothKernelPivotExponent_injective {m : ℕ}
    (k j : Fin m → Fin 3) (hkj : ∀ h, k h ≠ j h)
    (P : MvPolynomial (RothBlockVars m) ℤ) (r : Fin m → ℕ)
    (hhom : rothBlockHomogeneous r P)
    (hzero : ∀ b ∈ P.support, ∀ h i, i ≠ k h → i ≠ j h → b (h, i) = 0) :
    Set.InjOn (rothKernelPivotExponent k) (P.support : Set (RothBlockVars m →₀ ℕ)) := by
  intro b hb c hc he
  have hp (h) : b (h, k h) = c (h, k h) := congrArg (fun a : Fin m →₀ ℕ => a h) he
  have hj (h) : b (h, j h) = c (h, j h) := by
    have hb' := rothKernel_binary_sum (fun i => b (h, i)) (k h) (j h) (hkj h) (hzero b hb h)
    have hc' := rothKernel_binary_sum (fun i => c (h, i)) (k h) (j h) (hkj h) (hzero c hc h)
    dsimp only at hb' hc'
    have hbh := hhom b hb h
    have hch := hhom c hc h
    rw [hb'] at hbh
    rw [hc'] at hch
    have hpk := hp h
    omega
  ext ⟨h, i⟩
  by_cases hi : i = k h
  · simpa [hi] using hp h
  · by_cases hi' : i = j h
    · simpa [hi'] using hj h
    · rw [hzero b hb h i hi hi', hzero c hc h i hi hi']

theorem rothKernelDehom_coeff_at {m : ℕ} (k : Fin m → Fin 3)
    (P : MvPolynomial (RothBlockVars m) ℤ)
    (hinj : Set.InjOn (rothKernelPivotExponent k) (P.support : Set (RothBlockVars m →₀ ℕ)))
    (b : RothBlockVars m →₀ ℕ) (hb : b ∈ P.support) :
    (rothKernelDehom k P).coeff (rothKernelPivotExponent k b) = P.coeff b := by
  classical
  rw [rothKernelDehom, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c hc hcb
    have hne : rothKernelPivotExponent k c ≠ rothKernelPivotExponent k b :=
      fun he => hcb (hinj hc hb he)
    simp [MvPolynomial.coeff_monomial, hne]
  · exact fun h => (h hb).elim

theorem rothKernelDehom_nonzero_height_degree {m : ℕ}
    (k j : Fin m → Fin 3) (hkj : ∀ h, k h ≠ j h)
    (P : MvPolynomial (RothBlockVars m) ℤ) (hP : P ≠ 0) (r : Fin m → ℕ)
    (hhom : rothBlockHomogeneous r P)
    (hzero : ∀ b ∈ P.support, ∀ h i, i ≠ k h → i ≠ j h → b (h, i) = 0) :
    rothKernelDehom k P ≠ 0 ∧
    rothIntegerHeight (rothKernelDehom k P) ≤ P.support.sup (fun b => (P.coeff b).natAbs) ∧
    (∀ a ∈ (rothKernelDehom k P).support, ∀ h, a h ≤ r h) := by
  classical
  have hinj := rothKernelPivotExponent_injective k j hkj P r hhom hzero
  have hcoeff (a : Fin m →₀ ℕ) (ha : a ∈ (rothKernelDehom k P).support) :
      ∃ b ∈ P.support, rothKernelPivotExponent k b = a := by
    have hne := MvPolynomial.mem_support_iff.mp ha
    rw [rothKernelDehom, MvPolynomial.sum_def, MvPolynomial.coeff_sum] at hne
    obtain ⟨b, hb, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨b, hb, ?_⟩
    by_contra h
    exact hnonzero (by simp [MvPolynomial.coeff_monomial, h])
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr hP
    intro he
    have hh := rothKernelDehom_coeff_at k P hinj b hb
    rw [he, MvPolynomial.coeff_zero] at hh
    exact (MvPolynomial.mem_support_iff.mp hb) hh.symm
  · apply Finset.sup_le
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hcoeff a ha
    rw [rothKernelDehom_coeff_at k P hinj b hb]
    exact Finset.le_sup (f := fun b => (P.coeff b).natAbs) hb
  · intro a ha h
    obtain ⟨b, hb, rfl⟩ := hcoeff a ha
    have hle : b (h, k h) ≤ ∑ i : Fin 3, b (h, i) :=
      Finset.single_le_sum (f := fun i : Fin 3 => b (h, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (k h))
    simpa [rothKernelPivotExponent, hhom b hb h] using hle

noncomputable def rothKernelPivotOrder {m : ℕ} (k : Fin m → Fin 3)
    (a : Fin m →₀ ℕ) : RothBlockVars m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k u.1 then a u.1 else 0)

theorem rothKernelDehom_monomial {m : ℕ} (k : Fin m → Fin 3)
    (b : RothBlockVars m →₀ ℕ) (c : ℤ) :
    rothKernelDehom k (MvPolynomial.monomial b c) =
      MvPolynomial.monomial (rothKernelPivotExponent k b) c := by
  simp [rothKernelDehom]

theorem rothKernelDehom_add {m : ℕ} (k : Fin m → Fin 3)
    (P Q : MvPolynomial (RothBlockVars m) ℤ) :
    rothKernelDehom k (P + Q) = rothKernelDehom k P + rothKernelDehom k Q := by
  apply Finsupp.sum_add_index'
  · intro b
    simp
  · intro b c d
    simp [map_add]

theorem rothKernel_scalarDerivative_add {m : ℕ} (a : Fin m →₀ ℕ)
    (P Q : MvPolynomial (Fin m) ℤ) :
    rothIntegerDividedDerivative a (P + Q) =
      rothIntegerDividedDerivative a P + rothIntegerDividedDerivative a Q := by
  apply MvPolynomial.ext
  intro b
  simp only [rothIntegerDividedDerivative_coeff, MvPolynomial.coeff_add]
  ring

theorem rothBlockIntegerDividedDerivative_add {m : ℕ} (J : RothBlockVars m →₀ ℕ)
    (P Q : MvPolynomial (RothBlockVars m) ℤ) :
    rothBlockIntegerDividedDerivative J (P + Q) =
      rothBlockIntegerDividedDerivative J P + rothBlockIntegerDividedDerivative J Q := by
  apply MvPolynomial.ext
  intro b
  simp only [rothBlockIntegerDividedDerivative_coeff, MvPolynomial.coeff_add]
  ring

theorem rothKernelDehom_derivative {m : ℕ} (k : Fin m → Fin 3)
    (P : MvPolynomial (RothBlockVars m) ℤ) (a : Fin m →₀ ℕ) :
    rothIntegerDividedDerivative a (rothKernelDehom k P) =
      rothKernelDehom k (rothBlockIntegerDividedDerivative (rothKernelPivotOrder k a) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [rothKernelDehom_monomial]
    simp only [rothIntegerDividedDerivative, rothBlockIntegerDividedDerivative,
      MvPolynomial.sum_monomial_eq, zero_mul, MvPolynomial.monomial_zero]
    rw [rothKernelDehom_monomial]
    have he : rothKernelPivotExponent k (b - rothKernelPivotOrder k a) =
        rothKernelPivotExponent k b - a := by
      ext h
      simp [rothKernelPivotExponent, rothKernelPivotOrder, Finsupp.sub_apply]
    rw [he]
    congr 2
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro h _
    symm
    calc
      ∏ i : Fin 3, (Nat.choose (b (h, i)) (rothKernelPivotOrder k a (h, i)) : ℤ) =
          (Nat.choose (b (h, k h)) (rothKernelPivotOrder k a (h, k h)) : ℤ) := by
        apply Finset.prod_eq_single (k h)
        · intro i hi hine
          simp [rothKernelPivotOrder, hine]
        · simp
      _ = _ := by simp [rothKernelPivotExponent, rothKernelPivotOrder]
  | add P Q hP hQ =>
    rw [rothKernelDehom_add, rothKernel_scalarDerivative_add,
      rothBlockIntegerDividedDerivative_add, rothKernelDehom_add, hP, hQ]

theorem rothKernelPivotOrder_budget {m : ℕ} (k : Fin m → Fin 3)
    (a : Fin m →₀ ℕ) (r : Fin m → ℕ) :
    (∑ h : Fin m, (∑ i : Fin 3, (rothKernelPivotOrder k a (h, i) : ℝ)) / (r h : ℝ)) =
      ∑ h : Fin m, (a h : ℝ) / (r h : ℝ) := by
  apply Finset.sum_congr rfl
  intro h _
  simp [rothKernelPivotOrder]

theorem rothKernelDehom_eval {m : ℕ} (k : Fin m → Fin 3)
    (P : MvPolynomial (RothBlockVars m) ℤ) (x : Fin m → ℚ) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) x (rothKernelDehom k P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun u => if u.2 = k u.1 then x u.1 else 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [rothKernelDehom_monomial, MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial]
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp),
      Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
    congr 1
    apply Finset.prod_congr rfl
    intro h _
    symm
    calc
      ∏ i : Fin 3, (if i = k h then x h else 1) ^ b (h, i) =
          (if k h = k h then x h else 1) ^ b (h, k h) := by
        apply Finset.prod_eq_single (k h)
        · intro i hi hine
          simp [hine]
        · simp
      _ = _ := by simp [rothKernelPivotExponent]
  | add P Q hP hQ =>
    rw [rothKernelDehom_add, MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, hP, hQ]

theorem rothKernelRestriction_eval {m : ℕ} (V : Fin m → Fin 3 → ℤ)
    (k : Fin m → Fin 3) (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.eval₂ (RingHom.id ℚ) (fun _ => 1) (rothKernelRestriction V k P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun u => if u.2 = k u.1 then
          -(∑ i ∈ Finset.univ.erase (k u.1), (V u.1 i : ℚ) / (V u.1 (k u.1) : ℚ)) else 1) P := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ : RothBlockVars m => (1 : ℚ))
  have hc : f.comp (Int.castRingHom (MvPolynomial (RothBlockVars m) ℚ)) = Int.castRingHom ℚ := by
    ext n
    simp [f]
  change f (MvPolynomial.eval₂Hom (Int.castRingHom _) (rothKernelChart V k) P) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  change MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun u => f (rothKernelChart V k u)) P = _
  congr 1
  funext u
  by_cases hp : u.2 = k u.1
  · simp only [rothKernelChart, if_pos hp, map_neg, map_sum, map_mul]
    simp only [f, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, mul_one]
  · simp only [rothKernelChart, if_neg hp, f, MvPolynomial.eval₂Hom_X']

noncomputable def rothKernelDiscarded {m : ℕ} (k j : Fin m → Fin 3) : Finset (RothBlockVars m) :=
  Finset.univ.filter (fun u => u.2 ≠ k u.1 ∧ u.2 ≠ j u.1)

theorem rothKernelRestriction_binary_eval {m : ℕ}
    (V : Fin m → Fin 3 → ℤ) (k j : Fin m → Fin 3) (hkj : ∀ h, k h ≠ j h)
    (P : MvPolynomial (RothBlockVars m) ℤ) :
    MvPolynomial.eval₂ (RingHom.id ℚ) (fun _ => 1)
      (rothKernelRestriction (rothKernelZeroRows V (rothKernelDiscarded k j)) k P) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun u => if u.2 = k u.1 then -(V u.1 (j u.1) : ℚ) / (V u.1 (k u.1) : ℚ) else 1) P := by
  rw [rothKernelRestriction_eval]
  congr 1
  funext u
  split_ifs
  · congr 1
    have he : (∑ i ∈ Finset.univ.erase (k u.1),
        ((rothKernelZeroRows V (rothKernelDiscarded k j)) u.1 i : ℚ) /
        ((rothKernelZeroRows V (rothKernelDiscarded k j)) u.1 (k u.1) : ℚ)) =
        (V u.1 (j u.1) : ℚ) / (V u.1 (k u.1) : ℚ) := by
      rw [Finset.sum_eq_single (j u.1)]
      · simp [rothKernelZeroRows, rothKernelDiscarded]
      · intro i hi hij
        have hik : i ≠ k u.1 := (Finset.mem_erase.mp hi).1
        simp [rothKernelZeroRows, rothKernelDiscarded, hik, hij]
      · intro hj
        exact False.elim (hj (Finset.mem_erase.mpr ⟨Ne.symm (hkj u.1), Finset.mem_univ _⟩))
    simpa [neg_div] using congrArg Neg.neg he
  · rfl

noncomputable def rothKernelRowHeight (V : Fin 3 → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (V i).natAbs)

noncomputable def rothKernelBlockHeight {m : ℕ} (P : MvPolynomial (RothBlockVars m) ℤ) : ℕ :=
  P.support.sup (fun b => (P.coeff b).natAbs)

set_option maxHeartbeats 2400000 in
theorem roth_full_kernel_omega65_nonvanishing
    (m : ℕ) (hm : 0 < m) (theta Gamma : ℝ)
    (ht : 0 < theta) (ht' : theta < 1 / 12) (hG : 0 < Gamma) (hG' : Gamma ≤ 2)
    (r : Fin m → ℕ) (V : Fin m → Fin 3 → ℤ) (P : MvPolynomial (RothBlockVars m) ℤ)
    (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val + 1 < m),
      (r ⟨h.val + 1, hh⟩ : ℝ) ≤ rothInductionOmega m theta * (r h : ℝ))
    (hrow : ∀ h, (∃ i, V h i ≠ 0) ∧ Ideal.span (Set.range (V h)) = ⊤)
    (hgrowth : ∀ h : Fin m, h.val ≠ 0 →
      Real.rpow (rothKernelRowHeight (V ⟨0, hm⟩) : ℝ) ((r ⟨0, hm⟩ : ℝ) * Gamma) ≤
        (rothKernelRowHeight (V h) : ℝ) ^ r h)
    (hden : ∀ h, (2 : ℝ) ^ (12 * m) ≤ Real.rpow (rothKernelRowHeight (V h) : ℝ)
      (rothInductionOmega m theta * Gamma))
    (hP : P ≠ 0) (hhom : rothBlockHomogeneous r P)
    (hheight : (rothKernelBlockHeight P : ℝ) ^ 4 ≤
      Real.rpow (rothKernelRowHeight (V ⟨0, hm⟩) : ℝ)
        (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * Gamma)) :
    ∃ (J : RothBlockVars m →₀ ℕ) (k : Fin m → Fin 3),
      (∑ h : Fin m, (∑ i : Fin 3, (J (h, i) : ℝ)) / (r h : ℝ)) ≤ theta ∧
      (∀ h, V h (k h) ≠ 0) ∧
      rothKernelRestriction V k (rothBlockIntegerDividedDerivative J P) ≠ 0 := by
  classical
  choose k j p q hkj hk hmax hq hcop heval hqu hql using
    (fun h => rothPrimitiveTriple_rational_parameters (V h) (hrow h).2 (hrow h).1)
  have hmaxeq (h) : rothKernelRowHeight (V h) = (V h (k h)).natAbs := by
    apply le_antisymm
    · exact Finset.sup_le (fun i _ => hmax h i)
    · exact Finset.le_sup (f := fun i => (V h i).natAbs) (Finset.mem_univ (k h))
  let H : Fin m → ℝ := fun h => (rothKernelRowHeight (V h) : ℝ)
  let Q : Fin m → ℝ := fun h => ((q h).natAbs : ℝ)
  have hH (h) : 1 ≤ H h := by
    dsimp [H]
    rw [hmaxeq]
    exact_mod_cast (show 1 ≤ (V h (k h)).natAbs from Int.natAbs_pos.mpr (hk h))
  have hupper (h) : Q h ≤ H h := by
    dsimp [Q, H]
    rw [hmaxeq]
    exact_mod_cast hqu h
  have hlower (h) : H h ≤ Q h ^ 2 := by
    dsimp [Q, H]
    rw [hmaxeq]
    exact_mod_cast hql h
  have hQeq (h) : Q h = |(q h : ℝ)| := by simp only [Q, Int.cast_natAbs, Int.cast_abs]
  have hg : ∀ h : Fin m, h.val ≠ 0 →
      (H ⟨0, hm⟩) ^ ((r ⟨0, hm⟩ : ℝ) * Gamma) ≤ (H h) ^ (r h : ℝ) := by
    intro h hh
    rw [Real.rpow_natCast]
    exact hgrowth h hh
  obtain ⟨hC, hC', hgQ, hdQ, hHP⟩ := rothKernel_scalar_budgets m hm theta Gamma ht hG hG' r H Q
    (rothKernelBlockHeight P) hH (fun h => by dsimp [Q]; positivity) hupper hlower hg hden
    (by positivity) hheight
  let S := rothKernelDiscarded k j
  obtain ⟨R, d, hR, hhomR, hdr, htrack, hzero, hlift⟩ := rothKernel_eliminate_discarded S V k
    (fun z hz => (Finset.mem_filter.mp hz).2.1) P r hP hhom
  have hbinary : ∀ b ∈ R.support, ∀ h i, i ≠ k h → i ≠ j h → b (h, i) = 0 := by
    intro b hb h i hik hij
    exact hzero b hb (h, i) (by simp [S, rothKernelDiscarded, hik, hij])
  obtain ⟨hF, hHF, hdegF⟩ := rothKernelDehom_nonzero_height_degree k j hkj R hR d hhomR hbinary
  have hHR : R.support.sup (fun b => (R.coeff b).natAbs) ≤ rothKernelBlockHeight P := by
    apply Finset.sup_le
    intro b hb
    obtain ⟨c, hc, hbc, he⟩ := htrack b hb
    rw [he]
    exact Finset.le_sup (f := fun c => (P.coeff c).natAbs) hc
  have hFheight : (rothIntegerHeight (rothKernelDehom k R) : ℝ) ≤
      Real.rpow |(q ⟨0, hm⟩ : ℝ)| (rothInductionOmega m theta * (r ⟨0, hm⟩ : ℝ) * (Gamma / 2)) := by
    have hh : (rothIntegerHeight (rothKernelDehom k R) : ℝ) ≤ rothKernelBlockHeight P := by
      exact_mod_cast hHF.trans hHR
    rw [hQeq] at hHP
    exact hh.trans hHP
  obtain ⟨a, ha, hne⟩ := roth_scalar_omega65_nonvanishing m hm theta (Gamma / 2) ht ht' hC hC'
    r p q (rothKernelDehom k R) hr hsep (fun h => ⟨hq h, hcop h⟩)
    (by simpa only [hQeq, Real.rpow_natCast] using hgQ)
    (by simpa only [hQeq] using hdQ) hF (fun b hb h => (hdegF b hb h).trans (hdr h)) hFheight
  let J := rothKernelPivotOrder k a
  have hneR : rothKernelRestriction (rothKernelZeroRows V S) k
      (rothBlockIntegerDividedDerivative J R) ≠ 0 := by
    rw [rothKernelDehom_derivative, rothKernelDehom_eval] at hne
    have hp : (fun u : RothBlockVars m => if u.2 = k u.1 then (p u.1 : ℚ) / (q u.1 : ℚ) else 1) =
        (fun u => if u.2 = k u.1 then -(V u.1 (j u.1) : ℚ) / (V u.1 (k u.1) : ℚ) else 1) := by
      funext u
      by_cases hu : u.2 = k u.1 <;> simp only [hu, if_true, if_false]
      exact heval u.1
    rw [hp] at hne
    intro he
    apply hne
    rw [← rothKernelRestriction_binary_eval V k j hkj, he]
    simp
  refine ⟨J, k, ?_, hk, ?_⟩
  · simpa only [J, rothKernelPivotOrder_budget] using ha
  · apply hlift J ?_ hneR
    intro z hz
    have hh := (Finset.mem_filter.mp hz).2.1
    simp [J, rothKernelPivotOrder, hh]

end JSP000334
