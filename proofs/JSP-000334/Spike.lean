import Counting
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace JSP000334

open scoped BigOperators

def Nondegenerate {m : ℕ} (x : Fin m → ℚ) : Prop :=
  ∀ I : Finset (Fin m), I.Nonempty → I ≠ Finset.univ → ∑ i ∈ I, x i ≠ 0

def normalize {m : ℕ} (x : Fin m → ℚ) (j : Fin m) : Fin m → ℚ :=
  fun i => x i / x j

theorem normalize_coordinate {m : ℕ} (x : Fin m → ℚ) (j : Fin m)
    (hj : x j ≠ 0) : normalize x j j = 1 := by
  exact div_self hj

theorem normalize_sum {m : ℕ} (x : Fin m → ℚ) (j : Fin m)
    (hx : ∑ i, x i = 0) : ∑ i, normalize x j i = 0 := by
  simp only [normalize, ← Finset.sum_div, hx, zero_div]

theorem normalize_nondegenerate {m : ℕ} (x : Fin m → ℚ) (j : Fin m)
    (hj : x j ≠ 0) (hx : Nondegenerate x) : Nondegenerate (normalize x j) := by
  intro I hI hproper
  simpa only [normalize, ← Finset.sum_div, ne_eq, div_eq_zero_iff, hj,
    or_false] using hx I hI hproper

theorem normalize_units {m : ℕ} (G : Subgroup ℚˣ) (x : Fin m → G) (j : Fin m)
    (i : Fin m) :
    normalize (fun k => ((x k : ℚˣ) : ℚ)) j i = (((x i / x j : G) : ℚˣ) : ℚ) := by
  simp [normalize]

def normalizedRelations (G : Subgroup ℚˣ) (m : ℕ) : Set (Fin (m + 1) → ℚ) :=
  {x | x 0 = 1 ∧ (∀ i, ∃ u : G, (u : ℚˣ).val = x i) ∧
    (∑ i, x i = 0) ∧ Nondegenerate x}

def ProjectiveSUnitFiniteness : Prop :=
  ∀ generators : Finset ℚˣ, ∀ m : ℕ, 1 ≤ m → m ≤ 5 →
    (normalizedRelations (Subgroup.closure (generators : Set ℚˣ)) m).Finite

theorem normalize_mem_relations {m : ℕ} (G : Subgroup ℚˣ) (x : Fin (m + 1) → G)
    (hsum : ∑ i, ((x i : ℚˣ) : ℚ) = 0)
    (hnd : Nondegenerate (fun i => ((x i : ℚˣ) : ℚ))) :
    normalize (fun i => ((x i : ℚˣ) : ℚ)) 0 ∈ normalizedRelations G m := by
  have hzero : ((x 0 : ℚˣ) : ℚ) ≠ 0 := Units.ne_zero _
  refine ⟨normalize_coordinate _ _ hzero, ?_, normalize_sum _ _ hsum,
    normalize_nondegenerate _ _ hzero hnd⟩
  intro i
  exact ⟨x i / x 0, (normalize_units G x 0 i).symm⟩

theorem normalized_eq_iff_projectively_eq {m : ℕ} (x y : Fin m → ℚ) (j : Fin m)
    (hx : x j ≠ 0) (hy : y j ≠ 0) :
    normalize x j = normalize y j ↔ ∀ i, x i * y j = y i * x j := by
  constructor
  · intro h i
    exact (div_eq_div_iff hx hy).mp (congrFun h i)
  · intro h
    funext i
    exact (div_eq_div_iff hx hy).mpr (h i)

theorem normalized_two_term_finite (G : Subgroup ℚˣ) :
    (normalizedRelations G 1).Finite := by
  apply (Set.finite_singleton (![1, -1] : Fin 2 → ℚ)).subset
  intro x hx
  obtain ⟨hzero, _, hsum, _⟩ := hx
  have hone : x 1 = -1 := by
    simp [Fin.sum_univ_succ, hzero] at hsum
    linarith
  apply Set.mem_singleton_iff.mpr
  funext i
  fin_cases i <;> simp [hzero, hone]

def ThreeTermHyperplaneCover (G : Subgroup ℚˣ) : Prop :=
  ∃ B : Finset (ℚ × ℚ),
    (∀ p ∈ B, p ≠ (0, 0)) ∧
    ∀ x ∈ normalizedRelations G 2, ∃ p ∈ B, p.1 * x 0 + p.2 * x 1 = 0

theorem normalized_three_term_finite_of_hyperplane_cover (G : Subgroup ℚˣ)
    (hcover : ThreeTermHyperplaneCover G) : (normalizedRelations G 2).Finite := by
  classical
  obtain ⟨B, hproper, hcover⟩ := hcover
  let point : ℚ × ℚ → Fin 3 → ℚ := fun p => ![1, -(p.1 / p.2), p.1 / p.2 - 1]
  apply (B.finite_toSet.image point).subset
  intro x hx
  obtain ⟨p, hpB, hpx⟩ := hcover x hx
  obtain ⟨hx0, _, hxsum, _⟩ := hx
  have hp2 : p.2 ≠ 0 := by
    intro hp2
    have hp1 : p.1 = 0 := by simpa [hx0, hp2] using hpx
    exact hproper p hpB (Prod.ext hp1 hp2)
  have hx1 : x 1 = -(p.1 / p.2) := by
    rw [← neg_div]
    apply (eq_div_iff hp2).mpr
    rw [hx0, mul_one] at hpx
    nlinarith [hpx]
  have hx2 : x 2 = p.1 / p.2 - 1 := by
    simp [Fin.sum_univ_succ, hx0, hx1] at hxsum
    linarith
  refine ⟨p, hpB, ?_⟩
  funext i
  fin_cases i <;> simp [point, hx0, hx1, hx2]

theorem three_term_hyperplane_cover_iff_finite (G : Subgroup ℚˣ) :
    ThreeTermHyperplaneCover G ↔ (normalizedRelations G 2).Finite := by
  classical
  constructor
  · exact normalized_three_term_finite_of_hyperplane_cover G
  · intro hfinite
    let B := hfinite.toFinset.image (fun x => (-x 1, (1 : ℚ)))
    refine ⟨B, ?_, ?_⟩
    · intro p hp
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
      exact fun h => one_ne_zero (congrArg Prod.snd h)
    · intro x hx
      refine ⟨(-x 1, 1), Finset.mem_image.mpr ⟨x, hfinite.mem_toFinset.mpr hx, rfl⟩, ?_⟩
      simp [hx.1]

theorem positive_subsum {m : ℕ} (x : Fin m → ℚ) (hx : ∀ i, 0 < x i)
    (I : Finset (Fin m)) (hI : I.Nonempty) : 0 < ∑ i ∈ I, x i := by
  exact Finset.sum_pos (fun i _ => hx i) hI

theorem original_tw_lemma_counterexample :
    3 ^ 4 ∣ 2 ^ 27 + 1 ∧ ¬ (4 ≤ 3 : Prop) := by
  decide

theorem pointwise_finite_does_not_imply_uniform :
    (∀ n : ℕ, (↑(Finset.range n) : Set ℕ).Finite) ∧
      ¬ (∃ C : ℕ, ∀ n : ℕ, (↑(Finset.range n) : Set ℕ).ncard ≤ C) := by
  refine ⟨fun n => (Finset.range n).finite_toSet, ?_⟩
  rintro ⟨C, hC⟩
  have h := hC (C + 1)
  rw [Set.ncard_coe_Finset, Finset.card_range] at h
  omega

end JSP000334
