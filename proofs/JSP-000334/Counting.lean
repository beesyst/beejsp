import Statement
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace JSP000334

def summandList (r : Exponents) : List ℕ :=
  [2 ^ r.a, 3 ^ r.b, 2 ^ r.c * 3 ^ r.d]

def summands (r : Exponents) : Multiset ℕ := summandList r

def multisetSolutions (n : ℕ) : Set (Multiset ℕ) := summands '' solutions n

noncomputable def multisetCount (n : ℕ) : ℕ := (multisetSolutions n).ncard

theorem mixed_exponents_injective {a b c d : ℕ}
    (h : 2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d) : a = c ∧ b = d := by
  have h2 := congrArg (fun t : ℕ => t.factorization 2) h
  have h3 := congrArg (fun t : ℕ => t.factorization 3) h
  have p2 : Nat.Prime 2 := by decide
  have p3 : Nat.Prime 3 := by decide
  simp [Nat.factorization_mul (by positivity : 2 ^ a ≠ 0)
    (by positivity : 3 ^ b ≠ 0),
    Nat.factorization_mul (by positivity : 2 ^ c ≠ 0)
    (by positivity : 3 ^ d ≠ 0), p2.factorization_pow, p3.factorization_pow] at h2 h3
  exact ⟨h2, h3⟩

theorem summandList_injective : Function.Injective summandList := by
  intro r s h
  have hparts : 2 ^ r.a = 2 ^ s.a ∧ 3 ^ r.b = 3 ^ s.b ∧
      2 ^ r.c * 3 ^ r.d = 2 ^ s.c * 3 ^ s.d := by
    simpa [summandList] using h
  obtain ⟨hc, hd⟩ := mixed_exponents_injective hparts.2.2
  exact Exponents.ext (Nat.pow_right_injective (by norm_num) hparts.1)
    (Nat.pow_right_injective (by norm_num) hparts.2.1) hc hd

theorem multisetCount_le_tupleCount (n : ℕ) : multisetCount n ≤ tupleCount n :=
  Set.ncard_image_le (solutions_finite n)

theorem tupleCount_le_six_mul_multisetCount (n : ℕ) :
    tupleCount n ≤ 6 * multisetCount n := by
  classical
  let s := (solutions_finite n).toFinset
  have hfiber (m : Multiset ℕ) (hm : m ∈ s.image summands) :
      (s.filter (fun r => summands r = m)).card ≤ 6 := by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hm
    have hmap :
        (s.filter (fun t => summands t = summands r)).image summandList ⊆
          (summandList r).permutations.toFinset := by
      intro l hl
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl
      apply List.mem_toFinset.mpr
      apply List.mem_permutations.mpr
      exact Multiset.coe_eq_coe.mp (Finset.mem_filter.mp ht).2
    calc
      (s.filter (fun t => summands t = summands r)).card =
          ((s.filter (fun t => summands t = summands r)).image summandList).card :=
        (Finset.card_image_of_injective _ summandList_injective).symm
      _ ≤ (summandList r).permutations.toFinset.card := Finset.card_le_card hmap
      _ ≤ (summandList r).permutations.length := List.toFinset_card_le _
      _ = 6 := by simp [List.length_permutations, summandList, Nat.factorial]
  have hsum := Finset.card_eq_sum_card_image summands s
  have hbound : s.card ≤ 6 * (s.image summands).card := by
    rw [hsum]
    calc
      (∑ m ∈ s.image summands, (s.filter (fun r => summands r = m)).card) ≤
          ∑ _m ∈ s.image summands, 6 := Finset.sum_le_sum hfiber
      _ = 6 * (s.image summands).card := by simp [mul_comm]
  unfold tupleCount multisetCount multisetSolutions
  rw [Set.ncard_eq_toFinset_card _ (solutions_finite n),
    Set.ncard_eq_toFinset_card _ ((solutions_finite n).image summands),
    Set.Finite.toFinset_image]
  exact hbound

theorem counting_conventions_equivalent :
    NewmanConjecture ↔ ∃ C : ℕ, ∀ n : ℕ, 0 < n → multisetCount n ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun n hn => (multisetCount_le_tupleCount n).trans (hC n hn)⟩
  · rintro ⟨C, hC⟩
    exact ⟨6 * C, fun n hn => (tupleCount_le_six_mul_multisetCount n).trans
      (Nat.mul_le_mul_left 6 (hC n hn))⟩

end JSP000334
