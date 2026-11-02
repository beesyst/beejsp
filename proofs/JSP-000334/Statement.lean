import Mathlib.Data.Set.Card
import Mathlib.Data.Finite.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace JSP000334

@[ext] structure Exponents where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

def value (r : Exponents) : ℕ :=
  2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d

def solutions (n : ℕ) : Set Exponents := {r | value r = n}

noncomputable def tupleCount (n : ℕ) : ℕ := (solutions n).ncard

def NewmanConjecture : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 0 < n → tupleCount n ≤ C

def sourceValue (r : Exponents) : ℕ :=
  2 ^ r.a * 3 ^ r.b + 2 ^ r.c + 3 ^ r.d

def sourceToJsp (r : Exponents) : Exponents := ⟨r.c, r.d, r.a, r.b⟩

theorem sourceToJsp_involutive : Function.Involutive sourceToJsp := by
  intro r
  rfl

def sourceEquiv : Exponents ≃ Exponents :=
  ⟨sourceToJsp, sourceToJsp, sourceToJsp_involutive, sourceToJsp_involutive⟩

theorem sourceValue_eq (r : Exponents) : sourceValue r = value (sourceEquiv r) := by
  simp [sourceValue, value, sourceEquiv, sourceToJsp, add_comm, add_left_comm, add_assoc]

theorem source_parameterization_count (n : ℕ) :
    ({r | sourceValue r = n} : Set Exponents).ncard = tupleCount n := by
  rw [← Set.ncard_image_of_injective _ sourceEquiv.injective]
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (sourceValue_eq s).symm.trans hs
  · intro hr
    refine ⟨sourceEquiv.symm r, ?_, sourceEquiv.apply_symm_apply r⟩
    simpa only [sourceValue_eq, sourceEquiv.apply_symm_apply] using hr

theorem exponent_bounds {n : ℕ} {r : Exponents} (hr : r ∈ solutions n) :
    r.a < n ∧ r.b < n ∧ r.c < n ∧ r.d < n := by
  have hv : 2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d = n := hr
  have ha : 2 ^ r.a ≤ n := by
    rw [← hv]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hb : 3 ^ r.b ≤ n := by
    rw [← hv]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have hc : 2 ^ r.c ≤ 2 ^ r.c * 3 ^ r.d :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hd : 3 ^ r.d ≤ 2 ^ r.c * 3 ^ r.d :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hb2 := Nat.pow_le_pow_left (by norm_num : 2 ≤ 3) r.b
  have hd2 := Nat.pow_le_pow_left (by norm_num : 2 ≤ 3) r.d
  have hpa : r.a < 2 ^ r.a := Nat.lt_two_pow_self
  have hpb : r.b < 2 ^ r.b := Nat.lt_two_pow_self
  have hpc : r.c < 2 ^ r.c := Nat.lt_two_pow_self
  have hpd : r.d < 2 ^ r.d := Nat.lt_two_pow_self
  omega

theorem solutions_finite (n : ℕ) : (solutions n).Finite := by
  let box := (Set.Iio n).prod ((Set.Iio n).prod ((Set.Iio n).prod (Set.Iio n)))
  have hbox : box.Finite :=
    (Set.finite_Iio n).prod ((Set.finite_Iio n).prod
      ((Set.finite_Iio n).prod (Set.finite_Iio n)))
  apply (hbox.image (fun p => Exponents.mk p.1 p.2.1 p.2.2.1 p.2.2.2)).subset
  intro r hr
  exact ⟨(r.a, r.b, r.c, r.d), exponent_bounds hr, rfl⟩

theorem zero_solutions : solutions 0 = ∅ := by
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have := (exponent_bounds hr).1
  omega

end JSP000334
