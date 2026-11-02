import SubspaceBridge
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.IntervalCases

namespace JSP000334

private theorem three_pow_mod_eight (b : ℕ) : 3 ^ b % 8 = 3 ^ (b % 2) := by
  have h := Nat.mod_add_div b 2
  conv_lhs => rw [← h]
  rw [pow_add, pow_mul, Nat.mul_mod]
  norm_num only [show (3 : ℕ) ^ 2 = 9 from rfl]
  rw [Nat.pow_mod 9]
  norm_num
  have hr : b % 2 < 2 := Nat.mod_lt b (by decide)
  interval_cases hrem : b % 2 <;> norm_num

private theorem two_pow_mod_eight {a : ℕ} (ha : 3 ≤ a) : 2 ^ a % 8 = 0 := by
  exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 ha)

private theorem two_pow_mod_four {a : ℕ} (ha : 2 ≤ a) : 2 ^ a % 4 = 0 := by
  exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 ha)

private theorem adjacent_two_powers {r s : ℕ}
    (hr : 2 ≤ 2 ^ r) (hs : 2 ^ r + 2 = 2 ^ s) : 2 ^ r = 2 := by
  have hrsmall : r < 2 := by
    by_contra hrsmall
    have hr2 : 2 ≤ r := by omega
    have hr4 := two_pow_mod_four hr2
    by_cases hs2 : 2 ≤ s
    · have hs4 := two_pow_mod_four hs2
      omega
    · interval_cases s <;> norm_num at hs
      omega
  interval_cases r
  · norm_num at hr
  · norm_num

theorem two_pow_add_one_eq_three_pow_iff (a b : ℕ) :
    2 ^ a + 1 = 3 ^ b ↔ (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 2) := by
  constructor
  · intro h
    by_cases ha : a < 3
    · interval_cases a
      · have hmod := congrArg (fun n : ℕ => n % 3) h
        by_cases hb : b = 0
        · simp [hb] at h
        · have hd : 3 ∣ 3 ^ b := dvd_pow_self 3 hb
          have hm := Nat.mod_eq_zero_of_dvd hd
          norm_num at hmod
          omega
      · left
        refine ⟨rfl, Nat.pow_right_injective (a := 3) (by decide) ?_⟩
        simpa using h.symm
      · have hm := congrArg (fun n : ℕ => n % 8) h
        dsimp only at hm
        rw [three_pow_mod_eight] at hm
        have hr : b % 2 < 2 := Nat.mod_lt b (by decide)
        interval_cases hrem : b % 2 <;> norm_num [hrem] at hm
    · have ha3 : 3 ≤ a := by omega
      have hm := congrArg (fun n : ℕ => n % 8) h
      dsimp only at hm
      rw [Nat.add_mod, two_pow_mod_eight ha3, three_pow_mod_eight] at hm
      have hr : b % 2 < 2 := Nat.mod_lt b (by decide)
      have hbrem : b % 2 = 0 := by
        interval_cases hrem : b % 2 <;> norm_num [hrem] at hm ⊢
      have hb : b = 2 * (b / 2) := by omega
      let k := b / 2
      have hk : 1 ≤ k := by
        by_contra hk
        have hk0 : k = 0 := by omega
        change b = 2 * k at hb
        rw [hk0] at hb
        simp [hb] at h
      have hroot : 3 ≤ 3 ^ k := by
        exact Nat.pow_le_pow_right (n := 3) (by decide) hk
      have hsq : 2 ^ a + 1 = (3 ^ k) ^ 2 := by
        rw [hb, mul_comm 2, pow_mul] at h
        exact h
      have hprod : (3 ^ k - 1) * (3 ^ k + 1) = 2 ^ a := by
        nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 3 ^ k)]
      have hdlo : 3 ^ k - 1 ∣ 2 ^ a := by
        rw [← hprod]
        exact dvd_mul_right _ _
      have hdhi : 3 ^ k + 1 ∣ 2 ^ a := by
        rw [← hprod]
        exact dvd_mul_left _ _
      obtain ⟨r, _, heqr⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdlo
      obtain ⟨s, _, heqs⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdhi
      have hlow := adjacent_two_powers (r := r) (s := s) (by omega) (by omega)
      have hroot3 : 3 ^ k = 3 := by omega
      have hk1 : k = 1 := Nat.pow_right_injective (a := 3) (by decide) hroot3
      right
      have hb2 : b = 2 := by change b = 2 * k at hb; omega
      refine ⟨?_, hb2⟩
      apply Nat.pow_right_injective (by decide : 2 ≤ 2)
      norm_num [hb2] at h
      norm_num
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem three_pow_add_one_eq_two_pow_iff (a b : ℕ) :
    3 ^ b + 1 = 2 ^ a ↔ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1) := by
  constructor
  · intro h
    have hm := congrArg (fun n : ℕ => n % 8) h
    dsimp only at hm
    rw [Nat.add_mod, three_pow_mod_eight] at hm
    have ha : a < 3 := by
      by_contra ha
      rw [two_pow_mod_eight (by omega)] at hm
      have hr : b % 2 < 2 := Nat.mod_lt b (by decide)
      interval_cases hrem : b % 2 <;> norm_num [hrem] at hm
    interval_cases a
    · norm_num at h
    · left
      refine ⟨rfl, Nat.pow_right_injective (a := 3) (by decide) ?_⟩
      have heq : 3 ^ b = 1 := by norm_num only at h; omega
      simpa using heq
    · right
      refine ⟨rfl, Nat.pow_right_injective (a := 3) (by decide) ?_⟩
      norm_num at h ⊢
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

def Smooth23 (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3

theorem smooth23_factorization {n : ℕ} (hn : n ≠ 0) (hs : Smooth23 n) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by
  classical
  have hsupp : n.factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have h := Nat.mem_primeFactors.mp hp
    rcases hs p h.1 h.2.1 with rfl | rfl <;> simp
  calc
    n = n.factorization.prod (fun p k => p ^ k) :=
      (Nat.factorization_prod_pow_eq_self hn).symm
    _ = ∏ p ∈ ({2, 3} : Finset ℕ), p ^ n.factorization p :=
      Finsupp.prod_of_support_subset _ hsupp (fun p k => p ^ k) (by simp)
    _ = _ := by simp

private theorem smooth23_prime {n : ℕ} (hs : Smooth23 n) (hn : n ≠ 1) :
    2 ∣ n ∨ 3 ∣ n := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hn
  rcases hs p hp hd with rfl | rfl
  · exact Or.inl hd
  · exact Or.inr hd

private theorem no_common_prime {a b p : ℕ} (h : a.Coprime b) (hp : p.Prime) :
    ¬ (p ∣ a ∧ p ∣ b) := by
  rintro ⟨ha, hb⟩
  have hd := Nat.dvd_gcd ha hb
  rw [h.gcd_eq_one] at hd
  exact hp.not_dvd_one hd

theorem consecutive_smooth23_classification {n : ℕ} (hn : 0 < n)
    (hs : Smooth23 n) (ht : Smooth23 (n + 1)) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 8 := by
  by_cases h1 : n = 1
  · exact Or.inl h1
  have hc : n.Coprime (n + 1) := by simp
  have h2 := no_common_prime hc (by decide : Nat.Prime 2)
  have h3 := no_common_prime hc (by decide : Nat.Prime 3)
  have hn0 : n ≠ 0 := by omega
  have ht0 : n + 1 ≠ 0 := by omega
  have hsform := smooth23_factorization hn0 hs
  have htform := smooth23_factorization ht0 ht
  rcases smooth23_prime hs h1 with hs2 | hs3 <;>
    rcases smooth23_prime ht (by omega) with ht2 | ht3
  · exact False.elim (h2 ⟨hs2, ht2⟩)
  · have hn3 : ¬3 ∣ n := fun hd => h3 ⟨hd, ht3⟩
    have ht2' : ¬2 ∣ n + 1 := fun hd => h2 ⟨hs2, hd⟩
    rw [Nat.factorization_eq_zero_of_not_dvd hn3, pow_zero, mul_one] at hsform
    rw [Nat.factorization_eq_zero_of_not_dvd ht2', pow_zero, one_mul] at htform
    have heq : 2 ^ n.factorization 2 + 1 = 3 ^ (n + 1).factorization 3 := by omega
    rcases (two_pow_add_one_eq_three_pow_iff _ _).mp heq with h | h
    · right; left
      simpa [h.1] using hsform
    · right; right; right
      simpa [h.1] using hsform
  · have hn2 : ¬2 ∣ n := fun hd => h2 ⟨hd, ht2⟩
    have ht3' : ¬3 ∣ n + 1 := fun hd => h3 ⟨hs3, hd⟩
    rw [Nat.factorization_eq_zero_of_not_dvd hn2, pow_zero, one_mul] at hsform
    rw [Nat.factorization_eq_zero_of_not_dvd ht3', pow_zero, mul_one] at htform
    have heq : 3 ^ n.factorization 3 + 1 = 2 ^ (n + 1).factorization 2 := by omega
    rcases (three_pow_add_one_eq_two_pow_iff _ _).mp heq with h | h
    · simp [h.2] at hsform
      contradiction
    · right; right; left
      simpa [h.2] using hsform
  · exact False.elim (h3 ⟨hs3, ht3⟩)

private theorem smooth23_one_of_coprime {a b c : ℕ}
    (ha : Smooth23 a) (hb : Smooth23 b) (hc : Smooth23 c)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    a = 1 ∨ b = 1 ∨ c = 1 := by
  by_contra h
  have ha1 : a ≠ 1 := by tauto
  have hb1 : b ≠ 1 := by tauto
  have hc1 : c ≠ 1 := by tauto
  have h2ab := no_common_prime hab (by decide : Nat.Prime 2)
  have h3ab := no_common_prime hab (by decide : Nat.Prime 3)
  have h2ac := no_common_prime hac (by decide : Nat.Prime 2)
  have h3ac := no_common_prime hac (by decide : Nat.Prime 3)
  have h2bc := no_common_prime hbc (by decide : Nat.Prime 2)
  have h3bc := no_common_prime hbc (by decide : Nat.Prime 3)
  have has := smooth23_prime ha ha1
  have hbs := smooth23_prime hb hb1
  have hcs := smooth23_prime hc hc1
  tauto

private theorem abs_consecutive_of_sum {a b c : ℤ}
    (hs : a + b + c = 0) (ha : a.natAbs = 1) :
    b.natAbs + 1 = c.natAbs ∨ c.natAbs + 1 = b.natAbs := by
  rcases Int.natAbs_eq a with h | h <;>
    rcases Int.natAbs_eq b with h | h <;>
    rcases Int.natAbs_eq c with h | h <;> omega

theorem primitive_smooth23_bound (z : Fin 3 → ℤ)
    (hnz : ∀ i, z i ≠ 0) (hs : ∑ i, z i = 0)
    (hsmooth : ∀ i, Smooth23 (z i).natAbs)
    (hcop : ∀ i j, i ≠ j → ((z i).natAbs).Coprime (z j).natAbs) :
    ∀ i, (z i).natAbs ≤ 9 := by
  have hsum : z 0 + z 1 + z 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hs
  have hpos (i : Fin 3) : 0 < (z i).natAbs := Int.natAbs_pos.mpr (hnz i)
  have hbound {i j : Fin 3}
      (heq : (z i).natAbs + 1 = (z j).natAbs) :
      (z i).natAbs ≤ 9 ∧ (z j).natAbs ≤ 9 := by
    have ht : Smooth23 ((z i).natAbs + 1) := by rw [heq]; exact hsmooth j
    have hclass := consecutive_smooth23_classification (hpos i) (hsmooth i) ht
    omega
  have hone := smooth23_one_of_coprime (hsmooth 0) (hsmooth 1) (hsmooth 2)
    (hcop 0 1 (by decide)) (hcop 0 2 (by decide)) (hcop 1 2 (by decide))
  rcases hone with h0 | h1 | h2
  · have hc := abs_consecutive_of_sum hsum h0
    rcases hc with hc | hc
    · have hb := hbound (i := 1) (j := 2) hc
      intro i
      fin_cases i
      · change (z 0).natAbs ≤ 9
        rw [h0]
        decide
      · exact hb.1
      · exact hb.2
    · have hb := hbound (i := 2) (j := 1) hc
      intro i
      fin_cases i
      · change (z 0).natAbs ≤ 9
        rw [h0]
        decide
      · exact hb.2
      · exact hb.1
  · have hc := abs_consecutive_of_sum (a := z 1) (b := z 0) (c := z 2) (by omega) h1
    rcases hc with hc | hc
    · have hb := hbound (i := 0) (j := 2) hc
      intro i
      fin_cases i
      · exact hb.1
      · change (z 1).natAbs ≤ 9
        rw [h1]
        decide
      · exact hb.2
    · have hb := hbound (i := 2) (j := 0) hc
      intro i
      fin_cases i
      · exact hb.2
      · change (z 1).natAbs ≤ 9
        rw [h1]
        decide
      · exact hb.1
  · have hc := abs_consecutive_of_sum (a := z 2) (b := z 0) (c := z 1) (by omega) h2
    rcases hc with hc | hc
    · have hb := hbound (i := 0) (j := 1) hc
      intro i
      fin_cases i
      · exact hb.1
      · exact hb.2
      · change (z 2).natAbs ≤ 9
        rw [h2]
        decide
    · have hb := hbound (i := 1) (j := 0) hc
      intro i
      fin_cases i
      · exact hb.2
      · exact hb.1
      · change (z 2).natAbs ≤ 9
        rw [h2]
        decide

private theorem integer_sunit_smooth (z : ℤ) (u : fixedSUnitGroup)
    (hu : ((u : ℚˣ) : ℚ) = (z : ℚ)) : Smooth23 z.natAbs := by
  intro p hp hd
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  by_cases hp3 : p = 3
  · exact Or.inr hp3
  letI : Fact p.Prime := ⟨hp⟩
  have hnorm : padicNorm p (z : ℚ) = 1 := by
    rw [← hu]
    exact fixed_sunit_norm_outside p hp2 hp3 u
  have hnot := (padicNorm.int_eq_one_iff (p := p) z).mp hnorm
  exact False.elim (hnot (Int.natCast_dvd.mpr hd))

private theorem natAbs_coprime_of_bezout {a b u v : ℤ}
    (h : u * a + v * b = 1) : a.natAbs.Coprime b.natAbs := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  change Int.gcd a b = 1
  apply Nat.dvd_one.mp
  apply Int.gcd_dvd_iff.mpr
  exact ⟨u, v, by simpa only [Nat.cast_one, mul_comm] using h.symm⟩

def primitiveSmooth23Triples : Set (Fin 3 → ℤ) :=
  {z | (∀ i, z i ≠ 0) ∧ (∑ i, z i = 0) ∧ (∀ i, Smooth23 (z i).natAbs) ∧
    ∀ i j, i ≠ j → ((z i).natAbs).Coprime (z j).natAbs}

theorem exists_primitive_smooth23_triple {x : Fin 3 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 2) :
    ∃ z ∈ primitiveSmooth23Triples, ∃ s : fixedSUnitGroup,
      ∀ i, (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i := by
  obtain ⟨y, s, hy, _, hyscale, _⟩ := exists_primitive_sunit_pair hx
  let z : Fin 3 → ℤ := ![y 0, y 1, -y 0 - y 1]
  have hsumx : x 0 + x 1 + x 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hx.2.2.1
  have hscale (i : Fin 3) : (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i := by
    have h0 := hyscale 0
    have h1 := hyscale 1
    change (y 0 : ℚ) = ((s : ℚˣ) : ℚ) * x 0 at h0
    change (y 1 : ℚ) = ((s : ℚˣ) : ℚ) * x 1 at h1
    fin_cases i
    · exact h0
    · exact h1
    · change ((-y 0 - y 1 : ℤ) : ℚ) = ((s : ℚˣ) : ℚ) * x 2
      push_cast
      have hmul : ((s : ℚˣ) : ℚ) * (x 0 + x 1 + x 2) = 0 := by
        rw [hsumx, mul_zero]
      nlinarith [hmul, h0, h1]
  have hunit (i : Fin 3) :
      ∃ u : fixedSUnitGroup, ((u : ℚˣ) : ℚ) = (z i : ℚ) := by
    obtain ⟨u, hu⟩ := hx.2.1 i
    exact ⟨s * u, by simp only [Subgroup.coe_mul, Units.val_mul, hu, hscale]⟩
  have hnz (i : Fin 3) : z i ≠ 0 := by
    obtain ⟨u, hu⟩ := hunit i
    intro hz
    have hu0 : ((u : ℚˣ) : ℚ) = 0 := by simp [hz] at hu
    exact Units.ne_zero _ hu0
  have hsmooth (i : Fin 3) : Smooth23 (z i).natAbs := by
    obtain ⟨u, hu⟩ := hunit i
    exact integer_sunit_smooth _ u hu
  obtain ⟨c, hc⟩ := hy
  have hb : c 0 * y 0 + c 1 * y 1 = 1 := by
    simpa [Fin.sum_univ_succ] using hc
  have h01 : ((z 0).natAbs).Coprime (z 1).natAbs :=
    natAbs_coprime_of_bezout hb
  have h02 : ((z 0).natAbs).Coprime (z 2).natAbs := by
    apply natAbs_coprime_of_bezout (u := c 0 - c 1) (v := -c 1)
    dsimp [z]
    nlinarith [hb]
  have h12 : ((z 1).natAbs).Coprime (z 2).natAbs := by
    apply natAbs_coprime_of_bezout (u := c 1 - c 0) (v := -c 0)
    dsimp [z]
    nlinarith [hb]
  have hcop : ∀ i j : Fin 3, i ≠ j → ((z i).natAbs).Coprime (z j).natAbs := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hij rfl)
      | exact h01
      | exact h02
      | exact h12
      | exact h01.symm
      | exact h02.symm
      | exact h12.symm
  refine ⟨z, ⟨hnz, ?_, hsmooth, hcop⟩, s, hscale⟩
  simp [z, Fin.sum_univ_succ]

theorem primitive_smooth23_triples_finite : primitiveSmooth23Triples.Finite := by
  have hbox : (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-9 : ℤ) 9)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  apply hbox.subset
  intro z hz
  have hbound := primitive_smooth23_bound z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  intro i _
  have hb := hbound i
  rcases Int.natAbs_eq (z i) with h | h <;> constructor <;> omega

theorem fixed_three_term_finite :
    (normalizedRelations fixedSUnitGroup 2).Finite := by
  let point : (Fin 3 → ℤ) → Fin 3 → ℚ := fun z i => (z i : ℚ) / (z 0 : ℚ)
  apply (primitive_smooth23_triples_finite.image point).subset
  intro x hx
  obtain ⟨z, hz, s, hscale⟩ := exists_primitive_smooth23_triple hx
  refine ⟨z, hz, ?_⟩
  funext i
  dsimp [point]
  rw [hscale i, hscale 0, hx.1, mul_one]
  exact mul_div_cancel_left₀ (x i) (Units.ne_zero _)


private theorem primitive_triple_reduction (z : Fin 3 → ℤ) (hz0 : z 0 ≠ 0) :
    ∃ g : ℕ, 0 < g ∧ (g : ℤ) ∣ z 0 ∧ ∃ y : Fin 3 → ℤ,
      PrimitiveTriple y ∧ ∀ i, z i = (g : ℤ) * y i := by
  let k := Int.gcd (z 1) (z 2)
  let g := Int.gcd (z 0) (k : ℤ)
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left _ hz0
  have hg0 : (g : ℤ) ∣ z 0 := Int.gcd_dvd_left
  have hgk : (g : ℤ) ∣ (k : ℤ) := Int.gcd_dvd_right
  have hg1 : (g : ℤ) ∣ z 1 := hgk.trans (Int.gcd_dvd_left)
  have hg2 : (g : ℤ) ∣ z 2 := hgk.trans (Int.gcd_dvd_right)
  obtain ⟨y0, hy0⟩ := hg0
  obtain ⟨y1, hy1⟩ := hg1
  obtain ⟨y2, hy2⟩ := hg2
  let y : Fin 3 → ℤ := ![y0, y1, y2]
  have hscale (i : Fin 3) : z i = (g : ℤ) * y i := by
    fin_cases i <;> assumption
  let a := Int.gcdA (z 0) (k : ℤ)
  let b := Int.gcdB (z 0) (k : ℤ)
  let c := Int.gcdA (z 1) (z 2)
  let d := Int.gcdB (z 1) (z 2)
  have hgbez : (g : ℤ) = z 0 * a + (k : ℤ) * b := Int.gcd_eq_gcd_ab _ _
  have hkbez : (k : ℤ) = z 1 * c + z 2 * d := Int.gcd_eq_gcd_ab _ _
  have hcoeff : (g : ℤ) * (a * y0 + (b * c) * y1 + (b * d) * y2) = (g : ℤ) * 1 := by
    calc
      _ = z 0 * a + (k : ℤ) * b := by rw [hkbez, hy0, hy1, hy2]; ring
      _ = _ := by rw [← hgbez]; ring
  have hgneq : (g : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
  have hprimitive : PrimitiveTriple y := by
    refine ⟨![a, b * c, b * d], ?_⟩
    simpa [y, Fin.sum_univ_succ, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
      add_assoc] using mul_left_cancel₀ hgneq hcoeff
  exact ⟨g, hg, Int.gcd_dvd_left, y, hprimitive, hscale⟩

private theorem smooth23_nat_unit {g : ℕ} (hg : g ≠ 0) (hs : Smooth23 g) :
    ∃ u : fixedSUnitGroup, ((u : ℚˣ) : ℚ) = (g : ℚ) := by
  have htwo : twoUnit ∈ fixedSUnitGroup := Subgroup.subset_closure (by simp)
  have hthree : threeUnit ∈ fixedSUnitGroup := Subgroup.subset_closure (by simp)
  refine ⟨⟨twoUnit ^ g.factorization 2 * threeUnit ^ g.factorization 3,
    fixedSUnitGroup.mul_mem (fixedSUnitGroup.pow_mem htwo _) (fixedSUnitGroup.pow_mem hthree _)⟩, ?_⟩
  have h := smooth23_factorization hg hs
  have hc := congrArg ((↑) : ℕ → ℚ) h
  simpa [twoUnit, threeUnit] using hc.symm

theorem exists_primitive_sunit_triple {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    ∃ z : Fin 3 → ℤ, ∃ s : fixedSUnitGroup,
      PrimitiveTriple z ∧ z ≠ 0 ∧
      ∀ i : Fin 3, (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i.castSucc := by
  obtain ⟨u1, hu1⟩ := hx.2.1 1
  obtain ⟨u2, hu2⟩ := hx.2.1 2
  obtain ⟨s1, hs1⟩ := sunit_denominator u1
  obtain ⟨s2, hs2⟩ := sunit_denominator u2
  have hd1 : ((s1 : ℚˣ) : ℚ) = ((x 1).den : ℚ) := by simpa [hu1] using hs1
  have hd2 : ((s2 : ℚˣ) : ℚ) = ((x 2).den : ℚ) := by simpa [hu2] using hs2
  let D : ℕ := (x 1).den * (x 2).den
  let s0 : fixedSUnitGroup := s1 * s2
  let w : Fin 3 → ℤ := ![(D : ℤ), (x 1).num * (x 2).den, (x 2).num * (x 1).den]
  have hs0 : ((s0 : ℚˣ) : ℚ) = (D : ℚ) := by simp [s0, D, hd1, hd2]
  have hnum1 : ((x 1).num : ℚ) = ((x 1).den : ℚ) * x 1 := by
    have h := integralPair_scale (x 1) (1 : Fin 2)
    exact h
  have hnum2 : ((x 2).num : ℚ) = ((x 2).den : ℚ) * x 2 := by
    have h := integralPair_scale (x 2) (1 : Fin 2)
    exact h
  have hw (i : Fin 3) : (w i : ℚ) = ((s0 : ℚˣ) : ℚ) * x i.castSucc := by
    rw [hs0]
    fin_cases i
    · simp [w, hx.1]
    · change (((x 1).num * ((x 2).den : ℤ) : ℤ) : ℚ) = (D : ℚ) * x 1
      push_cast
      rw [hnum1]
      dsimp [D]
      push_cast
      ring
    · change (((x 2).num * ((x 1).den : ℤ) : ℤ) : ℚ) = (D : ℚ) * x 2
      push_cast
      rw [hnum2]
      dsimp [D]
      push_cast
      ring
  have hD : D ≠ 0 := mul_ne_zero (Rat.den_ne_zero _) (Rat.den_ne_zero _)
  have hw0 : w 0 ≠ 0 := by
    change (D : ℤ) ≠ 0
    exact_mod_cast hD
  obtain ⟨g, hg, hgdvd, z, hz, hscale⟩ := primitive_triple_reduction w hw0
  have hgD : g ∣ D := Int.natCast_dvd_natCast.mp hgdvd
  have hgsmooth : Smooth23 g := by
    intro p hp hpg
    rcases hp.dvd_mul.mp (hpg.trans hgD) with hp1 | hp2
    · apply sunit_den_prime_support u1 p hp
      simpa [hu1] using hp1
    · apply sunit_den_prime_support u2 p hp
      simpa [hu2] using hp2
  obtain ⟨ug, hug⟩ := smooth23_nat_unit (ne_of_gt hg) hgsmooth
  let s := s0 / ug
  have hzscale (i : Fin 3) : (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i.castSucc := by
    have hc := congrArg ((↑) : ℤ → ℚ) (hscale i)
    push_cast at hc
    have hsval : ((s : ℚˣ) : ℚ) = ((s0 : ℚˣ) : ℚ) / (g : ℚ) := by simp [s, hug]
    rw [hsval]
    have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hg0).mpr
    have hwi := hw i
    rw [hc] at hwi
    nlinarith [hwi]
  have hnz : z ≠ 0 := by
    intro heq
    have h0 := hzscale 0
    simp [heq, hx.1] at h0
    exact Units.ne_zero _ h0.symm
  exact ⟨z, s, hz, hnz, hzscale⟩

theorem exists_primitive_strong_triple {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    ∃ choice : Fin 3 → Fin 3, ∃ z : Fin 3 → ℤ, ∃ s : fixedSUnitGroup,
      PrimitiveTriple z ∧ z ≠ 0 ∧
      (∀ i : Fin 3, (z i : ℚ) = ((s : ℚˣ) : ℚ) * x i.castSucc) ∧
      tripleHeight (fun i => x i.castSucc) = archTripleHeight z ∧
      tripleChoiceFormsProduct choice (fun i => (z i : ℚ)) * archTripleHeight z = 1 := by
  obtain ⟨z, s, hz, hnz, hscale⟩ := exists_primitive_sunit_triple hx
  obtain ⟨choice, hret⟩ := four_term_retained_product_height hx
  have hvec : (fun i => (z i : ℚ)) = (fun i => ((s : ℚˣ) : ℚ) * x i.castSucc) :=
    funext hscale
  have hheight := primitive_triple_height z hz
  rw [hvec, tripleHeight_sunit_scale] at hheight
  refine ⟨choice, z, s, hz, hnz, hscale, hheight, ?_⟩
  rw [← hheight, hvec, tripleChoiceFormsProduct_sunit_scale]
  exact hret


theorem exists_primitive_four_term_relation {x : Fin 4 → ℚ}
    (hx : x ∈ normalizedRelations fixedSUnitGroup 3) :
    ∃ w : Fin 4 → ℤ, ∃ s : fixedSUnitGroup,
      PrimitiveTriple (fun i => w i.castSucc) ∧ (∀ i, w i ≠ 0) ∧
      (∑ i, w i = 0) ∧ Nondegenerate (fun i => (w i : ℚ)) ∧
      ∀ i, (w i : ℚ) = ((s : ℚˣ) : ℚ) * x i := by
  obtain ⟨z, s, hz, _, hscale⟩ := exists_primitive_sunit_triple hx
  let w : Fin 4 → ℤ := ![z 0, z 1, z 2, -z 0 - z 1 - z 2]
  have hsumx : x 0 + x 1 + x 2 + x 3 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hx.2.2.1
  have hw (i : Fin 4) : (w i : ℚ) = ((s : ℚˣ) : ℚ) * x i := by
    have h0 := hscale 0
    have h1 := hscale 1
    have h2 := hscale 2
    change (z 0 : ℚ) = ((s : ℚˣ) : ℚ) * x 0 at h0
    change (z 1 : ℚ) = ((s : ℚˣ) : ℚ) * x 1 at h1
    change (z 2 : ℚ) = ((s : ℚˣ) : ℚ) * x 2 at h2
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · change ((-z 0 - z 1 - z 2 : ℤ) : ℚ) = ((s : ℚˣ) : ℚ) * x 3
      push_cast
      have hmul : ((s : ℚˣ) : ℚ) * (x 0 + x 1 + x 2 + x 3) = 0 := by
        rw [hsumx, mul_zero]
      nlinarith [hmul, h0, h1, h2]
  have hfirst : (fun i : Fin 3 => w i.castSucc) = z := by
    funext i
    fin_cases i <;> rfl
  refine ⟨w, s, hfirst.symm ▸ hz, ?_, ?_, ?_, hw⟩
  · intro i hi
    obtain ⟨u, hu⟩ := hx.2.1 i
    have hx0 : x i ≠ 0 := by rw [← hu]; exact Units.ne_zero _
    have he := hw i
    rw [hi, Int.cast_zero] at he
    exact (mul_ne_zero (Units.ne_zero _) hx0) he.symm
  · simp [w, Fin.sum_univ_succ]
  · intro I hI hproper hzero
    have hfactor : (∑ i ∈ I, (w i : ℚ)) = ((s : ℚˣ) : ℚ) * ∑ i ∈ I, x i := by
      simp_rw [hw]
      rw [Finset.mul_sum]
    rw [hzero] at hfactor
    exact hx.2.2.2 I hI hproper
      ((mul_eq_zero.mp hfactor.symm).resolve_left (Units.ne_zero _))

end JSP000334
